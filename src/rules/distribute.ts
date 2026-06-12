import {
  cloneFresh,
  findById,
  findParent,
  product,
  rebuildNary,
  replaceTermRespectingInvariants,
  type Equation,
  type Expr,
  type NodeId,
  type Product,
  type Sum,
} from "../expr.js";
import {
  idSetDiff,
  RulePreconditionViolation,
  type Location,
  type Rule,
  type RuleApplication,
} from "../rule.js";

export interface DistributeParams {
  /** The factor to push in — any direct child of the Product at `location`. */
  readonly factorId: NodeId;
  /** A Sum that is a direct sibling factor. */
  readonly sumId: NodeId;
}

function resolve(
  tree: Equation,
  location: Location,
  params: DistributeParams,
): { product: Product; factor: Expr; sum: Sum } | undefined {
  const node = findById(tree, location);
  if (node === undefined || node.kind !== "product") return undefined;
  if (params.factorId === params.sumId) return undefined;
  const factor = node.children.find((c) => c.id === params.factorId);
  const sum = node.children.find((c) => c.id === params.sumId);
  if (factor === undefined || sum === undefined || sum.kind !== "sum") return undefined;
  return { product: node, factor, sum };
}

/**
 * Push one factor of a Product into a Sum sibling:
 *   2·(x + 3) ~> 2x + 2·3        y·2·(x + 3) ~> y·(2x + 2·3)
 * The factor survives by identity inside the FIRST term (its other copies
 * are fresh clones that fade in); the Sum keeps its id; every original term
 * keeps its id inside its new product. Exactly solution-preserving. The
 * inverse is factor-out.
 */
export const distribute: Rule<DistributeParams> = {
  id: "distribute",
  description: "Distribute a factor over a sum.",

  precondition(judgment, location, params) {
    return resolve(judgment.equation, location, params) !== undefined;
  },

  apply(judgment, location, params): RuleApplication {
    const tree = judgment.equation;
    const r = resolve(tree, location, params);
    if (r === undefined) {
      throw new RulePreconditionViolation(
        this.id,
        "location is not a product with the given factor and sum children",
      );
    }
    const terms = r.sum.children.map((t, i) =>
      product([i === 0 ? r.factor : cloneFresh(r.factor), t]),
    );
    const newSum: Sum = { ...r.sum, children: terms };
    const children = r.product.children
      .filter((c) => c.id !== params.factorId)
      .map((c) => (c.id === params.sumId ? (newSum as Expr) : c));
    const rebuilt = rebuildNary(r.product, children);
    const tree2 = replaceTermRespectingInvariants(tree, r.product.id, rebuilt);
    const factorParent = findParent(tree2, r.factor.id);
    return {
      equation: tree2,
      emits: [],
      diff: {
        ...idSetDiff(tree, tree2),
        merged: [],
        moved:
          factorParent === undefined
            ? []
            : [{ id: r.factor.id, from: r.product.id, to: factorParent.id }],
      },
    };
  },
};
