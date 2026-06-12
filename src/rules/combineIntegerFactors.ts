import {
  findById,
  int,
  rebuildNary,
  replaceTermRespectingInvariants,
  type Equation,
  type NodeId,
  type Product,
} from "../expr.js";
import {
  idSetDiff,
  RulePreconditionViolation,
  survivorMoved,
  type Location,
  type Rule,
  type RuleApplication,
} from "../rule.js";
import { literalValue } from "./combineIntegers.js";

export interface CombineIntegerFactorsParams {
  /** Direct children of the Product at `location`; integer literals (possibly negated). */
  readonly termA: NodeId;
  readonly termB: NodeId;
}

function resolve(
  tree: Equation,
  location: Location,
  params: CombineIntegerFactorsParams,
): { product: Product; valueA: bigint; valueB: bigint } | undefined {
  const node = findById(tree, location);
  if (node === undefined || node.kind !== "product") return undefined;
  if (params.termA === params.termB) return undefined;
  const termA = node.children.find((c) => c.id === params.termA);
  const termB = node.children.find((c) => c.id === params.termB);
  if (termA === undefined || termB === undefined) return undefined;
  const valueA = literalValue(termA);
  const valueB = literalValue(termB);
  if (valueA === undefined || valueB === undefined) return undefined;
  return { product: node, valueA, valueB };
}

/**
 * Two integer literal factors of a Product fold into one — the
 * multiplicative twin of combine-integers:
 *   3 · 2 · x  ~>  6x        x · 2 · (−3)  ~>  x · (−6)
 */
export const combineIntegerFactors: Rule<CombineIntegerFactorsParams> = {
  id: "combine-integer-factors",
  description: "Fold two integer factors of a product into a single integer.",

  precondition(judgment, location, params) {
    return resolve(judgment.equation, location, params) !== undefined;
  },

  apply(judgment, location, params): RuleApplication {
    const tree = judgment.equation;
    const r = resolve(tree, location, params);
    if (r === undefined) {
      throw new RulePreconditionViolation(
        this.id,
        "terms are not integer literal factors of this product",
      );
    }
    const folded = int(r.valueA * r.valueB);
    // The folded literal takes termA's position; termB disappears.
    const children = r.product.children
      .filter((c) => c.id !== params.termB)
      .map((c) => (c.id === params.termA ? folded : c));
    const rebuilt = rebuildNary(r.product, children);
    const tree2 = replaceTermRespectingInvariants(tree, r.product.id, rebuilt);
    // If the product collapsed to Neg(Integer) under a Neg parent, the
    // double-negation collapse swallowed `folded`; merge onto its child.
    const mergeTarget =
      findById(tree2, folded.id) !== undefined
        ? folded.id
        : folded.kind === "neg"
          ? folded.child.id
          : folded.id;
    return {
      equation: tree2,
      emits: [],
      diff: {
        ...idSetDiff(tree, tree2),
        merged: [{ sources: [params.termA, params.termB], target: mergeTarget }],
        moved: survivorMoved(tree2, rebuilt.id, r.product.id),
      },
    };
  },
};
