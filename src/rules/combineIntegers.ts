import {
  findById,
  int,
  rebuildNary,
  replaceTermRespectingInvariants,
  type Equation,
  type Expr,
  type NodeId,
  type Sum,
} from "../expr.js";
import {
  idSetDiff,
  RulePreconditionViolation,
  survivorMoved,
  type Location,
  type Rule,
  type RuleApplication,
} from "../rule.js";

export interface CombineIntegersParams {
  /** Direct children of the Sum at `location`; integer literals (possibly negated). */
  readonly termA: NodeId;
  readonly termB: NodeId;
}

/** Literal value of an Integer or Neg(Integer) term, else undefined. */
export function literalValue(e: Expr): bigint | undefined {
  if (e.kind === "int") return e.value;
  if (e.kind === "neg" && e.child.kind === "int") return -e.child.value;
  return undefined;
}

function resolve(
  tree: Equation,
  location: Location,
  params: CombineIntegersParams,
): { sum: Sum; valueA: bigint; valueB: bigint } | undefined {
  const node = findById(tree, location);
  if (node === undefined || node.kind !== "sum") return undefined;
  if (params.termA === params.termB) return undefined;
  const termA = node.children.find((c) => c.id === params.termA);
  const termB = node.children.find((c) => c.id === params.termB);
  if (termA === undefined || termB === undefined) return undefined;
  const valueA = literalValue(termA);
  const valueB = literalValue(termB);
  if (valueA === undefined || valueB === undefined) return undefined;
  return { sum: node, valueA, valueB };
}

/**
 * Two integer literal terms in a Sum fold into one:
 *   x + 2 + 3  ~>  x + 5        x + 2 + (-3)  ~>  x + (-1)
 */
export const combineIntegers: Rule<CombineIntegersParams> = {
  id: "combine-integers",
  description: "Fold two integer terms of a sum into a single integer.",

  precondition(judgment, location, params) {
    return resolve(judgment.equation, location, params) !== undefined;
  },

  apply(judgment, location, params): RuleApplication {
    const tree = judgment.equation;
    const r = resolve(tree, location, params);
    if (r === undefined) {
      throw new RulePreconditionViolation(this.id, "terms are not integer literals of this sum");
    }
    const folded = int(r.valueA + r.valueB);
    // The folded literal takes termA's position; termB disappears.
    const children = r.sum.children
      .filter((c) => c.id !== params.termB)
      .map((c) => (c.id === params.termA ? folded : c));
    const rebuilt = rebuildNary(r.sum, children);
    const tree2 = replaceTermRespectingInvariants(tree, r.sum.id, rebuilt);
    // If the sum collapsed to a Neg(Integer) under a Neg parent, the
    // double-negation collapse swallowed `folded`; the merge target the UI
    // can animate to is then its bare Integer child.
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
        moved: survivorMoved(tree2, rebuilt.id, r.sum.id),
      },
    };
  },
};
