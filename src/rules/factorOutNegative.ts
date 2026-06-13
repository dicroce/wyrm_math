import {
  findById,
  findParent,
  neg,
  replaceNode,
  sum,
  type Equation,
  type Sum,
} from "../expr.js";
import {
  idSetDiff,
  RulePreconditionViolation,
  type Location,
  type Rule,
  type RuleApplication,
} from "../rule.js";

// No params: the Sum at `location` is the whole input (a tap move).
export type FactorOutNegativeParams = Record<string, never>;

/**
 * Offered on a Sum that is a factor of a Product whose OTHER factor carries a
 * negative — exactly the spot where pulling the −1 out lets the two negatives
 * cancel. (1 − 2x)·(−3) qualifies; (x + 3)·2 does not.
 */
function resolve(tree: Equation, location: Location): { sum: Sum } | undefined {
  const node = findById(tree, location);
  if (node === undefined || node.kind !== "sum") return undefined;
  const parent = findParent(tree, location);
  if (parent === undefined || parent.kind !== "product") return undefined;
  const hasNegSibling = parent.children.some((c) => c.id !== node.id && c.kind === "neg");
  return hasNegSibling ? { sum: node } : undefined;
}

/**
 * Factor −1 out of a sum — negate every term and hang a Neg outside:
 *   1 − 2x  ~>  −(−1 + 2x)        x + 3  ~>  −(−x − 3)
 * An exact identity (double negation), so it emits nothing. The crucial move
 * for factoring by grouping when the leading coefficient ≠ 1: it flips a
 * group's binomial to match its neighbour's sign, e.g. (1−2x) into a form
 * structurally equal to (2x−1), so the shared factor can be pulled out.
 * Each term's body survives by identity (neg() reuses the term, or unwraps a
 * Neg); only the Neg wrappers change. The inner sum keeps the original id.
 */
export const factorOutNegative: Rule<FactorOutNegativeParams> = {
  id: "factor-out-negative",
  description: "Factor −1 out of a sum (a + b ~> −(−a − b)).",

  precondition(judgment, location) {
    return resolve(judgment.equation, location) !== undefined;
  },

  apply(judgment, location): RuleApplication {
    const tree = judgment.equation;
    const r = resolve(tree, location);
    if (r === undefined) {
      throw new RulePreconditionViolation(
        this.id,
        "not a sum factoring a product with a negative sibling",
      );
    }
    // Negate each term (neg() unwraps a Neg or wraps the rest), keep the
    // sum's id on the inner sum, hang one Neg outside.
    const inner = sum(r.sum.children.map((c) => neg(c)));
    const innerWithId = inner.kind === "sum" ? { ...inner, id: r.sum.id } : inner;
    const result = neg(innerWithId);
    const tree2 = replaceNode(tree, r.sum.id, result);
    return {
      equation: tree2,
      emits: [],
      diff: {
        ...idSetDiff(tree, tree2),
        merged: [],
        moved: [],
      },
    };
  },
};
