import {
  cloneFresh,
  findById,
  fraction,
  product,
  rebuildNary,
  replaceTermRespectingInvariants,
  sum,
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

export interface CombineFractionsParams {
  /** A Fraction child of the Sum at `location`. */
  readonly termA: NodeId;
  /** Another child — a Fraction, or a whole term treated as itself over 1. */
  readonly termB: NodeId;
}

/** A term as (numerator list, denominator list); a non-fraction is e over 1. */
function parts(e: Expr): { num: readonly Expr[]; den: readonly Expr[] } {
  return e.kind === "fraction" ? { num: e.num, den: e.den } : { num: [e], den: [] };
}

function resolve(
  tree: Equation,
  location: Location,
  params: CombineFractionsParams,
): { sum: Sum; termA: Expr; termB: Expr } | undefined {
  const node = findById(tree, location);
  if (node === undefined || node.kind !== "sum") return undefined;
  if (params.termA === params.termB) return undefined;
  const termA = node.children.find((c) => c.id === params.termA);
  const termB = node.children.find((c) => c.id === params.termB);
  if (termA === undefined || termB === undefined) return undefined;
  // termA carries the denominator; enumeration always puts a Fraction here.
  if (termA.kind !== "fraction") return undefined;
  return { sum: node, termA, termB };
}

/**
 * Add two terms of a Sum over a common denominator — the missing
 * unlike-denominator case (x/2 + x/3 had no path):
 *   a/b + c/d  ~>  (a·d + c·b)/(b·d)        x/2 + 3  ~>  (x + 3·2)/2
 * Exact: a/b + c/d and (ad+cb)/(bd) are undefined at exactly the same points
 * (b·d = 0 iff b = 0 or d = 0), so nothing is gained or lost — emits nothing.
 * The cross-products and shared denominator are fresh clones; the combining
 * terms are consumed, so no bystander ids move.
 */
export const combineFractions: Rule<CombineFractionsParams> = {
  id: "combine-fractions",
  description: "Add two fraction terms of a sum over a common denominator.",

  precondition(judgment, location, params) {
    return resolve(judgment.equation, location, params) !== undefined;
  },

  apply(judgment, location, params): RuleApplication {
    const tree = judgment.equation;
    const r = resolve(tree, location, params);
    if (r === undefined) {
      throw new RulePreconditionViolation(this.id, "termA is not a fraction sibling of termB");
    }
    const a = parts(r.termA);
    const b = parts(r.termB);
    // (a·d) + (c·b) over (b·d). Clone everything: both source terms are
    // consumed, and a denominator appears in both a cross-product and the bar.
    const cross1 = product([...a.num, ...b.den].map(cloneFresh));
    const cross2 = product([...b.num, ...a.den].map(cloneFresh));
    const result = fraction([sum([cross1, cross2])], [...a.den, ...b.den].map(cloneFresh));

    const children = r.sum.children
      .filter((c) => c.id !== r.termB.id)
      .map((c) => (c.id === r.termA.id ? result : c));
    const rebuilt = rebuildNary(r.sum, children);
    const tree2 = replaceTermRespectingInvariants(tree, r.sum.id, rebuilt);
    const mergeTarget = findById(tree2, result.id) !== undefined ? result.id : r.sum.id;
    return {
      equation: tree2,
      emits: [],
      diff: {
        ...idSetDiff(tree, tree2),
        merged: [{ sources: [r.termA.id, r.termB.id], target: mergeTarget }],
        moved: survivorMoved(tree2, rebuilt.id, r.sum.id),
      },
    };
  },
};
