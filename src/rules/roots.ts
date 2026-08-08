/**
 * Undo an nth power for n >= 3 — the general-degree companion to
 * sqrt-both-sides (which owns n = 2). The nth root is left SYMBOLIC (ⁿ√c),
 * exactly as sqrt leaves √c, so `simplify-nth-root` is the natural follow-up
 * that evaluates a perfect power. Because the radical is symbolic, an exact
 * root is NOT required — ∛7 is offered and simply stays a radical.
 *
 * Satisfies the UNION property (property-tested): the branches' solution sets
 * union to the original's. aⁿ = c has real solutions {r} for odd n and {r, −r}
 * for even n (r = the real nth root of c), because an odd power is injective and
 * an even power is even-symmetric; where c < 0 and n is even the radical is an
 * undefined point (no real root) and the branches claim nothing — sound.
 */
import {
  findById,
  neg,
  replaceTermRespectingInvariants,
  root,
  type Equation,
  type Expr,
} from "../expr.js";
import { constantRational, nthRootRational, rationalToExpr } from "../eval.js";
import {
  idSetDiff,
  RulePreconditionViolation,
  type BranchingRule,
  type BranchOutcome,
  type Rule,
  type RuleApplication,
} from "../rule.js";

type NoParams = Record<string, never>;

/** lhs = base^n with n an integer >= 3 and rhs a rational constant. Squares
 *  stay with sqrt-both-sides. Exactness is NOT required — the root stays
 *  symbolic. */
function rootData(eqn: Equation): { base: Expr; index: bigint; even: boolean } | undefined {
  if (eqn.relation !== "=") return undefined;
  const lhs = eqn.lhs;
  if (lhs.kind !== "pow") return undefined;
  if (lhs.exp.kind !== "int" || lhs.exp.value < 3n) return undefined;
  if (constantRational(eqn.rhs) === undefined) return undefined; // rhs must be a rational constant
  const n = lhs.exp.value;
  return { base: lhs.base, index: n, even: n % 2n === 0n };
}

export const nthRootBothSides: BranchingRule<NoParams> = {
  id: "nth-root-both-sides",
  description: "Take the nth root of both sides (± for even n).",

  precondition(judgment, location, _params) {
    return (
      location === judgment.equation.id && rootData(judgment.equation) !== undefined
    );
  },

  apply(judgment, location, _params): readonly BranchOutcome[] {
    const tree = judgment.equation;
    const data = location === tree.id ? rootData(tree) : undefined;
    if (data === undefined) {
      throw new RulePreconditionViolation(
        this.id,
        "left side is not base^n (n>=3) equal to a rational constant",
      );
    }
    const { base, index, even } = data;
    // The base is reused by identity across branches — separate trees, so
    // sharing is safe and id-keyed animation tracks it into either branch.
    const branch = (label: string, radical: Expr): BranchOutcome => {
      const next: Equation = { ...tree, lhs: base, rhs: radical };
      return {
        label,
        equation: next,
        emits: [],
        diff: { ...idSetDiff(tree, next), merged: [], moved: [] },
      };
    };
    // Odd degree: one real root. Even degree: ± (except the degenerate 0).
    const c = constantRational(tree.rhs)!; // defined by the precondition
    if (!even || c.isZero()) {
      return [branch("nth root", root(index, tree.rhs))];
    }
    return [
      branch("positive root", root(index, tree.rhs)),
      branch("negative root", neg(root(index, tree.rhs))),
    ];
  },
};

/** Tap a perfect nth-root radical to evaluate it: ∛64 → 4, ⁴√16 → 2,
 *  ∛(−8) → −2. Fires only when the radicand has an exact rational nth root; an
 *  irrational radical (∛7) is already in simplest form and offers nothing. */
export const simplifyNthRoot: Rule<NoParams> = {
  id: "simplify-nth-root",
  description: "Simplify an nth root by evaluating a perfect nth power.",

  precondition(judgment, location, _params) {
    const node = findById(judgment.equation, location);
    if (node === undefined || node.kind !== "root") return false;
    const value = constantRational(node.radicand);
    return value !== undefined && nthRootRational(value, node.index) !== undefined;
  },

  apply(judgment, location, _params): RuleApplication {
    const tree = judgment.equation;
    const node = findById(tree, location);
    if (node === undefined || node.kind !== "root") {
      throw new RulePreconditionViolation(this.id, "not an nth-root radical");
    }
    const value = constantRational(node.radicand);
    const r = value !== undefined ? nthRootRational(value, node.index) : undefined;
    if (r === undefined) {
      throw new RulePreconditionViolation(this.id, "radicand is not a perfect nth power");
    }
    const simplified = rationalToExpr(r);
    const tree2 = replaceTermRespectingInvariants(tree, node.id, simplified);
    return {
      equation: tree2,
      emits: [],
      diff: {
        ...idSetDiff(tree, tree2),
        merged: [{ sources: [location], target: simplified.id }],
        moved: [],
      },
    };
  },
};
