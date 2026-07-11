/**
 * Undo an nth power for n >= 3 — the general-degree companion to
 * sqrt-both-sides (which owns n = 2, including its surd results).
 *
 * Satisfies the UNION property (property-tested): the branches' solution sets
 * union to the original's. aⁿ = c has real solutions exactly {r} when n is odd
 * and {r, −r} when n is even (r = the real nth root of c), because an odd power
 * is injective and an even power is even-symmetric. The move is offered only
 * where c has an exact rational nth root; irrational roots (∛7) await a
 * symbolic radical representation and are simply not offered yet.
 */
import { type Equation, type Expr } from "../expr.js";
import { constantRational, nthRootRational, rationalToExpr } from "../eval.js";
import { Rational } from "../rational.js";
import {
  idSetDiff,
  RulePreconditionViolation,
  type BranchingRule,
  type BranchOutcome,
} from "../rule.js";

type NoParams = Record<string, never>;

/** lhs = base^n with n an integer >= 3 and rhs a constant that has an exact
 *  real nth root. Squares stay with sqrt-both-sides. */
function rootData(
  eqn: Equation,
): { base: Expr; even: boolean; root: Rational } | undefined {
  if (eqn.relation !== "=") return undefined;
  const lhs = eqn.lhs;
  if (lhs.kind !== "pow") return undefined;
  if (lhs.exp.kind !== "int" || lhs.exp.value < 3n) return undefined;
  const n = lhs.exp.value;
  const value = constantRational(eqn.rhs);
  if (value === undefined) return undefined;
  const root = nthRootRational(value, n);
  if (root === undefined) return undefined;
  return { base: lhs.base, even: n % 2n === 0n, root };
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
        "left side is not a perfect nth power equal to a constant",
      );
    }
    const { base, even, root } = data;
    // The base is reused by identity across branches — separate trees, so
    // sharing is safe and id-keyed animation tracks it into either branch.
    const branch = (label: string, value: Rational): BranchOutcome => {
      const next: Equation = { ...tree, lhs: base, rhs: rationalToExpr(value) };
      return {
        label,
        equation: next,
        emits: [],
        diff: { ...idSetDiff(tree, next), merged: [], moved: [] },
      };
    };
    // Odd degree: one real root. Even degree: ± (except the degenerate 0).
    if (!even || root.isZero()) {
      return [branch("nth root", root)];
    }
    return [branch("positive root", root), branch("negative root", root.neg())];
  },
};
