import { pinsEnv, restrictionStatus, signOf } from "../assumptions.js";
import { cloneFresh, flipRelation, fraction, type Expr } from "../expr.js";
import { Rational } from "../rational.js";
import {
  idSetDiff,
  RulePreconditionViolation,
  type Rule,
  type RuleApplication,
} from "../rule.js";

export interface DivideBothSidesParams {
  /**
   * The expression to divide by. Cloned before inserting, so callers may
   * pass subtrees of the current equation.
   */
  readonly divisor: Expr;
}

/**
 * Divide one side. A Fraction extends its denominator; a Product spreads its
 * factors into the numerator LIST — (3·x)/3 with 3 and x as separate
 * elements, not one lump — so multiplicative-cancellation can pair the
 * divisor with the factor it came from. Anything else becomes a fraction.
 */
function divideSide(side: Expr, divisor: Expr): Expr {
  // A Product divisor spreads into the list (fraction lists never hold
  // direct Products; the ctor enforces it for the other arms).
  const divisorParts = divisor.kind === "product" ? divisor.children : [divisor];
  if (side.kind === "fraction") return { ...side, den: [...side.den, ...divisorParts] };
  if (side.kind === "product") return fraction([...side.children], [divisor]);
  return fraction([side], [divisor]);
}

/**
 * Divides both sides by a user-chosen expression — a solution-LOSING move:
 * wherever the divisor is 0 the new equation says nothing, so the rule emits
 * Restriction(divisor ≠ 0). The precondition rejects divisors that decidably
 * ARE zero (a constant 0, or zero under current Pinned values); everything
 * else is allowed and the restriction travels with the judgment.
 */
export const divideBothSides: Rule<DivideBothSidesParams> = {
  id: "divide-both-sides",
  description: "Divide both sides of the equation by an expression (emits ≠ 0).",

  precondition(judgment, location, params) {
    if (location !== judgment.equation.id) return false;
    const pins = pinsEnv(judgment.assumptions);
    if (judgment.equation.relation !== "=") {
      // Inequalities need a decidable sign: positive keeps the relation,
      // negative flips it, unknown forbids the move (no sign analysis yet).
      const sign = signOf(params.divisor, pins);
      return sign === "positive" || sign === "negative";
    }
    const status = restrictionStatus(
      { expr: params.divisor, value: Rational.zero },
      pins,
    );
    return status !== "fails";
  },

  apply(judgment, location, params): RuleApplication {
    if (!this.precondition(judgment, location, params)) {
      throw new RulePreconditionViolation(
        this.id,
        "divisor is decidably zero, or location is not the equation root",
      );
    }
    const tree = judgment.equation;
    const flips =
      tree.relation !== "=" &&
      signOf(params.divisor, pinsEnv(judgment.assumptions)) === "negative";
    const tree2 = {
      ...tree,
      relation: flips ? flipRelation(tree.relation) : tree.relation,
      lhs: divideSide(tree.lhs, cloneFresh(params.divisor)),
      rhs: divideSide(tree.rhs, cloneFresh(params.divisor)),
    };
    return {
      equation: tree2,
      emits: [
        { kind: "restriction", expr: params.divisor, relation: "≠", value: Rational.zero },
      ],
      diff: { ...idSetDiff(tree, tree2), merged: [], moved: [] },
    };
  },
};
