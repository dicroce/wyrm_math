import { pinsEnv, restrictionStatus, signOf } from "../assumptions.js";
import { cloneFresh, flipRelation, fraction, neg, type Expr } from "../expr.js";
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
 * The elements an expression contributes to a fraction list. A Product
 * spreads — (3·x)/3 holds 3 and x as separate elements, not one lump, so
 * multiplicative-cancellation can pair the divisor with the factor it came
 * from — and so does a Neg over a Product: −5y is the same signed product as
 * (−5)·y wearing a different hat, with the sign on its leading factor (the
 * convention `divisorCandidates` in moves.ts enumerates by). Without that arm
 * ÷−5 on Neg(Product(5, y)) lands on a dead end: (−5y)/(−5) with nothing to
 * cancel. Anything else is its own single element.
 */
function factorList(e: Expr): Expr[] {
  if (e.kind === "product") return [...e.children];
  if (e.kind === "neg" && e.child.kind === "product") {
    const [head, ...rest] = e.child.children;
    // The Neg keeps its id when it can host the leading factor directly, so
    // the minus glides instead of fading; a Neg head would double up, so
    // there the ctor collapses it into a fresh node instead.
    const signed = head!.kind === "neg" ? neg(head!) : { ...e, child: head! };
    return [signed, ...rest];
  }
  return [e];
}

/** Divide one side: a Fraction extends its denominator, anything else becomes
 *  a fraction over the divisor (both lists spread per `factorList`). */
function divideSide(side: Expr, divisor: Expr): Expr {
  const divisorParts = factorList(divisor);
  if (side.kind === "fraction") return { ...side, den: [...side.den, ...divisorParts] };
  return fraction(factorList(side), divisorParts);
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
