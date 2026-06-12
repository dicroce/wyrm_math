import { pinsEnv, signOf } from "../assumptions.js";
import {
  cloneFresh,
  exprToString,
  flipRelation,
  product,
  rebuildNary,
  type Expr,
} from "../expr.js";
import {
  idSetDiff,
  RulePreconditionViolation,
  type Rule,
  type RuleApplication,
} from "../rule.js";

export interface MultiplyBothSidesParams {
  /** Cloned before inserting, so callers may pass subtrees of the equation. */
  readonly factor: Expr;
}

/**
 * Multiply one side. A Fraction side absorbs the factor into its numerator —
 * (x/2)·2 and (x·2)/2 are the same value, but only the latter puts the factor
 * where multiplicative-cancellation can reach it, which is the whole point of
 * the clear-the-denominator gesture. Products extend in place (id preserved);
 * anything else wraps in a new Product.
 */
function multiplySide(side: Expr, factor: Expr): Expr {
  if (side.kind === "fraction") {
    const factorParts = factor.kind === "product" ? factor.children : [factor];
    return { ...side, num: [...side.num, ...factorParts] };
  }
  if (side.kind === "product") return rebuildNary(side, [...side.children, factor]);
  return product([side, factor]);
}

/**
 * Multiplies both sides by a user-chosen expression — a solution-GAINING
 * move: wherever the factor is 0 the new equation is trivially true, so it
 * may admit solutions the original does not. The rule therefore emits an
 * Extension carrying the pre-move equation; the derivation is not settled
 * until candidate solutions are checked against it (checkSolution).
 */
export const multiplyBothSides: Rule<MultiplyBothSidesParams> = {
  id: "multiply-both-sides",
  description: "Multiply both sides of the equation by an expression (emits an obligation).",

  precondition(judgment, location, params) {
    if (location !== judgment.equation.id) return false;
    if (judgment.equation.relation === "=") {
      // Always sound under the Extension obligation, even for a zero factor.
      return true;
    }
    // Inequalities: decidable nonzero sign only (positive keeps, negative
    // flips); a zero or unknown factor could lose strict solutions.
    const sign = signOf(params.factor, pinsEnv(judgment.assumptions));
    return sign === "positive" || sign === "negative";
  },

  apply(judgment, location, params): RuleApplication {
    const tree = judgment.equation;
    if (!this.precondition(judgment, location, params)) {
      throw new RulePreconditionViolation(this.id, "not applicable to this relation/factor");
    }
    const flips =
      tree.relation !== "=" &&
      signOf(params.factor, pinsEnv(judgment.assumptions)) === "negative";
    const tree2 = {
      ...tree,
      relation: flips ? flipRelation(tree.relation) : tree.relation,
      lhs: multiplySide(tree.lhs, cloneFresh(params.factor)),
      rhs: multiplySide(tree.rhs, cloneFresh(params.factor)),
    };
    return {
      equation: tree2,
      // A decidably-signed nonzero multiply on an inequality is EXACT; the
      // gaining risk (zero factor) only exists for equalities.
      emits:
        tree.relation === "="
          ? [
              {
                kind: "extension",
                description: `multiplied both sides by ${exprToString(params.factor)}`,
                originalEquation: tree,
              },
            ]
          : [],
      diff: { ...idSetDiff(tree, tree2), merged: [], moved: [] },
    };
  },
};
