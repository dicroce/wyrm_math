import { flipRelation } from "../expr.js";
import {
  idSetDiff,
  RulePreconditionViolation,
  type Rule,
  type RuleApplication,
} from "../rule.js";

type NoParams = Record<string, never>;

/**
 * Swap the two sides: a R b ⇔ b flip(R) a, exactly, for every relation
 * (x < 5 becomes 5 > x; equalities just trade places). Gesture: a tap on the
 * relation sign (on '=' the square-both-sides tap outranks it).
 */
export const swapSides: Rule<NoParams> = {
  id: "swap-sides",
  description: "Swap the two sides of the relation.",

  precondition(judgment, location, _params) {
    return location === judgment.equation.id;
  },

  apply(judgment, location, _params): RuleApplication {
    const tree = judgment.equation;
    if (location !== tree.id) {
      throw new RulePreconditionViolation(this.id, "location must be the equation root");
    }
    const tree2 = {
      ...tree,
      lhs: tree.rhs,
      rhs: tree.lhs,
      relation: flipRelation(tree.relation),
    };
    return {
      equation: tree2,
      emits: [],
      diff: { ...idSetDiff(tree, tree2), merged: [], moved: [] },
    };
  },
};
