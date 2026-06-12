import { int, pow, type Pow } from "../expr.js";
import {
  idSetDiff,
  RulePreconditionViolation,
  type Rule,
  type RuleApplication,
} from "../rule.js";

type NoParams = Record<string, never>;

/**
 * Square both sides — the second solution-GAINING move (after
 * multiply-both-sides): x = 2 becomes x² = 4, which −2 also satisfies. Emits
 * an Extension carrying the pre-move equation; the derivation is not settled
 * until candidate solutions are checked against it. Gesture: a tap on the
 * equals sign.
 */
export const squareBothSides: Rule<NoParams> = {
  id: "square-both-sides",
  description: "Square both sides of the equation (emits an obligation).",

  precondition(judgment, location, _params) {
    // Squaring is not monotone: −3 < 2 but 9 > 4. Equalities only.
    return location === judgment.equation.id && judgment.equation.relation === "=";
  },

  apply(judgment, location, _params): RuleApplication {
    const tree = judgment.equation;
    if (location !== tree.id) {
      throw new RulePreconditionViolation(this.id, "location must be the equation root");
    }
    const lhs: Pow = pow(tree.lhs, int(2));
    const rhs: Pow = pow(tree.rhs, int(2));
    const tree2 = { ...tree, lhs, rhs };
    return {
      equation: tree2,
      emits: [
        {
          kind: "extension",
          description: "squared both sides",
          originalEquation: tree,
        },
      ],
      diff: {
        ...idSetDiff(tree, tree2),
        merged: [],
        moved: [
          { id: tree.lhs.id, from: tree.id, to: lhs.id },
          { id: tree.rhs.id, from: tree.id, to: rhs.id },
        ],
      },
    };
  },
};
