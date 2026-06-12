import {
  cloneFresh,
  freshId,
  neg,
  rebuildNary,
  type Expr,
  type Sum,
} from "../expr.js";
import {
  idSetDiff,
  RulePreconditionViolation,
  type Rule,
  type RuleApplication,
} from "../rule.js";

export interface AddToBothSidesParams {
  /**
   * The term whose negation is added to both sides. Typically a copy of an
   * existing term the user dragged; the rule clones it (fresh ids) before
   * inserting, so callers may pass subtrees of the current equation.
   */
  readonly term: Expr;
}

/** Append a term to one side, preserving the side's Sum id if it has one. */
function appendTerm(side: Expr, term: Expr): Expr {
  if (side.kind === "sum") return rebuildNary(side, [...side.children, term]);
  const flat = term.kind === "sum" ? term.children : [term];
  return { kind: "sum", id: freshId(), children: [side, ...flat] } satisfies Sum;
}

/**
 * Adds Neg(term) to both sides of the equation as ONE atomic application —
 * the transactional both-sides gesture is a UI concern; the engine commits
 * both sides at once, so no intermediate unbalanced state ever exists.
 */
export const addToBothSides: Rule<AddToBothSidesParams> = {
  id: "add-to-both-sides",
  description: "Add the negation of a term to both sides of the equation.",

  precondition(judgment, location, _params) {
    // Any term may be added; the only requirement is targeting the equation.
    return location === judgment.equation.id;
  },

  apply(judgment, location, params): RuleApplication {
    const tree = judgment.equation;
    if (location !== tree.id) {
      throw new RulePreconditionViolation(this.id, "location must be the equation root");
    }
    // Two independent clones: ids must stay unique within the result tree.
    const negLhsTerm = neg(cloneFresh(params.term));
    const negRhsTerm = neg(cloneFresh(params.term));
    const tree2 = {
      ...tree,
      lhs: appendTerm(tree.lhs, negLhsTerm),
      rhs: appendTerm(tree.rhs, negRhsTerm),
    };
    return {
      equation: tree2,
      emits: [],
      diff: { ...idSetDiff(tree, tree2), merged: [], moved: [] },
    };
  },
};
