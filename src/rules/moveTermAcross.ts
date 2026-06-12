import {
  findById,
  findParent,
  int,
  neg,
  rebuildNary,
  sum,
  type Equation,
  type Expr,
  type NodeId,
} from "../expr.js";
import {
  idSetDiff,
  RulePreconditionViolation,
  type Rule,
  type RuleApplication,
} from "../rule.js";

export interface MoveTermAcrossParams {
  /** A top-level term of either side (a Sum child, or the whole side). */
  readonly termId: NodeId;
}

interface Resolved {
  readonly term: Expr;
  readonly wholeSide: boolean;
  readonly onLhs: boolean;
}

function resolve(tree: Equation, params: MoveTermAcrossParams): Resolved | undefined {
  for (const onLhs of [true, false]) {
    const side = onLhs ? tree.lhs : tree.rhs;
    if (side.id === params.termId) return { term: side, wholeSide: true, onLhs };
    if (side.kind === "sum") {
      const term = side.children.find((c) => c.id === params.termId);
      if (term !== undefined) return { term, wholeSide: false, onLhs };
    }
  }
  return undefined;
}

/**
 * Move a term to the other side of the equals sign, sign-flipped — what a
 * human writes, in one gesture:
 *   2x = 10 − 3x   ~>   2x + 3x = 10        x + 2 = 5   ~>   x = 5 − 2
 *
 * Semantically this is add-to-both-sides followed by the exact structural
 * cancellation at the source (t + (−t) annihilates), so it is exactly
 * solution-preserving and emits nothing. The term's body travels by
 * identity: moving −3x re-uses the 3x node on the far side (the minus is
 * consumed); moving a positive term re-uses it under a fresh minus.
 */
export const moveTermAcross: Rule<MoveTermAcrossParams> = {
  id: "move-term-across",
  description: "Move a term to the other side of the equation, flipping its sign.",

  precondition(judgment, location, params) {
    return location === judgment.equation.id && resolve(judgment.equation, params) !== undefined;
  },

  apply(judgment, location, params): RuleApplication {
    const tree = judgment.equation;
    const r = location === tree.id ? resolve(tree, params) : undefined;
    if (r === undefined) {
      throw new RulePreconditionViolation(
        this.id,
        "termId is not a top-level term of either side",
      );
    }
    const source = r.onLhs ? tree.lhs : tree.rhs;
    const dest = r.onLhs ? tree.rhs : tree.lhs;

    // neg() collapses a Neg term to its body and wraps a positive term —
    // either way the body keeps its id and glides across in the animation.
    const arriving = neg(r.term);
    const newSource: Expr = r.wholeSide
      ? int(0)
      : source.kind === "sum"
        ? rebuildNary(source, source.children.filter((c) => c.id !== params.termId))
        : int(0); // unreachable: non-sum sides only match as wholeSide
    const newDest: Expr =
      dest.kind === "sum"
        ? rebuildNary(dest, [...dest.children, arriving])
        : sum([dest, arriving]);

    const tree2: Equation = {
      ...tree,
      lhs: r.onLhs ? newSource : newDest,
      rhs: r.onLhs ? newDest : newSource,
    };
    const movedId = r.term.kind === "neg" ? r.term.child.id : r.term.id;
    const newParent = findParent(tree2, movedId);
    return {
      equation: tree2,
      emits: [],
      diff: {
        ...idSetDiff(tree, tree2),
        merged: [],
        moved:
          newParent === undefined || findById(tree2, movedId) === undefined
            ? []
            : [{ id: movedId, from: source.id, to: newParent.id }],
      },
    };
  },
};
