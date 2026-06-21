/**
 * Elimination: the second cross-equation rule for systems. Replace one equation
 * B with a linear combination `α·A + β·B` of it and another equation A, chosen
 * to cancel a variable. Both must be equalities; β (the multiplier on the
 * equation being replaced) must be nonzero.
 *
 * Soundness — the system {A, B} and {A, α·A + β·B} have the same solutions:
 *  - {A, B} ⟹ α·A + β·B (a linear combination of two true equalities holds).
 *  - {A, α·A + β·B} ⟹ B, because under A the α·A part contributes 0, leaving
 *    β·(B_lhs − B_rhs) = 0, and β ≠ 0 ⟹ B holds.
 * The combination is left UNSIMPLIFIED so the learner does the cancelling.
 *
 * Integer coefficients (the LCM-matching school case); rationals can always be
 * cleared to integers first. Pure (no DOM); cloned subtrees keep ids unique.
 */
import {
  cloneFresh,
  equation,
  int,
  neg,
  product,
  sum,
  type Equation,
  type Expr,
} from "./expr.js";
import type { System } from "./system.js";

/** c·e for an integer coefficient, collapsing the ±1 and 0 cases. Clones e so
 *  the reused subtree gets fresh, tree-unique ids. */
function scale(c: bigint, e: Expr): Expr {
  if (c === 0n) return int(0);
  if (c === 1n) return cloneFresh(e);
  if (c === -1n) return neg(cloneFresh(e));
  return product([int(c), cloneFresh(e)]);
}

/** The equation `α·keep + β·replace` (unsimplified), or undefined if either is
 *  not an equality or β = 0 (which would make the step non-invertible). */
export function eliminate(
  keep: Equation,
  replace: Equation,
  alpha: bigint,
  beta: bigint,
): Equation | undefined {
  if (keep.relation !== "=" || replace.relation !== "=") return undefined;
  if (beta === 0n) return undefined;
  return equation(
    sum([scale(alpha, keep.lhs), scale(beta, replace.lhs)]),
    sum([scale(alpha, keep.rhs), scale(beta, replace.rhs)]),
  );
}

/** Replace equation `replaceIndex` with `α·keep + β·replace`, keeping `keep`,
 *  the other equations, and the assumptions. Undefined if the indices coincide,
 *  an equation is missing, an equation isn't an equality, or β = 0. */
export function eliminateInSystem(
  system: System,
  keepIndex: number,
  replaceIndex: number,
  alpha: bigint,
  beta: bigint,
): System | undefined {
  if (keepIndex === replaceIndex) return undefined;
  const keep = system.equations[keepIndex];
  const replace = system.equations[replaceIndex];
  if (keep === undefined || replace === undefined) return undefined;
  const combined = eliminate(keep, replace, alpha, beta);
  if (combined === undefined) return undefined;
  const equations = system.equations.map((e, i) => (i === replaceIndex ? combined : e));
  return { assumptions: system.assumptions, equations };
}
