/**
 * Substitution: the first cross-equation rule for systems. When one equation is
 * in SOLVED form `v = expr` (one side a bare variable not occurring in the
 * other), every occurrence of v in another equation is replaced by expr — the
 * "isolate, then substitute" move. Sound because, under `v = expr`, the target
 * and the substituted target are equivalent, so keeping the source and rewriting
 * the target preserves the system's (intersection) solution set.
 *
 * The same machinery serves calculus u-substitution later. Pure (no DOM);
 * rebuilds through the smart constructors and preserves the ids of v-free
 * subtrees (only paths touching v are rebuilt).
 */
import {
  cloneFresh,
  equation,
  fraction,
  neg,
  pow,
  product,
  sqrt,
  sum,
  variablesIn,
  type Equation,
  type Expr,
} from "./expr.js";
import type { System } from "./system.js";

/** If `eqn` is `v = expr` (or `expr = v`) with v a bare variable absent from
 *  expr, the variable it's solved for and that value; else undefined. */
export function solvedVariable(eqn: Equation): { variable: string; value: Expr } | undefined {
  if (eqn.relation !== "=") return undefined; // substitution needs an equality
  const fromSide = (v: Expr, other: Expr): { variable: string; value: Expr } | undefined =>
    v.kind === "var" && !variablesIn(other).has(v.name)
      ? { variable: v.name, value: other }
      : undefined;
  return fromSide(eqn.lhs, eqn.rhs) ?? fromSide(eqn.rhs, eqn.lhs);
}

/** Replace every occurrence of `name` with a fresh clone of `value`. v-free
 *  subtrees return by identity (ids preserved); touched paths rebuild through
 *  the smart constructors (which maintain the structural invariants). */
function substExpr(e: Expr, name: string, value: Expr): Expr {
  if (!variablesIn(e).has(name)) return e;
  switch (e.kind) {
    case "var":
      return cloneFresh(value); // e.name === name, since the subtree contains it
    case "neg":
      return neg(substExpr(e.child, name, value));
    case "sum":
      return sum(e.children.map((c) => substExpr(c, name, value)));
    case "product":
      return product(e.children.map((c) => substExpr(c, name, value)));
    case "fraction":
      return fraction(
        e.num.map((c) => substExpr(c, name, value)),
        e.den.map((c) => substExpr(c, name, value)),
      );
    case "pow":
      return pow(substExpr(e.base, name, value), substExpr(e.exp, name, value));
    case "sqrt":
      return sqrt(substExpr(e.child, name, value));
    case "int":
      return e; // unreachable: an int subtree has no variables
  }
}

/** Substitute the SOURCE's solved variable into TARGET. Returns the rewritten
 *  target (the source's relation is irrelevant to the target's), or undefined
 *  if source isn't in `v = expr` form. */
export function substitute(source: Equation, target: Equation): Equation | undefined {
  const solved = solvedVariable(source);
  if (solved === undefined) return undefined;
  return equation(
    substExpr(target.lhs, solved.variable, solved.value),
    substExpr(target.rhs, solved.variable, solved.value),
    target.relation,
  );
}

/** Substitute equation `sourceIndex` (in `v = expr` form) into `targetIndex`,
 *  keeping the source, every other equation, and the assumptions unchanged.
 *  Undefined if the indices coincide or the source isn't solved for a variable. */
export function substituteInSystem(
  system: System,
  sourceIndex: number,
  targetIndex: number,
): System | undefined {
  if (sourceIndex === targetIndex) return undefined;
  const source = system.equations[sourceIndex];
  const target = system.equations[targetIndex];
  if (source === undefined || target === undefined) return undefined;
  const rewritten = substitute(source, target);
  if (rewritten === undefined) return undefined;
  const equations = system.equations.map((e, i) => (i === targetIndex ? rewritten : e));
  return { assumptions: system.assumptions, equations };
}
