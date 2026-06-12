/**
 * Conditional soundness: assumptions and judgments.
 *
 * The core invariant evolved in this layer: every reachable state is
 * equivalent to the original equation GIVEN its assumption set. Moves that
 * are only valid under a condition (dividing by b needs b ≠ 0) or that can
 * gain solutions (multiplying both sides) are not forbidden — the condition
 * becomes a first-class, visible object that travels with the equation.
 *
 * THE POLARITY DISTINCTION (the heart of this design):
 *  - A Restriction is emitted by moves that may LOSE solutions. It narrows
 *    the domain: "this state is equivalent to the original wherever
 *    expr ≠ value holds."
 *  - An Extension is emitted by moves that may GAIN solutions. It carries an
 *    OBLIGATION: candidate solutions must be checked against the original
 *    equation (which the Extension carries) before the derivation is settled.
 *  - A Pinned is a user-introduced what-if ("assume x = 2"), never emitted by
 *    rewrite rules.
 */
import { cloneFresh, variablesIn, type Equation, type Expr } from "./expr.js";
import {
  evalExpr,
  InexactSqrt,
  NonIntegerExponent,
  truthValue,
  UnboundVariable,
  type Env,
} from "./eval.js";

function isUndefinedness(err: unknown): boolean {
  return (
    err instanceof UnboundVariable ||
    err instanceof DivisionByZero ||
    err instanceof NonIntegerExponent ||
    err instanceof InexactSqrt
  );
}
import { DivisionByZero, Rational } from "./rational.js";

export type AssumptionOrigin =
  | { readonly kind: "rule"; readonly stepId: string }
  | { readonly kind: "case-split"; readonly stepId: string }
  | { readonly kind: "user" };

export type DischargeReason = "constant" | "pins" | "solution-check";

interface AssumptionBase {
  readonly id: string;
  readonly origin: AssumptionOrigin;
  /** Discharged assumptions are kept, never deleted — the log shows they existed. */
  readonly status: "active" | "discharged";
  readonly dischargedBy?: DischargeReason;
}

/** Emitted by solution-LOSING moves (division, cancellation). */
export interface Restriction extends AssumptionBase {
  readonly kind: "restriction";
  /** Owned by the assumption (cloned on creation), not part of any equation tree. */
  readonly expr: Expr;
  readonly relation: "≠";
  readonly value: Rational;
}

/** Emitted by solution-GAINING moves (multiply both sides, squaring). */
export interface Extension extends AssumptionBase {
  readonly kind: "extension";
  readonly description: string;
  /** The equation BEFORE the gaining move — what candidates are checked against. */
  readonly originalEquation: Equation;
}

/** User what-if constraint; added/removed only via the Derivation pin API. */
export interface Pinned extends AssumptionBase {
  readonly kind: "pinned";
  readonly variable: string;
  readonly value: Rational;
}

export type Assumption = Restriction | Extension | Pinned;

/** What a rule emits: pure data, no origin/status — the engine stamps those. */
export type EmittedAssumption =
  | { readonly kind: "restriction"; readonly expr: Expr; readonly relation: "≠"; readonly value: Rational }
  | { readonly kind: "extension"; readonly description: string; readonly originalEquation: Equation };

/** The unit of state: an equation under an assumption set. */
export interface Judgment {
  readonly assumptions: readonly Assumption[];
  readonly equation: Equation;
}

export function mkJudgment(equation: Equation): Judgment {
  return { assumptions: [], equation };
}

let assumptionCounter = 0;
function freshAssumptionId(): string {
  return `a${++assumptionCounter}`;
}

export function materializeAssumption(
  emitted: EmittedAssumption,
  origin: AssumptionOrigin,
): Assumption {
  const base = { id: freshAssumptionId(), origin, status: "active" as const };
  if (emitted.kind === "restriction") {
    return {
      ...base,
      kind: "restriction",
      expr: cloneFresh(emitted.expr),
      relation: emitted.relation,
      value: emitted.value,
    };
  }
  return {
    ...base,
    kind: "extension",
    description: emitted.description,
    originalEquation: emitted.originalEquation,
  };
}

export function mkPinned(
  variable: string,
  value: Rational,
  origin: AssumptionOrigin,
): Pinned {
  return { id: freshAssumptionId(), origin, status: "active", kind: "pinned", variable, value };
}

export type Sign = "positive" | "negative" | "zero" | "unknown";

/**
 * Decides an expression's sign under the pinned values — what inequality
 * moves need: dividing both sides by a decidably negative quantity flips the
 * relation; an unknown sign forbids the move entirely.
 */
export function signOf(expr: Expr, pins: Env): Sign {
  try {
    const v = evalExpr(expr, pins);
    return v.isZero() ? "zero" : v.num > 0n ? "positive" : "negative";
  } catch (err) {
    if (isUndefinedness(err)) return "unknown";
    throw err;
  }
}

export class AssumptionConflict extends Error {
  constructor(detail: string) {
    super(`assumption conflict: ${detail}`);
    this.name = "AssumptionConflict";
  }
}

/** Environment containing exactly the pinned variables. */
export function pinsEnv(assumptions: readonly Assumption[]): Env {
  const env = new Map<string, Rational>();
  for (const a of assumptions) {
    if (a.kind === "pinned") env.set(a.variable, a.value);
  }
  return env;
}

export type RestrictionStatus = "holds" | "fails" | "unknown";

/**
 * Decides a restriction under the pinned values: "holds" / "fails" when the
 * expression is fully evaluable (constant, or constant-under-pins),
 * "unknown" when free variables remain or the expression is undefined there.
 */
export function restrictionStatus(
  r: { readonly expr: Expr; readonly value: Rational },
  pins: Env,
): RestrictionStatus {
  try {
    return evalExpr(r.expr, pins).equals(r.value) ? "fails" : "holds";
  } catch (err) {
    if (isUndefinedness(err)) return "unknown";
    throw err;
  }
}

/**
 * The discharge pass: emission is separate from discharge. Rules emit
 * assumptions unconditionally as data; this pass then resolves what it can.
 *
 * - Restrictions decidable now (constants, or decidable under current Pinned
 *   values) are marked discharged — recorded, never deleted.
 * - Restrictions that decidably FAIL are returned as conflicts; callers must
 *   reject the operation that caused them (rule preconditions and the pin
 *   API check this before committing).
 * - Pin-discharged restrictions are re-decided each pass, so removing a pin
 *   reactivates them. Constant- and solution-check discharges are permanent.
 * - Extensions discharge only via checkSolution.
 */
export function dischargePass(assumptions: readonly Assumption[]): {
  assumptions: Assumption[];
  conflicts: Restriction[];
} {
  const pins = pinsEnv(assumptions);
  const conflicts: Restriction[] = [];
  const out = assumptions.map((a): Assumption => {
    if (a.kind !== "restriction") return a;
    if (a.status === "discharged" && a.dischargedBy !== "pins") return a;
    const status = restrictionStatus(a, pins);
    if (status === "fails") {
      conflicts.push(a);
      return a;
    }
    if (status === "holds") {
      const reason: DischargeReason =
        variablesIn(a.expr).size === 0 ? "constant" : "pins";
      return { ...a, status: "discharged", dischargedBy: reason };
    }
    if (a.status === "discharged") {
      // The pin that justified this discharge is gone — reactivate.
      const { dischargedBy: _gone, ...rest } = a;
      return { ...rest, status: "active" };
    }
    return a;
  });
  return { assumptions: out, conflicts };
}

/**
 * Does this variable assignment satisfy the judgment's conditions? Pinned
 * variables must match exactly; every Restriction (discharged ones included —
 * they are facts either way) must hold and be defined. Extensions impose no
 * pointwise condition; they are obligations on candidate solutions.
 */
export function envSatisfiesAssumptions(judgment: Judgment, env: Env): boolean {
  for (const a of judgment.assumptions) {
    if (a.kind === "pinned") {
      const v = env.get(a.variable);
      if (v === undefined || !v.equals(a.value)) return false;
    } else if (a.kind === "restriction") {
      try {
        if (evalExpr(a.expr, env).equals(a.value)) return false;
      } catch {
        return false; // restriction undefined at this point — not satisfied
      }
    }
  }
  return true;
}

export type CheckVerdict = "verified" | "extraneous";

/**
 * The Extension discharge mechanism: substitute a candidate solution into the
 * ORIGINAL equation(s) the Extensions carry (every one of them — by the
 * subset chain the earliest implies the rest, but checking all is cheap) and
 * evaluate exactly. With no Extensions present the current equation is the
 * original up to Restrictions, so it is checked directly.
 *
 * verified  -> all active Extensions discharge (recorded, kept).
 * extraneous -> the judgment is unchanged; the caller records the condemned
 *               candidate in the derivation log.
 */
export function checkSolution(
  judgment: Judgment,
  candidate: Env,
): { verdict: CheckVerdict; judgment: Judgment } {
  const extensions = judgment.assumptions.filter((a) => a.kind === "extension");
  const targets =
    extensions.length > 0
      ? extensions.map((e) => e.originalEquation)
      : [judgment.equation];
  const verified = targets.every((t) => truthValue(t, candidate) === true);
  if (!verified) return { verdict: "extraneous", judgment };
  const assumptions = judgment.assumptions.map((a): Assumption => {
    if (a.kind !== "extension" || a.status !== "active") return a;
    return { ...a, status: "discharged", dischargedBy: "solution-check" };
  });
  return { verdict: "verified", judgment: { ...judgment, assumptions } };
}
