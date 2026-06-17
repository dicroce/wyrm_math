import { fraction, int, type Equation, type Expr } from "./expr.js";
import { DivisionByZero, Rational } from "./rational.js";
import { Surd } from "./surd.js";

/** Variable assignment used by the substitution evaluator. */
export type Env = ReadonlyMap<string, Rational>;

export class UnboundVariable extends Error {
  constructor(name: string) {
    super(`unbound variable ${name}`);
    this.name = "UnboundVariable";
  }
}

export class NonIntegerExponent extends Error {
  constructor() {
    super("exponent did not evaluate to an integer");
    this.name = "NonIntegerExponent";
  }
}

/** √v has no exact value in the engine's number domain: a NEGATIVE radicand
 *  (complex — deferred) or a NESTED radical that escapes the surd field. A
 *  non-perfect-square like √2 is no longer inexact — it's an exact Surd. */
export class InexactSqrt extends Error {
  constructor() {
    super("square root has no exact value here (negative or nested)");
    this.name = "InexactSqrt";
  }
}

/** Floor integer square root (n >= 0). */
function isqrt(n: bigint): bigint {
  if (n < 2n) return n;
  let x = n;
  let y = (x + 1n) >> 1n;
  while (y < x) {
    x = y;
    y = (x + n / x) >> 1n;
  }
  return x;
}

/** Exact rational square root, or undefined when irrational/negative. */
export function sqrtRational(v: Rational): Rational | undefined {
  if (v.num < 0n) return undefined;
  const sn = isqrt(v.num);
  const sd = isqrt(v.den);
  if (sn * sn !== v.num || sd * sd !== v.den) return undefined;
  return new Rational(sn, sd);
}

/**
 * Exact evaluation under a variable assignment, over the surd-closed exact
 * domain (`Surd`; a Rational is the degenerate element). Throws DivisionByZero
 * when a denominator vanishes, UnboundVariable for missing assignments,
 * NonIntegerExponent for non-integer exponents, and InexactSqrt where a root
 * has no exact value (negative radicand → complex; nested radical → out of the
 * surd field). These are the engine's UNDEFINED POINTS — never approximated.
 */
export function evalExpr(e: Expr, env: Env): Surd {
  switch (e.kind) {
    case "int":
      return Surd.rational(new Rational(e.value));
    case "var": {
      const v = env.get(e.name);
      if (v === undefined) throw new UnboundVariable(e.name);
      return Surd.rational(v);
    }
    case "neg":
      return evalExpr(e.child, env).neg();
    case "sum":
      return e.children.reduce((acc, c) => acc.add(evalExpr(c, env)), Surd.zero);
    case "product":
      return e.children.reduce((acc, c) => acc.mul(evalExpr(c, env)), Surd.one);
    case "fraction": {
      const num = e.num.reduce((acc, c) => acc.mul(evalExpr(c, env)), Surd.one);
      const den = e.den.reduce((acc, c) => acc.mul(evalExpr(c, env)), Surd.one);
      if (den.isZero()) throw new DivisionByZero();
      const q = num.div(den);
      if (q === undefined) throw new InexactSqrt(); // multiquadratic denominator — out of scope
      return q;
    }
    case "pow": {
      const exp = evalExpr(e.exp, env).asRational();
      if (exp === undefined || !exp.isInteger()) throw new NonIntegerExponent();
      const base = evalExpr(e.base, env);
      const r = base.powInt(exp.num);
      if (r === undefined) throw base.isZero() ? new DivisionByZero() : new InexactSqrt();
      return r;
    }
    case "sqrt": {
      const radicand = evalExpr(e.child, env).asRational();
      if (radicand === undefined) throw new InexactSqrt(); // nested radical
      const v = Surd.sqrt(radicand);
      if (v === undefined) throw new InexactSqrt(); // negative radicand (complex)
      return v;
    }
  }
}

/** Exact literal for a rational value: an Integer, Neg(Integer), or Fraction. */
export function rationalToExpr(r: Rational): Expr {
  if (r.den === 1n) return int(r.num);
  return fraction([int(r.num)], [int(r.den)]);
}

/**
 * Truth value of an equation or inequality under an assignment, or undefined
 * when either side is undefined there (division by zero / non-integer
 * exponent). The solution-set property tests skip undefined sample points.
 */
export function truthValue(eqn: Equation, env: Env): boolean | undefined {
  try {
    // Work with the difference: equality is decidable over surds (structural,
    // by ℚ-linear independence), and order is decidable whenever the difference
    // is rational (e.g. √2+1 vs √2). An irrational difference (√2 vs 1) needs
    // exact surd ORDERING — deferred — so it reads as undefined and is skipped.
    const diff = evalExpr(eqn.lhs, env).sub(evalExpr(eqn.rhs, env));
    if (eqn.relation === "=") return diff.isZero();
    const d = diff.asRational();
    if (d === undefined) return undefined;
    const cmp = d.compare(Rational.zero); // sign of (lhs − rhs)
    switch (eqn.relation) {
      case "<":
        return cmp < 0;
      case "≤":
        return cmp <= 0;
      case ">":
        return cmp > 0;
      case "≥":
        return cmp >= 0;
    }
  } catch (err) {
    if (
      err instanceof DivisionByZero ||
      err instanceof NonIntegerExponent ||
      err instanceof InexactSqrt
    ) {
      return undefined;
    }
    throw err;
  }
}
