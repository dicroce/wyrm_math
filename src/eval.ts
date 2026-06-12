import { fraction, int, type Equation, type Expr } from "./expr.js";
import { DivisionByZero, Rational } from "./rational.js";

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

/** √v has no exact rational value (negative, or not a perfect square). */
export class InexactSqrt extends Error {
  constructor() {
    super("square root is not an exact rational");
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
 * Exact evaluation under a variable assignment. Throws DivisionByZero when a
 * denominator vanishes, UnboundVariable for missing assignments, and
 * NonIntegerExponent for exponents outside exact rational arithmetic.
 */
export function evalExpr(e: Expr, env: Env): Rational {
  switch (e.kind) {
    case "int":
      return new Rational(e.value);
    case "var": {
      const v = env.get(e.name);
      if (v === undefined) throw new UnboundVariable(e.name);
      return v;
    }
    case "neg":
      return evalExpr(e.child, env).neg();
    case "sum":
      return e.children.reduce((acc, c) => acc.add(evalExpr(c, env)), Rational.zero);
    case "product":
      return e.children.reduce((acc, c) => acc.mul(evalExpr(c, env)), Rational.one);
    case "fraction": {
      const num = e.num.reduce((acc, c) => acc.mul(evalExpr(c, env)), Rational.one);
      const den = e.den.reduce((acc, c) => acc.mul(evalExpr(c, env)), Rational.one);
      return num.div(den);
    }
    case "pow": {
      const exp = evalExpr(e.exp, env);
      if (!exp.isInteger()) throw new NonIntegerExponent();
      const base = evalExpr(e.base, env);
      return base.powInt(exp.num);
    }
    case "sqrt": {
      const v = sqrtRational(evalExpr(e.child, env));
      if (v === undefined) throw new InexactSqrt();
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
    const cmp = evalExpr(eqn.lhs, env).compare(evalExpr(eqn.rhs, env));
    switch (eqn.relation) {
      case "=":
        return cmp === 0;
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
