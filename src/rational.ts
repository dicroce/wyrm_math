/**
 * Exact rational arithmetic over bigint. No floating point is ever used in
 * correctness checks — rule property tests compare equation truth values
 * computed with this type.
 *
 * Always normalized: den > 0, gcd(|num|, den) === 1, and 0 is 0/1.
 */
export class Rational {
  readonly num: bigint;
  readonly den: bigint;

  constructor(num: bigint, den: bigint = 1n) {
    if (den === 0n) throw new DivisionByZero();
    if (den < 0n) {
      num = -num;
      den = -den;
    }
    const g = gcd(num < 0n ? -num : num, den);
    this.num = g === 0n ? 0n : num / g;
    this.den = g === 0n ? 1n : den / g;
  }

  static of(n: bigint | number): Rational {
    return new Rational(typeof n === "number" ? BigInt(n) : n);
  }

  /** Parse "3", "-3", or "3/4" (whitespace tolerated). Undefined on anything else. */
  static parse(s: string): Rational | undefined {
    const m = /^\s*(-?\d+)\s*(?:\/\s*(-?\d+)\s*)?$/.exec(s);
    if (m === null) return undefined;
    const den = m[2] === undefined ? 1n : BigInt(m[2]);
    if (den === 0n) return undefined;
    return new Rational(BigInt(m[1]!), den);
  }

  static readonly zero = new Rational(0n);
  static readonly one = new Rational(1n);

  add(o: Rational): Rational {
    return new Rational(this.num * o.den + o.num * this.den, this.den * o.den);
  }

  sub(o: Rational): Rational {
    return this.add(o.neg());
  }

  mul(o: Rational): Rational {
    return new Rational(this.num * o.num, this.den * o.den);
  }

  div(o: Rational): Rational {
    if (o.isZero()) throw new DivisionByZero();
    return new Rational(this.num * o.den, this.den * o.num);
  }

  neg(): Rational {
    return new Rational(-this.num, this.den);
  }

  /** Integer exponent only; negative exponents of zero throw. */
  powInt(e: bigint): Rational {
    if (e < 0n) {
      if (this.isZero()) throw new DivisionByZero();
      return new Rational(this.den ** -e, this.num ** -e);
    }
    return new Rational(this.num ** e, this.den ** e);
  }

  isZero(): boolean {
    return this.num === 0n;
  }

  isInteger(): boolean {
    return this.den === 1n;
  }

  equals(o: Rational): boolean {
    return this.num === o.num && this.den === o.den;
  }

  /** Exact ordering: -1, 0, or 1. */
  compare(o: Rational): -1 | 0 | 1 {
    const d = this.num * o.den - o.num * this.den; // both dens > 0
    return d < 0n ? -1 : d > 0n ? 1 : 0;
  }

  toString(): string {
    return this.den === 1n ? `${this.num}` : `${this.num}/${this.den}`;
  }
}

export class DivisionByZero extends Error {
  constructor() {
    super("division by zero");
    this.name = "DivisionByZero";
  }
}

/** Greatest common divisor; expects non-negative inputs. */
export function gcd(a: bigint, b: bigint): bigint {
  while (b !== 0n) {
    [a, b] = [b, a % b];
  }
  return a;
}
