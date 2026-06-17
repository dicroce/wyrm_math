/**
 * Exact surd values — the engine's exact-number domain beyond ℚ.
 *
 * A value is `q₀ + Σ qᵢ·√nᵢ` (qᵢ ∈ Rational, nᵢ distinct square-free integers).
 * Internally one Map keyed by square-free radicand (`1n` is the rational part);
 * every stored coefficient is nonzero, so canonical form makes equality
 * STRUCTURAL — which is sound because the √ of distinct square-free integers are
 * ℚ-linearly independent, so `q₀ + Σ qᵢ√nᵢ = 0` iff every qᵢ = 0.
 *
 * Closed under `+ − ×`, and under `÷` for the cases quadratic work produces:
 * division by a rational, or by a single-radical value `a + b√n` (via its
 * conjugate). A denominator with TWO OR MORE distinct radicals needs
 * multiquadratic rationalization — out of scope here, so `inverse()` returns
 * `undefined` (an honest undefined point, never an approximation). `√` of a
 * negative is `undefined` too (complex numbers are a later step).
 *
 * No floating point, no DOM — exact bigint/Rational arithmetic only.
 */
import { Rational } from "./rational.js";

const ONE = 1n;

/** Write n = coeff²·radicand with radicand square-free (n ≥ 1). */
function squareFreeFactor(n: bigint): { coeff: bigint; radicand: bigint } {
  let coeff = 1n;
  let rem = n;
  let d = 2n;
  while (d * d <= rem) {
    const dd = d * d;
    while (rem % dd === 0n) {
      rem /= dd;
      coeff *= d;
    }
    d += 1n;
  }
  return { coeff, radicand: rem };
}

export class Surd {
  /** square-free radicand (1n = rational part) → nonzero coefficient */
  private constructor(readonly terms: ReadonlyMap<bigint, Rational>) {}

  /** Drop zero coefficients so equality can stay structural. */
  private static build(raw: Map<bigint, Rational>): Surd {
    const terms = new Map<bigint, Rational>();
    for (const [n, c] of raw) if (!c.isZero()) terms.set(n, c);
    return new Surd(terms);
  }

  static rational(r: Rational): Surd {
    return Surd.build(new Map([[ONE, r]]));
  }

  static readonly zero = new Surd(new Map());
  static readonly one = Surd.rational(Rational.one);

  /** √v for a non-negative rational v, as an exact surd; undefined if v < 0. */
  static sqrt(v: Rational): Surd | undefined {
    if (v.num < 0n) return undefined;
    if (v.isZero()) return Surd.zero;
    // √(num/den) = √(num·den)/den
    const { coeff, radicand } = squareFreeFactor(v.num * v.den);
    return Surd.build(new Map([[radicand, new Rational(coeff, v.den)]]));
  }

  get rationalPart(): Rational {
    return this.terms.get(ONE) ?? Rational.zero;
  }

  isRational(): boolean {
    for (const n of this.terms.keys()) if (n !== ONE) return false;
    return true;
  }

  asRational(): Rational | undefined {
    return this.isRational() ? this.rationalPart : undefined;
  }

  isZero(): boolean {
    return this.terms.size === 0;
  }

  neg(): Surd {
    const m = new Map<bigint, Rational>();
    for (const [n, c] of this.terms) m.set(n, c.neg());
    return Surd.build(m);
  }

  add(o: Surd): Surd {
    const m = new Map<bigint, Rational>(this.terms);
    for (const [n, c] of o.terms) {
      const cur = m.get(n);
      m.set(n, cur === undefined ? c : cur.add(c));
    }
    return Surd.build(m);
  }

  sub(o: Surd): Surd {
    return this.add(o.neg());
  }

  mul(o: Surd): Surd {
    const m = new Map<bigint, Rational>();
    for (const [i, ci] of this.terms) {
      for (const [j, cj] of o.terms) {
        // √i · √j = √(ij) = coeff·√radicand
        const { coeff, radicand } = squareFreeFactor(i * j);
        const term = ci.mul(cj).mul(new Rational(coeff));
        const cur = m.get(radicand);
        m.set(radicand, cur === undefined ? term : cur.add(term));
      }
    }
    return Surd.build(m);
  }

  /** Integer power. Negative exponents need `inverse()`, so they return
   *  undefined for zero (0⁻ⁿ) or ≥2-radical bases. `x⁰ = 1` (incl. `0⁰`,
   *  matching the exact evaluator). */
  powInt(e: bigint): Surd | undefined {
    if (e < 0n) {
      const inv = this.inverse();
      return inv === undefined ? undefined : inv.powInt(-e);
    }
    let result = Surd.one;
    let base: Surd = this;
    let n = e;
    while (n > 0n) {
      if ((n & 1n) === 1n) result = result.mul(base);
      n >>= 1n;
      if (n > 0n) base = base.mul(base);
    }
    return result;
  }

  /** Multiplicative inverse, or undefined when zero or when ≥2 radicals appear. */
  inverse(): Surd | undefined {
    if (this.isZero()) return undefined;
    const radicals = [...this.terms.keys()].filter((n) => n !== ONE);
    if (radicals.length === 0) {
      return Surd.rational(Rational.one.div(this.rationalPart));
    }
    if (radicals.length === 1) {
      const n = radicals[0]!;
      const a = this.rationalPart; // possibly zero
      const b = this.terms.get(n)!; // nonzero
      // (a + b√n)(a − b√n) = a² − b²n, rational and nonzero for square-free n>1.
      const denom = a.mul(a).sub(b.mul(b).mul(new Rational(n)));
      const m = new Map<bigint, Rational>();
      m.set(ONE, a.div(denom));
      m.set(n, b.neg().div(denom));
      return Surd.build(m);
    }
    return undefined; // ≥2 radicals: multiquadratic rationalization, out of scope
  }

  div(o: Surd): Surd | undefined {
    const inv = o.inverse();
    return inv === undefined ? undefined : this.mul(inv);
  }

  equals(o: Surd): boolean {
    if (this.terms.size !== o.terms.size) return false;
    for (const [n, c] of this.terms) {
      const oc = o.terms.get(n);
      if (oc === undefined || !c.equals(oc)) return false;
    }
    return true;
  }

  toString(): string {
    if (this.isZero()) return "0";
    const parts: string[] = [];
    const rat = this.terms.get(ONE);
    if (rat !== undefined) parts.push(rat.toString());
    for (const [n, c] of this.terms) {
      if (n !== ONE) parts.push(`${c.toString()}√${n}`);
    }
    return parts.join(" + ");
  }
}
