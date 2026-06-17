import fc from "fast-check";
import { describe, expect, it } from "vitest";
import { Rational } from "../src/rational.js";
import { Surd } from "../src/surd.js";
import { arbRational } from "./gen.js";

const rat = (n: bigint, d = 1n): Surd => Surd.rational(new Rational(n, d));
const sqrt = (n: bigint, d = 1n): Surd => Surd.sqrt(new Rational(n, d))!;

/** p + q√n — a single-radical surd, so its inverse is always defined. */
const arbSurd: fc.Arbitrary<Surd> = fc
  .tuple(arbRational, arbRational, fc.constantFrom(2n, 3n, 5n, 6n, 7n, 10n, 11n, 13n))
  .map(([p, q, n]) => Surd.rational(p).add(Surd.sqrt(new Rational(n))!.mul(Surd.rational(q))));

/** A non-negative rational, for √ inputs. */
const arbNonNeg: fc.Arbitrary<Rational> = arbRational.map((r) =>
  r.compare(Rational.zero) < 0 ? r.neg() : r,
);

describe("Surd", () => {
  it("collapses perfect squares to rationals", () => {
    expect(sqrt(9n).equals(rat(3n))).toBe(true);
    expect(sqrt(9n, 4n).equals(rat(3n, 2n))).toBe(true); // √(9/4) = 3/2
    expect(sqrt(9n).isRational()).toBe(true);
  });

  it("pulls the square factor out of a radical", () => {
    expect(sqrt(8n).equals(sqrt(2n).mul(rat(2n)))).toBe(true); // √8 = 2√2
    expect(sqrt(12n).equals(sqrt(3n).mul(rat(2n)))).toBe(true); // √12 = 2√3
    expect(sqrt(8n).isRational()).toBe(false);
  });

  it("√a·√b = √(ab) and √n·√n = n", () => {
    expect(sqrt(2n).mul(sqrt(2n)).equals(rat(2n))).toBe(true);
    expect(sqrt(2n).mul(sqrt(3n)).equals(sqrt(6n))).toBe(true);
  });

  it("treats √ of a negative as undefined (defer ℂ)", () => {
    expect(Surd.sqrt(new Rational(-2n))).toBeUndefined();
  });

  it("inverts a single radical and a conjugate pair", () => {
    expect(sqrt(2n).mul(sqrt(2n).inverse()!).equals(Surd.one)).toBe(true);
    const x = rat(1n).add(sqrt(2n)); // 1 + √2
    expect(x.mul(x.inverse()!).equals(Surd.one)).toBe(true); // (1+√2)(−1+√2)=1
  });

  it("refuses to invert a value with two distinct radicals", () => {
    expect(sqrt(2n).add(sqrt(3n)).inverse()).toBeUndefined();
    expect(Surd.zero.inverse()).toBeUndefined();
  });

  it("distinguishes different radicands", () => {
    expect(rat(2n).add(sqrt(3n)).equals(rat(2n).add(sqrt(5n)))).toBe(false);
  });

  describe("field laws (property)", () => {
    it("√v · √v = v for non-negative v", () => {
      fc.assert(
        fc.property(arbNonNeg, (v) => {
          const s = Surd.sqrt(v)!;
          expect(s.mul(s).equals(Surd.rational(v))).toBe(true);
        }),
      );
    });

    it("addition and multiplication commute", () => {
      fc.assert(
        fc.property(arbSurd, arbSurd, (a, b) => {
          expect(a.add(b).equals(b.add(a))).toBe(true);
          expect(a.mul(b).equals(b.mul(a))).toBe(true);
        }),
      );
    });

    it("multiplication distributes over addition", () => {
      fc.assert(
        fc.property(arbSurd, arbSurd, arbSurd, (a, b, c) => {
          expect(a.mul(b.add(c)).equals(a.mul(b).add(a.mul(c)))).toBe(true);
        }),
      );
    });

    it("x · x⁻¹ = 1 for nonzero single-radical values", () => {
      fc.assert(
        fc.property(arbSurd, (x) => {
          fc.pre(!x.isZero());
          expect(x.mul(x.inverse()!).equals(Surd.one)).toBe(true);
        }),
      );
    });
  });
});
