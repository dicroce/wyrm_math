import fc from "fast-check";
import { describe, expect, it } from "vitest";
import { DivisionByZero, Rational } from "../src/index.js";
import { arbRational } from "./gen.js";

describe("Rational", () => {
  it("normalizes sign and gcd", () => {
    const r = new Rational(4n, -6n);
    expect(r.num).toBe(-2n);
    expect(r.den).toBe(3n);
    expect(new Rational(0n, 7n).equals(Rational.zero)).toBe(true);
  });

  it("rejects zero denominators", () => {
    expect(() => new Rational(1n, 0n)).toThrow(DivisionByZero);
    expect(() => Rational.one.div(Rational.zero)).toThrow(DivisionByZero);
    expect(() => Rational.zero.powInt(-1n)).toThrow(DivisionByZero);
  });

  it("does exact field arithmetic", () => {
    const third = new Rational(1n, 3n);
    const sixth = new Rational(1n, 6n);
    expect(third.add(sixth).equals(new Rational(1n, 2n))).toBe(true);
    expect(third.sub(third).isZero()).toBe(true);
    expect(third.mul(new Rational(3n)).equals(Rational.one)).toBe(true);
    expect(third.div(sixth).equals(new Rational(2n))).toBe(true);
    expect(new Rational(2n, 3n).powInt(-2n).equals(new Rational(9n, 4n))).toBe(true);
  });

  it("parses user input exactly", () => {
    expect(Rational.parse("3")?.equals(Rational.of(3))).toBe(true);
    expect(Rational.parse("-3")?.equals(Rational.of(-3))).toBe(true);
    expect(Rational.parse(" 3 / 4 ")?.equals(new Rational(3n, 4n))).toBe(true);
    expect(Rational.parse("-2/6")?.equals(new Rational(-1n, 3n))).toBe(true);
    expect(Rational.parse("x")).toBeUndefined();
    expect(Rational.parse("1/0")).toBeUndefined();
    expect(Rational.parse("1.5")).toBeUndefined();
    expect(Rational.parse("")).toBeUndefined();
  });

  it("property: a + (-a) = 0 and (a*b)/b = a (b != 0)", () => {
    fc.assert(
      fc.property(arbRational, arbRational, (a, b) => {
        expect(a.add(a.neg()).isZero()).toBe(true);
        if (!b.isZero()) {
          expect(a.mul(b).div(b).equals(a)).toBe(true);
        }
      }),
    );
  });
});
