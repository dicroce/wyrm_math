import { describe, expect, it } from "vitest";
import {
  equation,
  evalExpr,
  fraction,
  int,
  neg,
  pow,
  product,
  Rational,
  sqrt,
  Surd,
  sum,
  truthValue,
  UnboundVariable,
  variable,
  type Env,
} from "../src/index.js";

const env = (x: number): Env => new Map([["x", Rational.of(x)]]);

describe("evalExpr", () => {
  const surd = (r: Rational): Surd => Surd.rational(r);

  it("evaluates (x + 2) * 3 exactly", () => {
    const e = product([sum([variable("x"), int(2)]), int(3)]);
    expect(evalExpr(e, env(1)).equals(surd(Rational.of(9)))).toBe(true);
  });

  it("evaluates negation, fractions and powers", () => {
    const e = fraction([sum([variable("x"), neg(int(1))])], [int(2)]);
    expect(evalExpr(e, env(5)).equals(surd(Rational.of(2)))).toBe(true);
    expect(evalExpr(pow(variable("x"), int(3)), env(-2)).equals(surd(Rational.of(-8)))).toBe(true);
    expect(evalExpr(pow(int(7), int(0)), env(0)).equals(surd(Rational.one))).toBe(true);
  });

  it("collapses rational roots, makes irrationals exact surds, defers complex", () => {
    expect(evalExpr(sqrt(int(9)), env(0)).equals(surd(Rational.of(3)))).toBe(true);
    expect(
      evalExpr(sqrt(fraction([int(9)], [int(4)])), env(0)).equals(surd(new Rational(3n, 2n))),
    ).toBe(true);
    // √2 is an exact value now, so √2 = 1 is decidably FALSE (not undefined).
    expect(truthValue(equation(sqrt(int(2)), int(1)), env(0))).toBe(false);
    // √(−1) has no real value — undefined (complex deferred), not a lie.
    expect(truthValue(equation(sqrt(int(-1)), int(1)), env(0))).toBeUndefined();
  });

  it("treats empty fraction lists as 1", () => {
    expect(evalExpr(fraction([], []), env(0)).equals(surd(Rational.one))).toBe(true);
  });

  it("throws on unbound variables", () => {
    expect(() => evalExpr(variable("q"), env(1))).toThrow(UnboundVariable);
  });
});

describe("truthValue", () => {
  it("is boolean where defined", () => {
    const eqn = equation(sum([variable("x"), int(2)]), int(5));
    expect(truthValue(eqn, env(3))).toBe(true);
    expect(truthValue(eqn, env(4))).toBe(false);
  });

  it("is undefined at poles instead of lying", () => {
    // 1/x = 1/x is undefined at x = 0, not true.
    const oneOverX = () => fraction([int(1)], [variable("x")]);
    const eqn = equation(oneOverX(), oneOverX());
    expect(truthValue(eqn, env(0))).toBeUndefined();
    expect(truthValue(eqn, env(2))).toBe(true);
  });
});
