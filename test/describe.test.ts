import { describe, expect, it } from "vitest";
import {
  describeExpr,
  describeMove,
  enumerateMoves,
  fraction,
  int,
  mkJudgment,
  neg,
  parseEquation,
  pow,
  product,
  sqrt,
  sum,
  variable,
  type Move,
} from "../src/index.js";

const captionsFor = (src: string, ruleId: string): (string | undefined)[] => {
  const j = mkJudgment(parseEquation(src));
  return enumerateMoves(j)
    .filter((m: Move) => m.ruleId === ruleId)
    .map((m) => describeMove(j, m));
};

describe("describeExpr", () => {
  it("renders atoms", () => {
    expect(describeExpr(int(5))).toBe("5");
    expect(describeExpr(variable("x"))).toBe("x");
    expect(describeExpr(neg(int(3)))).toBe("−3");
  });

  it("uses implicit multiplication for coefficients", () => {
    expect(describeExpr(product([int(3), variable("x")]))).toBe("3x");
    expect(describeExpr(product([variable("x"), variable("y")]))).toBe("xy");
    // two integers must stay separated, or 2·3 would read as 23
    expect(describeExpr(product([int(2), int(3)]))).toBe("2·3");
  });

  it("uses superscripts for integer powers", () => {
    expect(describeExpr(pow(variable("x"), int(2)))).toBe("x²");
    expect(describeExpr(pow(variable("x"), int(10)))).toBe("x¹⁰");
  });

  it("renders radicals and fractions", () => {
    expect(describeExpr(sqrt(int(2)))).toBe("√2");
    expect(describeExpr(fraction([int(1)], [int(2)]))).toBe("1/2");
    expect(describeExpr(fraction([variable("x")], [int(2)]))).toBe("x/2");
  });

  it("renders sums with leading-sign awareness", () => {
    expect(describeExpr(sum([variable("x"), int(3)]))).toBe("x + 3");
    expect(describeExpr(sum([variable("x"), neg(int(3))]))).toBe("x − 3");
  });
});

describe("describeMove — both-sides moves name their operand", () => {
  it("subtracts a positive term moved across", () => {
    const caps = captionsFor("x + 3 = 5", "move-term-across");
    expect(caps).toContain("Subtract 3 from both sides");
    expect(caps).toContain("Subtract x from both sides");
  });

  it("adds when a negative term is moved across", () => {
    const caps = captionsFor("x - 3 = 5", "move-term-across");
    expect(caps).toContain("Add 3 to both sides");
  });

  it("names the divisor", () => {
    const caps = captionsFor("2x = 8", "divide-both-sides");
    expect(caps).toContain("Divide both sides by 2");
    expect(caps).toContain("Divide both sides by 2x");
  });

  it("names the multiplier when clearing a denominator", () => {
    const caps = captionsFor("x/2 = 3", "multiply-both-sides");
    expect(caps).toContain("Multiply both sides by 2");
  });
});

describe("describeMove — structural and relation moves", () => {
  it("captions square-both-sides", () => {
    expect(captionsFor("x = 2", "square-both-sides")).toContain("Square both sides");
  });

  it("names both operands for combine-integers, showing the negative", () => {
    // subtraction reads as adding the opposite — the second operand keeps its sign
    expect(captionsFor("x = 6 - 1", "combine-integers")).toContain("Add 6 and −1");
    expect(captionsFor("x = 6 + 1", "combine-integers")).toContain("Add 6 and 1");
    // sum order, not drag order, drives the reading
    expect(captionsFor("x = 6 - 1", "combine-integers")).not.toContain("Add −1 and 6");
  });

  it("returns undefined for an unknown rule id", () => {
    const j = mkJudgment(parseEquation("x = 1"));
    const fake: Move = { ruleId: "no-such-rule", location: "n1", params: {}, handle: "n1" };
    expect(describeMove(j, fake)).toBeUndefined();
  });
});
