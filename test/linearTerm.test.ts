import { describe, expect, it } from "vitest";
import { int, linearTerm, neg, parseEquation, pow, product, variable } from "../src/index.js";

describe("linearTerm", () => {
  it("reads the signed coefficient + variable of a simple linear term", () => {
    expect(linearTerm(variable("y"))).toEqual({ coeff: 1n, variable: "y" });
    expect(linearTerm(neg(variable("y")))).toEqual({ coeff: -1n, variable: "y" });
    expect(linearTerm(product([int(2), variable("x")]))).toEqual({ coeff: 2n, variable: "x" });
    // Neg OVER the product (binary minus): −(3·x)
    expect(linearTerm(neg(product([int(3), variable("x")])))).toEqual({ coeff: -3n, variable: "x" });
    // Neg INSIDE as a factor (unary minus): (−3)·x
    expect(linearTerm(product([int(-3), variable("x")]))).toEqual({ coeff: -3n, variable: "x" });
    // Double negative collapses: (−2)(−y) → 2y
    expect(linearTerm(parseEquation("(-2)(-y) = 1").lhs)).toEqual({ coeff: 2n, variable: "y" });
  });

  it("rejects terms that aren't a single linear variable", () => {
    expect(linearTerm(product([variable("x"), variable("y")]))).toBeUndefined(); // x·y
    expect(linearTerm(pow(variable("x"), int(2)))).toBeUndefined(); // x²
    expect(linearTerm(int(6))).toBeUndefined(); // a bare constant
    expect(linearTerm(parseEquation("6 = x").lhs)).toBeUndefined();
  });
});
