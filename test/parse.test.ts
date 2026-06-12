import fc from "fast-check";
import { describe, expect, it } from "vitest";
import {
  eq,
  equation,
  exprToString,
  fraction,
  int,
  neg,
  ParseError,
  parseEquation,
  pow,
  product,
  sqrt,
  sum,
  variable,
} from "../src/index.js";
import { arbEquation } from "./gen.js";

describe("parseEquation", () => {
  it("parses the motivating example: (1/4)*2 = 1/2", () => {
    const parsed = parseEquation("(1/4)*2 = 1/2");
    const expected = equation(
      product([fraction([int(1)], [int(4)]), int(2)]),
      fraction([int(1)], [int(2)]),
    );
    expect(eq(parsed, expected)).toBe(true);
  });

  it("parses juxtaposition, relations, powers, radicals, and unary minus", () => {
    expect(
      eq(
        parseEquation("2x + 3 < 11"),
        equation(sum([product([int(2), variable("x")]), int(3)]), int(11), "<"),
      ),
    ).toBe(true);
    expect(
      eq(parseEquation("x^2 = 9"), equation(pow(variable("x"), int(2)), int(9))),
    ).toBe(true);
    expect(
      eq(parseEquation("x^-1 = 2"), equation(pow(variable("x"), int(-1)), int(2))),
    ).toBe(true);
    expect(eq(parseEquation("sqrt(9) = 3"), equation(sqrt(int(9)), int(3)))).toBe(true);
    expect(eq(parseEquation("√9 = 3"), equation(sqrt(int(9)), int(3)))).toBe(true);
    expect(
      eq(parseEquation("-2x <= 6"), equation(product([int(-2), variable("x")]), int(6), "≤")),
    ).toBe(true);
    expect(
      eq(
        parseEquation("(x+2)(x+3) = 0"),
        equation(
          product([sum([variable("x"), int(2)]), sum([variable("x"), int(3)])]),
          int(0),
        ),
      ),
    ).toBe(true);
  });

  it("absorbs product parts into fraction lists and chains division", () => {
    // (a·b)/c keeps the numerator as a LIST — the engine's canonical form.
    const parsed = parseEquation("(2x)/3 = y");
    const expected = equation(
      fraction([int(2), variable("x")], [int(3)]),
      variable("y"),
    );
    expect(eq(parsed, expected)).toBe(true);

    // a/b/c = a/(b·c).
    expect(
      eq(
        parseEquation("1/2/x = y"),
        equation(fraction([int(1)], [int(2), variable("x")]), variable("y")),
      ),
    ).toBe(true);

    // 2 - x/3: subtraction binds looser than division.
    expect(
      eq(
        parseEquation("2 - x/3 = y"),
        equation(sum([int(2), neg(fraction([variable("x")], [int(3)]))]), variable("y")),
      ),
    ).toBe(true);
  });

  it("rejects bad input with helpful messages", () => {
    expect(() => parseEquation("")).toThrow(ParseError);
    expect(() => parseEquation("x + 2")).toThrow(/relation/);
    expect(() => parseEquation("0.5 = x")).toThrow(/fraction like 1\/2/);
    expect(() => parseEquation("x² = 9")).toThrow(/caret/);
    expect(() => parseEquation("(x = 3")).toThrow(ParseError);
    expect(() => parseEquation("x = 3 = 4")).toThrow(ParseError);
    expect(() => parseEquation("x = ")).toThrow(ParseError);
    expect(() => parseEquation("x ? 3")).toThrow(/unexpected character/);
  });

  it("property: round-trips every printable equation", () => {
    fc.assert(
      fc.property(arbEquation, (eqn) => {
        const printed = exprToString(eqn);
        const reparsed = parseEquation(printed);
        expect(eq(reparsed, eqn), printed).toBe(true);
      }),
    );
  });
});
