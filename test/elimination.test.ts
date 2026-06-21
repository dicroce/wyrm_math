import fc from "fast-check";
import { describe, expect, it } from "vitest";
import {
  eliminate,
  eliminateInSystem,
  equation,
  exprToString,
  int,
  mkSystem,
  neg,
  sum,
  systemTruth,
  variable,
} from "../src/index.js";
import { arbEnvs, arbEquation } from "./gen.js";

const xPlusY = (): ReturnType<typeof sum> => sum([variable("x"), variable("y")]);
const xMinusY = (): ReturnType<typeof sum> => sum([variable("x"), neg(variable("y"))]);

describe("eliminate", () => {
  it("builds the unsimplified linear combination α·A + β·B", () => {
    const a = equation(xPlusY(), int(5)); // x + y = 5
    const b = equation(xMinusY(), int(1)); // x − y = 1
    // the sum constructor flattens, so adding the two sides gives one flat sum
    expect(exprToString(eliminate(a, b, 1n, 1n)!)).toBe("(x + y + x + -y) = (5 + 1)");
  });

  it("shows coefficients for |c| ≠ 1", () => {
    const a = equation(xPlusY(), int(5));
    const b = equation(xMinusY(), int(1));
    expect(exprToString(eliminate(a, b, 2n, 3n)!)).toBe(
      "((2 * (x + y)) + (3 * (x + -y))) = ((2 * 5) + (3 * 1))",
    );
  });

  it("rejects β = 0 (non-invertible) and non-equalities", () => {
    const a = equation(xPlusY(), int(5));
    const b = equation(xMinusY(), int(1));
    expect(eliminate(a, b, 1n, 0n)).toBeUndefined();
    expect(eliminate(equation(xPlusY(), int(5), "<"), b, 1n, 1n)).toBeUndefined();
  });
});

describe("eliminateInSystem", () => {
  it("replaces the target with the combination, keeps the other equation", () => {
    const sys = mkSystem([equation(xPlusY(), int(5)), equation(xMinusY(), int(1))]);
    const out = eliminateInSystem(sys, 0, 1, 1n, 1n)!;
    expect(out.equations[0]).toBe(sys.equations[0]); // kept (identity)
    expect(exprToString(out.equations[1]!)).toBe("(x + y + x + -y) = (5 + 1)");
  });

  it("rejects same-index", () => {
    const sys = mkSystem([equation(xPlusY(), int(5)), equation(xMinusY(), int(1))]);
    expect(eliminateInSystem(sys, 1, 1, 1n, 1n)).toBeUndefined();
  });
});

// Soundness: {A, B} and {A, α·A + β·B} (β ≠ 0) have the same solution set.
describe("elimination soundness", () => {
  it("preserves the system's solution set for any α and nonzero β", () => {
    const coeff = fc.integer({ min: -5, max: 5 }).map(BigInt);
    const nonzero = fc
      .integer({ min: -5, max: 5 })
      .filter((n) => n !== 0)
      .map(BigInt);
    fc.assert(
      fc.property(arbEquation, arbEquation, coeff, nonzero, arbEnvs, (a, b, alpha, beta, envs) => {
        const sys = mkSystem([a, b]);
        const sys2 = eliminateInSystem(sys, 0, 1, alpha, beta)!;
        for (const env of envs) {
          const t1 = systemTruth(sys, env);
          const t2 = systemTruth(sys2, env);
          if (t1 === undefined || t2 === undefined) continue;
          expect(t2).toBe(t1);
        }
      }),
    );
  });
});
