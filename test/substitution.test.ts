import fc from "fast-check";
import { describe, expect, it } from "vitest";
import {
  equation,
  exprToString,
  int,
  mkSystem,
  product,
  solvedVariable,
  substitute,
  substituteInSystem,
  sum,
  systemTruth,
  variable,
  variablesIn,
} from "../src/index.js";
import { arbEnvs, arbExpr, VAR_POOL } from "./gen.js";

describe("solvedVariable", () => {
  it("recognizes v = expr (either side)", () => {
    expect(solvedVariable(equation(variable("y"), product([int(2), variable("x")])))).toMatchObject({
      variable: "y",
    });
    expect(
      solvedVariable(equation(product([int(2), variable("x")]), variable("y"))),
    ).toMatchObject({ variable: "y" });
  });

  it("rejects non-solved forms", () => {
    expect(solvedVariable(equation(product([int(2), variable("x")]), int(5)))).toBeUndefined();
    // self-referential: x = 1·x
    expect(
      solvedVariable(equation(variable("x"), product([int(1), variable("x")]))),
    ).toBeUndefined();
    // inequalities can't drive substitution
    expect(solvedVariable(equation(variable("y"), int(3), "<"))).toBeUndefined();
  });
});

describe("substitute", () => {
  it("replaces the solved variable in the target", () => {
    const source = equation(variable("y"), product([int(2), variable("x")])); // y = 2x
    const target = equation(sum([variable("x"), variable("y")]), int(6)); // x + y = 6
    const out = substitute(source, target)!;
    // x + 2x = 6  (unfolded — the learner simplifies next)
    expect(exprToString(out)).toBe("(x + (2 * x)) = 6");
  });

  it("is a no-op when the variable is absent from the target", () => {
    const source = equation(variable("y"), int(2));
    const target = equation(variable("x"), int(5)); // no y
    expect(exprToString(substitute(source, target)!)).toBe(exprToString(target));
  });

  it("returns undefined when the source isn't solved", () => {
    const source = equation(product([int(2), variable("x")]), int(5));
    const target = equation(variable("x"), int(1));
    expect(substitute(source, target)).toBeUndefined();
  });
});

describe("substituteInSystem", () => {
  it("rewrites the target, keeps the source and assumptions", () => {
    const sys = mkSystem([
      equation(variable("y"), product([int(2), variable("x")])), // y = 2x
      equation(sum([variable("x"), variable("y")]), int(6)), // x + y = 6
    ]);
    const out = substituteInSystem(sys, 0, 1)!;
    expect(out.equations[0]).toBe(sys.equations[0]); // source untouched (identity)
    expect(exprToString(out.equations[1]!)).toBe("(x + (2 * x)) = 6");
  });

  it("rejects same-index and unsolved sources", () => {
    const sys = mkSystem([equation(variable("y"), int(2)), equation(variable("x"), int(5))]);
    expect(substituteInSystem(sys, 0, 0)).toBeUndefined();
  });
});

// THE soundness property: substituting into a system preserves its intersection
// solution set. Pick a variable absent from a random value (so `v = value` is
// genuinely solved form), substitute into a random target, and compare
// systemTruth([v=value, target]) with systemTruth([v=value, target']) at every
// defined sample point.
describe("substitution soundness", () => {
  it("preserves the system's solution set", () => {
    fc.assert(
      fc.property(arbExpr, arbExpr, arbEnvs, (value, target, envs) => {
        const free = VAR_POOL.find((v) => !variablesIn(value).has(v));
        fc.pre(free !== undefined);
        const sys = mkSystem([equation(variable(free!), value), equation(target, int(0))]);
        const sys2 = substituteInSystem(sys, 0, 1)!;
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
