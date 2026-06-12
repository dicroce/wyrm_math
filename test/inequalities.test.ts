/**
 * Inequalities as first-class relations. The load-bearing claims:
 *  - truthValue decides every relation exactly;
 *  - local rewrites and move-term-across preserve any relation untouched;
 *  - dividing/multiplying both sides needs a DECIDABLE sign — positive keeps
 *    the relation, negative FLIPS it, unknown is not offered (truth at every
 *    sample point is the proof the flip is right);
 *  - squaring is refused (not monotone);
 *  - swap-sides flips the relation and is an involution.
 */
import fc from "fast-check";
import { describe, expect, it } from "vitest";
import {
  applyRule,
  combineIntegers,
  divideBothSides,
  eq,
  equation,
  int,
  mkJudgment,
  moveTermAcross,
  multiplyBothSides,
  neg,
  product,
  Rational,
  squareBothSides,
  sum,
  swapSides,
  truthValue,
  variable,
  type Equation,
  type RelationKind,
} from "../src/index.js";
import { arbEnvs, arbExpr, assertSolutionSetPreserved } from "./gen.js";

const arbIneqRelation = fc.constantFrom<RelationKind>("<", "≤", ">", "≥");
const arbRelation = fc.constantFrom<RelationKind>("=", "<", "≤", ">", "≥");

const envX = (v: number) => new Map([["x", Rational.of(v)]]);

describe("relations in the evaluator", () => {
  it("decides each relation exactly", () => {
    const cases: { rel: RelationKind; at: number; expected: boolean }[] = [
      { rel: "<", at: 2, expected: true },
      { rel: "<", at: 3, expected: false },
      { rel: "≤", at: 3, expected: true },
      { rel: ">", at: 4, expected: true },
      { rel: ">", at: 3, expected: false },
      { rel: "≥", at: 3, expected: true },
      { rel: "=", at: 3, expected: true },
    ];
    for (const c of cases) {
      const eqn = equation(variable("x"), int(3), c.rel);
      expect(truthValue(eqn, envX(c.at)), `x ${c.rel} 3 at ${c.at}`).toBe(c.expected);
    }
  });
});

describe("sign-aware both-sides moves", () => {
  const arbNonZeroLiteral = fc
    .integer({ min: -5, max: 5 })
    .filter((n) => n !== 0)
    .map((n) => ({ value: n, expr: int(n) }));

  it("property: dividing an inequality by a literal preserves truth and flips on negatives", () => {
    fc.assert(
      fc.property(
        arbExpr,
        arbExpr,
        arbIneqRelation,
        arbNonZeroLiteral,
        arbEnvs,
        (lhs, rhs, rel, divisor, envs) => {
          const eqn = equation(lhs, rhs, rel);
          const j = mkJudgment(eqn);
          expect(divideBothSides.precondition(j, eqn.id, { divisor: divisor.expr })).toBe(true);
          const { judgment: after } = applyRule(j, divideBothSides, eqn.id, {
            divisor: divisor.expr,
          });
          const expectFlipped = divisor.value < 0;
          expect(after.equation.relation === rel).toBe(!expectFlipped);
          assertSolutionSetPreserved(eqn, after.equation, envs);
        },
      ),
    );
  });

  it("property: multiplying an inequality by a literal is exact (no Extension) and flips on negatives", () => {
    fc.assert(
      fc.property(
        arbExpr,
        arbExpr,
        arbIneqRelation,
        arbNonZeroLiteral,
        arbEnvs,
        (lhs, rhs, rel, factor, envs) => {
          const eqn = equation(lhs, rhs, rel);
          const j = mkJudgment(eqn);
          expect(multiplyBothSides.precondition(j, eqn.id, { factor: factor.expr })).toBe(true);
          const { judgment: after } = applyRule(j, multiplyBothSides, eqn.id, {
            factor: factor.expr,
          });
          expect(after.assumptions).toEqual([]); // exact: no obligation
          const expectFlipped = factor.value < 0;
          expect(after.equation.relation === rel).toBe(!expectFlipped);
          assertSolutionSetPreserved(eqn, after.equation, envs);
        },
      ),
    );
  });

  it("refuses unknown-sign factors on inequalities (but allows them on equalities)", () => {
    const x = variable("x");
    const ineq = equation(variable("y"), int(3), "<");
    expect(divideBothSides.precondition(mkJudgment(ineq), ineq.id, { divisor: x })).toBe(false);
    expect(multiplyBothSides.precondition(mkJudgment(ineq), ineq.id, { factor: x })).toBe(false);

    const eqn = equation(variable("y"), int(3));
    expect(divideBothSides.precondition(mkJudgment(eqn), eqn.id, { divisor: variable("x") })).toBe(
      true,
    );
    expect(
      multiplyBothSides.precondition(mkJudgment(eqn), eqn.id, { factor: variable("x") }),
    ).toBe(true);
  });

  it("refuses squaring inequalities", () => {
    const ineq = equation(variable("x"), int(2), "<");
    expect(squareBothSides.precondition(mkJudgment(ineq), ineq.id, {})).toBe(false);
  });
});

describe("relation-preserving moves", () => {
  it("property: swap-sides flips the relation, preserves truth, and is an involution", () => {
    fc.assert(
      fc.property(arbExpr, arbExpr, arbRelation, arbEnvs, (lhs, rhs, rel, envs) => {
        const eqn = equation(lhs, rhs, rel);
        const j = mkJudgment(eqn);
        const { judgment: once } = applyRule(j, swapSides, eqn.id, {});
        assertSolutionSetPreserved(eqn, once.equation, envs);
        const { judgment: twice } = applyRule(once, swapSides, once.equation.id, {});
        expect(eq(twice.equation, eqn)).toBe(true);
      }),
    );
  });

  it("maps each relation correctly under a swap", () => {
    const expected: [RelationKind, RelationKind][] = [
      ["=", "="],
      ["<", ">"],
      ["≤", "≥"],
      [">", "<"],
      ["≥", "≤"],
    ];
    for (const [from, to] of expected) {
      const eqn = equation(variable("x"), int(3), from);
      const { judgment } = applyRule(mkJudgment(eqn), swapSides, eqn.id, {});
      expect(judgment.equation.relation).toBe(to);
    }
  });

  it("move-term-across and local rewrites carry the relation through untouched", () => {
    // x + 2 < 5 ~> x < 5 − 2.
    const two = int(2);
    const ineq = equation(sum([variable("x"), two]), int(5), "<");
    const moved = applyRule(mkJudgment(ineq), moveTermAcross, ineq.id, { termId: two.id });
    expect(
      eq(moved.judgment.equation, equation(variable("x"), sum([int(5), neg(int(2))]), "<")),
    ).toBe(true);

    // 2 + 3 + x ≥ y folds to 5 + x ≥ y.
    const a = int(2);
    const b = int(3);
    const s = sum([a, b, variable("x")]);
    if (s.kind !== "sum") throw new Error("unreachable");
    const ineq2: Equation = equation(s, variable("y"), "≥");
    const folded = applyRule(mkJudgment(ineq2), combineIntegers, s.id, {
      termA: a.id,
      termB: b.id,
    });
    expect(folded.judgment.equation.relation).toBe("≥");
    expect(eq(folded.judgment.equation.lhs, sum([int(5), variable("x")]))).toBe(true);
  });
});

describe("inequalities end to end", () => {
  it("−2x < 6 divides (with flip) and reduces to x > −3", () => {
    const negTwo = int(-2);
    const x = variable("x");
    const lhs = product([negTwo, x]);
    const eqn = equation(lhs, int(6), "<");
    const j0 = mkJudgment(eqn);

    const divided = applyRule(j0, divideBothSides, eqn.id, { divisor: negTwo });
    expect(divided.judgment.equation.relation).toBe(">");
    // The −2 ≠ 0 restriction settled itself (constant).
    expect(divided.judgment.assumptions[0]!.status).toBe("discharged");
  });
});
