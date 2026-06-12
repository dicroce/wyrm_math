/**
 * Disjunctive rewrites. THE UNION PROPERTY is the soundness contract:
 *   - completeness: every solution of the original satisfies AT LEAST ONE
 *     branch (where the branch is defined);
 *   - soundness: every branch solution satisfies the original.
 * Plus the end-to-end quadratic flows these rules exist for.
 */
import fc from "fast-check";
import { describe, expect, it } from "vitest";
import {
  applyBranchingRule,
  branchingRuleById,
  Derivation,
  eq,
  equation,
  int,
  invariantViolations,
  mkJudgment,
  movesFrom,
  pow,
  product,
  Rational,
  ruleById,
  simplifySqrt,
  sqrt,
  sqrtBothSides,
  sum,
  truthValue,
  variable,
  zeroProduct,
  type Env,
  type Equation,
  type Move,
} from "../src/index.js";
import { arbEnvs, arbExpr } from "./gen.js";

function assertUnionProperty(
  original: Equation,
  branches: readonly { judgment: { equation: Equation } }[],
  envs: readonly Env[],
): void {
  for (const env of envs) {
    const orig = truthValue(original, env);
    const branchTruths = branches.map((b) => truthValue(b.judgment.equation, env));
    if (orig === true) {
      // Completeness: some branch must hold (an undefined branch makes no claim,
      // but at least one branch must be defined-and-true).
      expect(
        branchTruths.some((t) => t === true),
        `original true but no branch true under ${[...env]}`,
      ).toBe(true);
    }
    for (const t of branchTruths) {
      if (t === true && orig !== undefined) {
        expect(orig, "branch true but original false").toBe(true); // soundness
      }
    }
  }
}

describe("sqrt-both-sides", () => {
  it("property: the ± branches union to exactly the original solutions", () => {
    fc.assert(
      fc.property(arbExpr, arbExpr, arbEnvs, (base, rhs, envs) => {
        const eqn = equation(pow(base, int(2)), rhs);
        const j = mkJudgment(eqn);
        expect(sqrtBothSides.precondition(j, eqn.id, {})).toBe(true);
        const branches = applyBranchingRule(j, sqrtBothSides, eqn.id, {});
        expect(branches).toHaveLength(2);
        for (const b of branches) {
          expect(invariantViolations(b.judgment.equation)).toEqual([]);
        }
        assertUnionProperty(eqn, branches, envs);
      }),
    );
  });

  it("rejects non-squares, inequalities, and higher powers", () => {
    const e1 = equation(variable("x"), int(9));
    expect(sqrtBothSides.precondition(mkJudgment(e1), e1.id, {})).toBe(false);
    const e2 = equation(pow(variable("x"), int(2)), int(9), "<");
    expect(sqrtBothSides.precondition(mkJudgment(e2), e2.id, {})).toBe(false);
    const e3 = equation(pow(variable("x"), int(3)), int(8));
    expect(sqrtBothSides.precondition(mkJudgment(e3), e3.id, {})).toBe(false);
  });
});

describe("zero-product", () => {
  it("property: one branch per factor, union equals the original", () => {
    fc.assert(
      fc.property(
        fc.array(
          arbExpr.filter((e) => e.kind !== "product"),
          { minLength: 2, maxLength: 3 },
        ),
        fc.boolean(),
        arbEnvs,
        (factors, productOnLhs, envs) => {
          const p = product(factors);
          if (p.kind !== "product") return;
          const eqn = productOnLhs ? equation(p, int(0)) : equation(int(0), p);
          const j = mkJudgment(eqn);
          expect(zeroProduct.precondition(j, eqn.id, {})).toBe(true);
          const branches = applyBranchingRule(j, zeroProduct, eqn.id, {});
          expect(branches).toHaveLength(p.children.length);
          assertUnionProperty(eqn, branches, envs);
        },
      ),
    );
  });

  it("rejects a nonzero right side", () => {
    const p = product([variable("x"), variable("y")]);
    if (p.kind !== "product") throw new Error("unreachable");
    const eqn = equation(p, int(5));
    expect(zeroProduct.precondition(mkJudgment(eqn), eqn.id, {})).toBe(false);
  });
});

describe("simplify-sqrt", () => {
  it("evaluates perfect squares and rejects everything else", () => {
    const nine = sqrt(int(9));
    const eqn = equation(variable("x"), nine);
    const j = mkJudgment(eqn);
    expect(simplifySqrt.precondition(j, nine.id, {})).toBe(true);
    const { equation: after } = simplifySqrt.apply(j, nine.id, {});
    expect(eq(after, equation(variable("x"), int(3)))).toBe(true);

    const eight = sqrt(int(8));
    const eqn2 = equation(variable("x"), eight);
    expect(simplifySqrt.precondition(mkJudgment(eqn2), eight.id, {})).toBe(false);
    const negNine = sqrt(int(-9));
    const eqn3 = equation(variable("x"), negNine);
    expect(simplifySqrt.precondition(mkJudgment(eqn3), negNine.id, {})).toBe(false);
  });
});

describe("quadratics end to end", () => {
  function moveFor(d: Derivation, handle: string, ruleId: string): Move {
    const m = movesFrom(d.current, handle).find((mv) => mv.ruleId === ruleId);
    expect(m, `no ${ruleId} move from ${handle}`).toBeDefined();
    return m!;
  }

  it("solves x² = 9 to x = 3 AND x = −3, both branches live and verified", () => {
    const square = pow(variable("x"), int(2));
    const eqn = equation(square, int(9));
    const d = new Derivation(eqn);

    // Tap the square: a branching move with no drop target.
    const tap = moveFor(d, square.id, "sqrt-both-sides");
    expect(tap.branching).toBe(true);
    expect(tap.dropTarget).toBeUndefined();
    const branches = d.applyBranching(branchingRuleById(tap.ruleId), tap.location, tap.params);
    expect(branches).toHaveLength(2);
    expect(d.currentNode).toBe(branches[0]);

    // Positive branch: x = √9 — tap the radical — x = 3.
    const rhs1 = d.current.equation.rhs;
    expect(rhs1.kind).toBe("sqrt");
    const m1 = moveFor(d, rhs1.id, "simplify-sqrt");
    d.apply(ruleById(m1.ruleId), m1.location, m1.params);
    expect(eq(d.current.equation, equation(variable("x"), int(3)))).toBe(true);
    expect(d.checkSolution(new Map([["x", Rational.of(3)]])).verdict).toBe("verified");

    // Negative branch stays live: x = −√9 — tap the radical — x = −3.
    d.goto(branches[1]!.id);
    const rhs2 = d.current.equation.rhs;
    if (rhs2.kind !== "neg") throw new Error("unreachable");
    expect(rhs2.child.kind).toBe("sqrt");
    const m2 = moveFor(d, rhs2.child.id, "simplify-sqrt");
    d.apply(ruleById(m2.ruleId), m2.location, m2.params);
    expect(eq(d.current.equation, equation(variable("x"), int(-3)))).toBe(true);
    expect(d.checkSolution(new Map([["x", Rational.of(-3)]])).verdict).toBe("verified");
  });

  it("solves (x+2)·(x+3) = 0 via zero-product to x = −2, with x+3 = 0 live", () => {
    const f1 = sum([variable("x"), int(2)]);
    const f2 = sum([variable("x"), int(3)]);
    const p = product([f1, f2]);
    if (p.kind !== "product") throw new Error("unreachable");
    const eqn = equation(p, int(0));
    const d = new Derivation(eqn);

    const tap = moveFor(d, p.id, "zero-product");
    expect(tap.branching).toBe(true);
    const branches = d.applyBranching(branchingRuleById(tap.ruleId), tap.location, tap.params);
    expect(branches).toHaveLength(2);
    expect(eq(d.current.equation, equation(sum([variable("x"), int(2)]), int(0)))).toBe(true);

    // Solve branch 1: move the 2 across, fold 0 − 2.
    const lhs1 = d.current.equation.lhs;
    if (lhs1.kind !== "sum") throw new Error("unreachable");
    const two = lhs1.children.find((c) => c.kind === "int")!;
    const mv = moveFor(d, two.id, "move-term-across");
    d.apply(ruleById(mv.ruleId), mv.location, mv.params);
    const rhsSum = d.current.equation.rhs;
    if (rhsSum.kind !== "sum") throw new Error("unreachable");
    const mc = moveFor(d, rhsSum.children[0]!.id, "combine-integers");
    d.apply(ruleById(mc.ruleId), mc.location, mc.params);
    expect(eq(d.current.equation, equation(variable("x"), int(-2)))).toBe(true);
    expect(d.checkSolution(new Map([["x", Rational.of(-2)]])).verdict).toBe("verified");

    // The sibling branch is a live, navigable state.
    d.goto(branches[1]!.id);
    expect(eq(d.current.equation, equation(sum([variable("x"), int(3)]), int(0)))).toBe(true);
  });
});
