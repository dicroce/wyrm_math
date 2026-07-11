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
  evalExpr,
  int,
  invariantViolations,
  mkJudgment,
  movesFrom,
  neg,
  nthRootBothSides,
  pow,
  product,
  quadraticFormula,
  rationalToExpr,
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
import { termFromCoeff } from "../src/rules/splitTerm.js";
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

describe("nth-root-both-sides", () => {
  const arbRoot = fc
    .tuple(fc.bigInt({ min: -4n, max: 4n }), fc.bigInt({ min: 1n, max: 4n }))
    .map(([num, den]) => new Rational(num, den));
  const arbDegree = fc.bigInt({ min: 3n, max: 6n });

  it("property: the branches union to exactly the original solutions", () => {
    fc.assert(
      fc.property(arbExpr, arbRoot, arbDegree, arbEnvs, (base, r, n, envs) => {
        // rhs = rⁿ, a constant with an exact nth root, so the rule fires.
        const eqn = equation(pow(base, int(n)), rationalToExpr(r.powInt(n)));
        const j = mkJudgment(eqn);
        expect(nthRootBothSides.precondition(j, eqn.id, {})).toBe(true);
        const branches = applyBranchingRule(j, nthRootBothSides, eqn.id, {});
        expect(branches.length).toBeGreaterThanOrEqual(1);
        expect(branches.length).toBeLessThanOrEqual(2);
        for (const b of branches) {
          expect(invariantViolations(b.judgment.equation)).toEqual([]);
        }
        assertUnionProperty(eqn, branches, envs);
      }),
    );
  });

  it("solves x³ = 8 to x = 2 (single real root)", () => {
    const eqn = equation(pow(variable("x"), int(3)), int(8));
    const branches = applyBranchingRule(mkJudgment(eqn), nthRootBothSides, eqn.id, {});
    expect(branches).toHaveLength(1);
    const only = branches[0]!.judgment.equation;
    expect(eq(only.lhs, variable("x"))).toBe(true);
    expect(evalExpr(only.rhs, new Map()).asRational()?.equals(new Rational(2n))).toBe(true);
  });

  it("solves x⁴ = 16 to x = 2 and x = −2", () => {
    const eqn = equation(pow(variable("x"), int(4)), int(16));
    const branches = applyBranchingRule(mkJudgment(eqn), nthRootBothSides, eqn.id, {});
    expect(branches).toHaveLength(2);
    const values = branches.map((b) =>
      evalExpr(b.judgment.equation.rhs, new Map()).asRational(),
    );
    expect(values[0]?.equals(new Rational(2n))).toBe(true);
    expect(values[1]?.equals(new Rational(-2n))).toBe(true);
    for (const b of branches) {
      expect(eq(b.judgment.equation.lhs, variable("x"))).toBe(true);
    }
  });

  it("solves x³ = −8 to x = −2 (odd root of a negative)", () => {
    const eqn = equation(pow(variable("x"), int(3)), neg(int(8)));
    const branches = applyBranchingRule(mkJudgment(eqn), nthRootBothSides, eqn.id, {});
    expect(branches).toHaveLength(1);
    expect(evalExpr(branches[0]!.judgment.equation.rhs, new Map()).asRational()?.equals(new Rational(-2n))).toBe(true);
  });

  it("does not fire on squares or non-perfect powers", () => {
    const square = equation(pow(variable("x"), int(2)), int(9));
    expect(nthRootBothSides.precondition(mkJudgment(square), square.id, {})).toBe(false);
    const imperfect = equation(pow(variable("x"), int(3)), int(7));
    expect(nthRootBothSides.precondition(mkJudgment(imperfect), imperfect.id, {})).toBe(false);
    // x⁴ = −16 has no real root — not offered.
    const negEven = equation(pow(variable("x"), int(4)), neg(int(16)));
    expect(nthRootBothSides.precondition(mkJudgment(negEven), negEven.id, {})).toBe(false);
    const inequality = equation(pow(variable("x"), int(3)), int(8), "<");
    expect(nthRootBothSides.precondition(mkJudgment(inequality), inequality.id, {})).toBe(false);
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

describe("quadratic-formula", () => {
  // a·x² + b·x + c, expanded (integer coefficients), as a side = 0 equation.
  const quadratic = (a: bigint, b: bigint, c: bigint, v = "x"): Equation => {
    const terms = [termFromCoeff(a, [pow(variable(v), int(2))])];
    if (b !== 0n) terms.push(termFromCoeff(b, [variable(v)]));
    if (c !== 0n) terms.push(termFromCoeff(c, []));
    return equation(terms.length === 1 ? terms[0]! : sum(terms), int(0));
  };

  it("property: the ± branches union to the quadratic's solutions", () => {
    fc.assert(
      fc.property(
        fc.integer({ min: 1, max: 3 }),
        fc.integer({ min: -4, max: 4 }),
        fc.integer({ min: -4, max: 4 }),
        (a, r1, r2) => {
          // Built from known roots r1, r2 → the discriminant is a perfect
          // square, so completeness (not just vacuous soundness) is exercised.
          const A = BigInt(a);
          const B = -A * BigInt(r1 + r2);
          const C = A * BigInt(r1) * BigInt(r2);
          const eqn = quadratic(A, B, C);
          const j = mkJudgment(eqn);
          expect(quadraticFormula.precondition(j, eqn.id, {})).toBe(true);
          const branches = applyBranchingRule(j, quadraticFormula, eqn.id, {});
          expect(branches).toHaveLength(2);
          for (const b of branches) expect(invariantViolations(b.judgment.equation)).toEqual([]);
          const envs: Env[] = [r1, r2, r1 + 1, r2 - 1, 0].map(
            (x) => new Map([["x", Rational.of(x)]]),
          );
          assertUnionProperty(eqn, branches, envs);
        },
      ),
    );
  });

  it("solves 2x² + 5x − 3 = 0 to x = 1/2 and x = −3 (subsumes factoring)", () => {
    const eqn = quadratic(2n, 5n, -3n);
    const branches = applyBranchingRule(mkJudgment(eqn), quadraticFormula, eqn.id, {});
    const roots = branches.map((b) => evalExpr(b.judgment.equation.rhs, new Map()).asRational()!);
    // Each computed root is exact and actually satisfies the original.
    for (const root of roots) {
      expect(truthValue(eqn, new Map([["x", root]]))).toBe(true);
    }
    expect(roots.map((r) => r.toString()).sort()).toEqual(["-3", "1/2"].sort());
  });

  it("reports no real solution for a negative discriminant (x² + 1 = 0)", () => {
    const eqn = quadratic(1n, 0n, 1n);
    const j = mkJudgment(eqn);
    expect(quadraticFormula.precondition(j, eqn.id, {})).toBe(true);
    const branches = applyBranchingRule(j, quadraticFormula, eqn.id, {});
    // √(−4) is an undefined point — no real value at any rational x.
    for (const b of branches) {
      expect(truthValue(b.judgment.equation, new Map([["x", Rational.of(0)]]))).toBeUndefined();
    }
  });

  it("is offered as a branching tap on an expanded quadratic = 0", () => {
    const eqn = quadratic(1n, -5n, 6n);
    const d = new Derivation(eqn);
    const m = movesFrom(d.current, eqn.lhs.id).find((mv) => mv.ruleId === "quadratic-formula");
    expect(m, "no quadratic-formula move offered").toBeDefined();
    expect(m!.branching).toBe(true);
  });
});

describe("simplify-sqrt", () => {
  it("evaluates perfect squares and pulls out square factors", () => {
    const nine = sqrt(int(9));
    const jNine = mkJudgment(equation(variable("x"), nine));
    expect(simplifySqrt.precondition(jNine, nine.id, {})).toBe(true);
    expect(eq(simplifySqrt.apply(jNine, nine.id, {}).equation, equation(variable("x"), int(3)))).toBe(
      true,
    );

    // √8 → 2√2 (pull out the square factor)
    const eight = sqrt(int(8));
    const jEight = mkJudgment(equation(variable("x"), eight));
    expect(simplifySqrt.precondition(jEight, eight.id, {})).toBe(true);
    const expected = equation(variable("x"), product([int(2), sqrt(int(2))]));
    expect(eq(simplifySqrt.apply(jEight, eight.id, {}).equation, expected)).toBe(true);

    // √1 → 1 (a perfect square; common as a quadratic discriminant when D = 1)
    const one = sqrt(int(1));
    const jOne = mkJudgment(equation(variable("x"), one));
    expect(simplifySqrt.precondition(jOne, one.id, {})).toBe(true);
    expect(eq(simplifySqrt.apply(jOne, one.id, {}).equation, equation(variable("x"), int(1)))).toBe(
      true,
    );
  });

  it("rejects an already-simplest or negative radical", () => {
    // √7 is square-free — already simplest, no move.
    const seven = sqrt(int(7));
    expect(simplifySqrt.precondition(mkJudgment(equation(variable("x"), seven)), seven.id, {})).toBe(
      false,
    );
    // √(−9) has no real value (it parses as √(Neg 9), child isn't an int).
    const negNine = sqrt(int(-9));
    expect(
      simplifySqrt.precondition(mkJudgment(equation(variable("x"), negNine)), negNine.id, {}),
    ).toBe(false);
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
