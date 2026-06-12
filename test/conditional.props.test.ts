/**
 * Property tests for CONDITIONAL soundness — the revised core invariant:
 * every reachable state is equivalent to the original equation GIVEN its
 * assumption set.
 *
 *  - Restriction-emitting rules: truth preserved at every sample point
 *    satisfying the result judgment's Restrictions/Pinned values.
 *  - Extension-emitting rules: one direction only — solutions are never
 *    lost; gaining is permitted and the obligation is checked separately.
 *  - Case splits: every solution of the original lands in exactly one live
 *    branch and satisfies that branch's judgment.
 *  - checkSolution: verified candidates satisfy the original; extraneous
 *    ones (built by multiplying both sides by x - k) do not.
 */
import fc from "fast-check";
import { describe, expect, it } from "vitest";
import {
  applyRule,
  cloneFresh,
  Derivation,
  divideBothSides,
  envSatisfiesAssumptions,
  eq,
  equation,
  evalExpr,
  fraction,
  int,
  invariantViolations,
  mkJudgment,
  multiplicativeCancellation,
  multiplyBothSides,
  pow,
  quotientOfPowers,
  Rational,
  rationalToExpr,
  restrictionStatus,
  squareBothSides,
  sum,
  truthValue,
  variable,
  type Expr,
  type Extension,
  type Restriction,
} from "../src/index.js";
import {
  arbEnv,
  arbEnvs,
  arbEquation,
  arbExpr,
  arbWrap,
  assertConditionallyPreserved,
  embed,
  VAR_POOL,
} from "./gen.js";

const noPins = new Map<string, Rational>();

describe("divide-both-sides (Restriction polarity)", () => {
  it("property: emits divisor ≠ 0 and preserves truth wherever it holds", () => {
    fc.assert(
      fc.property(arbEquation, arbExpr, arbEnvs, (eqn, divisor, envs) => {
        const j = mkJudgment(eqn);
        if (!divideBothSides.precondition(j, eqn.id, { divisor })) {
          // The only legitimate rejection without pins: a decidable zero.
          expect(restrictionStatus({ expr: divisor, value: Rational.zero }, noPins)).toBe("fails");
          return;
        }
        const { judgment: after } = applyRule(
          j,
          divideBothSides,
          eqn.id,
          { divisor },
          "test-step",
        );
        const r = after.assumptions.find((a) => a.kind === "restriction") as Restriction;
        expect(r).toBeDefined();
        expect(r.origin).toEqual({ kind: "rule", stepId: "test-step" });
        expect(invariantViolations(after.equation)).toEqual([]);
        assertConditionallyPreserved(eqn, after, envs);
      }),
    );
  });
});

describe("multiplicative-cancellation (Restriction polarity)", () => {
  const arbScenario = fc
    .tuple(
      // Product elements spread into fraction lists, so the pinned ids must
      // be non-products to stay direct list elements.
      arbExpr.filter((e) => e.kind !== "product"),
      fc.array(arbExpr, { maxLength: 2 }),
      fc.array(arbExpr, { maxLength: 2 }),
      arbWrap,
      fc.boolean(),
      arbExpr,
    )
    .map(([t, numExtras, denExtras, wrap, onLhs, other]) => {
      const tClone = cloneFresh(t);
      const f = fraction([t, ...numExtras], [tClone, ...denExtras]);
      return {
        t,
        eqn: embed(f, wrap, other, onLhs),
        loc: f.id,
        params: { numTermId: t.id, denTermId: tClone.id },
      };
    });

  it("property: cancels, emits t ≠ 0, preserves truth wherever it holds", () => {
    fc.assert(
      fc.property(arbScenario, arbEnvs, (sc, envs) => {
        const j = mkJudgment(sc.eqn);
        if (!multiplicativeCancellation.precondition(j, sc.loc, sc.params)) {
          expect(restrictionStatus({ expr: sc.t, value: Rational.zero }, noPins)).toBe("fails");
          return;
        }
        const { judgment: after } = applyRule(j, multiplicativeCancellation, sc.loc, sc.params);
        const r = after.assumptions.find((a) => a.kind === "restriction") as Restriction;
        expect(r).toBeDefined();
        expect(invariantViolations(after.equation)).toEqual([]);
        // Emission is unconditional; discharge resolves what is decidable.
        const decidable = restrictionStatus({ expr: sc.t, value: Rational.zero }, noPins);
        if (decidable === "holds") expect(r.status).toBe("discharged");
        assertConditionallyPreserved(sc.eqn, after, envs);
      }),
    );
  });
});

describe("quotient-of-powers (Restriction polarity)", () => {
  // Bare bases or literal powers of a shared base; Pow bases would
  // decompose one level deeper on the bare side (same caveat as
  // combine-like-factors), and Product bases would spread into the lists.
  const arbBase = arbExpr.filter((e) => e.kind !== "pow" && e.kind !== "product");
  const arbMaybeExp = fc.option(fc.integer({ min: 0, max: 3 }), { nil: undefined });

  const arbScenario = fc
    .tuple(
      arbBase,
      arbMaybeExp,
      arbMaybeExp,
      fc.array(arbExpr, { maxLength: 2 }),
      fc.array(arbExpr, { maxLength: 2 }),
      arbWrap,
      fc.boolean(),
      arbExpr,
    )
    .map(([base, expA, expB, numExtras, denExtras, wrap, onLhs, other]) => {
      const numTerm = expA === undefined ? base : pow(base, int(expA));
      const denBase = cloneFresh(base);
      const denTerm = expB === undefined ? denBase : pow(denBase, int(expB));
      const f = fraction([numTerm, ...numExtras], [denTerm, ...denExtras]);
      return {
        base,
        eqn: embed(f, wrap, other, onLhs),
        loc: f.id,
        params: { numTermId: numTerm.id, denTermId: denTerm.id },
      };
    });

  it("property: reduces exponents, emits base ≠ 0, preserves truth where it holds", () => {
    fc.assert(
      fc.property(arbScenario, arbEnvs, (sc, envs) => {
        const j = mkJudgment(sc.eqn);
        if (!quotientOfPowers.precondition(j, sc.loc, sc.params)) {
          expect(restrictionStatus({ expr: sc.base, value: Rational.zero }, noPins)).toBe("fails");
          return;
        }
        const { judgment: after } = applyRule(j, quotientOfPowers, sc.loc, sc.params);
        const r = after.assumptions.find((a) => a.kind === "restriction") as Restriction;
        expect(r).toBeDefined();
        expect(invariantViolations(after.equation)).toEqual([]);
        assertConditionallyPreserved(sc.eqn, after, envs);
      }),
    );
  });

  it("computes the textbook cases", () => {
    const cases: { m: number | undefined; n: number | undefined; expected: Expr }[] = [
      { m: 3, n: 2, expected: variable("x") },
      { m: 2, n: 3, expected: fraction([], [variable("x")]) },
      { m: undefined, n: 2, expected: fraction([], [variable("x")]) }, // x/x²
      { m: 5, n: 2, expected: pow(variable("x"), int(3)) },
    ];
    for (const c of cases) {
      const base = variable("x");
      const numTerm = c.m === undefined ? base : pow(base, int(c.m));
      const denBase = variable("x");
      const denTerm = c.n === undefined ? denBase : pow(denBase, int(c.n));
      const f = fraction([numTerm], [denTerm]);
      const eqn = equation(f, int(4));
      const { judgment: after } = applyRule(mkJudgment(eqn), quotientOfPowers, f.id, {
        numTermId: numTerm.id,
        denTermId: denTerm.id,
      });
      expect(eq(after.equation.lhs, c.expected), `x^${c.m}/x^${c.n}`).toBe(true);
      expect(after.assumptions[0]!.status).toBe("active"); // x ≠ 0 not decidable
    }

    // Constant bases discharge on the spot: 2³/2² ~> 2.
    const a = pow(int(2), int(3));
    const b = pow(int(2), int(2));
    const f = fraction([a], [b]);
    const eqn = equation(f, int(4));
    const { judgment: after } = applyRule(mkJudgment(eqn), quotientOfPowers, f.id, {
      numTermId: a.id,
      denTermId: b.id,
    });
    expect(eq(after.equation.lhs, int(2))).toBe(true);
    expect(after.assumptions[0]!.status).toBe("discharged");
  });

  it("rejects different bases and symbolic exponents", () => {
    const a = pow(variable("x"), int(3));
    const b = pow(variable("y"), int(2));
    const f = fraction([a], [b]);
    const eqn = equation(f, int(4));
    expect(
      quotientOfPowers.precondition(mkJudgment(eqn), f.id, { numTermId: a.id, denTermId: b.id }),
    ).toBe(false);

    const sym = pow(variable("x"), variable("a"));
    const d = pow(variable("x"), int(2));
    const f2 = fraction([sym], [d]);
    const eqn2 = equation(f2, int(4));
    expect(
      quotientOfPowers.precondition(mkJudgment(eqn2), f2.id, {
        numTermId: sym.id,
        denTermId: d.id,
      }),
    ).toBe(false);
  });
});

describe("multiply-both-sides (Extension polarity)", () => {
  it("property: solutions are NEVER lost (one-direction check)", () => {
    fc.assert(
      fc.property(arbExpr, arbExpr, arbEnv, (lhs, factor, env) => {
        let v: Rational;
        try {
          v = evalExpr(lhs, env);
        } catch {
          return; // lhs undefined at this sample point
        }
        // env satisfies this equation by construction.
        const eqn = equation(lhs, rationalToExpr(v));
        expect(truthValue(eqn, env)).toBe(true);

        const { judgment: after } = applyRule(mkJudgment(eqn), multiplyBothSides, eqn.id, {
          factor,
        });
        const ext = after.assumptions.find((a) => a.kind === "extension") as Extension;
        expect(ext).toBeDefined();
        expect(ext.status).toBe("active"); // the obligation is open
        expect(ext.originalEquation).toBe(eqn); // carried for checkSolution
        expect(invariantViolations(after.equation)).toEqual([]);

        const ta = truthValue(after.equation, env);
        if (ta !== undefined) expect(ta).toBe(true);
      }),
    );
  });
});

describe("square-both-sides (Extension polarity)", () => {
  it("property: solutions are NEVER lost (one-direction check)", () => {
    fc.assert(
      fc.property(arbExpr, arbEnv, (lhs, env) => {
        let v: Rational;
        try {
          v = evalExpr(lhs, env);
        } catch {
          return;
        }
        const eqn = equation(lhs, rationalToExpr(v)); // env satisfies by construction
        const { judgment: after } = applyRule(mkJudgment(eqn), squareBothSides, eqn.id, {});
        const ext = after.assumptions.find((a) => a.kind === "extension") as Extension;
        expect(ext).toBeDefined();
        expect(ext.status).toBe("active");
        expect(ext.originalEquation).toBe(eqn);
        expect(invariantViolations(after.equation)).toEqual([]);
        const ta = truthValue(after.equation, env);
        if (ta !== undefined) expect(ta).toBe(true);
      }),
    );
  });

  it("worked example: squaring x = 2 admits −2, and the check condemns it", () => {
    const eqn = equation(variable("x"), int(2));
    const d = new Derivation(eqn);
    d.apply(squareBothSides, eqn.id, {});

    // −2 satisfies x² = 4...
    const minusTwo = new Map([["x", Rational.of(-2)]]);
    expect(truthValue(d.current.equation, minusTwo)).toBe(true);
    // ...but the obligation routes it to the ORIGINAL equation.
    expect(d.checkSolution(minusTwo).verdict).toBe("extraneous");
    expect(
      (d.current.assumptions.find((a) => a.kind === "extension") as Extension).status,
    ).toBe("active");

    const two = new Map([["x", Rational.of(2)]]);
    expect(d.checkSolution(two).verdict).toBe("verified");
    expect(
      (d.current.assumptions.find((a) => a.kind === "extension") as Extension).status,
    ).toBe("discharged");
  });
});

describe("case split", () => {
  it("property: every solution of the original lands in exactly one live branch", () => {
    fc.assert(
      fc.property(
        arbExpr,
        fc.constantFrom(...VAR_POOL),
        arbEnv,
        arbEnvs,
        (lhs, vName, env0, envs) => {
          let v: Rational;
          try {
            v = evalExpr(lhs, env0);
          } catch {
            return;
          }
          const eqn = equation(lhs, rationalToExpr(v)); // env0 is a solution
          const d = new Derivation(eqn);
          const { restricted, pinned } = d.caseSplit(divideBothSides, eqn.id, {
            divisor: variable(vName),
          });
          expect(d.currentNode).toBe(restricted);

          for (const env of [env0, ...envs]) {
            if (truthValue(eqn, env) !== true) continue; // solutions only
            const inA = envSatisfiesAssumptions(restricted.judgment, env);
            const inB = envSatisfiesAssumptions(pinned.judgment, env);
            expect(inA !== inB, "must land in exactly one branch").toBe(true);
            const branch = inA ? restricted : pinned;
            const bt = truthValue(branch.judgment.equation, env);
            if (bt !== undefined) expect(bt).toBe(true);
          }

          // Both branches stay live and navigable.
          expect(d.goto(pinned.id)).toBe(pinned.judgment);
          expect(d.goto(restricted.id)).toBe(restricted.judgment);
        },
      ),
    );
  });
});

describe("checkSolution", () => {
  it("property: multiplying by (x - k) makes x = k pass the new equation, and the check catches it", () => {
    fc.assert(
      fc.property(arbEquation, fc.integer({ min: -5, max: 5 }), arbEnv, (eqn, k, baseEnv) => {
        const d = new Derivation(eqn);
        const factor: Expr = sum([variable("x"), int(-k)]); // x - k
        d.apply(multiplyBothSides, eqn.id, { factor });

        const candidate = new Map(baseEnv);
        candidate.set("x", Rational.of(k));

        // The trap: the candidate satisfies the CURRENT equation...
        const trapped = truthValue(d.current.equation, candidate);
        if (trapped !== undefined) expect(trapped).toBe(true);

        // ...but the check substitutes into the ORIGINAL.
        const isTrueSolution = truthValue(eqn, candidate) === true;
        const { verdict } = d.checkSolution(candidate);
        expect(verdict).toBe(isTrueSolution ? "verified" : "extraneous");

        const ext = d.current.assumptions.find((a) => a.kind === "extension") as Extension;
        expect(ext.status).toBe(isTrueSolution ? "discharged" : "active");
        if (isTrueSolution) expect(ext.dischargedBy).toBe("solution-check");
      }),
    );
  });

  it("worked example: x = 3 times (x - 5) verifies 3 and condemns 5", () => {
    const x = variable("x");
    const eqn = equation(x, int(3));
    const d = new Derivation(eqn);
    d.apply(multiplyBothSides, eqn.id, { factor: sum([cloneFresh(x), int(-5)]) });

    // x = 5 satisfies (x)(x-5) = 3(x-5) — both sides 0 — but is extraneous.
    const five = new Map([["x", Rational.of(5)]]);
    expect(truthValue(d.current.equation, five)).toBe(true);
    expect(d.checkSolution(five).verdict).toBe("extraneous");
    expect(
      (d.current.assumptions.find((a) => a.kind === "extension") as Extension).status,
    ).toBe("active");
    expect(d.currentNode.kind).toBe("check-solution"); // the condemnation is in the log

    // x = 3 is the real one and settles the obligation.
    const three = new Map([["x", Rational.of(3)]]);
    expect(d.checkSolution(three).verdict).toBe("verified");
    expect(
      (d.current.assumptions.find((a) => a.kind === "extension") as Extension).status,
    ).toBe("discharged");
  });
});
