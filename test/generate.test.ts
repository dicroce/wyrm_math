/**
 * The generator's soundness contract: every problem it emits is well-formed,
 * contains the variable, and is satisfied EXACTLY by the solution(s) it reports.
 * Backward-from-the-answer construction makes this hold by design; the property
 * test is the guard that it stays that way as templates change.
 */
import fc from "fast-check";
import { describe, expect, it } from "vitest";
import {
  DIFFICULTIES,
  generateProblem,
  PROBLEM_TOPICS,
  Rational,
  truthValue,
  variablesIn,
} from "../src/index.js";

/** Deterministic PRNG so failures reproduce from the fast-check seed. */
function mulberry32(a: number): () => number {
  return () => {
    a |= 0;
    a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

describe("problem generator", () => {
  for (const { id: topic } of PROBLEM_TOPICS) {
    for (const difficulty of DIFFICULTIES) {
      it(`${topic} / ${difficulty}: the stated answer solves the problem`, () => {
        fc.assert(
          fc.property(fc.integer(), (seed) => {
            const p = generateProblem({ topic, difficulty }, mulberry32(seed));
            expect(variablesIn(p.equation).has("x")).toBe(true);
            expect(p.solutions.length).toBeGreaterThan(0);
            for (const s of p.solutions) {
              expect(truthValue(p.equation, new Map([["x", s]]))).toBe(true);
            }
          }),
        );
      });
    }
  }

  it("easy tier stays non-negative (answers)", () => {
    const rng = mulberry32(97);
    for (let i = 0; i < 250; i++) {
      for (const { id: topic } of PROBLEM_TOPICS) {
        const p = generateProblem({ topic, difficulty: "easy" }, rng);
        for (const s of p.solutions) expect(s.num > 0n).toBe(true);
      }
    }
  });

  it("quadratics report both roots (or one when it is a perfect square)", () => {
    const rng = mulberry32(2024);
    let sawTwo = false;
    for (let i = 0; i < 100; i++) {
      const p = generateProblem({ topic: "quadratic", difficulty: "medium" }, rng);
      expect(p.solutions.length).toBeGreaterThanOrEqual(1);
      expect(p.solutions.length).toBeLessThanOrEqual(2);
      if (p.solutions.length === 2) sawTwo = true;
      for (const s of p.solutions) {
        expect(truthValue(p.equation, new Map([["x", s]]))).toBe(true);
      }
    }
    expect(sawTwo, "expected at least one two-root quadratic in 100 draws").toBe(true);
  });
});
