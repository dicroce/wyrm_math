/**
 * The two halves of "legal moves are possible, illegal moves are impossible"
 * at the enumeration layer:
 *  - SOUNDNESS: everything enumerated is legal — precondition passes and the
 *    move applies cleanly (no possible-looking affordance ever fails).
 *  - COMPLETENESS (id-parameterized rules, whose candidate space is finite):
 *    every legal application is enumerated — no legal gesture is missing.
 *    Expr-parameterized rules are deliberately curated, not complete.
 */
import fc from "fast-check";
import { describe, expect, it } from "vitest";
import {
  additiveCancellation,
  allNodes,
  applyBranchingRule,
  applyRule,
  branchingRuleById,
  combineIntegerFactors,
  combineIntegers,
  combineLikeFactors,
  distribute,
  dropOneFactor,
  dropZeroTerm,
  enumerateMoves,
  expandPower,
  factorOut,
  findById,
  invariantViolations,
  mkJudgment,
  movesFrom,
  distributePower,
  moveTermAcross,
  multiplicativeCancellation,
  negativeExponent,
  powerOfPower,
  powerOne,
  powerZero,
  quotientOfPowers,
  reduceIntegerFraction,
  ruleById,
  simplifySqrt,
  sqrtBothSides,
  squareBothSides,
  swapSides,
  zeroProduct,
  type Judgment,
  type Move,
} from "../src/index.js";
import { arbEquation } from "./gen.js";

function expectEnumerated(
  moves: Move[],
  ruleId: string,
  location: string,
  params: Record<string, unknown>,
): void {
  const found = moves.some(
    (m) =>
      m.ruleId === ruleId &&
      m.location === location &&
      Object.entries(params).every(([k, v]) => (m.params as Record<string, unknown>)[k] === v),
  );
  expect(found, `missing legal move ${ruleId}@${location} ${JSON.stringify(params)}`).toBe(true);
}

describe("move enumeration properties", () => {
  it("soundness: every enumerated move is legal and applies cleanly", () => {
    fc.assert(
      fc.property(arbEquation, (eqn) => {
        const j: Judgment = mkJudgment(eqn);
        const moves = enumerateMoves(j);
        for (const m of moves) {
          if (m.branching === true) {
            const rule = branchingRuleById(m.ruleId);
            expect(rule.precondition(j, m.location, m.params)).toBe(true);
            for (const b of applyBranchingRule(j, rule, m.location, m.params)) {
              expect(invariantViolations(b.judgment.equation)).toEqual([]);
            }
          } else {
            const rule = ruleById(m.ruleId);
            expect(rule.precondition(j, m.location, m.params)).toBe(true);
            const { judgment: after } = applyRule(j, rule, m.location, m.params);
            expect(invariantViolations(after.equation)).toEqual([]);
          }
          // Gesture anchors resolve to real nodes in the current tree.
          expect(findById(eqn, m.handle)).toBeDefined();
          if (m.dropTarget !== undefined) expect(findById(eqn, m.dropTarget)).toBeDefined();
        }
      }),
      { numRuns: 60 },
    );
  });

  it("completeness: every legal pair application is enumerated", () => {
    fc.assert(
      fc.property(arbEquation, (eqn) => {
        const j = mkJudgment(eqn);
        const moves = enumerateMoves(j);
        if (squareBothSides.precondition(j, eqn.id, {})) {
          expectEnumerated(moves, squareBothSides.id, eqn.id, {});
        }
        if (swapSides.precondition(j, eqn.id, {})) {
          expectEnumerated(moves, swapSides.id, eqn.id, {});
        }
        if (sqrtBothSides.precondition(j, eqn.id, {})) {
          expectEnumerated(moves, sqrtBothSides.id, eqn.id, {});
        }
        if (zeroProduct.precondition(j, eqn.id, {})) {
          expectEnumerated(moves, zeroProduct.id, eqn.id, {});
        }
        for (const side of [eqn.lhs, eqn.rhs]) {
          const terms = side.kind === "sum" ? side.children : [side];
          for (const t of terms) {
            const p = { termId: t.id };
            if (moveTermAcross.precondition(j, eqn.id, p)) {
              expectEnumerated(moves, moveTermAcross.id, eqn.id, p);
            }
          }
        }
        for (const node of allNodes(eqn)) {
          if (node.kind === "sum") {
            for (const a of node.children) {
              for (const b of node.children) {
                if (a.id === b.id) continue;
                const params = { termA: a.id, termB: b.id };
                for (const rule of [additiveCancellation, combineIntegers]) {
                  if (rule.precondition(j, node.id, params)) {
                    expectEnumerated(moves, rule.id, node.id, params);
                  }
                }
                // Factor-out candidates: any node pair within the two terms;
                // the precondition narrows to instance-level matches.
                for (const fa of allNodes(a)) {
                  for (const fb of allNodes(b)) {
                    const fp = { factorA: fa.id, factorB: fb.id };
                    if (factorOut.precondition(j, node.id, fp)) {
                      expectEnumerated(moves, factorOut.id, node.id, fp);
                    }
                  }
                }
              }
              const tp = { termId: a.id };
              if (dropZeroTerm.precondition(j, node.id, tp)) {
                expectEnumerated(moves, dropZeroTerm.id, node.id, tp);
              }
            }
          }
          if (node.kind === "product") {
            for (const a of node.children) {
              for (const b of node.children) {
                if (a.id === b.id) continue;
                const params = { termA: a.id, termB: b.id };
                for (const rule of [combineIntegerFactors, combineLikeFactors]) {
                  if (rule.precondition(j, node.id, params)) {
                    expectEnumerated(moves, rule.id, node.id, params);
                  }
                }
                const dp = { factorId: a.id, sumId: b.id };
                if (distribute.precondition(j, node.id, dp)) {
                  expectEnumerated(moves, distribute.id, node.id, dp);
                }
              }
              const tp = { termId: a.id };
              if (dropOneFactor.precondition(j, node.id, tp)) {
                expectEnumerated(moves, dropOneFactor.id, node.id, tp);
              }
            }
          }
          if (node.kind === "pow") {
            for (const rule of [
              expandPower,
              powerOne,
              powerZero,
              negativeExponent,
              powerOfPower,
              distributePower,
            ]) {
              if (rule.precondition(j, node.id, {})) {
                expectEnumerated(moves, rule.id, node.id, {});
              }
            }
          }
          if (node.kind === "sqrt" && simplifySqrt.precondition(j, node.id, {})) {
            expectEnumerated(moves, simplifySqrt.id, node.id, {});
          }
          if (node.kind === "fraction") {
            for (const n of node.num) {
              for (const d of node.den) {
                const params = { numTermId: n.id, denTermId: d.id };
                for (const rule of [
                  multiplicativeCancellation,
                  reduceIntegerFraction,
                  quotientOfPowers,
                ]) {
                  if (rule.precondition(j, node.id, params)) {
                    expectEnumerated(moves, rule.id, node.id, params);
                  }
                }
              }
            }
          }
        }
      }),
      { numRuns: 60 },
    );
  });

  it("movesFrom partitions enumerateMoves by handle", () => {
    fc.assert(
      fc.property(arbEquation, (eqn) => {
        const j = mkJudgment(eqn);
        const all = enumerateMoves(j);
        const byHandle = new Map<string, number>();
        for (const m of all) byHandle.set(m.handle, (byHandle.get(m.handle) ?? 0) + 1);
        let total = 0;
        for (const [handle, count] of byHandle) {
          const filtered = movesFrom(j, handle);
          expect(filtered).toHaveLength(count);
          expect(filtered.every((m) => m.handle === handle)).toBe(true);
          total += filtered.length;
        }
        expect(total).toBe(all.length);
      }),
      { numRuns: 40 },
    );
  });
});
