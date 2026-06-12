import { describe, expect, it } from "vitest";
import {
  additiveCancellation,
  addToBothSides,
  combineIntegers,
  Derivation,
  eq,
  equation,
  findById,
  int,
  RulePreconditionViolation,
  sum,
  variable,
  type Sum,
} from "../src/index.js";

/** Solve x + 2 = 5 the way a user would: drag the 2 across, then tidy up. */
function solveXPlus2Equals5() {
  const x = variable("x");
  const two = int(2);
  const lhs = sum([x, two]);
  if (lhs.kind !== "sum") throw new Error("unreachable");
  const eqn = equation(lhs, int(5));
  const d = new Derivation(eqn);
  return { d, x, two, lhs, eqn };
}

describe("Derivation (tree log)", () => {
  it("solves x + 2 = 5 to x = 3 in three rule applications", () => {
    const { d, x, two, lhs, eqn } = solveXPlus2Equals5();

    // 1. Subtract 2 from both sides (one atomic application).
    d.apply(addToBothSides, eqn.id, { term: two });
    const lhsAfter = findById(d.current.equation, lhs.id) as Sum;
    expect(lhsAfter.children).toHaveLength(3);
    const minusTwo = lhsAfter.children.find((c) => c.kind === "neg")!;

    // 2. 2 and -2 annihilate on the left; lhs collapses to the ORIGINAL x node.
    d.apply(additiveCancellation, lhs.id, { termA: two.id, termB: minusTwo.id });
    expect(d.current.equation.lhs).toBe(x);

    // 3. Fold 5 + (-2) on the right.
    const rhsSum = d.current.equation.rhs as Sum;
    expect(rhsSum.kind).toBe("sum");
    const [five, minusTwoR] = rhsSum.children;
    d.apply(combineIntegers, rhsSum.id, { termA: five!.id, termB: minusTwoR!.id });

    expect(eq(d.current.equation, equation(variable("x"), int(3)))).toBe(true);
    expect(d.current.assumptions).toEqual([]); // nothing here needed conditions
    expect(d.path).toHaveLength(4); // root + 3 steps
    expect(d.path.at(-1)!.judgment).toBe(d.current);
  });

  it("undo moves the pointer; applying while undone BRANCHES instead of truncating", () => {
    const { d, eqn, two } = solveXPlus2Equals5();
    expect(d.canUndo()).toBe(false);
    expect(() => d.undo()).toThrow();

    const a = d.apply(addToBothSides, eqn.id, { term: two });
    d.undo();
    expect(d.currentNode.id).toBe(d.rootId);
    const b = d.apply(addToBothSides, eqn.id, { term: int(7) });

    // Both branches hang off the root and both stay live.
    expect(d.childrenOf(d.rootId)).toEqual([a.id, b.id]);
    expect(d.goto(a.id)).toBe(a.judgment);
    expect(d.goto(b.id)).toBe(b.judgment);

    // redo from the fork goes to the most recent child; goto picks any.
    d.goto(d.rootId);
    expect(d.canRedo()).toBe(true);
    expect(d.redo()).toBe(b.judgment);
  });

  it("makes illegal moves impossible, not just discouraged", () => {
    const { d, x, two, lhs } = solveXPlus2Equals5();
    const before = d.currentNode;

    // x and 2 do not annihilate; x and 2 are not two integer literals.
    expect(() =>
      d.apply(additiveCancellation, lhs.id, { termA: x.id, termB: two.id }),
    ).toThrow(RulePreconditionViolation);
    expect(() =>
      d.apply(combineIntegers, lhs.id, { termA: x.id, termB: two.id }),
    ).toThrow(RulePreconditionViolation);
    // Wrong location for a both-sides move.
    expect(() =>
      d.apply(addToBothSides, lhs.id, { term: int(1) }),
    ).toThrow(RulePreconditionViolation);

    // A rejected move leaves no trace: same node, no new children.
    expect(d.currentNode).toBe(before);
    expect(d.childrenOf(d.rootId)).toEqual([]);
  });
});
