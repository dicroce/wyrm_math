import { describe, expect, it } from "vitest";
import {
  allNodes,
  applyBranchingRule,
  applyRule,
  branchingRuleById,
  cloneFresh,
  Derivation,
  enumerateMoves,
  eq,
  equation,
  exprToString,
  fraction,
  int,
  mkJudgment,
  movesFrom,
  neg,
  pow,
  product,
  Rational,
  ruleById,
  sum,
  variable,
  type Expr,
  type Move,
  type Node,
} from "../src/index.js";

const byRule = (moves: Move[], ruleId: string) => moves.filter((m) => m.ruleId === ruleId);
const handles = (moves: Move[]) => moves.map((m) => m.handle).sort();

describe("enumerateMoves", () => {
  it("offers exactly the sensible affordances on x + 2 = 5", () => {
    const x = variable("x");
    const two = int(2);
    const lhs = sum([x, two]);
    const five = int(5);
    const eqn = equation(lhs, five);
    const j = mkJudgment(eqn);
    const moves = enumerateMoves(j);

    // Drag any top-level term across the equals sign (it moves, sign-flipped).
    const movesAcross = byRule(moves, "move-term-across");
    expect(handles(movesAcross)).toEqual([x.id, two.id, five.id].sort());
    expect(movesAcross.every((m) => m.location === eqn.id)).toBe(true);

    // Divide by a whole side (lhs is a sum; rhs is a literal).
    const divs = byRule(moves, "divide-both-sides");
    expect(handles(divs)).toEqual([lhs.id, five.id].sort());

    // Nothing cancels, folds, or clears here.
    expect(byRule(moves, "additive-cancellation")).toEqual([]);
    expect(byRule(moves, "combine-integers")).toEqual([]);
    expect(byRule(moves, "multiply-both-sides")).toEqual([]);

    // Grabbing the 2 offers exactly the drag-across move.
    const fromTwo = movesFrom(j, two.id);
    expect(fromTwo).toHaveLength(1);
    expect(fromTwo[0]!.ruleId).toBe("move-term-across");
    expect(fromTwo[0]!.dropTarget).toBe(five.id);
  });

  it("offers cancellation in both drag directions, plus an alias inside the Neg", () => {
    const t = variable("x");
    const nt = neg(cloneFresh(t));
    if (nt.kind !== "neg") throw new Error("unreachable");
    const s = sum([t, nt, int(1)]);
    const eqn = equation(s as Expr, int(0));
    const moves = byRule(enumerateMoves(mkJudgment(eqn)), "additive-cancellation");
    // Handles: t, nt, and nt's body (grabbing the digit grabs the signed term).
    expect(moves).toHaveLength(3);
    expect(handles(moves)).toEqual([t.id, nt.id, nt.child.id].sort());
    expect(moves.every((m) => m.location === s.id)).toBe(true);
  });

  it("offers integer folding for literal pairs, including negated ones", () => {
    const a = int(2);
    const b = int(-3); // Neg(Integer)
    if (b.kind !== "neg") throw new Error("unreachable");
    const s = sum([a, b, variable("x")]);
    const eqn = equation(s as Expr, int(0));
    const moves = byRule(enumerateMoves(mkJudgment(eqn)), "combine-integers");
    // (a,b), (b,a), and (b,a) aliased to b's digit; x pairs are rejected.
    expect(moves).toHaveLength(3);
    expect(handles(moves)).toEqual([a.id, b.id, b.child.id].sort());
  });

  it("offers multiplicative cancellation across the bar, both directions", () => {
    const x1 = variable("x");
    const y = variable("y");
    const x2 = variable("x");
    const f = fraction([x1, y], [x2]);
    const eqn = equation(f, int(1));
    const moves = byRule(enumerateMoves(mkJudgment(eqn)), "multiplicative-cancellation");
    expect(moves).toHaveLength(2); // x over x, dragged from either end; y matches nothing
    expect(handles(moves)).toEqual([x1.id, x2.id].sort());
  });

  it("offers clearing a denominator via multiply-both-sides, dropping across OR up", () => {
    const num = variable("x");
    const den = int(2);
    const f = fraction([num], [den]);
    const eqn = equation(f, int(1));
    const moves = byRule(enumerateMoves(mkJudgment(eqn)), "multiply-both-sides");
    // Same grab (the denominator 2), two drop targets: the other side and
    // each numerator element. Same params either way.
    expect(moves).toHaveLength(2);
    expect(moves.every((m) => m.handle === den.id)).toBe(true);
    expect(moves.map((m) => m.dropTarget).sort()).toEqual([eqn.rhs.id, num.id].sort());
    const [a, b] = moves;
    expect(a!.params).toEqual(b!.params);
  });

  it("offers product factors as divisors and respects pins", () => {
    const three = int(3);
    const x = variable("x");
    const lhs = product([three, x]);
    const six = int(6);
    const eqn = equation(lhs as Expr, six);

    const before = byRule(enumerateMoves(mkJudgment(eqn)), "divide-both-sides");
    expect(handles(before)).toEqual([lhs.id, three.id, x.id, six.id].sort());

    // Pin x = 0: dividing by x — or by 3x, which is now decidably zero —
    // must vanish from the affordances.
    const d = new Derivation(eqn);
    d.pinVariable("x", Rational.zero);
    const after = byRule(enumerateMoves(d.current), "divide-both-sides");
    expect(handles(after)).toEqual([three.id, six.id].sort());
  });

  it("never offers dividing by a literal zero", () => {
    const zero = int(0);
    const eqn = equation(variable("x"), zero);
    const divs = byRule(enumerateMoves(mkJudgment(eqn)), "divide-both-sides");
    expect(handles(divs)).toEqual([eqn.lhs.id]); // only the x side
    expect(divs.some((m) => m.handle === zero.id)).toBe(false);
  });

  it("offers integer factor folding inside products", () => {
    const three = int(3);
    const two = int(2);
    const p = product([three, two, variable("x")]);
    const eqn = equation(p as Expr, int(0));
    const moves = byRule(enumerateMoves(mkJudgment(eqn)), "combine-integer-factors");
    expect(moves).toHaveLength(2); // (3,2) and (2,3); pairs with x are rejected
    expect(handles(moves)).toEqual([three.id, two.id].sort());
  });

  // Regression: the x/2 = 3 preset must be drag-solvable end to end —
  // multiplying by the denominator puts the factor in the NUMERATOR (not
  // wrapped around the fraction), so cancellation can reach it, and integer
  // FACTORS fold just like integer terms.
  it("drag-solves x / 2 = 3 to x = 6 using only enumerated moves", () => {
    const x = variable("x");
    const two = int(2);
    const f = fraction([x], [two]);
    const eqn = equation(f, int(3));
    const d = new Derivation(eqn);

    // 1. Clear the denominator: drag the 2 under the bar onto the other side.
    const clear = movesFrom(d.current, two.id).find((m) => m.ruleId === "multiply-both-sides");
    expect(clear).toBeDefined();
    d.apply(ruleById(clear!.ruleId), clear!.location, clear!.params);
    const lhs = d.current.equation.lhs;
    expect(lhs.kind).toBe("fraction");
    if (lhs.kind !== "fraction") return;
    expect(lhs.num).toHaveLength(2); // (x·2)/2 = 3·2

    // 2. Cancel the 2s across the bar.
    const numTwo = lhs.num.find((c) => c.kind === "int")!;
    const cancel = movesFrom(d.current, numTwo.id).find(
      (m) => m.ruleId === "multiplicative-cancellation",
    );
    expect(cancel).toBeDefined();
    d.apply(ruleById(cancel!.ruleId), cancel!.location, cancel!.params);
    expect(d.current.equation.lhs).toBe(x); // the bar is gone, x survives by identity

    // 3. Fold 3·2 on the right.
    const rhs = d.current.equation.rhs;
    expect(rhs.kind).toBe("product");
    if (rhs.kind !== "product") return;
    const three = rhs.children[0]!;
    const fold = movesFrom(d.current, three.id).find(
      (m) => m.ruleId === "combine-integer-factors",
    );
    expect(fold).toBeDefined();
    d.apply(ruleById(fold!.ruleId), fold!.location, fold!.params);

    expect(eq(d.current.equation, equation(variable("x"), int(6)))).toBe(true);

    // The 2 ≠ 0 restriction discharged itself (constant); the multiply
    // obligation settles against the original equation.
    const restriction = d.current.assumptions.find((a) => a.kind === "restriction")!;
    expect(restriction.status).toBe("discharged");
    expect(d.checkSolution(new Map([["x", Rational.of(6)]])).verdict).toBe("verified");
  });

  // Regression: the DragonBox-style "drag the 3 down to divide" flow —
  // dividing spreads product factors into the numerator list so the 3s can
  // cancel, and integer/integer fractions reduce by gcd.
  it("drag-solves 3x = 6 to x = 2 using only enumerated moves", () => {
    const three = int(3);
    const x = variable("x");
    const lhs = product([three, x]);
    const six = int(6);
    const eqn = equation(lhs as Expr, six);
    const d = new Derivation(eqn);

    // 1. Drag the 3 under the other side: a bar appears under BOTH sides.
    const divide = movesFrom(d.current, three.id).find((m) => m.ruleId === "divide-both-sides");
    expect(divide).toBeDefined();
    expect(divide!.dropTarget).toBe(six.id);
    d.apply(ruleById(divide!.ruleId), divide!.location, divide!.params);
    const newLhs = d.current.equation.lhs;
    expect(newLhs.kind).toBe("fraction");
    if (newLhs.kind !== "fraction") return;
    expect(newLhs.num.map((c) => c.id)).toEqual([three.id, x.id]); // spread, not lumped
    // The 3 ≠ 0 restriction discharged itself immediately.
    expect(d.current.assumptions[0]!.status).toBe("discharged");

    // 2. Cancel the 3s across the left bar.
    const cancel = movesFrom(d.current, three.id).find(
      (m) => m.ruleId === "multiplicative-cancellation",
    );
    expect(cancel).toBeDefined();
    d.apply(ruleById(cancel!.ruleId), cancel!.location, cancel!.params);
    expect(d.current.equation.lhs).toBe(x); // bar gone, the original x survives

    // 3. Reduce 6/3 on the right.
    const reduce = movesFrom(d.current, six.id).find(
      (m) => m.ruleId === "reduce-integer-fraction",
    );
    expect(reduce).toBeDefined();
    d.apply(ruleById(reduce!.ruleId), reduce!.location, reduce!.params);

    expect(eq(d.current.equation, equation(variable("x"), int(2)))).toBe(true);
    expect(d.checkSolution(new Map([["x", Rational.of(2)]])).verdict).toBe("verified");
  });

  it("offers expand-power as a TAP move (no drop target) on literal powers only", () => {
    const p = pow(variable("x"), int(3));
    const eqn = equation(p, int(8));
    const taps = byRule(enumerateMoves(mkJudgment(eqn)), "expand-power");
    expect(taps).toHaveLength(1);
    expect(taps[0]!.handle).toBe(p.id);
    expect(taps[0]!.dropTarget).toBeUndefined();

    const p1 = pow(variable("x"), int(1));
    const eqn1 = equation(p1, int(8));
    expect(byRule(enumerateMoves(mkJudgment(eqn1)), "expand-power")).toEqual([]);
  });

  it("round-trips: tap-expand x³, then drag-collapse back to x³", () => {
    const x = variable("x");
    const p = pow(x, int(3));
    const eqn = equation(p, int(8));
    const d = new Derivation(eqn);

    // Tap the power: x³ becomes x·x·x; the original base survives by identity.
    const tap = movesFrom(d.current, p.id).find((m) => m.ruleId === "expand-power");
    expect(tap).toBeDefined();
    d.apply(ruleById(tap!.ruleId), tap!.location, tap!.params);
    const expanded = d.current.equation.lhs;
    expect(expanded.kind).toBe("product");
    if (expanded.kind !== "product") return;
    expect(expanded.children).toHaveLength(3);
    expect(expanded.children[0]).toBe(x);

    // Drag the first x onto the second: x²·x.
    const [a, b, c] = expanded.children;
    const m1 = movesFrom(d.current, a!.id).find(
      (m) => m.ruleId === "combine-like-factors" && m.dropTarget === b!.id,
    );
    expect(m1).toBeDefined();
    d.apply(ruleById(m1!.ruleId), m1!.location, m1!.params);
    const mid = d.current.equation.lhs;
    expect(mid.kind).toBe("product");
    if (mid.kind !== "product") return;
    const squared = mid.children.find((ch) => ch.kind === "pow")!;

    // Drag x² onto the last x: back to x³.
    const m2 = movesFrom(d.current, squared.id).find(
      (m) => m.ruleId === "combine-like-factors" && m.dropTarget === c!.id,
    );
    expect(m2).toBeDefined();
    d.apply(ruleById(m2!.ruleId), m2!.location, m2!.params);

    expect(eq(d.current.equation, equation(pow(variable("x"), int(3)), int(8)))).toBe(true);
    expect(d.current.assumptions).toEqual([]); // the whole trip was assumption-free
  });

  it("enumerates the unique ac-method split on factorable trinomials only", () => {
    // x² − 6x + 9: D = 0, the split is −3x − 3x.
    const mid = neg(product([int(6), variable("x")]));
    const lhs = sum([pow(variable("x"), int(2)), mid, int(9)]);
    if (lhs.kind !== "sum") throw new Error("unreachable");
    const splits = byRule(enumerateMoves(mkJudgment(equation(lhs, int(0)))), "split-term");
    expect(splits).toHaveLength(1);
    expect(splits[0]!.handle).toBe(mid.id);
    expect(splits[0]!.dropTarget).toBeUndefined(); // a tap
    expect(splits[0]!.params).toEqual({ termId: mid.id, first: -3n });

    // x² + x − 6: the bare x splits into −2x + 3x.
    const bareX = variable("x");
    const lhs2 = sum([pow(variable("x"), int(2)), bareX, int(-6)]);
    if (lhs2.kind !== "sum") throw new Error("unreachable");
    const splits2 = byRule(enumerateMoves(mkJudgment(equation(lhs2, int(0)))), "split-term");
    expect(splits2).toHaveLength(1);
    expect(splits2[0]!.params).toEqual({ termId: bareX.id, first: -2n });

    // x² + x + 1 (D < 0) and x² + 4x + 2 (D not a square): nothing offered.
    for (const c of [int(1), int(2)]) {
      const mid3 = c.kind === "int" && c.value === 1n ? variable("x") : product([int(4), variable("x")]);
      const lhs3 = sum([pow(variable("x"), int(2)), mid3, c]);
      if (lhs3.kind !== "sum") throw new Error("unreachable");
      expect(byRule(enumerateMoves(mkJudgment(equation(lhs3, int(0)))), "split-term")).toEqual([]);
    }
  });

  // THE escalating-grab regression: in (−3)(−2x) the −3 now has a fold of its
  // own (absorb into the −2x coefficient → 6x), so it is individually
  // grabbable; and x·(−1) folds to −x.
  it("offers −3·−2x ~> 6x and x·(−1) ~> −x as integer-factor folds", () => {
    const neg3 = neg(int(3));
    const neg2x = neg(product([int(2), variable("x")]));
    const p = product([neg3, neg2x]);
    if (p.kind !== "product") throw new Error("unreachable");
    const j = mkJudgment(equation(p, int(0)));
    const m = movesFrom(j, neg3.id).find(
      (mv) => mv.ruleId === "combine-integer-factors" && mv.dropTarget === neg2x.id,
    );
    expect(m).toBeDefined();
    expect(eq(ruleById(m!.ruleId).apply(j, m!.location, m!.params).equation.lhs,
      product([int(6), variable("x")]))).toBe(true);

    const x = variable("x");
    const negOne = neg(int(1));
    const p2 = product([x, negOne]);
    if (p2.kind !== "product") throw new Error("unreachable");
    const j2 = mkJudgment(equation(p2, int(0)));
    const m2 = movesFrom(j2, x.id).find(
      (mv) => mv.ruleId === "combine-integer-factors" && mv.dropTarget === negOne.id,
    );
    expect(m2).toBeDefined();
    expect(eq(ruleById(m2!.ruleId).apply(j2, m2!.location, m2!.params).equation.lhs,
      neg(variable("x")))).toBe(true);
  });

  // THE xx-in-a-denominator regression: like factors under a bar still merge.
  it("drag-merges x·x inside a denominator to x², then offers the expand tap back", () => {
    const x1 = variable("x");
    const x2 = variable("x");
    const f = fraction([int(1)], [x1, x2]);
    const eqn = equation(f, int(4));
    const d = new Derivation(eqn);

    // Both drag directions are offered between the two denominator x's.
    const m1 = movesFrom(d.current, x1.id).find(
      (m) => m.ruleId === "combine-like-factors" && m.dropTarget === x2.id,
    );
    const m2 = movesFrom(d.current, x2.id).find(
      (m) => m.ruleId === "combine-like-factors" && m.dropTarget === x1.id,
    );
    expect(m1).toBeDefined();
    expect(m2).toBeDefined();

    d.apply(ruleById(m1!.ruleId), m1!.location, m1!.params);
    const lhs = d.current.equation.lhs;
    expect(eq(lhs, fraction([int(1)], [pow(variable("x"), int(2))]))).toBe(true);
    expect(lhs.id).toBe(f.id); // the bar survived in place
    expect(d.current.assumptions).toEqual([]); // merging emits nothing

    // The result offers the follow-up a user expects: tap x² to expand it.
    if (lhs.kind !== "fraction") throw new Error("unreachable");
    const squared = lhs.den[0]!;
    expect(
      movesFrom(d.current, squared.id).some((m) => m.ruleId === "expand-power"),
    ).toBe(true);
  });

  /** Find a move by handle and rule, or fail loudly. */
  function moveFor(d: Derivation, handle: string, ruleId: string): Move {
    const m = movesFrom(d.current, handle).find((mv) => mv.ruleId === ruleId);
    expect(m, `no ${ruleId} move from ${handle}`).toBeDefined();
    return m!;
  }

  function applyMove(d: Derivation, m: Move): void {
    d.apply(ruleById(m.ruleId), m.location, m.params);
  }

  // THE quadratic regression: x² − 6x + 9 = 0 solves to x = 3 with only
  // enumerated gestures — the ac-method split, factoring by grouping (incl.
  // the literal-divisor factor-out that reaches the constant), zero-product.
  it("solves x² − 6x + 9 = 0 to x = 3 using only enumerated moves", () => {
    const mid = neg(product([int(6), variable("x")]));
    const lhs0 = sum([pow(variable("x"), int(2)), mid, int(9)]);
    if (lhs0.kind !== "sum") throw new Error("unreachable");
    const d = new Derivation(equation(lhs0, int(0)));

    // 1. Tap −6x: the curated ac split, −3x − 3x.
    applyMove(d, moveFor(d, mid.id, "split-term"));
    let L = d.current.equation.lhs;
    if (L.kind !== "sum") throw new Error("unreachable");
    expect(L.children).toHaveLength(4);

    // 2. Tap x² open: x·x exposes the instance the grouping grabs.
    const sq = L.children.find((c) => c.kind === "pow")!;
    applyMove(d, moveFor(d, sq.id, "expand-power"));
    L = d.current.equation.lhs;
    if (L.kind !== "sum") throw new Error("unreachable");

    // 3. Drag the x of x·x onto the first −3x: (x + −3)·x.
    const xx = L.children.find((c) => c.kind === "product");
    if (xx === undefined || xx.kind !== "product") throw new Error("unreachable");
    const firstNeg = L.children.find((c) => c.kind === "neg")!;
    const m3 = movesFrom(d.current, xx.children[0]!.id).find(
      (m) => m.ruleId === "factor-out" && m.dropTarget === firstNeg.id,
    );
    expect(m3).toBeDefined();
    applyMove(d, m3!);
    L = d.current.equation.lhs;
    if (L.kind !== "sum") throw new Error("unreachable");

    // 4. Drag the 3 of the remaining −3x onto the 9: the literal-divisor
    // factor-out — (x + −3)·(−3).
    const negTerm = L.children.find((c) => c.kind === "neg");
    if (negTerm === undefined || negTerm.kind !== "neg" || negTerm.child.kind !== "product") {
      throw new Error("unreachable");
    }
    const three = negTerm.child.children.find((c) => c.kind === "int")!;
    const nine = L.children.find((c) => c.kind === "int")!;
    const m4 = movesFrom(d.current, three.id).find(
      (m) => m.ruleId === "factor-out" && m.dropTarget === nine.id,
    );
    expect(m4).toBeDefined();
    applyMove(d, m4!);
    L = d.current.equation.lhs;
    if (L.kind !== "sum") throw new Error("unreachable");
    expect(L.children).toHaveLength(2);

    // 5. Drag one (x + −3) onto the other term: (x + −3)(x + −3).
    const t1 = L.children[0]!;
    const t2 = L.children[1]!;
    if (t1.kind !== "product") throw new Error("unreachable");
    const groupSum = t1.children.find((c) => c.kind === "sum")!;
    const m5 = movesFrom(d.current, groupSum.id).find(
      (m) => m.ruleId === "factor-out" && m.dropTarget === t2.id,
    );
    expect(m5).toBeDefined();
    applyMove(d, m5!);
    const P = d.current.equation.lhs;
    expect(
      eq(P, product([sum([variable("x"), int(-3)]), sum([variable("x"), int(-3)])])),
    ).toBe(true);

    // 6. Tap the product: zero-product (both arms read x − 3 = 0).
    const zp = moveFor(d, P.id, "zero-product");
    expect(zp.branching).toBe(true);
    d.applyBranching(branchingRuleById(zp.ruleId), zp.location, zp.params);
    L = d.current.equation.lhs;
    if (L.kind !== "sum") throw new Error("unreachable");

    // 7–8. Drag the −3 across, drop the +0.
    const negThree = L.children.find((c) => c.kind === "neg")!;
    applyMove(d, moveFor(d, negThree.id, "move-term-across"));
    const R = d.current.equation.rhs;
    if (R.kind !== "sum") throw new Error("unreachable");
    const zero = R.children.find((c) => c.kind === "int" && c.value === 0n)!;
    applyMove(d, moveFor(d, zero.id, "drop-zero-term"));

    expect(eq(d.current.equation, equation(variable("x"), int(3)))).toBe(true);
    expect(d.current.assumptions).toEqual([]); // the whole factoring is exact
  });

  // THE leading-coefficient-≠1 quadratic: 2x²+5x−3=0 factors to (x+3)(2x−1)
  // and solves to x=−3 and x=1/2 — the path factor-out-negative unblocks.
  it("solves 2x²+5x−3=0 to x=−3 and x=1/2 using only enumerated moves", () => {
    const j0 = mkJudgment(
      equation(sum([product([int(2), pow(variable("x"), int(2))]), product([int(5), variable("x")]), int(-3)]), int(0)),
    );
    const str = (jj: typeof j0) => exprToString(jj.equation);
    const result = (jj: typeof j0, m: Move) =>
      exprToString(applyRule(jj, ruleById(m.ruleId), m.location, m.params).judgment.equation);
    const step = (jj: typeof j0, pred: (m: Move) => boolean): ReturnType<typeof mkJudgment> => {
      const m = enumerateMoves(jj).find(pred);
      expect(m, `no move at "${str(jj)}"`).toBeDefined();
      return applyRule(jj, ruleById(m!.ruleId), m!.location, m!.params).judgment;
    };

    let j = step(j0, (m) => m.ruleId === "split-term");
    j = step(j, (m) => m.ruleId === "expand-power");
    j = step(j, (m) => m.ruleId === "factor-out" && result(j, m).startsWith("((((2 * x) + -1) * x)"));
    j = step(j, (m) => m.ruleId === "factor-out" && result(j, m).includes("(1 + -(2 * x)) * -3"));
    j = step(j, (m) => m.ruleId === "factor-out-negative");
    j = step(j, (m) => m.ruleId === "combine-integer-factors" && result(j, m).includes("3 * (-1 + (2 * x))"));
    j = step(j, (m) => m.ruleId === "factor-out" && /\(x \+ 3\)|\(3 \+ x\)/.test(result(j, m)));

    // Factored — under multiset eq the term order doesn't matter.
    expect(
      eq(j.equation.lhs, product([sum([variable("x"), int(3)]), sum([product([int(2), variable("x")]), int(-1)])])),
    ).toBe(true);

    // Zero-product splits into the two linear factors.
    const zp = enumerateMoves(j).find((m) => m.ruleId === "zero-product");
    expect(zp).toBeDefined();
    const arms = applyBranchingRule(j, branchingRuleById(zp!.ruleId), zp!.location, zp!.params);
    expect(arms).toHaveLength(2);

    // Solve each arm with explicit moves; collect the roots.
    const node = (jj: ReturnType<typeof mkJudgment>, pred: (n: Node) => boolean) =>
      [...allNodes(jj.equation)].find(pred) as Expr;
    const moveFrom = (jj: ReturnType<typeof mkJudgment>, ruleId: string, handlePred: (n: Node) => boolean) =>
      movesFrom(jj, node(jj, handlePred).id).find((m) => m.ruleId === ruleId)!;
    const ap = (jj: ReturnType<typeof mkJudgment>, m: Move) =>
      applyRule(jj, ruleById(m.ruleId), m.location, m.params).judgment;

    const roots = new Set<string>();
    for (const arm of arms) {
      let a = arm.judgment;
      const c = (a.equation.lhs.kind === "sum" ? a.equation.lhs : a.equation.rhs) as Expr;
      if (c.kind !== "sum") throw new Error("expected a linear sum arm");
      const constTerm = c.children.find((t) => t.kind === "int" || (t.kind === "neg" && t.child.kind === "int"))!;
      a = ap(a, moveFrom(a, "move-term-across", (n) => n.id === constTerm.id));
      a = ap(a, moveFrom(a, "drop-zero-term", (n) => n.kind === "int" && n.value === 0n));
      // Arm B still has a 2·x; divide it out.
      const two = [...allNodes(a.equation)].find((n) => n.kind === "int" && n.value === 2n && a.equation.lhs.kind === "product");
      if (two !== undefined) {
        a = ap(a, movesFrom(a, two.id).find((m) => m.ruleId === "divide-both-sides")!);
        a = ap(a, [...allNodes(a.equation)].flatMap((n) => movesFrom(a, n.id)).find((m) => m.ruleId === "multiplicative-cancellation")!);
      }
      roots.add(exprToString(a.equation));
    }
    expect(roots.has("x = -3")).toBe(true);
    expect(roots.has("x = ((1) / (2))")).toBe(true);
  });

  // THE like-terms regression: 3x + 2x = 10 drag-solves to x = 2.
  it("drag-solves 3x + 2x = 10 to x = 2 using only enumerated moves", () => {
    const x1 = variable("x");
    const x2 = variable("x");
    const three = int(3);
    const two = int(2);
    const lhs = sum([product([three, x1]), product([two, x2])]);
    if (lhs.kind !== "sum") throw new Error("unreachable");
    const eqn = equation(lhs, int(10));
    const d = new Derivation(eqn);

    // 1. Drag the x in 3x onto the 2x term: (3 + 2)·x. (The drop target is
    // the whole term; the params pin the matching x instances.)
    const factor = movesFrom(d.current, x1.id).find((m) => {
      const p = m.params as { factorA?: string; factorB?: string };
      return m.ruleId === "factor-out" && p.factorA === x1.id && p.factorB === x2.id;
    });
    expect(factor).toBeDefined();
    applyMove(d, factor!);
    expect(eq(d.current.equation.lhs, product([sum([int(3), int(2)]), variable("x")]))).toBe(true);

    // 2. Drag the 3 onto the 2 inside the cofactor sum: 5·x. The original
    // literal nodes survived factoring by identity, so their ids still work.
    applyMove(d, moveFor(d, three.id, "combine-integers"));
    expect(eq(d.current.equation.lhs, product([int(5), variable("x")]))).toBe(true);

    // 3. Drag the 5 under the other side, cancel it, reduce 10/5.
    const lhsNow = d.current.equation.lhs;
    if (lhsNow.kind !== "product") throw new Error("unreachable");
    const five = lhsNow.children.find((c) => c.kind === "int")!;
    applyMove(d, moveFor(d, five.id, "divide-both-sides"));
    applyMove(d, moveFor(d, five.id, "multiplicative-cancellation"));
    const rhsNow = d.current.equation.rhs;
    if (rhsNow.kind !== "fraction") throw new Error("unreachable");
    applyMove(d, moveFor(d, rhsNow.num[0]!.id, "reduce-integer-fraction"));

    expect(eq(d.current.equation, equation(variable("x"), int(2)))).toBe(true);
    expect(d.checkSolution(new Map([["x", Rational.of(2)]])).verdict).toBe("verified");
  });

  // THE distribute regression: 2·(x + 3) = 10 drag-solves to x = 2.
  it("drag-solves 2·(x + 3) = 10 to x = 2 using only enumerated moves", () => {
    const two = int(2);
    const s = sum([variable("x"), int(3)]);
    if (s.kind !== "sum") throw new Error("unreachable");
    const lhs = product([two, s]);
    if (lhs.kind !== "product") throw new Error("unreachable");
    const eqn = equation(lhs, int(10));
    const d = new Derivation(eqn);

    // 1. Drag the 2 onto (x + 3): 2x + 2·3.
    const dist = movesFrom(d.current, two.id).find(
      (m) => m.ruleId === "distribute" && m.dropTarget === s.id,
    );
    expect(dist).toBeDefined();
    applyMove(d, dist!);

    // 2. Fold 2·3 into 6.
    let lhsSum = d.current.equation.lhs;
    if (lhsSum.kind !== "sum") throw new Error("unreachable");
    const constTerm = lhsSum.children[1]!;
    if (constTerm.kind !== "product") throw new Error("unreachable");
    applyMove(d, moveFor(d, constTerm.children[0]!.id, "combine-integer-factors"));
    expect(
      eq(d.current.equation.lhs, sum([product([int(2), variable("x")]), int(6)])),
    ).toBe(true);

    // 3. Drag the 6 across (one move: it leaves the left, arrives as −6), fold 10 − 6.
    lhsSum = d.current.equation.lhs;
    if (lhsSum.kind !== "sum") throw new Error("unreachable");
    const six = lhsSum.children.find((c) => c.kind === "int")!;
    applyMove(d, moveFor(d, six.id, "move-term-across"));
    const rhsSum = d.current.equation.rhs;
    if (rhsSum.kind !== "sum") throw new Error("unreachable");
    applyMove(d, moveFor(d, rhsSum.children[0]!.id, "combine-integers"));
    expect(eq(d.current.equation.rhs, int(4))).toBe(true);

    // 4. Divide by 2, cancel, reduce.
    applyMove(d, moveFor(d, two.id, "divide-both-sides"));
    applyMove(d, moveFor(d, two.id, "multiplicative-cancellation"));
    const rhsFrac = d.current.equation.rhs;
    if (rhsFrac.kind !== "fraction") throw new Error("unreachable");
    applyMove(d, moveFor(d, rhsFrac.num[0]!.id, "reduce-integer-fraction"));

    expect(eq(d.current.equation, equation(variable("x"), int(2)))).toBe(true);
    expect(d.checkSolution(new Map([["x", Rational.of(2)]])).verdict).toBe("verified");
  });

  // THE move-across regression: 2x = 10 − 3x drag-solves to x = 2, starting
  // with dragging the −3x onto the 2x (one move, sign-flipped in transit).
  it("drag-solves 2x = 10 − 3x to x = 2 using only enumerated moves", () => {
    const x1 = variable("x");
    const x2 = variable("x");
    const lhs = product([int(2), x1]);
    const threeX = product([int(3), x2]);
    const negTerm = neg(threeX as Expr);
    const eqn = equation(lhs as Expr, sum([int(10), negTerm]) as Expr);
    const d = new Derivation(eqn);

    // 1. Drag −3x onto the 2x: it moves across as +3x.
    const across = movesFrom(d.current, negTerm.id).find(
      (m) => m.ruleId === "move-term-across",
    );
    expect(across).toBeDefined();
    expect(across!.dropTarget).toBe(lhs.id);
    d.apply(ruleById(across!.ruleId), across!.location, across!.params);
    expect(eq(d.current.equation.rhs, int(10))).toBe(true);
    const newLhs = d.current.equation.lhs;
    expect(newLhs.kind).toBe("sum");
    if (newLhs.kind !== "sum") return;
    expect(newLhs.children).toHaveLength(2); // 2x + 3x, the 3x by identity

    // 2. Like terms: drag x onto x, fold 2 + 3, divide by 5, cancel, reduce.
    applyMove(d, moveFor(d, x1.id, "factor-out"));
    const lhsNow = d.current.equation.lhs;
    if (lhsNow.kind !== "product") throw new Error("unreachable");
    const cofSum = lhsNow.children.find((c) => c.kind === "sum")!;
    if (cofSum.kind !== "sum") throw new Error("unreachable");
    applyMove(d, moveFor(d, cofSum.children[0]!.id, "combine-integers"));
    const lhsFolded = d.current.equation.lhs;
    if (lhsFolded.kind !== "product") throw new Error("unreachable");
    const five = lhsFolded.children.find((c) => c.kind === "int")!;
    applyMove(d, moveFor(d, five.id, "divide-both-sides"));
    applyMove(d, moveFor(d, five.id, "multiplicative-cancellation"));
    const rhsFrac = d.current.equation.rhs;
    if (rhsFrac.kind !== "fraction") throw new Error("unreachable");
    applyMove(d, moveFor(d, rhsFrac.num[0]!.id, "reduce-integer-fraction"));

    expect(eq(d.current.equation, equation(variable("x"), int(2)))).toBe(true);
    expect(d.checkSolution(new Map([["x", Rational.of(2)]])).verdict).toBe("verified");
  });

  // The negative-exponent flow: x⁻¹ = 2 drag/tap-solves to 1/2 = x.
  it("solves x⁻¹ = 2 to 1/2 = x using only enumerated moves", () => {
    const x = variable("x");
    const p = pow(x, int(-1));
    const eqn = equation(p, int(2));
    const d = new Derivation(eqn);

    // 1. Tap the power: x⁻¹ becomes 1/x¹.
    applyMove(d, moveFor(d, p.id, "negative-exponent"));
    let lhs = d.current.equation.lhs;
    expect(lhs.kind).toBe("fraction");
    if (lhs.kind !== "fraction") return;

    // 2. Tap x¹ down to x.
    applyMove(d, moveFor(d, lhs.den[0]!.id, "power-one"));
    lhs = d.current.equation.lhs;
    if (lhs.kind !== "fraction") return;
    expect(lhs.den[0]).toBe(x); // the original variable node, by identity

    // 3. Clear the denominator (multiply both sides by x), cancel x/x.
    applyMove(d, moveFor(d, x.id, "multiply-both-sides"));
    applyMove(d, moveFor(d, x.id, "multiplicative-cancellation"));
    expect(eq(d.current.equation.lhs, int(1))).toBe(true);

    // 4. Divide by 2 and cancel.
    const rhs = d.current.equation.rhs;
    if (rhs.kind !== "product") throw new Error("unreachable");
    const two = rhs.children.find((c) => c.kind === "int")!;
    applyMove(d, moveFor(d, two.id, "divide-both-sides"));
    applyMove(d, moveFor(d, two.id, "multiplicative-cancellation"));

    expect(
      eq(d.current.equation, equation(fraction([int(1)], [int(2)]), variable("x"))),
    ).toBe(true);

    // The multiply obligation and the x ≠ 0 restriction both settle.
    expect(d.checkSolution(new Map([["x", new Rational(1n, 2n)]])).verdict).toBe("verified");
    const restrictions = d.current.assumptions.filter((a) => a.kind === "restriction");
    expect(restrictions.some((a) => a.status === "active")).toBe(true); // x ≠ 0 stays active (not decidable)
  });

  // Inequality flagship: −2x < 6 drag-solves to x > −3, flipping at the divide.
  it("drag-solves −2x < 6 to x > −3 using only enumerated moves", () => {
    const negTwo = int(-2);
    const x = variable("x");
    const lhs = product([negTwo, x]);
    const eqn = equation(lhs as Expr, int(6), "<");
    const d = new Derivation(eqn);

    // 1. Drag the −2 under the 6: the relation flips.
    applyMove(d, moveFor(d, negTwo.id, "divide-both-sides"));
    expect(d.current.equation.relation).toBe(">");

    // 2. Cancel −2/−2 on the left; reduce 6/−2 on the right.
    applyMove(d, moveFor(d, negTwo.id, "multiplicative-cancellation"));
    expect(d.current.equation.lhs).toBe(x);
    const rhs = d.current.equation.rhs;
    if (rhs.kind !== "fraction") throw new Error("unreachable");
    applyMove(d, moveFor(d, rhs.num[0]!.id, "reduce-integer-fraction"));

    expect(eq(d.current.equation, equation(variable("x"), int(-3), ">"))).toBe(true);
    // x = 0 satisfies x > −3: checkSolution works on inequalities too.
    expect(d.checkSolution(new Map([["x", Rational.zero]])).verdict).toBe("verified");
  });

  it("solves x³/x² = 4 via quotient-of-powers, tracking x ≠ 0", () => {
    const numPow = pow(variable("x"), int(3));
    const denPow = pow(variable("x"), int(2));
    const f = fraction([numPow], [denPow]);
    const eqn = equation(f, int(4));
    const d = new Derivation(eqn);

    applyMove(d, moveFor(d, numPow.id, "quotient-of-powers"));
    expect(eq(d.current.equation, equation(variable("x"), int(4)))).toBe(true);
    const restriction = d.current.assumptions[0]!;
    expect(restriction.kind).toBe("restriction");
    expect(restriction.status).toBe("active"); // x ≠ 0 rides along
    expect(d.checkSolution(new Map([["x", Rational.of(4)]])).verdict).toBe("verified");
  });

  it("offers identity taps with no drop target", () => {
    const zero = int(0);
    const s = sum([zero, variable("x")]);
    if (s.kind !== "sum") throw new Error("unreachable");
    const d = new Derivation(equation(s, int(5)));
    const tap = movesFrom(d.current, zero.id).find((m) => m.ruleId === "drop-zero-term");
    expect(tap).toBeDefined();
    expect(tap!.dropTarget).toBeUndefined();
    applyMove(d, tap!);
    expect(d.current.equation.lhs.kind).toBe("var");
  });

  it("returns moves that Derivation.apply accepts verbatim", () => {
    const x = variable("x");
    const two = int(2);
    const eqn = equation(sum([x, two]) as Expr, int(5));
    const d = new Derivation(eqn);
    const move = movesFrom(d.current, two.id)[0]!;
    const node = d.apply(ruleById(move.ruleId), move.location, move.params);
    // The 2 moved across: x = 5 − 2.
    expect(node.judgment.equation.lhs).toBe(x);
    expect(node.judgment.equation.rhs.kind).toBe("sum");
  });
});
