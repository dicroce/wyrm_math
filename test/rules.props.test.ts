import fc from "fast-check";
import { describe, expect, it } from "vitest";
import {
  additiveCancellation,
  addToBothSides,
  cancelNegatives,
  allNodes,
  childrenOf,
  cloneFresh,
  combineFractions,
  combineIntegerFactors,
  combineLikeFactors,
  distribute,
  distributeNegation,
  dropOneFactor,
  dropZeroTerm,
  eq,
  equation,
  exprToString,
  expandPower,
  factorOut,
  factorOutNegative,
  findParent,
  fraction,
  combineIntegers,
  findById,
  int,
  splitTerm,
  invariantViolations,
  mkJudgment,
  moveTermAcross,
  multiplyByZero,
  neg,
  negativeExponent,
  pow,
  powerOfPower,
  powerOne,
  powerZero,
  distributePower,
  product,
  reduceIntegerFraction,
  sum,
  variable,
  type Equation,
  type Expr,
  type NodeId,
} from "../src/index.js";
import {
  arbEnvs,
  arbEquation,
  arbExpr,
  arbWrap,
  assertSolutionSetPreserved,
  embed,
  subtreeIdenticalWithIds,
  type Wrap,
} from "./gen.js";

/** Ids of every node in a tree. */
function idsOf(root: Equation): Set<NodeId> {
  return new Set([...allNodes(root)].map((n) => n.id));
}

function checkAfter(before: Equation, after: Equation): void {
  expect(invariantViolations(after)).toEqual([]);
}

/**
 * Untouched terms must survive byte-for-byte: same ids, same structure. One
 * exception: when the sum collapses to a single surviving term, the splice
 * point may swallow that survivor's root to repair an invariant (Neg under
 * Neg, Product under Product) — then its child subtrees must still survive
 * intact.
 */
function checkBystandersStable(
  after: Equation,
  bystanders: readonly Expr[],
  collapseSurvivorAllowed = false,
): void {
  for (const b of bystanders) {
    const found = findById(after, b.id);
    if (found !== undefined) {
      expect(subtreeIdenticalWithIds(found, b)).toBe(true);
      continue;
    }
    expect(
      collapseSurvivorAllowed && bystanders.length === 1,
      `bystander ${b.id} disappeared`,
    ).toBe(true);
    for (const child of childrenOf(b)) {
      const foundChild = findById(after, child.id);
      expect(foundChild, `swallowed survivor's child ${child.id} disappeared`).toBeDefined();
      expect(subtreeIdenticalWithIds(foundChild!, child)).toBe(true);
    }
  }
}

interface SumScenario {
  eqn: Equation;
  loc: NodeId;
  termA: NodeId;
  termB: NodeId;
  bystanders: readonly Expr[];
}

/**
 * Builds an equation containing a Sum or Product with two designated terms
 * plus bystander terms, embedded at various depths/shapes on either side.
 */
function buildNaryScenario(
  kind: "sum" | "product",
  a: Expr,
  b: Expr,
  extras: readonly Expr[],
  posA: number,
  posB: number,
  wrap: Wrap,
  onLhs: boolean,
  other: Expr,
): SumScenario {
  const terms: Expr[] = [...extras];
  terms.splice(posA % (terms.length + 1), 0, a);
  terms.splice(posB % (terms.length + 1), 0, b);
  const s = kind === "sum" ? sum(terms) : product(terms);
  if (s.kind !== kind) throw new Error(`scenario ${kind} unexpectedly collapsed`);
  const bystanders = (s as Expr & { children: readonly Expr[] }).children.filter(
    (c) => c.id !== a.id && c.id !== b.id,
  );
  return {
    eqn: embed(s, wrap, other, onLhs),
    loc: s.id,
    termA: a.id,
    termB: b.id,
    bystanders,
  };
}

function buildSumScenario(
  a: Expr,
  b: Expr,
  extras: readonly Expr[],
  posA: number,
  posB: number,
  wrap: Wrap,
  onLhs: boolean,
  other: Expr,
): SumScenario {
  return buildNaryScenario("sum", a, b, extras, posA, posB, wrap, onLhs, other);
}

/**
 * Builds an equation containing a Fraction with the two designated factors in
 * the SAME list (num or den) plus extras spliced around them; a lone literal
 * sits on the other side of the bar. `a` and `b` must not be Products (the
 * ctor would spread them). Bystanders are read off the constructed lists, so
 * extras that ARE products contribute their spread children.
 */
function buildFractionListScenario(
  a: Expr,
  b: Expr,
  extras: readonly Expr[],
  posA: number,
  posB: number,
  inDen: boolean,
  onLhs: boolean,
  other: Expr,
): SumScenario {
  const list: Expr[] = [...extras];
  list.splice(posA % (list.length + 1), 0, a);
  list.splice(posB % (list.length + 1), 0, b);
  const f = inDen ? fraction([int(7)], list) : fraction(list, [int(7)]);
  const bystanders = [...f.num, ...f.den].filter((c) => c.id !== a.id && c.id !== b.id);
  return {
    eqn: onLhs ? equation(f, other) : equation(other, f),
    loc: f.id,
    termA: a.id,
    termB: b.id,
    bystanders,
  };
}

describe("additive-cancellation", () => {
  // Terms whose top level survives sum-flattening when inserted (and whose
  // negation does too): not a Sum, and not Neg(Sum).
  const arbCancellableTerm = arbExpr.filter(
    (e) => e.kind !== "sum" && !(e.kind === "neg" && e.child.kind === "sum"),
  );

  const arbScenario = fc
    .tuple(
      arbCancellableTerm,
      fc.array(arbExpr, { maxLength: 3 }),
      fc.integer({ min: 0, max: 7 }),
      fc.integer({ min: 0, max: 7 }),
      arbWrap,
      fc.boolean(),
      arbExpr,
    )
    .map(([t, extras, posA, posB, wrap, onLhs, other]) =>
      buildSumScenario(t, neg(cloneFresh(t)), extras, posA, posB, wrap, onLhs, other),
    );

  it("property: preserves the solution set", () => {
    fc.assert(
      fc.property(arbScenario, arbEnvs, (sc, envs) => {
        expect(
          additiveCancellation.precondition(mkJudgment(sc.eqn), sc.loc, {
            termA: sc.termA,
            termB: sc.termB,
          }),
        ).toBe(true);
        const { equation: after } = additiveCancellation.apply(mkJudgment(sc.eqn), sc.loc, {
          termA: sc.termA,
          termB: sc.termB,
        });
        assertSolutionSetPreserved(sc.eqn, after, envs);
      }),
    );
  });

  it("property: structural invariants, removals, and bystander id stability", () => {
    fc.assert(
      fc.property(arbScenario, (sc) => {
        const params = { termA: sc.termA, termB: sc.termB };
        const { equation: after, diff } = additiveCancellation.apply(
          mkJudgment(sc.eqn),
          sc.loc,
          params,
        );
        checkAfter(sc.eqn, after);
        expect(findById(after, sc.termA)).toBeUndefined();
        expect(findById(after, sc.termB)).toBeUndefined();
        expect(diff.removed).toContain(sc.termA);
        expect(diff.removed).toContain(sc.termB);
        checkBystandersStable(after, sc.bystanders, true);
      }),
    );
  });

  it("rejects terms that are not negations of each other", () => {
    const s = sum([int(2), int(3)]);
    if (s.kind !== "sum") throw new Error("unreachable");
    const eqn = embed(s, "top", int(1), true);
    const [a, b] = s.children;
    expect(
      additiveCancellation.precondition(mkJudgment(eqn), s.id, { termA: a!.id, termB: b!.id }),
    ).toBe(false);
    expect(() =>
      additiveCancellation.apply(mkJudgment(eqn), s.id, { termA: a!.id, termB: b!.id }),
    ).toThrow();
  });

  it("cancels like terms with opposite coefficients (2x and (−2)x)", () => {
    const a = product([int(2), variable("x")]);
    const b = product([int(-2), variable("x")]); // (−2)x — a product, not a Neg node
    const s = sum([a, b, product([int(3), variable("y")])]);
    if (s.kind !== "sum") throw new Error("unreachable");
    const eqn = embed(s, "top", int(0), true);
    expect(
      additiveCancellation.precondition(mkJudgment(eqn), s.id, { termA: a.id, termB: b.id }),
    ).toBe(true);
    const { equation: after } = additiveCancellation.apply(mkJudgment(eqn), s.id, {
      termA: a.id,
      termB: b.id,
    });
    expect(findById(after, a.id)).toBeUndefined();
    expect(findById(after, b.id)).toBeUndefined();
  });
});

describe("multiply-by-zero", () => {
  it("property: 0·x preserves the solution set", () => {
    fc.assert(
      fc.property(arbExpr, arbEnvs, (factor, envs) => {
        const prod = product([int(0), factor]);
        if (prod.kind !== "product") return; // a product is what the rule targets
        const eqn = embed(prod, "top", int(1), true); // (0·factor) = 1
        const { equation: after } = multiplyByZero.apply(mkJudgment(eqn), prod.id, {});
        assertSolutionSetPreserved(eqn, after, envs);
      }),
    );
  });

  it("collapses a zero-factor product to 0", () => {
    const prod = product([int(0), variable("x")]);
    const eqn = embed(prod, "top", int(0), true);
    const { equation: after } = multiplyByZero.apply(mkJudgment(eqn), prod.id, {});
    expect(after.lhs.kind).toBe("int");
    expect(after.lhs.kind === "int" && after.lhs.value).toBe(0n);
  });
});

describe("cancel-negatives", () => {
  it("property: (−a)(−b) preserves the solution set", () => {
    fc.assert(
      fc.property(arbExpr, arbExpr, arbEnvs, (a, b, envs) => {
        const prod = product([neg(a), neg(b)]);
        if (prod.kind !== "product" || prod.children.filter((c) => c.kind === "neg").length < 2) {
          return; // a or b was itself a Neg (collapsed) — not the case under test
        }
        const eqn = embed(prod, "top", int(1), true); // ((−a)(−b)) = 1
        const { equation: after } = cancelNegatives.apply(mkJudgment(eqn), prod.id, {});
        assertSolutionSetPreserved(eqn, after, envs);
      }),
    );
  });

  it("turns (−2)(−y) into 2·y", () => {
    const prod = product([int(-2), neg(variable("y"))]);
    const eqn = embed(prod, "top", int(0), true);
    const { equation: after } = cancelNegatives.apply(mkJudgment(eqn), prod.id, {});
    expect(exprToString(after.lhs)).toBe("(2 * y)");
  });
});

describe("distribute-negation", () => {
  it("property: −(a + b) preserves the solution set", () => {
    fc.assert(
      fc.property(arbExpr, arbExpr, arbEnvs, (a, b, envs) => {
        const ns = neg(sum([a, b]));
        if (ns.kind !== "neg" || ns.child.kind !== "sum") return;
        const eqn = embed(ns, "top", int(0), true);
        const { equation: after } = distributeNegation.apply(mkJudgment(eqn), ns.id, {});
        assertSolutionSetPreserved(eqn, after, envs);
      }),
    );
  });

  it("turns −(x − y) into −x + y", () => {
    const ns = neg(sum([variable("x"), neg(variable("y"))]));
    if (ns.kind !== "neg") throw new Error("unreachable");
    const eqn = embed(ns, "top", int(0), true);
    const { equation: after } = distributeNegation.apply(mkJudgment(eqn), ns.id, {});
    expect(exprToString(after.lhs)).toBe("(-x + y)");
  });
});

describe("add-to-both-sides", () => {
  it("property: preserves the solution set", () => {
    fc.assert(
      fc.property(arbEquation, arbExpr, arbEnvs, (eqn, term, envs) => {
        expect(addToBothSides.precondition(mkJudgment(eqn), eqn.id, { term })).toBe(true);
        const { equation: after } = addToBothSides.apply(mkJudgment(eqn), eqn.id, { term });
        assertSolutionSetPreserved(eqn, after, envs);
      }),
    );
  });

  it("property: removes nothing, clones the term, keeps every original id", () => {
    fc.assert(
      fc.property(arbEquation, arbExpr, (eqn, term) => {
        const { equation: after, diff } = addToBothSides.apply(mkJudgment(eqn), eqn.id, { term });
        checkAfter(eqn, after);
        expect(diff.removed).toEqual([]);
        expect(diff.created.length).toBeGreaterThan(0);
        const afterIds = idsOf(after);
        for (const id of idsOf(eqn)) {
          expect(afterIds.has(id), `original node ${id} vanished`).toBe(true);
        }
        // The caller's term instance must not be captured into the tree.
        for (const n of allNodes(term)) {
          expect(afterIds.has(n.id)).toBe(false);
        }
      }),
    );
  });

  it("rejects any location other than the equation root", () => {
    fc.assert(
      fc.property(arbEquation, arbExpr, (eqn, term) => {
        expect(addToBothSides.precondition(mkJudgment(eqn), eqn.lhs.id, { term })).toBe(false);
      }),
    );
  });
});

describe("combine-integers", () => {
  const arbScenario = fc
    .tuple(
      fc.integer({ min: -9, max: 9 }),
      fc.integer({ min: -9, max: 9 }),
      fc.array(arbExpr, { maxLength: 3 }),
      fc.integer({ min: 0, max: 7 }),
      fc.integer({ min: 0, max: 7 }),
      arbWrap,
      fc.boolean(),
      arbExpr,
    )
    .map(([va, vb, extras, posA, posB, wrap, onLhs, other]) => {
      const sc = buildSumScenario(int(va), int(vb), extras, posA, posB, wrap, onLhs, other);
      const total = BigInt(va + vb);
      // When the whole sum folds to Neg(Integer) under a Neg parent, the
      // double negation collapses too, so the literal left in the tree is
      // the positive child.
      const swallowed = wrap === "neg" && sc.bystanders.length === 0 && total < 0n;
      return { ...sc, expected: swallowed ? -total : total };
    });

  /** Reads an Integer / Neg(Integer) literal back out of the result tree. */
  function literalValue(e: Expr | undefined): bigint | undefined {
    if (e === undefined) return undefined;
    if (e.kind === "int") return e.value;
    if (e.kind === "neg" && e.child.kind === "int") return -e.child.value;
    return undefined;
  }

  it("property: preserves the solution set", () => {
    fc.assert(
      fc.property(arbScenario, arbEnvs, (sc, envs) => {
        const params = { termA: sc.termA, termB: sc.termB };
        expect(combineIntegers.precondition(mkJudgment(sc.eqn), sc.loc, params)).toBe(true);
        const { equation: after } = combineIntegers.apply(mkJudgment(sc.eqn), sc.loc, params);
        assertSolutionSetPreserved(sc.eqn, after, envs);
      }),
    );
  });

  it("property: folds to the right literal, keeps bystanders, holds invariants", () => {
    fc.assert(
      fc.property(arbScenario, (sc) => {
        const params = { termA: sc.termA, termB: sc.termB };
        const { equation: after, diff } = combineIntegers.apply(mkJudgment(sc.eqn), sc.loc, params);
        checkAfter(sc.eqn, after);
        expect(diff.merged).toHaveLength(1);
        const folded = findById(after, diff.merged[0]!.target) as Expr | undefined;
        expect(literalValue(folded)).toBe(sc.expected);
        checkBystandersStable(after, sc.bystanders);
      }),
    );
  });

  it("rejects non-integer terms", () => {
    // x + 2: combining x with 2 must be impossible.
    const sx = sum([int(2), variable("x")]);
    if (sx.kind !== "sum") throw new Error("unreachable");
    const eqn = embed(sx, "top", int(0), true);
    const [a, b] = sx.children;
    expect(
      combineIntegers.precondition(mkJudgment(eqn), sx.id, { termA: a!.id, termB: b!.id }),
    ).toBe(false);
    expect(() =>
      combineIntegers.apply(mkJudgment(eqn), sx.id, { termA: a!.id, termB: b!.id }),
    ).toThrow();
  });
});

describe("combine-integer-factors", () => {
  // No "product" wrap: embedding a Product inside a Product would flatten it
  // and invalidate the location.
  const arbProductWrap = fc.constantFrom<Wrap>("top", "neg", "fraction");

  const arbScenario = fc
    .tuple(
      fc.integer({ min: -9, max: 9 }),
      fc.integer({ min: -9, max: 9 }),
      fc.array(arbExpr, { maxLength: 3 }),
      fc.integer({ min: 0, max: 7 }),
      fc.integer({ min: 0, max: 7 }),
      arbProductWrap,
      fc.boolean(),
      arbExpr,
    )
    .map(([va, vb, extras, posA, posB, wrap, onLhs, other]) => {
      const sc = buildNaryScenario(
        "product",
        int(va),
        int(vb),
        extras,
        posA,
        posB,
        wrap,
        onLhs,
        other,
      );
      const total = BigInt(va) * BigInt(vb);
      // A full collapse to Neg(Integer) under a Neg parent swallows the
      // double negation, leaving the positive child literal. The fraction
      // wrap ALSO negs product targets (embed keeps them intact that way).
      const swallowed =
        (wrap === "neg" || wrap === "fraction") &&
        sc.bystanders.length === 0 &&
        total < 0n;
      return { ...sc, expected: swallowed ? -total : total };
    });

  function literalValue(e: Expr | undefined): bigint | undefined {
    if (e === undefined) return undefined;
    if (e.kind === "int") return e.value;
    if (e.kind === "neg" && e.child.kind === "int") return -e.child.value;
    return undefined;
  }

  it("property: preserves the solution set", () => {
    fc.assert(
      fc.property(arbScenario, arbEnvs, (sc, envs) => {
        const params = { termA: sc.termA, termB: sc.termB };
        expect(combineIntegerFactors.precondition(mkJudgment(sc.eqn), sc.loc, params)).toBe(true);
        const { equation: after } = combineIntegerFactors.apply(mkJudgment(sc.eqn), sc.loc, params);
        assertSolutionSetPreserved(sc.eqn, after, envs);
      }),
    );
  });

  it("property: folds to the right literal, keeps bystanders, holds invariants", () => {
    fc.assert(
      fc.property(arbScenario, (sc) => {
        const params = { termA: sc.termA, termB: sc.termB };
        const { equation: after, diff } = combineIntegerFactors.apply(
          mkJudgment(sc.eqn),
          sc.loc,
          params,
        );
        checkAfter(sc.eqn, after);
        expect(diff.merged).toHaveLength(1);
        const folded = findById(after, diff.merged[0]!.target) as Expr | undefined;
        expect(literalValue(folded)).toBe(sc.expected);
        checkBystandersStable(after, sc.bystanders, true);
      }),
    );
  });

  const arbListScenario = fc
    .tuple(
      fc.integer({ min: -9, max: 9 }),
      fc.integer({ min: -9, max: 9 }),
      fc.array(arbExpr, { maxLength: 2 }),
      fc.integer({ min: 0, max: 7 }),
      fc.integer({ min: 0, max: 7 }),
      fc.boolean(),
      fc.boolean(),
      arbExpr,
    )
    .map(([va, vb, extras, posA, posB, inDen, onLhs, other]) => {
      const sc = buildFractionListScenario(int(va), int(vb), extras, posA, posB, inDen, onLhs, other);
      // No swallowing inside a list: the bar survives, the literal lands as-is.
      return { ...sc, expected: BigInt(va) * BigInt(vb) };
    });

  it("property: folds inside fraction lists too (the lists are implicit products)", () => {
    fc.assert(
      fc.property(arbListScenario, arbEnvs, (sc, envs) => {
        const params = { termA: sc.termA, termB: sc.termB };
        const j = mkJudgment(sc.eqn);
        expect(combineIntegerFactors.precondition(j, sc.loc, params)).toBe(true);
        const { equation: after, diff } = combineIntegerFactors.apply(j, sc.loc, params);
        checkAfter(sc.eqn, after);
        expect(findById(after, sc.loc)).toBeDefined();
        expect(diff.merged).toHaveLength(1);
        const folded = findById(after, diff.merged[0]!.target) as Expr | undefined;
        expect(literalValue(folded)).toBe(sc.expected);
        assertSolutionSetPreserved(sc.eqn, after, envs);
        checkBystandersStable(after, sc.bystanders);
      }),
    );
  });

  it("rejects non-integer factors", () => {
    // 3x: folding 3 with x must be impossible (no coefficient to absorb into).
    const px = product([int(3), variable("x")]);
    if (px.kind !== "product") throw new Error("unreachable");
    const eqn = embed(px, "top", int(0), true);
    const [a, b] = px.children;
    expect(
      combineIntegerFactors.precondition(mkJudgment(eqn), px.id, { termA: a!.id, termB: b!.id }),
    ).toBe(false);
    expect(() =>
      combineIntegerFactors.apply(mkJudgment(eqn), px.id, { termA: a!.id, termB: b!.id }),
    ).toThrow();
  });

  // The generalization: a bare integer absorbs into a sibling's coefficient,
  // reaching it through a Neg wrapper (the "−3 onto −2x" case that previously
  // had no move, so the grab escalated to the whole product).
  const arbBody = arbExpr.filter(
    (e) => e.kind !== "int" && e.kind !== "neg" && e.kind !== "sum" && e.kind !== "product",
  );
  const arbAbsorb = fc
    .tuple(
      fc.integer({ min: -9, max: 9 }).filter((v) => v !== 0),
      fc.integer({ min: 1, max: 9 }),
      arbBody,
      fc.array(arbExpr, { maxLength: 2 }),
      fc.integer({ min: 0, max: 7 }),
      fc.integer({ min: 0, max: 7 }),
      arbProductWrap,
      fc.boolean(),
      arbExpr,
    )
    .map(([v, m, body, extras, posA, posB, wrap, onLhs, other]) => {
      // Neg wrapper keeps the coefficient nested (a bare product would flatten
      // into the outer one). coeff of the target is −m: −body or −(m·body).
      const target = neg(m === 1 ? body : product([int(m), body]));
      const sc = buildNaryScenario("product", int(v), target, extras, posA, posB, wrap, onLhs, other);
      return { ...sc, body, expectedCoeff: BigInt(v) * BigInt(-m) };
    });

  it("property: a bare integer absorbs into a Neg-wrapped coefficient, soundly", () => {
    fc.assert(
      fc.property(arbAbsorb, arbEnvs, (sc, envs) => {
        const j = mkJudgment(sc.eqn);
        const params = { termA: sc.termA, termB: sc.termB };
        expect(combineIntegerFactors.precondition(j, sc.loc, params)).toBe(true);
        const { equation: after, emits, diff } = combineIntegerFactors.apply(j, sc.loc, params);
        expect(emits).toEqual([]);
        expect(invariantViolations(after)).toEqual([]);
        expect(diff.merged).toHaveLength(1);
        // The body survives by identity (unless it dissolved into a flattening
        // parent — a product body would, but arbBody excludes products).
        expect(findById(after, sc.body.id)).toBeDefined();
        assertSolutionSetPreserved(sc.eqn, after, envs);
        checkBystandersStable(after, sc.bystanders, true);
      }),
    );
  });

  it("builds the textbook shapes the playtest asked for", () => {
    // −3 · −(2x) ~> 6x  (the reported grab/fold)
    const neg3 = neg(int(3));
    const neg2x = neg(product([int(2), variable("x")]));
    const p1 = product([neg3, neg2x]);
    if (p1.kind !== "product") throw new Error("unreachable");
    const r1 = combineIntegerFactors.apply(mkJudgment(equation(p1, int(0))), p1.id, {
      termA: neg3.id,
      termB: neg2x.id,
    });
    expect(eq(r1.equation.lhs, product([int(6), variable("x")]))).toBe(true);

    // x · (−1) ~> −x  (the −1 sign absorber)
    const x = variable("x");
    const negOne = neg(int(1));
    const p2 = product([x, negOne]);
    if (p2.kind !== "product") throw new Error("unreachable");
    const r2 = combineIntegerFactors.apply(mkJudgment(equation(p2, int(0))), p2.id, {
      termA: x.id,
      termB: negOne.id,
    });
    expect(eq(r2.equation.lhs, neg(variable("x")))).toBe(true);

    // 3 · (−x) ~> −3x  and  (−1)(−x) ~> x
    const three = int(3);
    const negX = neg(variable("x"));
    const p3 = product([three, negX]);
    if (p3.kind !== "product") throw new Error("unreachable");
    const r3 = combineIntegerFactors.apply(mkJudgment(equation(p3, int(0))), p3.id, {
      termA: three.id,
      termB: negX.id,
    });
    expect(eq(r3.equation.lhs, neg(product([int(3), variable("x")])))).toBe(true);

    const nOne = neg(int(1));
    const nX = neg(variable("x"));
    const p4 = product([nOne, nX]);
    if (p4.kind !== "product") throw new Error("unreachable");
    const r4 = combineIntegerFactors.apply(mkJudgment(equation(p4, int(0))), p4.id, {
      termA: nOne.id,
      termB: nX.id,
    });
    expect(eq(r4.equation.lhs, variable("x"))).toBe(true);
  });

  it("rejects the no-op 3·x but accepts the absorbing 3·(2x)", () => {
    const three = int(3);
    const x = variable("x");
    const noop = product([three, x]); // 3·x ~> 3x is no simplification
    if (noop.kind !== "product") throw new Error("unreachable");
    expect(
      combineIntegerFactors.precondition(mkJudgment(equation(noop, int(0))), noop.id, {
        termA: three.id,
        termB: x.id,
      }),
    ).toBe(false);

    const three2 = int(3);
    const twoX = neg(product([int(2), variable("x")]));
    const yes = product([three2, twoX]);
    if (yes.kind !== "product") throw new Error("unreachable");
    expect(
      combineIntegerFactors.precondition(mkJudgment(equation(yes, int(0))), yes.id, {
        termA: three2.id,
        termB: twoX.id,
      }),
    ).toBe(true);
  });
});

describe("combine-fractions", () => {
  // Two fraction terms of a sum, embedded at depth, plus bystanders.
  const arbFracPart = fc.array(arbExpr.filter((e) => e.kind !== "product"), { minLength: 1, maxLength: 2 });
  const arbScenario = fc
    .tuple(
      arbFracPart,
      arbFracPart,
      arbFracPart,
      arbFracPart,
      fc.array(arbExpr, { maxLength: 2 }),
      fc.integer({ min: 0, max: 7 }),
      fc.integer({ min: 0, max: 7 }),
      arbWrap,
      fc.boolean(),
      arbExpr,
    )
    .map(([n1, d1, n2, d2, extras, posA, posB, wrap, onLhs, other]) => {
      const fa = fraction(n1, d1);
      const fb = fraction(n2, d2);
      const sc = buildNaryScenario("sum", fa, fb, extras, posA, posB, wrap, onLhs, other);
      return { ...sc, fa: fa.id, fb: fb.id };
    });

  it("property: adds over a common denominator, preserving the solution set", () => {
    fc.assert(
      fc.property(arbScenario, arbEnvs, (sc, envs) => {
        const j = mkJudgment(sc.eqn);
        const params = { termA: sc.fa, termB: sc.fb };
        expect(combineFractions.precondition(j, sc.loc, params)).toBe(true);
        const { equation: after, emits } = combineFractions.apply(j, sc.loc, params);
        expect(emits).toEqual([]);
        expect(invariantViolations(after)).toEqual([]);
        assertSolutionSetPreserved(sc.eqn, after, envs);
        checkBystandersStable(after, sc.bystanders, true);
      }),
    );
  });

  it("builds the textbook shapes", () => {
    // x/2 + x/3 ~> (x·3 + x·2)/(2·3)
    const fa = fraction([variable("x")], [int(2)]);
    const fb = fraction([variable("x")], [int(3)]);
    const s = sum([fa, fb]);
    if (s.kind !== "sum") throw new Error("unreachable");
    const r = combineFractions.apply(mkJudgment(equation(s, int(5))), s.id, { termA: fa.id, termB: fb.id });
    const expected = fraction(
      [sum([product([variable("x"), int(3)]), product([variable("x"), int(2)])])],
      [int(2), int(3)],
    );
    expect(eq(r.equation.lhs, expected)).toBe(true);

    // x/2 + 3 ~> (x + 3·2)/2  (a whole term is itself over 1)
    const fc2 = fraction([variable("x")], [int(2)]);
    const three = int(3);
    const s2 = sum([fc2, three]);
    if (s2.kind !== "sum") throw new Error("unreachable");
    const r2 = combineFractions.apply(mkJudgment(equation(s2, int(4))), s2.id, { termA: fc2.id, termB: three.id });
    const expected2 = fraction([sum([variable("x"), product([int(3), int(2)])])], [int(2)]);
    expect(eq(r2.equation.lhs, expected2)).toBe(true);
  });

  it("rejects when neither term is a fraction", () => {
    const s = sum([variable("x"), int(3)]);
    if (s.kind !== "sum") throw new Error("unreachable");
    const [a, b] = s.children;
    expect(
      combineFractions.precondition(mkJudgment(equation(s, int(0))), s.id, { termA: a!.id, termB: b!.id }),
    ).toBe(false);
  });
});

describe("reduce-integer-fraction", () => {
  const arbScenario = fc
    .tuple(
      fc.integer({ min: -9, max: 9 }), // numerator base (0 allowed)
      fc.integer({ min: 1, max: 9 }), // denominator base magnitude
      fc.boolean(), // denominator sign
      fc.integer({ min: 2, max: 5 }), // guaranteed common factor
      fc.array(arbExpr, { maxLength: 2 }),
      fc.array(arbExpr, { maxLength: 2 }),
      arbWrap,
      fc.boolean(),
      arbExpr,
    )
    .map(([a0, b0, bNeg, g0, numExtras, denExtras, wrap, onLhs, other]) => {
      const aNode = int(a0 * g0);
      const bNode = int((bNeg ? -b0 : b0) * g0);
      const f = fraction([aNode, ...numExtras], [bNode, ...denExtras]);
      return {
        eqn: embed(f, wrap, other, onLhs),
        loc: f.id,
        params: { numTermId: aNode.id, denTermId: bNode.id },
      };
    });

  it("property: reduces exactly, preserving the solution set with NO assumptions", () => {
    fc.assert(
      fc.property(arbScenario, arbEnvs, (sc, envs) => {
        const j = mkJudgment(sc.eqn);
        expect(reduceIntegerFraction.precondition(j, sc.loc, sc.params)).toBe(true);
        const { equation: after, emits } = reduceIntegerFraction.apply(j, sc.loc, sc.params);
        expect(emits).toEqual([]);
        expect(invariantViolations(after)).toEqual([]);
        assertSolutionSetPreserved(sc.eqn, after, envs);
      }),
    );
  });

  it("computes the textbook cases", () => {
    const cases: { num: number; den: number; expected: Expr }[] = [
      { num: 6, den: 3, expected: int(2) },
      { num: 6, den: 4, expected: fraction([int(3)], [int(2)]) },
      { num: -6, den: 3, expected: int(-2) },
      { num: 6, den: -3, expected: int(-2) },
      { num: 0, den: 3, expected: int(0) },
    ];
    for (const c of cases) {
      const a = int(c.num);
      const b = int(c.den);
      const f = fraction([a], [b]);
      const eqn = equation(f, variable("y"));
      const { equation: after } = reduceIntegerFraction.apply(mkJudgment(eqn), f.id, {
        numTermId: a.id,
        denTermId: b.id,
      });
      expect(eq(after.lhs, c.expected), `${c.num}/${c.den}`).toBe(true);
    }
  });

  it("leaves an implicit 1 numerator: 3/(3x) ~> 1/x", () => {
    const a = int(3);
    const b = int(3);
    const f = fraction([a], [b, variable("x")]);
    const eqn = equation(f, variable("y"));
    const { equation: after } = reduceIntegerFraction.apply(mkJudgment(eqn), f.id, {
      numTermId: a.id,
      denTermId: b.id,
    });
    expect(eq(after.lhs, fraction([], [variable("x")]))).toBe(true);
  });

  it("rejects coprime pairs and zero denominators", () => {
    const a = int(5);
    const b = int(3);
    const f = fraction([a], [b]);
    const eqn = equation(f, variable("y"));
    expect(
      reduceIntegerFraction.precondition(mkJudgment(eqn), f.id, {
        numTermId: a.id,
        denTermId: b.id,
      }),
    ).toBe(false);

    const a2 = int(6);
    const b2 = int(0);
    const f2 = fraction([a2], [b2]);
    const eqn2 = equation(f2, variable("y"));
    expect(
      reduceIntegerFraction.precondition(mkJudgment(eqn2), f2.id, {
        numTermId: a2.id,
        denTermId: b2.id,
      }),
    ).toBe(false);
  });
});

describe("expand-power", () => {
  const arbScenario = fc
    .tuple(arbExpr, fc.integer({ min: 2, max: 4 }), arbWrap, fc.boolean(), arbExpr)
    .map(([base, n, wrap, onLhs, other]) => {
      const p = pow(base, int(n));
      return { eqn: embed(p, wrap, other, onLhs), loc: p.id, base, n };
    });

  it("property: unrolls exactly, preserving the solution set and the base's identity", () => {
    fc.assert(
      fc.property(arbScenario, arbEnvs, (sc, envs) => {
        const j = mkJudgment(sc.eqn);
        expect(expandPower.precondition(j, sc.loc, {})).toBe(true);
        const { equation: after, emits } = expandPower.apply(j, sc.loc, {});
        expect(emits).toEqual([]);
        expect(invariantViolations(after)).toEqual([]);
        expect(findById(after, sc.loc)).toBeUndefined(); // the Pow is gone
        // The base survives by identity — except a Product base, whose root
        // dissolves into the surrounding flattening; then its children survive.
        const survivors = sc.base.kind === "product" ? sc.base.children : [sc.base];
        for (const s of survivors) {
          expect(findById(after, s.id), `base part ${s.id} vanished`).toBeDefined();
        }
        assertSolutionSetPreserved(sc.eqn, after, envs);
      }),
    );
  });

  it("rejects x^1, x^0, and symbolic exponents", () => {
    for (const exp of [int(1), int(0), variable("y")]) {
      const p = pow(variable("x"), exp);
      const eqn = equation(p, int(1));
      expect(expandPower.precondition(mkJudgment(eqn), p.id, {})).toBe(false);
      expect(() => expandPower.apply(mkJudgment(eqn), p.id, {})).toThrow();
    }
  });
});

describe("combine-like-factors", () => {
  // Bare factors and literal powers of a shared base. Bases must not be
  // Products (a Product can't be a direct Product child) nor Pows (a bare
  // Pow factor decomposes one level deeper than pow(base, n) does, so the
  // two terms would read off different bases — nested-pow combining is
  // future work).
  const arbBase = arbExpr.filter((e) => e.kind !== "product" && e.kind !== "pow");
  const arbMaybeExp = fc.option(fc.integer({ min: 0, max: 3 }), { nil: undefined });
  const arbProductWrap = fc.constantFrom<Wrap>("top", "neg", "fraction");

  const arbScenario = fc
    .tuple(
      arbBase,
      arbMaybeExp,
      arbMaybeExp,
      fc.array(arbExpr, { maxLength: 2 }),
      fc.integer({ min: 0, max: 7 }),
      fc.integer({ min: 0, max: 7 }),
      arbProductWrap,
      fc.boolean(),
      arbExpr,
    )
    .map(([base, expA, expB, extras, posA, posB, wrap, onLhs, other]) => {
      const termA = expA === undefined ? base : pow(base, int(expA));
      const termB =
        expB === undefined ? cloneFresh(base) : pow(cloneFresh(base), int(expB));
      const sc = buildNaryScenario(
        "product",
        termA,
        termB,
        extras,
        posA,
        posB,
        wrap,
        onLhs,
        other,
      );
      return { ...sc, total: BigInt(expA ?? 1) + BigInt(expB ?? 1) };
    });

  it("property: merges exponents exactly, preserving the solution set", () => {
    fc.assert(
      fc.property(arbScenario, arbEnvs, (sc, envs) => {
        const j = mkJudgment(sc.eqn);
        const params = { termA: sc.termA, termB: sc.termB };
        expect(combineLikeFactors.precondition(j, sc.loc, params)).toBe(true);
        const { equation: after, emits, diff } = combineLikeFactors.apply(j, sc.loc, params);
        expect(emits).toEqual([]);
        expect(invariantViolations(after)).toEqual([]);
        // A merge target exists unless the splice swallowed every candidate
        // (e.g. a Product result dissolving into a flattening parent).
        expect(diff.merged.length).toBeLessThanOrEqual(1);
        for (const m of diff.merged) {
          expect(findById(after, m.target)).toBeDefined();
        }
        assertSolutionSetPreserved(sc.eqn, after, envs);
        checkBystandersStable(after, sc.bystanders, true);
      }),
    );
  });

  const arbListScenario = fc
    .tuple(
      arbBase,
      arbMaybeExp,
      arbMaybeExp,
      fc.array(arbExpr, { maxLength: 2 }),
      fc.integer({ min: 0, max: 7 }),
      fc.integer({ min: 0, max: 7 }),
      fc.boolean(),
      fc.boolean(),
      arbExpr,
    )
    .map(([base, expA, expB, extras, posA, posB, inDen, onLhs, other]) => {
      const termA = expA === undefined ? base : pow(base, int(expA));
      const termB =
        expB === undefined ? cloneFresh(base) : pow(cloneFresh(base), int(expB));
      return buildFractionListScenario(termA, termB, extras, posA, posB, inDen, onLhs, other);
    });

  it("property: merges inside fraction lists too (the lists are implicit products)", () => {
    fc.assert(
      fc.property(arbListScenario, arbEnvs, (sc, envs) => {
        const j = mkJudgment(sc.eqn);
        const params = { termA: sc.termA, termB: sc.termB };
        expect(combineLikeFactors.precondition(j, sc.loc, params)).toBe(true);
        const { equation: after, emits, diff } = combineLikeFactors.apply(j, sc.loc, params);
        expect(emits).toEqual([]);
        expect(invariantViolations(after)).toEqual([]);
        // The bar always survives a same-list merge (two elements became one).
        expect(findById(after, sc.loc)).toBeDefined();
        expect(diff.merged.length).toBeLessThanOrEqual(1);
        for (const m of diff.merged) {
          expect(findById(after, m.target)).toBeDefined();
        }
        assertSolutionSetPreserved(sc.eqn, after, envs);
        checkBystandersStable(after, sc.bystanders);
      }),
    );
  });

  it("merges x·x inside a denominator (the regression that motivated list sites)", () => {
    const x1 = variable("x");
    const x2 = variable("x");
    const f = fraction([int(1)], [x1, x2]);
    const eqn = equation(f, int(4));
    const j = mkJudgment(eqn);
    const params = { termA: x1.id, termB: x2.id };
    expect(combineLikeFactors.precondition(j, f.id, params)).toBe(true);
    const r = combineLikeFactors.apply(j, f.id, params);
    expect(eq(r.equation.lhs, fraction([int(1)], [pow(variable("x"), int(2))]))).toBe(true);
    expect(findById(r.equation, f.id)).toBeDefined();
  });

  it("rejects a num/den pair (that is cancellation territory, not combining)", () => {
    const xn = variable("x");
    const xd = variable("x");
    const f = fraction([xn], [xd]);
    const eqn = equation(f, int(1));
    expect(
      combineLikeFactors.precondition(mkJudgment(eqn), f.id, { termA: xn.id, termB: xd.id }),
    ).toBe(false);
  });

  it("builds the textbook shapes", () => {
    const x1 = variable("x");
    const x2 = variable("x");
    const p1 = product([x1, x2]);
    if (p1.kind !== "product") throw new Error("unreachable");
    const eqn1 = equation(p1, int(4));
    const r1 = combineLikeFactors.apply(mkJudgment(eqn1), p1.id, { termA: x1.id, termB: x2.id });
    expect(eq(r1.equation.lhs, pow(variable("x"), int(2)))).toBe(true);

    const a = pow(variable("x"), int(2));
    const b = pow(variable("x"), int(3));
    const p2 = product([a, b]);
    if (p2.kind !== "product") throw new Error("unreachable");
    const eqn2 = equation(p2, int(4));
    const r2 = combineLikeFactors.apply(mkJudgment(eqn2), p2.id, { termA: a.id, termB: b.id });
    expect(eq(r2.equation.lhs, pow(variable("x"), int(5)))).toBe(true);

    // x^0 · x collapses all the way to the bare base.
    const z = pow(variable("x"), int(0));
    const x3 = variable("x");
    const p3 = product([z, x3]);
    if (p3.kind !== "product") throw new Error("unreachable");
    const eqn3 = equation(p3, int(4));
    const r3 = combineLikeFactors.apply(mkJudgment(eqn3), p3.id, { termA: z.id, termB: x3.id });
    expect(eq(r3.equation.lhs, variable("x"))).toBe(true);
  });

  it("rejects different bases and symbolic exponents", () => {
    const x = variable("x");
    const y = variable("y");
    const p = product([x, y]);
    if (p.kind !== "product") throw new Error("unreachable");
    const eqn = equation(p, int(4));
    expect(
      combineLikeFactors.precondition(mkJudgment(eqn), p.id, { termA: x.id, termB: y.id }),
    ).toBe(false);

    const sym = pow(variable("x"), variable("a"));
    const x2 = variable("x");
    const p2 = product([sym, x2]);
    if (p2.kind !== "product") throw new Error("unreachable");
    const eqn2 = equation(p2, int(4));
    expect(
      combineLikeFactors.precondition(mkJudgment(eqn2), p2.id, { termA: sym.id, termB: x2.id }),
    ).toBe(false);
  });
});

describe("factor-out-negative", () => {
  // A sum that is a factor of a product with a negative sibling — the spot
  // the rule is offered. Terms kept non-sum so the sum survives construction.
  const arbTerm = arbExpr.filter((e) => e.kind !== "sum");
  const arbScenario = fc
    .tuple(
      fc.array(arbTerm, { minLength: 2, maxLength: 3 }),
      arbExpr.filter((e) => e.kind !== "neg"), // neg(this) is a real Neg sibling
      fc.boolean(),
      arbExpr,
    )
    .map(([terms, sib, onLhs, other]) => {
      const s = sum(terms);
      const prod = product([s, neg(sib)]);
      return { s, prod, eqn: onLhs ? equation(prod, other) : equation(other, prod) };
    })
    .filter((sc) => sc.s.kind === "sum" && sc.prod.kind === "product");

  it("property: −1 factors out exactly (an identity), preserving the solution set", () => {
    fc.assert(
      fc.property(arbScenario, arbEnvs, (sc, envs) => {
        const j = mkJudgment(sc.eqn);
        expect(factorOutNegative.precondition(j, sc.s.id, {})).toBe(true);
        const { equation: after, emits } = factorOutNegative.apply(j, sc.s.id, {});
        expect(emits).toEqual([]);
        expect(invariantViolations(after)).toEqual([]);
        // The sum kept its id but now hangs under a fresh Neg.
        const moved = findById(after, sc.s.id);
        expect(moved?.kind).toBe("sum");
        expect(findParent(after, sc.s.id)?.kind).toBe("neg");
        assertSolutionSetPreserved(sc.eqn, after, envs);
      }),
    );
  });

  it("builds the textbook shapes", () => {
    // (1 − 2x)·(−3) ~> (−(−1 + 2x))·(−3)   [the grouping-sign fix]
    const binom = sum([int(1), neg(product([int(2), variable("x")]))]);
    if (binom.kind !== "sum") throw new Error("unreachable");
    const p = product([binom, neg(int(3))]);
    const r = factorOutNegative.apply(mkJudgment(equation(p, int(0))), binom.id, {});
    const expected = product([
      neg(sum([int(-1), product([int(2), variable("x")])])),
      neg(int(3)),
    ]);
    expect(eq(r.equation.lhs, expected)).toBe(true);
  });

  it("is offered only with a negative sibling, never on a bare or positive context", () => {
    const binom = sum([variable("x"), int(3)]);
    if (binom.kind !== "sum") throw new Error("unreachable");
    // (x+3)·(−2): offered.
    const pNeg = product([binom, neg(int(2))]);
    expect(factorOutNegative.precondition(mkJudgment(equation(pNeg, int(0))), binom.id, {})).toBe(true);
    // (x+3)·2: positive sibling, NOT offered.
    const binom2 = sum([variable("x"), int(3)]);
    if (binom2.kind !== "sum") throw new Error("unreachable");
    const pPos = product([binom2, int(2)]);
    expect(factorOutNegative.precondition(mkJudgment(equation(pPos, int(0))), binom2.id, {})).toBe(false);
    // A top-level sum (not a product factor): NOT offered.
    const binom3 = sum([variable("x"), int(3)]);
    if (binom3.kind !== "sum") throw new Error("unreachable");
    expect(factorOutNegative.precondition(mkJudgment(equation(binom3, int(0))), binom3.id, {})).toBe(false);
  });
});

describe("distribute", () => {
  const arbProductWrap = fc.constantFrom<Wrap>("top", "neg", "fraction");

  const arbScenario = fc
    .tuple(
      arbExpr.filter((e) => e.kind !== "product"), // a direct Product child
      fc.array(arbExpr, { minLength: 2, maxLength: 4 }), // sum terms
      fc.array(arbExpr, { maxLength: 2 }), // extra factors
      arbProductWrap,
      fc.boolean(),
      arbExpr,
    )
    .map(([factor, terms, extras, wrap, onLhs, other]) => {
      const s = sum(terms);
      if (s.kind !== "sum") throw new Error("unreachable: >= 2 terms");
      const p = product([factor, s, ...extras]);
      if (p.kind !== "product") throw new Error("unreachable");
      return {
        eqn: embed(p, wrap, other, onLhs),
        loc: p.id,
        params: { factorId: factor.id, sumId: s.id },
        factorId: factor.id,
        sumId: s.id,
      };
    });

  it("property: distributes exactly, preserving solutions and the factor/sum ids", () => {
    fc.assert(
      fc.property(arbScenario, arbEnvs, (sc, envs) => {
        const j = mkJudgment(sc.eqn);
        expect(distribute.precondition(j, sc.loc, sc.params)).toBe(true);
        const { equation: after, emits } = distribute.apply(j, sc.loc, sc.params);
        expect(emits).toEqual([]);
        expect(invariantViolations(after)).toEqual([]);
        expect(findById(after, sc.factorId)).toBeDefined(); // survives in the first term
        const s = findById(after, sc.sumId);
        expect(s?.kind).toBe("sum");
        assertSolutionSetPreserved(sc.eqn, after, envs);
      }),
    );
  });

  it("builds the textbook shape: 2·(x + 3) ~> 2x + 2·3", () => {
    const two = int(2);
    const s = sum([variable("x"), int(3)]);
    const p = product([two, s]);
    if (p.kind !== "product") throw new Error("unreachable");
    const eqn = equation(p, int(10));
    const { equation: after } = distribute.apply(mkJudgment(eqn), p.id, {
      factorId: two.id,
      sumId: s.id,
    });
    const expected = sum([
      product([int(2), variable("x")]),
      product([int(2), int(3)]),
    ]);
    expect(eq(after.lhs, expected)).toBe(true);
  });
});

describe("split-term", () => {
  /** coeff·body as a canonical term, mirroring the rule's own builder. */
  function coeffTerm(b: bigint, body: Expr): Expr {
    const mag = b < 0n ? -b : b;
    const core = mag === 1n ? body : product([int(mag), body]);
    return b < 0n ? neg(core) : core;
  }

  // Bodies that survive term construction intact: not a Sum (would flatten
  // into the surrounding sum when bare), not a Neg (coeffTerm would collapse
  // Neg(Neg)), not an Integer — including inside a Product body, where a
  // literal child would read as the coefficient instead of `b`.
  const arbBody = arbExpr.filter(
    (e) =>
      e.kind !== "sum" &&
      e.kind !== "neg" &&
      e.kind !== "int" &&
      !(
        e.kind === "product" &&
        e.children.some((c) => c.kind === "int" || (c.kind === "neg" && c.child.kind === "int"))
      ),
  );
  const arbCoeff = fc
    .integer({ min: -9, max: 9 })
    .filter((b) => b !== 0)
    .map(BigInt);

  const arbScenario = fc
    .tuple(
      arbCoeff,
      arbBody,
      fc.integer({ min: -12, max: 12 }).map(BigInt),
      fc.array(arbExpr, { maxLength: 2 }),
      fc.integer({ min: 0, max: 7 }),
      arbWrap,
      fc.boolean(),
      arbExpr,
    )
    .filter(([b, , first]) => first !== 0n && first !== b)
    .map(([b, body, first, extras, pos, wrap, onLhs, other]) => {
      const term = coeffTerm(b, body);
      const filler = extras.filter((e) => e.kind !== "sum");
      const terms: Expr[] = [...filler, int(1)]; // ensure the sum survives as a sum
      terms.splice(pos % (terms.length + 1), 0, term);
      const s = sum(terms);
      if (s.kind !== "sum") throw new Error("scenario sum unexpectedly collapsed");
      const bystanders = s.children.filter((c) => c.id !== term.id);
      return {
        eqn: embed(s, wrap, other, onLhs),
        loc: s.id,
        term,
        body,
        first,
        bystanders,
      };
    });

  it("property: splits exactly — an identity that preserves the solution set", () => {
    fc.assert(
      fc.property(arbScenario, arbEnvs, (sc, envs) => {
        const j = mkJudgment(sc.eqn);
        const params = { termId: sc.term.id, first: sc.first };
        expect(splitTerm.precondition(j, sc.loc, params)).toBe(true);
        const { equation: after, emits } = splitTerm.apply(j, sc.loc, params);
        expect(emits).toEqual([]);
        expect(invariantViolations(after)).toEqual([]);
        // The sum survives with its id, one term longer.
        const s = findById(after, sc.loc);
        expect(s).toBeDefined();
        if (s === undefined || s.kind !== "sum") throw new Error("sum vanished");
        expect(s.children.length).toBe(sc.bystanders.length + 2);
        // The first part keeps the original body by identity — except a
        // Product body, whose root dissolves into the rebuilt term's
        // flattening; then its children survive instead (splice exception).
        if (findById(after, sc.body.id) === undefined) {
          expect(sc.body.kind).toBe("product");
          for (const child of childrenOf(sc.body)) {
            expect(findById(after, child.id), `body child ${child.id} vanished`).toBeDefined();
          }
        }
        assertSolutionSetPreserved(sc.eqn, after, envs);
        checkBystandersStable(after, sc.bystanders);
      }),
    );
  });

  it("builds the textbook shape: −6x in x² − 6x + 9 splits to −3x − 3x", () => {
    const x = variable("x");
    const mid = neg(product([int(6), variable("x")]));
    const lhs = sum([pow(x, int(2)), mid, int(9)]);
    if (lhs.kind !== "sum") throw new Error("unreachable");
    const eqn = equation(lhs, int(0));
    const r = splitTerm.apply(mkJudgment(eqn), lhs.id, { termId: mid.id, first: -3n });
    const expected = sum([
      pow(variable("x"), int(2)),
      neg(product([int(3), variable("x")])),
      neg(product([int(3), variable("x")])),
      int(9),
    ]);
    expect(eq(r.equation.lhs, expected)).toBe(true);
  });

  it("rejects degenerate splits and bare literals", () => {
    const term = product([int(6), variable("x")]);
    const nine = int(9);
    const lhs = sum([term, nine]);
    if (lhs.kind !== "sum") throw new Error("unreachable");
    const j = mkJudgment(equation(lhs, int(0)));
    expect(splitTerm.precondition(j, lhs.id, { termId: term.id, first: 0n })).toBe(false);
    expect(splitTerm.precondition(j, lhs.id, { termId: term.id, first: 6n })).toBe(false);
    expect(splitTerm.precondition(j, lhs.id, { termId: nine.id, first: 4n })).toBe(false);
    expect(splitTerm.precondition(j, lhs.id, { termId: term.id, first: 2n })).toBe(true);
  });
});

describe("factor-out", () => {
  type TermShape = "bare" | "cof" | "neg-bare" | "neg-cof";
  const arbShape = fc.constantFrom<TermShape>("bare", "cof", "neg-bare", "neg-cof");
  // Shared factors must be valid as bare sum terms and product factors, and
  // must survive neg() without collapsing.
  const arbFactor = arbExpr.filter(
    (e) => e.kind !== "product" && e.kind !== "sum" && e.kind !== "neg",
  );

  function mkTerm(shape: TermShape, instance: Expr, cof: Expr): Expr {
    switch (shape) {
      case "bare":
        return instance;
      case "cof":
        return product([cof, instance]);
      case "neg-bare":
        return neg(instance);
      case "neg-cof":
        return neg(product([cof, instance]));
    }
  }

  const arbScenario = fc
    .tuple(
      arbFactor,
      arbShape,
      arbShape,
      arbExpr.filter((e) => e.kind !== "neg"), // cofactors (kept non-neg so neg() wraps)
      arbExpr.filter((e) => e.kind !== "neg"),
      fc.array(arbExpr, { maxLength: 2 }),
      fc.integer({ min: 0, max: 7 }),
      fc.integer({ min: 0, max: 7 }),
      arbWrap,
      fc.boolean(),
      arbExpr,
    )
    .map(([g, shapeA, shapeB, cofA, cofB, extras, posA, posB, wrap, onLhs, other]) => {
      const ga = g;
      const gb = cloneFresh(g);
      const termA = mkTerm(shapeA, ga, cofA);
      const termB = mkTerm(shapeB, gb, cofB);
      const sc = buildNaryScenario("sum", termA, termB, extras, posA, posB, wrap, onLhs, other);
      return { ...sc, params: { factorA: ga.id, factorB: gb.id }, faId: ga.id };
    });

  it("property: factors out exactly across bare/cofactored/negated terms", () => {
    fc.assert(
      fc.property(arbScenario, arbEnvs, (sc, envs) => {
        const j = mkJudgment(sc.eqn);
        expect(factorOut.precondition(j, sc.loc, sc.params)).toBe(true);
        const { equation: after, emits, diff } = factorOut.apply(j, sc.loc, sc.params);
        expect(emits).toEqual([]);
        expect(invariantViolations(after)).toEqual([]);
        expect(findById(after, sc.faId)).toBeDefined(); // kept instance survives
        expect(diff.merged).toHaveLength(1);
        assertSolutionSetPreserved(sc.eqn, after, envs);
        checkBystandersStable(after, sc.bystanders, true);
      }),
    );
  });

  // The literal-divisor mode: the grabbed literal, read with its term's
  // sign, divides the other term's literal and comes out of both whole.
  const arbDivisorScenario = fc
    .tuple(
      fc.integer({ min: 2, max: 9 }).map(BigInt),
      fc.boolean(), // sign of the divisor
      fc.integer({ min: -9, max: 9 }).filter((m) => m !== 0).map(BigInt),
      arbExpr.filter((e) => e.kind !== "sum" && e.kind !== "neg" && e.kind !== "int"),
      fc.option(
        arbExpr.filter((e) => e.kind !== "sum" && e.kind !== "neg" && e.kind !== "int"),
        { nil: undefined },
      ),
      fc.array(arbExpr, { maxLength: 2 }),
      fc.integer({ min: 0, max: 7 }),
      fc.integer({ min: 0, max: 7 }),
      arbWrap,
      fc.boolean(),
      arbExpr,
    )
    .map(([mag, negA, m, bodyA, bodyB, extras, posA, posB, wrap, onLhs, other]) => {
      const sa = negA ? -mag : mag;
      const sb = sa * m;
      const litA = int(mag); // positive: the raw instance node
      const termA = sa < 0n ? neg(product([litA, bodyA])) : product([litA, bodyA]);
      const litB = int(sb < 0n ? -sb : sb);
      const coreB = bodyB === undefined ? litB : product([litB, bodyB]);
      const termB = sb < 0n ? neg(coreB) : coreB;
      const sc = buildNaryScenario("sum", termA, termB, extras, posA, posB, wrap, onLhs, other);
      return { ...sc, params: { factorA: litA.id, factorB: litB.id }, sa, sb };
    });

  it("property: a signed literal divisor factors out of both terms soundly", () => {
    fc.assert(
      fc.property(arbDivisorScenario, arbEnvs, (sc, envs) => {
        const j = mkJudgment(sc.eqn);
        expect(factorOut.precondition(j, sc.loc, sc.params)).toBe(true);
        const { equation: after, emits } = factorOut.apply(j, sc.loc, sc.params);
        expect(emits).toEqual([]);
        expect(invariantViolations(after)).toEqual([]);
        assertSolutionSetPreserved(sc.eqn, after, envs);
        checkBystandersStable(after, sc.bystanders, true);
      }),
    );
  });

  it("factors the signed coefficient out of the constant: −3x + 9 ~> (x + −3)·(−3)", () => {
    const three = int(3);
    const x = variable("x");
    const termA = neg(product([three, x]));
    const nine = int(9);
    const s = sum([termA, nine]);
    if (s.kind !== "sum") throw new Error("unreachable");
    const r = factorOut.apply(mkJudgment(equation(s, int(0))), s.id, {
      factorA: three.id,
      factorB: nine.id,
    });
    expect(
      eq(r.equation.lhs, product([sum([variable("x"), int(-3)]), int(-3)])),
    ).toBe(true);

    // Positive divisor: 3x + 9 ~> (x + 3)·3, the grabbed 3 surviving by id.
    const three2 = int(3);
    const termC = product([three2, variable("x")]);
    const nine2 = int(9);
    const s2 = sum([termC, nine2]);
    if (s2.kind !== "sum") throw new Error("unreachable");
    const r2 = factorOut.apply(mkJudgment(equation(s2, int(0))), s2.id, {
      factorA: three2.id,
      factorB: nine2.id,
    });
    expect(eq(r2.equation.lhs, product([sum([variable("x"), int(3)]), int(3)]))).toBe(true);
    expect(findById(r2.equation, three2.id)).toBeDefined();
  });

  it("rejects non-divisor literal pairs and ±1 divisors", () => {
    const nine = int(9);
    const x = variable("x");
    const termA = product([nine, x]);
    const three = int(3);
    const s = sum([termA, three]);
    if (s.kind !== "sum") throw new Error("unreachable");
    const j = mkJudgment(equation(s, int(0)));
    // 9 does not divide 3 — only the divisor side initiates.
    expect(factorOut.precondition(j, s.id, { factorA: nine.id, factorB: three.id })).toBe(false);

    const one = int(1);
    const termC = product([one, variable("x")]);
    const six = int(6);
    const s2 = sum([termC, six]);
    if (s2.kind !== "sum") throw new Error("unreachable");
    const j2 = mkJudgment(equation(s2, int(0)));
    expect(factorOut.precondition(j2, s2.id, { factorA: one.id, factorB: six.id })).toBe(false);
  });

  it("builds the textbook shapes", () => {
    // 3x + 2x ~> (3 + 2)·x
    const x1 = variable("x");
    const x2 = variable("x");
    const s1 = sum([product([int(3), x1]), product([int(2), x2])]);
    if (s1.kind !== "sum") throw new Error("unreachable");
    const r1 = factorOut.apply(mkJudgment(equation(s1, int(10))), s1.id, {
      factorA: x1.id,
      factorB: x2.id,
    });
    expect(eq(r1.equation.lhs, product([sum([int(3), int(2)]), variable("x")]))).toBe(true);

    // x + 2x ~> (1 + 2)·x — the bare term gets cofactor 1.
    const y1 = variable("x");
    const y2 = variable("x");
    const s2 = sum([y1, product([int(2), y2])]);
    if (s2.kind !== "sum") throw new Error("unreachable");
    const r2 = factorOut.apply(mkJudgment(equation(s2, int(10))), s2.id, {
      factorA: y1.id,
      factorB: y2.id,
    });
    expect(eq(r2.equation.lhs, product([sum([int(1), int(2)]), variable("x")]))).toBe(true);

    // x − 2x ~> (1 + (−2))·x — subtraction terms get negative cofactors.
    const z1 = variable("x");
    const z2 = variable("x");
    const s3 = sum([z1, neg(product([int(2), z2]))]);
    if (s3.kind !== "sum") throw new Error("unreachable");
    const r3 = factorOut.apply(mkJudgment(equation(s3, int(10))), s3.id, {
      factorA: z1.id,
      factorB: z2.id,
    });
    expect(eq(r3.equation.lhs, product([sum([int(1), int(-2)]), variable("x")]))).toBe(true);
  });

  it("rejects unequal factors", () => {
    const x = variable("x");
    const y = variable("y");
    const s = sum([x, y]);
    if (s.kind !== "sum") throw new Error("unreachable");
    const eqn = equation(s, int(1));
    expect(
      factorOut.precondition(mkJudgment(eqn), s.id, { factorA: x.id, factorB: y.id }),
    ).toBe(false);
  });
});

describe("identity taps", () => {
  it("property: dropping a literal zero term preserves solutions", () => {
    fc.assert(
      fc.property(
        fc.boolean(),
        fc.array(arbExpr, { minLength: 1, maxLength: 3 }),
        arbWrap,
        fc.boolean(),
        arbExpr,
        arbEnvs,
        (negZero, extras, wrap, onLhs, other, envs) => {
          const zero = negZero ? neg(int(0)) : int(0);
          const s = sum([zero, ...extras]);
          if (s.kind !== "sum") return; // a lone Sum extra can't shrink below 2
          const eqn = embed(s, wrap, other, onLhs);
          const j = mkJudgment(eqn);
          expect(dropZeroTerm.precondition(j, s.id, { termId: zero.id })).toBe(true);
          const { equation: after } = dropZeroTerm.apply(j, s.id, { termId: zero.id });
          expect(invariantViolations(after)).toEqual([]);
          expect(findById(after, zero.id)).toBeUndefined();
          assertSolutionSetPreserved(eqn, after, envs);
        },
      ),
    );
  });

  it("property: dropping a literal one factor preserves solutions", () => {
    fc.assert(
      fc.property(
        fc.array(arbExpr, { minLength: 1, maxLength: 3 }),
        fc.constantFrom<Wrap>("top", "neg", "fraction"),
        fc.boolean(),
        arbExpr,
        arbEnvs,
        (extras, wrap, onLhs, other, envs) => {
          const one = int(1);
          const p = product([one, ...extras]);
          if (p.kind !== "product") return;
          const eqn = embed(p, wrap, other, onLhs);
          const j = mkJudgment(eqn);
          expect(dropOneFactor.precondition(j, p.id, { termId: one.id })).toBe(true);
          const { equation: after } = dropOneFactor.apply(j, p.id, { termId: one.id });
          expect(invariantViolations(after)).toEqual([]);
          expect(findById(after, one.id)).toBeUndefined();
          assertSolutionSetPreserved(eqn, after, envs);
        },
      ),
    );
  });

  it("property: x^1 unwraps and x^0 collapses to 1, preserving solutions", () => {
    fc.assert(
      fc.property(arbExpr, fc.boolean(), arbWrap, fc.boolean(), arbExpr, arbEnvs, (
        base,
        isOne,
        wrap,
        onLhs,
        other,
        envs,
      ) => {
        const p = pow(base, int(isOne ? 1 : 0));
        const eqn = embed(p, wrap, other, onLhs);
        const j = mkJudgment(eqn);
        const rule = isOne ? powerOne : powerZero;
        expect(rule.precondition(j, p.id, {})).toBe(true);
        const { equation: after } = rule.apply(j, p.id, {});
        expect(invariantViolations(after)).toEqual([]);
        expect(findById(after, p.id)).toBeUndefined();
        if (isOne) {
          // The base survives — except when the splice dissolves its root
          // (Product flattening into a Product/Fraction parent, Neg under
          // Neg); then its children survive.
          const survivors =
            base.kind === "product"
              ? base.children
              : base.kind === "neg"
                ? [base.child]
                : [base];
          for (const s of survivors) {
            expect(findById(after, s.id), `base part ${s.id} vanished`).toBeDefined();
          }
        }
        assertSolutionSetPreserved(eqn, after, envs);
      }),
    );
  });

  it("rejects non-identities", () => {
    const two = int(2);
    const x = variable("x");
    const s = sum([two, x]);
    if (s.kind !== "sum") throw new Error("unreachable");
    const eqn = equation(s, int(1));
    expect(dropZeroTerm.precondition(mkJudgment(eqn), s.id, { termId: two.id })).toBe(false);

    const negOne = int(-1);
    const p = product([negOne, variable("x")]);
    if (p.kind !== "product") throw new Error("unreachable");
    const eqn2 = equation(p, int(1));
    expect(dropOneFactor.precondition(mkJudgment(eqn2), p.id, { termId: negOne.id })).toBe(false);

    const p3 = pow(variable("x"), int(2));
    const eqn3 = equation(p3, int(1));
    expect(powerOne.precondition(mkJudgment(eqn3), p3.id, {})).toBe(false);
    expect(powerZero.precondition(mkJudgment(eqn3), p3.id, {})).toBe(false);
  });
});

describe("move-term-across", () => {
  const arbScenario = fc
    .tuple(
      fc.array(
        arbExpr.filter((e) => e.kind !== "sum"), // valid direct Sum children
        { minLength: 1, maxLength: 3 },
      ),
      fc.integer({ min: 0, max: 2 }),
      arbExpr,
      fc.boolean(),
    )
    .map(([terms, idx, other, onLhs]) => {
      const side: Expr = terms.length === 1 ? terms[0]! : (sum(terms) as Expr);
      const term = terms[idx % terms.length]!;
      const termId = terms.length === 1 ? side.id : term.id;
      const eqn = onLhs ? equation(side, other) : equation(other, side);
      // A −(a+b) term arrives as a bare Sum and flattens into the
      // destination — its root dissolves, its children survive.
      const body = term.kind === "neg" ? term.child : term;
      const survivorIds =
        term.kind === "neg" && body.kind === "sum"
          ? body.children.map((c) => c.id)
          : [body.id];
      return { eqn, termId, survivorIds };
    });

  it("property: moves exactly — the term body arrives by identity, truth preserved", () => {
    fc.assert(
      fc.property(arbScenario, arbEnvs, (sc, envs) => {
        const j = mkJudgment(sc.eqn);
        expect(moveTermAcross.precondition(j, sc.eqn.id, { termId: sc.termId })).toBe(true);
        const { equation: after, emits } = moveTermAcross.apply(j, sc.eqn.id, {
          termId: sc.termId,
        });
        expect(emits).toEqual([]);
        expect(invariantViolations(after)).toEqual([]);
        for (const id of sc.survivorIds) {
          expect(findById(after, id), `moved part ${id} vanished`).toBeDefined();
        }
        assertSolutionSetPreserved(sc.eqn, after, envs);
      }),
    );
  });

  it("moves the textbook shapes", () => {
    // 2x = 10 − 3x ~> 2x + 3x = 10 (the minus is consumed in transit).
    const negTerm = neg(product([int(3), variable("x")]));
    const eqn1 = equation(
      product([int(2), variable("x")]),
      sum([int(10), negTerm]),
    );
    const r1 = moveTermAcross.apply(mkJudgment(eqn1), eqn1.id, { termId: negTerm.id });
    expect(
      eq(
        r1.equation,
        equation(
          sum([product([int(2), variable("x")]), product([int(3), variable("x")])]),
          int(10),
        ),
      ),
    ).toBe(true);

    // x + 2 = 5 ~> x = 5 − 2.
    const two = int(2);
    const eqn2 = equation(sum([variable("x"), two]), int(5));
    const r2 = moveTermAcross.apply(mkJudgment(eqn2), eqn2.id, { termId: two.id });
    expect(eq(r2.equation, equation(variable("x"), sum([int(5), neg(int(2))])))).toBe(true);

    // Whole side: 2x = 4 moving the 2x ~> 0 = 4 − 2x.
    const lhs = product([int(2), variable("x")]);
    const eqn3 = equation(lhs as Expr, int(4));
    const r3 = moveTermAcross.apply(mkJudgment(eqn3), eqn3.id, { termId: lhs.id });
    expect(
      eq(
        r3.equation,
        equation(int(0), sum([int(4), neg(product([int(2), variable("x")]))])),
      ),
    ).toBe(true);
  });

  it("rejects non-top-level ids", () => {
    const two = int(2);
    const lhs = product([two, variable("x")]); // 2 is a factor, not a term
    const eqn = equation(lhs as Expr, int(4));
    expect(moveTermAcross.precondition(mkJudgment(eqn), eqn.id, { termId: two.id })).toBe(false);
  });
});

describe("power rules", () => {
  it("property: x^(−n) becomes 1/x^n exactly, the Pow surviving by id", () => {
    fc.assert(
      fc.property(
        arbExpr,
        fc.integer({ min: 1, max: 3 }),
        arbWrap,
        fc.boolean(),
        arbExpr,
        arbEnvs,
        (base, n, wrap, onLhs, other, envs) => {
          const p = pow(base, int(-n));
          const eqn = embed(p, wrap, other, onLhs);
          const j = mkJudgment(eqn);
          expect(negativeExponent.precondition(j, p.id, {})).toBe(true);
          const { equation: after, emits } = negativeExponent.apply(j, p.id, {});
          expect(emits).toEqual([]);
          expect(invariantViolations(after)).toEqual([]);
          const survivor = findById(after, p.id);
          expect(survivor?.kind).toBe("pow"); // same Pow, exponent un-negated
          assertSolutionSetPreserved(eqn, after, envs);
        },
      ),
    );
  });

  it("property: (x^m)^n folds to x^(m·n) exactly", () => {
    fc.assert(
      fc.property(
        arbExpr,
        fc.integer({ min: 0, max: 3 }),
        fc.integer({ min: 0, max: 3 }),
        arbWrap,
        fc.boolean(),
        arbExpr,
        arbEnvs,
        (base, m, n, wrap, onLhs, other, envs) => {
          const inner = pow(base, int(m));
          const outer = pow(inner, int(n));
          const eqn = embed(outer, wrap, other, onLhs);
          const j = mkJudgment(eqn);
          expect(powerOfPower.precondition(j, outer.id, {})).toBe(true);
          const { equation: after, emits } = powerOfPower.apply(j, outer.id, {});
          expect(emits).toEqual([]);
          expect(invariantViolations(after)).toEqual([]);
          const survivor = findById(after, inner.id);
          expect(survivor?.kind).toBe("pow");
          if (survivor?.kind === "pow" && survivor.exp.kind === "int") {
            expect(survivor.exp.value).toBe(BigInt(m * n));
          }
          assertSolutionSetPreserved(eqn, after, envs);
        },
      ),
    );
  });

  it("property: (x·y)^n distributes exactly, factors surviving as bases", () => {
    fc.assert(
      fc.property(
        fc.array(
          arbExpr.filter((e) => e.kind !== "product"),
          { minLength: 2, maxLength: 3 },
        ),
        fc.integer({ min: 2, max: 3 }),
        fc.constantFrom<Wrap>("top", "neg", "fraction"),
        fc.boolean(),
        arbExpr,
        arbEnvs,
        (factors, n, wrap, onLhs, other, envs) => {
          const base = product(factors);
          if (base.kind !== "product") return;
          const p = pow(base, int(n));
          const eqn = embed(p, wrap, other, onLhs);
          const j = mkJudgment(eqn);
          expect(distributePower.precondition(j, p.id, {})).toBe(true);
          const { equation: after, emits } = distributePower.apply(j, p.id, {});
          expect(emits).toEqual([]);
          expect(invariantViolations(after)).toEqual([]);
          for (const f of factors) {
            expect(findById(after, f.id), `factor ${f.id} vanished`).toBeDefined();
          }
          assertSolutionSetPreserved(eqn, after, envs);
        },
      ),
    );
  });

  it("rejects the wrong shapes", () => {
    const plain = pow(variable("x"), int(2));
    const eqn = equation(plain, int(1));
    const j = mkJudgment(eqn);
    expect(negativeExponent.precondition(j, plain.id, {})).toBe(false);
    expect(powerOfPower.precondition(j, plain.id, {})).toBe(false);
    expect(distributePower.precondition(j, plain.id, {})).toBe(false);

    const symNested = pow(pow(variable("x"), variable("a")), int(2));
    const eqn2 = equation(symNested, int(1));
    expect(powerOfPower.precondition(mkJudgment(eqn2), symNested.id, {})).toBe(false);
  });
});
