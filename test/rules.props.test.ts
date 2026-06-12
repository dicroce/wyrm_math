import fc from "fast-check";
import { describe, expect, it } from "vitest";
import {
  additiveCancellation,
  addToBothSides,
  allNodes,
  childrenOf,
  cloneFresh,
  combineIntegerFactors,
  combineLikeFactors,
  distribute,
  dropOneFactor,
  dropZeroTerm,
  eq,
  equation,
  expandPower,
  factorOut,
  fraction,
  combineIntegers,
  findById,
  int,
  invariantViolations,
  mkJudgment,
  moveTermAcross,
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

  it("rejects non-integer factors", () => {
    // 3x: folding 3 with x must be impossible.
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
