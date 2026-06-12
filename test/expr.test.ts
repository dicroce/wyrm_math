import fc from "fast-check";
import { describe, expect, it } from "vitest";
import {
  allNodes,
  cloneFresh,
  eq,
  equation,
  findById,
  int,
  invariantViolations,
  neg,
  product,
  replaceNode,
  sum,
  variable,
  type Expr,
} from "../src/index.js";
import { arbEquation, arbExpr, subtreeIdenticalWithIds } from "./gen.js";

describe("smart constructors", () => {
  it("flatten nested sums (and keep grandchild ids)", () => {
    const a = variable("x");
    const b = int(2);
    const c = int(3);
    const inner = sum([b, c]);
    const outer = sum([a, inner]);
    expect(outer.kind).toBe("sum");
    if (outer.kind !== "sum") return;
    expect(outer.children.map((ch) => ch.id)).toEqual([a.id, b.id, c.id]);
  });

  it("collapse to identity / single child", () => {
    expect(eq(sum([]), int(0))).toBe(true);
    expect(eq(product([]), int(1))).toBe(true);
    const x = variable("x");
    expect(sum([x])).toBe(x);
    expect(product([x])).toBe(x);
  });

  it("collapse double negation to the original node", () => {
    const x = variable("x");
    expect(neg(neg(x))).toBe(x);
  });

  it("canonicalize negative integer literals as Neg(Integer)", () => {
    const m = int(-5);
    expect(m.kind).toBe("neg");
    if (m.kind !== "neg") return;
    expect(m.child.kind).toBe("int");
    expect(eq(m, neg(int(5)))).toBe(true);
  });

  it("property: every generated tree satisfies the structural invariants", () => {
    fc.assert(
      fc.property(arbEquation, (eqn) => {
        expect(invariantViolations(eqn)).toEqual([]);
      }),
    );
  });
});

describe("eq (structural equality)", () => {
  it("is order-insensitive for sums and products", () => {
    fc.assert(
      fc.property(
        fc.array(arbExpr, { minLength: 2, maxLength: 4 }),
        (terms) => {
          const forward = sum(terms.map(cloneFresh));
          const backward = sum([...terms].reverse().map(cloneFresh));
          expect(eq(forward, backward)).toBe(true);
          const pf = product(terms.map(cloneFresh));
          const pb = product([...terms].reverse().map(cloneFresh));
          expect(eq(pf, pb)).toBe(true);
        },
      ),
    );
  });

  it("is reflexive and survives cloneFresh", () => {
    fc.assert(
      fc.property(arbExpr, (e) => {
        expect(eq(e, e)).toBe(true);
        const clone = cloneFresh(e);
        expect(eq(e, clone)).toBe(true);
        const originalIds = new Set([...allNodes(e)].map((n) => n.id));
        for (const n of allNodes(clone)) {
          expect(originalIds.has(n.id)).toBe(false);
        }
      }),
    );
  });

  it("compares children as multisets, not sets", () => {
    const xxy = sum([variable("x"), variable("x"), variable("y")]);
    const xyy = sum([variable("x"), variable("y"), variable("y")]);
    expect(eq(xxy, xyy)).toBe(false);
    expect(eq(int(2), int(3))).toBe(false);
    expect(eq(variable("x"), variable("y"))).toBe(false);
    expect(eq(equation(variable("x"), int(1)), equation(int(1), variable("x")))).toBe(false);
  });
});

describe("replaceNode", () => {
  it("reuses untouched sibling subtrees by object identity", () => {
    fc.assert(
      fc.property(arbEquation, fc.boolean(), (eqn, replaceLhs) => {
        const target: Expr = replaceLhs ? eqn.lhs : eqn.rhs;
        const untouched: Expr = replaceLhs ? eqn.rhs : eqn.lhs;
        const replacement = variable("z");
        const next = replaceNode(eqn, target.id, replacement);
        expect(next.id).toBe(eqn.id);
        const survivor = replaceLhs ? next.rhs : next.lhs;
        expect(survivor).toBe(untouched);
        expect(findById(next, target.id)).toBeUndefined();
        expect(subtreeIdenticalWithIds(survivor, untouched)).toBe(true);
      }),
    );
  });

  it("throws on unknown ids and on replacing the root", () => {
    const eqn = equation(variable("x"), int(1));
    expect(() => replaceNode(eqn, "no-such-id", int(2))).toThrow();
    expect(() => replaceNode(eqn, eqn.id, int(2))).toThrow();
  });
});
