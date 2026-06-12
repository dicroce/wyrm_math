/**
 * Geometry properties of the layout engine. These are what the future UI
 * leans on: complete id coverage (hit testing), nesting + sibling
 * disjointness (unambiguous deepest-hit), glyph containment (visuals stay
 * inside their draggable region), and context independence of subtree
 * geometry (id-keyed animation can move boxes rigidly).
 */
import fc from "fast-check";
import { describe, expect, it } from "vitest";
import {
  allNodes,
  childrenOf,
  equation,
  findById,
  fraction,
  hitTest,
  int,
  layoutNode,
  neg,
  pow,
  type Expr,
  type Layout,
  type LayoutRect,
  type Node,
} from "../src/index.js";
import { arbEquation, arbExpr } from "./gen.js";

const EPS = 1e-9;

function inside(inner: LayoutRect, outer: LayoutRect): boolean {
  return (
    inner.x >= outer.x - EPS &&
    inner.y >= outer.y - EPS &&
    inner.x + inner.width <= outer.x + outer.width + EPS &&
    inner.y + inner.height <= outer.y + outer.height + EPS
  );
}

function overlap(a: LayoutRect, b: LayoutRect): boolean {
  const ox = Math.min(a.x + a.width, b.x + b.width) - Math.max(a.x, b.x);
  const oy = Math.min(a.y + a.height, b.y + b.height) - Math.max(a.y, b.y);
  return ox > EPS && oy > EPS;
}

function contains(rect: LayoutRect, x: number, y: number): boolean {
  return x >= rect.x && x <= rect.x + rect.width && y >= rect.y && y <= rect.y + rect.height;
}

function checkGeometry(root: Node, l: Layout): void {
  // 1. Complete, exact id coverage.
  const treeIds = [...allNodes(root)].map((n) => n.id);
  expect(new Set(l.boxes.keys())).toEqual(new Set(treeIds));
  expect(l.boxes.size).toBe(treeIds.length);

  for (const node of allNodes(root)) {
    const box = l.boxes.get(node.id)!;
    // 2. Sane, finite, positive dimensions.
    expect(Number.isFinite(box.rect.x + box.rect.y + box.rect.width + box.rect.height)).toBe(true);
    expect(box.rect.width).toBeGreaterThan(0);
    expect(box.rect.height).toBeGreaterThan(0);

    const kids = childrenOf(node);
    for (const child of kids) {
      // 3. Children nest inside their parent.
      expect(
        inside(l.boxes.get(child.id)!.rect, box.rect),
        `child ${child.id} escapes parent ${node.id}`,
      ).toBe(true);
    }
    // 4. Siblings never overlap.
    for (let i = 0; i < kids.length; i++) {
      for (let j = i + 1; j < kids.length; j++) {
        expect(
          overlap(l.boxes.get(kids[i]!.id)!.rect, l.boxes.get(kids[j]!.id)!.rect),
          `siblings ${kids[i]!.id} and ${kids[j]!.id} overlap under ${node.id}`,
        ).toBe(false);
      }
    }
  }

  // 5. Glyphs stay inside their owner's box.
  for (const g of l.glyphs) {
    const owner = l.boxes.get(g.owner)!.rect;
    const rect: LayoutRect =
      g.kind === "char"
        ? { x: g.x, y: g.baseline - g.ascent, width: g.width, height: g.ascent + g.descent }
        : { x: g.x, y: g.y - g.thickness / 2, width: g.width, height: g.thickness };
    expect(inside(rect, owner), `glyph ${JSON.stringify(g)} escapes its owner`).toBe(true);
  }
}

describe("layout geometry properties", () => {
  it("coverage, nesting, sibling disjointness, glyph containment", () => {
    fc.assert(
      fc.property(arbEquation, (eqn) => {
        checkGeometry(eqn, layoutNode(eqn));
      }),
    );
  });

  it("hitTest returns the locally deepest box at every box center", () => {
    fc.assert(
      fc.property(arbEquation, (eqn) => {
        const l = layoutNode(eqn);
        for (const node of allNodes(eqn)) {
          const r = l.boxes.get(node.id)!.rect;
          const cx = r.x + r.width / 2;
          const cy = r.y + r.height / 2;
          const hitId = hitTest(l, cx, cy);
          expect(hitId).toBeDefined();
          const hitNode = findById(eqn, hitId!)!;
          expect(contains(l.boxes.get(hitId!)!.rect, cx, cy)).toBe(true);
          for (const child of childrenOf(hitNode)) {
            expect(
              contains(l.boxes.get(child.id)!.rect, cx, cy),
              `hit ${hitId} is not deepest: child ${child.id} also contains the point`,
            ).toBe(false);
          }
          // Leaves are their own deepest hit.
          if (childrenOf(node).length === 0) expect(hitId).toBe(node.id);
        }
        expect(hitTest(l, -1, -1)).toBeUndefined();
        expect(hitTest(l, l.width + 1, l.height + 1)).toBeUndefined();
      }),
    );
  });

  it("subtree geometry is context-independent up to translation and scale", () => {
    fc.assert(
      fc.property(arbExpr, fc.constantFrom(0, 1, 2, 3), (e, ctx) => {
        const standalone = layoutNode(e);
        const host: Node =
          ctx === 0
            ? equation(e, int(1))
            : ctx === 1
              ? // Product list elements spread (ctor invariant); ride in a Neg.
                fraction([e.kind === "product" ? neg(e) : e], [int(2)])
              : ctx === 2
                ? pow(int(2), e) // e in the exponent: scaled context
                : e.kind !== "neg"
                  ? neg(e)
                  : equation(e, int(1)); // neg(e) would collapse a Neg

        const embedded = layoutNode(host);
        const eStd = standalone.boxes.get(e.id)!;
        const eEmb = embedded.boxes.get(e.id)!;
        const k = eEmb.scale; // standalone scale is 1

        for (const d of allNodes(e)) {
          const std = standalone.boxes.get(d.id)!;
          const emb = embedded.boxes.get(d.id)!;
          expect(emb.scale).toBeCloseTo(k * std.scale, 9);
          expect(emb.rect.x - eEmb.rect.x).toBeCloseTo(k * (std.rect.x - eStd.rect.x), 9);
          expect(emb.baseline - eEmb.baseline).toBeCloseTo(k * (std.baseline - eStd.baseline), 9);
          expect(emb.rect.width).toBeCloseTo(k * std.rect.width, 9);
          expect(emb.rect.height).toBeCloseTo(k * std.rect.height, 9);
        }
      }),
    );
  });

  it("layout is deterministic", () => {
    fc.assert(
      fc.property(arbEquation, (eqn) => {
        const a = layoutNode(eqn);
        const b = layoutNode(eqn);
        expect(b.glyphs).toEqual(a.glyphs);
        expect([...b.boxes.entries()]).toEqual([...a.boxes.entries()]);
      }),
    );
  });
});
