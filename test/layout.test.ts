import { describe, expect, it } from "vitest";
import {
  equation,
  fraction,
  hitTest,
  int,
  layoutNode,
  METRICS,
  neg,
  pow,
  product,
  sum,
  variable,
  type Layout,
  type PlacedGlyph,
} from "../src/index.js";

/** Glyph chars in left-to-right order (only sensible for single-line rows). */
function text(layout: Layout): string {
  return [...layout.glyphs]
    .filter((g): g is PlacedGlyph & { kind: "char" } => g.kind === "char")
    .sort((a, b) => a.x - b.x)
    .map((g) => g.char)
    .join("");
}

function charGlyph(layout: Layout, char: string): PlacedGlyph & { kind: "char" } {
  const g = layout.glyphs.find((g) => g.kind === "char" && g.char === char);
  if (g === undefined || g.kind !== "char") throw new Error(`no glyph ${char}`);
  return g;
}

describe("notation rules", () => {
  it("renders x + 2 with the plus owned by the Sum", () => {
    const s = sum([variable("x"), int(2)]);
    const l = layoutNode(s);
    expect(text(l)).toBe("x+2");
    expect(charGlyph(l, "+").owner).toBe(s.id);
  });

  it("renders a − b as binary subtraction, minus owned by the Neg", () => {
    const b = variable("b");
    const negB = neg(b);
    const s = sum([variable("a"), negB]);
    const l = layoutNode(s);
    expect(text(l)).toBe("a−b");
    expect(charGlyph(l, "−").owner).toBe(negB.id);
    // The Neg's box covers its minus sign — dragging the term grabs the sign.
    const negBox = l.boxes.get(negB.id)!;
    const minus = charGlyph(l, "−");
    expect(minus.x).toBeGreaterThanOrEqual(negBox.rect.x);
  });

  it("renders negative literals as −3", () => {
    const l = layoutNode(int(-3));
    expect(text(l)).toBe("−3");
  });

  it("parenthesizes a Sum under Neg and inside a Product", () => {
    const s1 = sum([variable("x"), int(1)]);
    expect(text(layoutNode(neg(s1)))).toBe("−(x+1)");
    const s2 = sum([variable("x"), int(1)]);
    expect(text(layoutNode(product([variable("y"), s2])))).toBe("y(x+1)");
  });

  it("uses · only where juxtaposition would glue digits", () => {
    expect(text(layoutNode(product([int(2), int(3)])))).toBe("2·3");
    expect(text(layoutNode(product([int(3), variable("x")])))).toBe("3x");
    expect(text(layoutNode(product([variable("x"), int(3)])))).toBe("x·3");
    expect(text(layoutNode(product([variable("x"), neg(variable("y"))])))).toBe("x(−y)");
  });

  it("parenthesizes compound Pow bases but not leaves", () => {
    expect(text(layoutNode(pow(variable("x"), int(2))))).toBe("x2");
    const p = product([int(3), variable("x")]);
    expect(text(layoutNode(pow(p, int(2))))).toBe("(3x)2");
  });

  it("raises and shrinks exponents", () => {
    const e = int(2);
    const p = pow(variable("x"), e);
    const l = layoutNode(p);
    const baseBox = l.boxes.get(p.base.id)!;
    const expBox = l.boxes.get(e.id)!;
    expect(expBox.scale).toBeCloseTo(METRICS.SUP_SCALE);
    expect(expBox.baseline).toBeLessThan(baseBox.baseline);
    expect(expBox.rect.x).toBeGreaterThanOrEqual(baseBox.rect.x + baseBox.rect.width);
  });

  it("stacks fractions: numerator above bar above denominator", () => {
    const n = variable("x");
    const d = int(2);
    const f = fraction([n], [d]);
    const l = layoutNode(equation(f, int(1)));
    const numBox = l.boxes.get(n.id)!;
    const denBox = l.boxes.get(d.id)!;
    const bar = l.glyphs.find((g) => g.kind === "bar")!;
    expect(bar.kind).toBe("bar");
    if (bar.kind !== "bar") return;
    expect(bar.owner).toBe(f.id);
    expect(numBox.rect.y + numBox.rect.height).toBeLessThanOrEqual(bar.y);
    expect(denBox.rect.y).toBeGreaterThanOrEqual(bar.y);
    // Bar spans the fraction's full width.
    const fracBox = l.boxes.get(f.id)!;
    expect(bar.width).toBeCloseTo(fracBox.rect.width);
  });

  it("renders empty fraction lists as an implicit 1", () => {
    const l = layoutNode(fraction([], [int(2)]));
    expect(text(l)).toBe("12"); // the 1 above, the 2 below
    const one = charGlyph(l, "1");
    expect(one.owner).toBe(l.rootId);
  });

  it("lays an equation on one shared baseline", () => {
    const eqn = equation(variable("x"), int(3));
    const l = layoutNode(eqn);
    expect(text(l)).toBe("x=3");
    expect(charGlyph(l, "=").owner).toBe(eqn.id);
    expect(l.boxes.get(eqn.lhs.id)!.baseline).toBeCloseTo(l.boxes.get(eqn.rhs.id)!.baseline);
  });
});

describe("hitTest", () => {
  it("resolves digits, operators, and empty space correctly", () => {
    const two = int(2);
    const x = variable("x");
    const s = sum([x, two]);
    const eqn = equation(s, int(5));
    const l = layoutNode(eqn);

    const twoBox = l.boxes.get(two.id)!;
    expect(
      hitTest(l, twoBox.rect.x + twoBox.rect.width / 2, twoBox.rect.y + twoBox.rect.height / 2),
    ).toBe(two.id);

    // A point on the plus sign belongs to the Sum.
    const plus = charGlyph(l, "+");
    expect(hitTest(l, plus.x + 0.01, plus.baseline - 0.01)).toBe(s.id);

    expect(hitTest(l, -1, -1)).toBeUndefined();
    expect(hitTest(l, l.width + 1, 0)).toBeUndefined();
  });
});
