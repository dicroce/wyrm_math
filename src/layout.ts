/**
 * Layout geometry: a PURE function from expression trees to positioned,
 * id-keyed boxes and glyphs. No DOM, no font measurement — static metric
 * tables only. The UI package projects this onto SVG; hit testing is a
 * geometry query answered here.
 *
 * Design rules (the display decisions the AST deliberately does not encode):
 *  - Sum(a, Neg(b)) renders as binary subtraction "a − b". The minus sign is
 *    owned by the NEG node (so dragging the signed term grabs sign and all);
 *    the Sum only contributes "+" separators and spacing.
 *  - Negative literals (canonically Neg(Integer)) render as "−3".
 *  - Parentheses are owned by the PARENT that requires them: a Sum factor in
 *    a Product, a Sum under Neg, compound Pow bases, Neg factors.
 *  - Products juxtapose ("3x"); a "·" appears only where juxtaposition would
 *    glue digits to digits.
 *  - Fraction numerator/denominator lists render as centered rows above and
 *    below the bar; empty lists render an implicit "1".
 *  - Pow exponents are raised and scaled by SUP_SCALE.
 *
 * Geometry invariants (property-tested):
 *  - every tree node has exactly one box; child boxes nest inside parents;
 *  - sibling boxes never overlap;
 *  - glyphs stay inside their owner's box;
 *  - a subtree's internal geometry is context-independent up to translation
 *    and uniform scale (what makes id-keyed animation work);
 *  - hitTest returns the deepest box containing a point.
 */
import type { Expr, Node, NodeId } from "./expr.js";

// ---------------------------------------------------------------------------
// Metrics (in em units at scale 1; every value scales linearly)
// ---------------------------------------------------------------------------

export const METRICS = {
  ASCENT: 0.78, // glyph top above baseline
  DESCENT: 0.22, // glyph bottom below baseline
  AXIS: 0.26, // math axis (fraction bar center) above baseline
  DIGIT_W: 0.54,
  LETTER_W: 0.54,
  SIGN_W: 0.58, // + − =
  DOT_W: 0.3, // ·
  PAREN_W: 0.34,
  OP_PAD: 0.18, // space on each side of +/− in sums
  EQ_PAD: 0.26, // space on each side of =
  MUL_GAP: 0.07, // juxtaposition gap between product factors
  NEG_GAP: 0.05, // gap between a minus sign and its operand
  EXP_GAP: 0.04, // gap between a base and its superscript
  SUP_SCALE: 0.7,
  SUP_RAISE: 0.42, // superscript baseline raise
  FRAC_GAP: 0.12, // gap between bar and numerator/denominator
  FRAC_PAD: 0.08, // horizontal bar overhang
  BAR_TH: 0.06, // bar thickness
  RADICAL_W: 0.5, // √ glyph
  RAD_GAP: 0.1, // clearance between the radicand and the vinculum
} as const;

const M = METRICS;

function charWidth(char: string): number {
  if (char >= "0" && char <= "9") return M.DIGIT_W;
  if (char === "(" || char === ")") return M.PAREN_W;
  if (char === "·") return M.DOT_W; // ·
  if (char === "√") return M.RADICAL_W;
  if ("+−=<>≤≥".includes(char)) return M.SIGN_W;
  return M.LETTER_W;
}

// ---------------------------------------------------------------------------
// Output types
// ---------------------------------------------------------------------------

export interface LayoutRect {
  readonly x: number;
  readonly y: number;
  readonly width: number;
  readonly height: number;
}

export interface LayoutBox {
  readonly nodeId: NodeId;
  readonly kind: Node["kind"];
  readonly rect: LayoutRect;
  /** Absolute y of this node's baseline. */
  readonly baseline: number;
  /** Font scale relative to the root (1 = base size). */
  readonly scale: number;
  /** Tree depth from the layout root (root = 0); hitTest picks the max. */
  readonly depth: number;
}

export type PlacedGlyph =
  | {
      readonly kind: "char";
      readonly char: string;
      readonly x: number;
      /** Absolute y of the glyph baseline. */
      readonly baseline: number;
      readonly scale: number;
      readonly width: number;
      readonly ascent: number;
      readonly descent: number;
      readonly owner: NodeId;
    }
  | {
      readonly kind: "bar";
      readonly x: number;
      /** Absolute y of the bar's vertical center. */
      readonly y: number;
      readonly width: number;
      readonly thickness: number;
      readonly owner: NodeId;
    };

export interface Layout {
  readonly rootId: NodeId;
  readonly width: number;
  readonly height: number;
  readonly boxes: ReadonlyMap<NodeId, LayoutBox>;
  readonly glyphs: readonly PlacedGlyph[];
}

// ---------------------------------------------------------------------------
// Relative layout (phase 1)
// ---------------------------------------------------------------------------

interface RGlyph {
  readonly kind: "char" | "bar";
  readonly char: string; // "" for bars
  readonly x: number; // from box left
  readonly dy: number; // baseline (chars) / center (bars) relative to box baseline
  readonly scale: number;
  readonly ascent: number; // above its own baseline/center line
  readonly descent: number;
  readonly width: number; // used for bars and containment
}

interface RBox {
  readonly node: Node;
  readonly scale: number;
  readonly width: number;
  readonly ascent: number;
  readonly descent: number;
  readonly glyphs: readonly RGlyph[];
  readonly children: readonly { box: RBox; dx: number; dy: number }[];
}

type Part =
  | { kind: "box"; box: RBox; dy?: number }
  | { kind: "glyph"; char: string; scale: number; dy?: number; ascent?: number; descent?: number }
  | { kind: "space"; width: number };

/** Assemble parts left-to-right on a shared baseline. */
function row(parts: readonly Part[]): {
  width: number;
  ascent: number;
  descent: number;
  glyphs: RGlyph[];
  children: { box: RBox; dx: number; dy: number }[];
} {
  let x = 0;
  let ascent = 0;
  let descent = 0;
  const glyphs: RGlyph[] = [];
  const children: { box: RBox; dx: number; dy: number }[] = [];
  for (const p of parts) {
    if (p.kind === "space") {
      x += p.width;
    } else if (p.kind === "glyph") {
      const dy = p.dy ?? 0;
      const a = p.ascent ?? M.ASCENT * p.scale;
      const d = p.descent ?? M.DESCENT * p.scale;
      const width = charWidth(p.char) * p.scale;
      glyphs.push({ kind: "char", char: p.char, x, dy, scale: p.scale, ascent: a, descent: d, width });
      ascent = Math.max(ascent, a - dy);
      descent = Math.max(descent, d + dy);
      x += width;
    } else {
      const dy = p.dy ?? 0;
      children.push({ box: p.box, dx: x, dy });
      ascent = Math.max(ascent, p.box.ascent - dy);
      descent = Math.max(descent, p.box.descent + dy);
      x += p.box.width;
    }
  }
  return { width: x, ascent, descent, glyphs, children };
}

/** Parenthesis parts stretched to cover `inner`, owned by the caller's node. */
function parens(inner: RBox, scale: number): { open: Part; close: Part } {
  const innerH = inner.ascent + inner.descent;
  const pScale = Math.max(scale, innerH / (M.ASCENT + M.DESCENT));
  // Center the paren on the inner content's vertical center.
  const contentCenter = (inner.descent - inner.ascent) / 2;
  const ownCenter = (M.DESCENT * pScale - M.ASCENT * pScale) / 2;
  const dy = contentCenter - ownCenter;
  const mk = (char: string): Part => ({
    kind: "glyph",
    char,
    scale: pScale,
    dy,
    ascent: M.ASCENT * pScale,
    descent: M.DESCENT * pScale,
  });
  return { open: mk("("), close: mk(")") };
}

/** Does this expression's leftmost rendered glyph belong to a number? */
function startsWithDigit(e: Expr): boolean {
  switch (e.kind) {
    case "int":
      return true;
    case "pow":
      return startsWithDigit(e.base);
    default:
      return false;
  }
}

function needsParensAsFactor(e: Expr): boolean {
  return e.kind === "sum" || e.kind === "neg";
}

function needsParensAsPowBase(e: Expr): boolean {
  return e.kind !== "int" && e.kind !== "var";
}

/** Product-style row over a factor list (used by Product and Fraction lists). */
function factorParts(factors: readonly Expr[], scale: number): Part[] {
  const parts: Part[] = [];
  factors.forEach((f, i) => {
    const box = lay(f, scale);
    const wrapped = needsParensAsFactor(f);
    if (i > 0) {
      const prev = factors[i - 1]!;
      const dotNeeded = !wrapped && !needsParensAsFactor(prev) && startsWithDigit(f);
      if (dotNeeded) {
        parts.push({ kind: "space", width: M.MUL_GAP * scale });
        parts.push({ kind: "glyph", char: "·", scale });
        parts.push({ kind: "space", width: M.MUL_GAP * scale });
      } else {
        parts.push({ kind: "space", width: M.MUL_GAP * scale });
      }
    }
    if (wrapped) {
      const { open, close } = parens(box, scale);
      parts.push(open, { kind: "box", box }, close);
    } else {
      parts.push({ kind: "box", box });
    }
  });
  return parts;
}

function lay(node: Node, scale: number): RBox {
  switch (node.kind) {
    case "int": {
      const parts: Part[] = [...`${node.value}`].map((char) => ({ kind: "glyph", char, scale }));
      return { node, scale, ...row(parts) };
    }
    case "var": {
      return { node, scale, ...row([{ kind: "glyph", char: node.name, scale }]) };
    }
    case "neg": {
      const child = lay(node.child, scale);
      const parts: Part[] = [
        { kind: "glyph", char: "−", scale },
        { kind: "space", width: M.NEG_GAP * scale },
      ];
      if (node.child.kind === "sum") {
        const { open, close } = parens(child, scale);
        parts.push(open, { kind: "box", box: child }, close);
      } else {
        parts.push({ kind: "box", box: child });
      }
      return { node, scale, ...row(parts) };
    }
    case "sum": {
      const parts: Part[] = [];
      node.children.forEach((term, i) => {
        const box = lay(term, scale);
        if (i > 0) {
          if (term.kind === "neg") {
            // Binary subtraction: the Neg's own minus is the operator.
            parts.push({ kind: "space", width: M.OP_PAD * scale });
          } else {
            parts.push(
              { kind: "space", width: M.OP_PAD * scale },
              { kind: "glyph", char: "+", scale },
              { kind: "space", width: M.OP_PAD * scale },
            );
          }
        }
        parts.push({ kind: "box", box });
      });
      return { node, scale, ...row(parts) };
    }
    case "product": {
      return { node, scale, ...row(factorParts(node.children, scale)) };
    }
    case "pow": {
      const base = lay(node.base, scale);
      const exp = lay(node.exp, scale * M.SUP_SCALE);
      const expDy = -M.SUP_RAISE * scale;
      const parts: Part[] = [];
      if (needsParensAsPowBase(node.base)) {
        const { open, close } = parens(base, scale);
        parts.push(open, { kind: "box", box: base }, close);
      } else {
        parts.push({ kind: "box", box: base });
      }
      parts.push({ kind: "space", width: M.EXP_GAP * scale });
      parts.push({ kind: "box", box: exp, dy: expDy });
      return { node, scale, ...row(parts) };
    }
    case "fraction": {
      const num = row(
        node.num.length > 0
          ? factorParts(node.num, scale)
          : [{ kind: "glyph", char: "1", scale }],
      );
      const den = row(
        node.den.length > 0
          ? factorParts(node.den, scale)
          : [{ kind: "glyph", char: "1", scale }],
      );
      const width = Math.max(num.width, den.width) + 2 * M.FRAC_PAD * scale;
      const barY = -M.AXIS * scale;
      const barTop = barY - (M.BAR_TH * scale) / 2;
      const barBot = barY + (M.BAR_TH * scale) / 2;
      const numDy = barTop - M.FRAC_GAP * scale - num.descent;
      const denDy = barBot + M.FRAC_GAP * scale + den.ascent;
      const numX = (width - num.width) / 2;
      const denX = (width - den.width) / 2;
      const shift = (r: ReturnType<typeof row>, dx: number, dy: number) => ({
        glyphs: r.glyphs.map((g) => ({ ...g, x: g.x + dx, dy: g.dy + dy })),
        children: r.children.map((c) => ({ ...c, dx: c.dx + dx, dy: c.dy + dy })),
      });
      const numS = shift(num, numX, numDy);
      const denS = shift(den, denX, denDy);
      const bar: RGlyph = {
        kind: "bar",
        char: "",
        x: 0,
        dy: barY,
        scale,
        ascent: (M.BAR_TH * scale) / 2,
        descent: (M.BAR_TH * scale) / 2,
        width,
      };
      return {
        node,
        scale,
        width,
        ascent: -(numDy - num.ascent),
        descent: denDy + den.descent,
        glyphs: [...numS.glyphs, bar, ...denS.glyphs],
        children: [...numS.children, ...denS.children],
      };
    }
    case "sqrt": {
      const child = lay(node.child, scale);
      const th = M.BAR_TH * scale;
      const gap = M.RAD_GAP * scale;
      const coverAscent = child.ascent + gap + th; // vinculum sits this high
      // The radical sign stretches to the covered height, like a paren.
      const radScale = Math.max(scale, (coverAscent + child.descent) / (M.ASCENT + M.DESCENT));
      const radW = M.RADICAL_W * radScale;
      const contentCenter = (child.descent - coverAscent) / 2;
      const radDy = contentCenter + ((M.ASCENT - M.DESCENT) / 2) * radScale;
      const radical: RGlyph = {
        kind: "char",
        char: "√",
        x: 0,
        dy: radDy,
        scale: radScale,
        ascent: M.ASCENT * radScale,
        descent: M.DESCENT * radScale,
        width: radW,
      };
      const bar: RGlyph = {
        kind: "bar",
        char: "",
        x: radW,
        dy: -(coverAscent - th / 2),
        scale,
        ascent: th / 2,
        descent: th / 2,
        width: child.width,
      };
      return {
        node,
        scale,
        width: radW + child.width,
        ascent: Math.max(coverAscent, M.ASCENT * radScale - radDy),
        descent: Math.max(child.descent, M.DESCENT * radScale + radDy),
        glyphs: [radical, bar],
        children: [{ box: child, dx: radW, dy: 0 }],
      };
    }
    case "equation": {
      const lhs = lay(node.lhs, scale);
      const rhs = lay(node.rhs, scale);
      return {
        node,
        scale,
        ...row([
          { kind: "box", box: lhs },
          { kind: "space", width: M.EQ_PAD * scale },
          { kind: "glyph", char: node.relation, scale },
          { kind: "space", width: M.EQ_PAD * scale },
          { kind: "box", box: rhs },
        ]),
      };
    }
  }
}

// ---------------------------------------------------------------------------
// Absolute placement (phase 2)
// ---------------------------------------------------------------------------

export function layoutNode(root: Node): Layout {
  const r = lay(root, 1);
  const boxes = new Map<NodeId, LayoutBox>();
  const glyphs: PlacedGlyph[] = [];

  function emit(box: RBox, x: number, baseline: number, depth: number): void {
    boxes.set(box.node.id, {
      nodeId: box.node.id,
      kind: box.node.kind,
      rect: { x, y: baseline - box.ascent, width: box.width, height: box.ascent + box.descent },
      baseline,
      scale: box.scale,
      depth,
    });
    for (const g of box.glyphs) {
      if (g.kind === "bar") {
        glyphs.push({
          kind: "bar",
          x: x + g.x,
          y: baseline + g.dy,
          width: g.width,
          thickness: g.ascent + g.descent,
          owner: box.node.id,
        });
      } else {
        glyphs.push({
          kind: "char",
          char: g.char,
          x: x + g.x,
          baseline: baseline + g.dy,
          scale: g.scale,
          width: g.width,
          ascent: g.ascent,
          descent: g.descent,
          owner: box.node.id,
        });
      }
    }
    for (const c of box.children) {
      emit(c.box, x + c.dx, baseline + c.dy, depth + 1);
    }
  }

  emit(r, 0, r.ascent, 0);
  return {
    rootId: root.id,
    width: r.width,
    height: r.ascent + r.descent,
    boxes,
    glyphs,
  };
}

// ---------------------------------------------------------------------------
// Hit testing
// ---------------------------------------------------------------------------

function contains(rect: LayoutRect, x: number, y: number): boolean {
  return x >= rect.x && x <= rect.x + rect.width && y >= rect.y && y <= rect.y + rect.height;
}

/**
 * The deepest node whose box contains the point, or undefined. Sibling boxes
 * are disjoint (property-tested), so "deepest containing" is unambiguous: the
 * containing boxes always form a single ancestor chain.
 */
export function hitTest(layout: Layout, x: number, y: number): NodeId | undefined {
  let best: LayoutBox | undefined;
  for (const box of layout.boxes.values()) {
    if (!contains(box.rect, x, y)) continue;
    if (best === undefined || box.depth > best.depth) best = box;
  }
  return best?.nodeId;
}

/** Convenience: the center of a node's box (a natural anchor for gestures). */
export function boxCenter(layout: Layout, id: NodeId): { x: number; y: number } {
  const box = layout.boxes.get(id);
  if (box === undefined) throw new Error(`no layout box for node ${id}`);
  return { x: box.rect.x + box.rect.width / 2, y: box.rect.y + box.rect.height / 2 };
}
