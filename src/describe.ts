/**
 * Plain-language narration of a Move: "Subtract 3 from both sides", "Divide
 * both sides by 2", … A UI shows this beside the drag preview so a silent
 * gesture is also a NAMED algebraic step — the vocabulary a learner carries to
 * the page. Pure (no DOM): maps (judgment, move) to a phrase, deriving any
 * operand text from the tree the move references.
 */
import type { Judgment } from "./assumptions.js";
import { findById, type Expr } from "./expr.js";
import type { Move } from "./moves.js";

const SUPERSCRIPT: Record<string, string> = {
  "0": "⁰", "1": "¹", "2": "²", "3": "³", "4": "⁴",
  "5": "⁵", "6": "⁶", "7": "⁷", "8": "⁸", "9": "⁹",
};

/** Unicode superscript for a run of digits, or undefined if any char isn't one. */
function superscript(digits: string): string | undefined {
  let out = "";
  for (const ch of digits) {
    const s = SUPERSCRIPT[ch];
    if (s === undefined) return undefined;
    out += s;
  }
  return out;
}

/** A factor/base/operand, parenthesized when it wouldn't read unambiguously. */
function atom(e: Expr): string {
  if (e.kind === "sum" || e.kind === "neg") return `(${describeExpr(e)})`;
  return describeExpr(e);
}

/** Implicit-multiplication join: 3x, xy — but 2·3, since 23 would be one number. */
function renderFactorList(list: readonly Expr[]): string {
  if (list.length === 0) return "1";
  let out = atom(list[0]!);
  for (let i = 1; i < list.length; i++) {
    const sep = list[i - 1]!.kind === "int" && list[i]!.kind === "int" ? "·" : "";
    out += sep + atom(list[i]!);
  }
  return out;
}

function wrapList(list: readonly Expr[]): string {
  return list.length > 1 ? `(${renderFactorList(list)})` : renderFactorList(list);
}

/**
 * Compact, human-friendly rendering of an expression for captions: implicit
 * multiplication (3x), superscript powers (x²), √, fraction bars. Distinct
 * from exprToString, whose job is a reparseable round-trip (3 * x, x^2).
 */
export function describeExpr(e: Expr): string {
  switch (e.kind) {
    case "int":
      return e.value.toString();
    case "var":
      return e.name;
    case "neg":
      return `−${atom(e.child)}`;
    case "sqrt":
      return `√${atom(e.child)}`;
    case "pow": {
      const base =
        e.base.kind === "var" || e.base.kind === "int"
          ? describeExpr(e.base)
          : `(${describeExpr(e.base)})`;
      if (e.exp.kind === "int" && e.exp.value >= 0n) {
        const sup = superscript(e.exp.value.toString());
        if (sup !== undefined) return `${base}${sup}`;
      }
      return `${base}^${describeExpr(e.exp)}`;
    }
    case "fraction":
      return `${wrapList(e.num)}/${wrapList(e.den)}`;
    case "sum": {
      let out = "";
      e.children.forEach((c, i) => {
        if (c.kind === "neg") out += (i === 0 ? "−" : " − ") + describeExpr(c.child);
        else out += (i === 0 ? "" : " + ") + describeExpr(c);
      });
      return out;
    }
    case "product":
      return renderFactorList(e.children);
  }
}

/**
 * A plain-language name for a Move, or undefined when there is no caption worth
 * showing. Both-sides moves name their operand from the tree; structural moves
 * get a fixed, learner-facing verb.
 */
export function describeMove(judgment: Judgment, move: Move): string | undefined {
  const params = move.params as Record<string, unknown>;
  const termOf = (id: unknown): Expr | undefined => {
    if (typeof id !== "string") return undefined;
    const n = findById(judgment.equation, id);
    return n !== undefined && n.kind !== "equation" ? n : undefined;
  };
  const exprOf = (v: unknown): Expr | undefined =>
    v !== null && typeof v === "object" && "kind" in (v as object) ? (v as Expr) : undefined;

  switch (move.ruleId) {
    // — moves that change both sides (name the operand) —
    case "move-term-across": {
      const t = termOf(params.termId);
      if (t === undefined) return undefined;
      // Crossing the equals sign flips the term's sign: + term ⇒ subtract it,
      // − term ⇒ add its magnitude.
      return t.kind === "neg"
        ? `Add ${describeExpr(t.child)} to both sides`
        : `Subtract ${describeExpr(t)} from both sides`;
    }
    case "add-to-both-sides": {
      const t = exprOf(params.term);
      if (t === undefined) return undefined;
      return t.kind === "neg"
        ? `Add ${describeExpr(t.child)} to both sides`
        : `Subtract ${describeExpr(t)} from both sides`;
    }
    case "divide-both-sides": {
      const d = exprOf(params.divisor);
      return d ? `Divide both sides by ${describeExpr(d)}` : undefined;
    }
    case "multiply-both-sides": {
      const f = exprOf(params.factor);
      return f ? `Multiply both sides by ${describeExpr(f)}` : undefined;
    }
    case "square-both-sides":
      return "Square both sides";
    case "swap-sides":
      return "Swap the two sides";

    // — disjunctive / branching —
    case "sqrt-both-sides":
      return "Take the square root of both sides (±)";
    case "nth-root-both-sides":
      return "Take the nth root of both sides";
    case "zero-product":
      return "Set each factor equal to zero";
    case "quadratic-formula":
      return "Apply the quadratic formula";

    // — structural rewrites (fixed verbs) —
    case "additive-cancellation":
      return "Cancel";
    case "multiplicative-cancellation":
      return "Cancel the common factor";
    case "combine-integers": {
      const a = termOf(params.termA);
      const b = termOf(params.termB);
      if (a === undefined || b === undefined) return "Add the numbers";
      // Read in sum order so "6 − 1" stays "Add 6 and −1" whichever way it was
      // dragged. Showing the second number's sign is what makes "Add" honest:
      // subtracting is adding the opposite.
      let first = a;
      let second = b;
      const host = findById(judgment.equation, move.location);
      if (host !== undefined && host.kind === "sum") {
        const ia = host.children.findIndex((c) => c.id === a.id);
        const ib = host.children.findIndex((c) => c.id === b.id);
        if (ia !== -1 && ib !== -1 && ib < ia) {
          first = b;
          second = a;
        }
      }
      return `Add ${describeExpr(first)} and ${describeExpr(second)}`;
    }
    case "combine-integer-factors":
      return "Multiply the numbers";
    case "combine-like-factors":
      return "Combine like factors";
    case "combine-fractions":
      return "Add over a common denominator";
    case "factor-out":
      return "Combine like terms";
    case "factor-out-negative":
      return "Factor out −1";
    case "distribute":
      return "Distribute";
    case "distribute-power":
      return "Distribute the exponent";
    case "reduce-integer-fraction":
      return "Reduce the fraction";
    case "quotient-of-powers":
      return "Subtract the exponents";
    case "expand-power":
      return "Expand the power";
    case "power-of-power":
      return "Multiply the exponents";
    case "negative-exponent":
      return "Rewrite the negative exponent";
    case "power-one":
      return "x¹ = x";
    case "power-zero":
      return "x⁰ = 1";
    case "multiply-by-zero":
      return "0 times anything is 0";
    case "cancel-negatives":
      return "Two negatives make a positive";
    case "distribute-negation":
      return "Distribute the negative";
    case "drop-zero-term":
      return "Drop the zero";
    case "drop-one-factor":
      return "Drop the factor of 1";
    case "simplify-sqrt":
      return "Simplify the radical";
    case "split-term":
      return "Split the middle term";

    default:
      return undefined;
  }
}
