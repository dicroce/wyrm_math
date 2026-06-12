/**
 * Text -> Equation. Pure (no DOM), and the inverse of exprToString up to the
 * structural invariants: the round-trip property
 *   eq(parseEquation(exprToString(e)), e)
 * holds for every generated equation, which pressure-tests printer and
 * parser together.
 *
 * Grammar (recursive descent):
 *   equation := expr REL expr            REL: = < <= >= > ≤ ≥
 *   expr     := term (('+'|'-') term)*           a - b is Sum(a, Neg(b))
 *   term     := factor (('*'|'·'|'/'|juxt) factor)*   left-assoc; / builds Fractions
 *   factor   := '-' factor | power
 *   power    := atom ('^' factor)?               right-assoc; x^-2 works
 *   atom     := INT | VAR | '(' expr ')' | ('sqrt'|'√') radicand
 *
 * Conventions matching the engine:
 *  - Integers only — the engine is exact. Decimals are rejected with a hint
 *    to write a fraction instead.
 *  - Variables are single letters; juxtaposition multiplies (2x, x(x+1)).
 *  - a/b becomes a Fraction whose lists absorb Product parts ((a·b)/c has
 *    num [a, b]) — lists ARE implicit products, the engine's canonical form.
 */
import {
  equation,
  fraction,
  int,
  neg,
  pow,
  product,
  sqrt,
  sum,
  variable,
  type Equation,
  type Expr,
  type Fraction,
  type RelationKind,
} from "./expr.js";

export class ParseError extends Error {
  constructor(
    message: string,
    readonly position: number,
  ) {
    super(message);
    this.name = "ParseError";
  }
}

type Token =
  | { readonly kind: "int"; readonly value: bigint; readonly pos: number }
  | { readonly kind: "var"; readonly name: string; readonly pos: number }
  | { readonly kind: "op"; readonly op: string; readonly pos: number };

const RELATIONS: readonly RelationKind[] = ["=", "<", "≤", ">", "≥"];

function tokenize(src: string): Token[] {
  const out: Token[] = [];
  let i = 0;
  while (i < src.length) {
    const c = src[i]!;
    if (/\s/.test(c)) {
      i++;
      continue;
    }
    if (c >= "0" && c <= "9") {
      const start = i;
      while (i < src.length && src[i]! >= "0" && src[i]! <= "9") i++;
      if (src[i] === ".") {
        throw new ParseError(
          "decimals aren't supported — the engine is exact; write a fraction like 1/2",
          i,
        );
      }
      out.push({ kind: "int", value: BigInt(src.slice(start, i)), pos: start });
      continue;
    }
    if (/[a-zA-Z]/.test(c)) {
      const start = i;
      while (i < src.length && /[a-zA-Z]/.test(src[i]!)) i++;
      const run = src.slice(start, i);
      if (run === "sqrt") {
        out.push({ kind: "op", op: "sqrt", pos: start });
      } else {
        // Single-letter variables; runs multiply by juxtaposition (xy = x·y).
        for (let k = 0; k < run.length; k++) {
          out.push({ kind: "var", name: run[k]!, pos: start + k });
        }
      }
      continue;
    }
    if (c === "√") {
      out.push({ kind: "op", op: "sqrt", pos: i });
      i++;
      continue;
    }
    if (c === "·" || c === "*") {
      out.push({ kind: "op", op: "*", pos: i });
      i++;
      continue;
    }
    if (c === "−" || c === "-") {
      out.push({ kind: "op", op: "-", pos: i });
      i++;
      continue;
    }
    if (c === "<" && src[i + 1] === "=") {
      out.push({ kind: "op", op: "≤", pos: i });
      i += 2;
      continue;
    }
    if (c === ">" && src[i + 1] === "=") {
      out.push({ kind: "op", op: "≥", pos: i });
      i += 2;
      continue;
    }
    if ("+/^()=<>≤≥".includes(c)) {
      out.push({ kind: "op", op: c, pos: i });
      i++;
      continue;
    }
    if (c === "²" || c === "³") {
      throw new ParseError(`write exponents with a caret: x^${c === "²" ? 2 : 3}`, i);
    }
    throw new ParseError(`unexpected character "${c}"`, i);
  }
  return out;
}

class Parser {
  private idx = 0;

  constructor(
    private readonly tokens: Token[],
    private readonly length: number,
  ) {}

  private peek(): Token | undefined {
    return this.tokens[this.idx];
  }

  private isOp(op: string): boolean {
    const t = this.peek();
    return t !== undefined && t.kind === "op" && t.op === op;
  }

  private takeOp(op: string): boolean {
    if (!this.isOp(op)) return false;
    this.idx++;
    return true;
  }

  private fail(message: string): never {
    throw new ParseError(message, this.peek()?.pos ?? this.length);
  }

  parseEquation(): Equation {
    const lhs = this.parseExpr();
    const t = this.peek();
    if (t === undefined || t.kind !== "op" || !RELATIONS.includes(t.op as RelationKind)) {
      this.fail("expected a relation: =, <, ≤, > or ≥");
    }
    this.idx++;
    const rhs = this.parseExpr();
    if (this.peek() !== undefined) this.fail("unexpected input after the equation");
    return equation(lhs, rhs, t.op as RelationKind);
  }

  private parseExpr(): Expr {
    const terms: Expr[] = [this.parseTerm()];
    for (;;) {
      if (this.takeOp("+")) terms.push(this.parseTerm());
      else if (this.takeOp("-")) terms.push(neg(this.parseTerm()));
      else break;
    }
    return terms.length === 1 ? terms[0]! : sum(terms);
  }

  private parseTerm(): Expr {
    let cur = this.parseFactor();
    let dividing: Fraction | null = null; // the fraction this chain is building
    for (;;) {
      if (this.takeOp("*")) {
        cur = product([cur, this.parseFactor()]);
        dividing = null;
      } else if (this.takeOp("/")) {
        // The fraction ctor spreads Product parts into the lists (lists are
        // implicit products). a/b/c chains extend the denominator.
        const den = this.parseFactor();
        cur = dividing =
          dividing !== null
            ? fraction(dividing.num, [...dividing.den, den])
            : fraction([cur], [den]);
      } else if (this.startsAtom()) {
        cur = product([cur, this.parseFactor()]); // juxtaposition: 2x, x(x+1)
        dividing = null;
      } else {
        break;
      }
    }
    return cur;
  }

  private startsAtom(): boolean {
    const t = this.peek();
    if (t === undefined) return false;
    if (t.kind === "int" || t.kind === "var") return true;
    return t.kind === "op" && (t.op === "(" || t.op === "sqrt");
  }

  private parseFactor(): Expr {
    if (this.takeOp("-")) return neg(this.parseFactor());
    return this.parsePower();
  }

  private parsePower(): Expr {
    const base = this.parseAtom();
    if (this.takeOp("^")) return pow(base, this.parseFactor());
    return base;
  }

  private parseAtom(): Expr {
    const t = this.peek();
    if (t === undefined) this.fail("expected a number, variable, or parenthesis");
    if (t.kind === "int") {
      this.idx++;
      return int(t.value);
    }
    if (t.kind === "var") {
      this.idx++;
      return variable(t.name);
    }
    if (t.op === "(") {
      this.idx++;
      const inner = this.parseExpr();
      if (!this.takeOp(")")) this.fail("expected )");
      return inner;
    }
    if (t.op === "sqrt") {
      this.idx++;
      if (this.takeOp("(")) {
        const inner = this.parseExpr();
        if (!this.takeOp(")")) this.fail("expected )");
        return sqrt(inner);
      }
      return sqrt(this.parseAtom()); // √9, √x
    }
    this.fail(`unexpected "${t.op}"`);
  }
}

/** Parse user input into an Equation. Throws ParseError with a position. */
export function parseEquation(src: string): Equation {
  if (src.trim() === "") throw new ParseError("type an equation, e.g. 2x + 3 = 11", 0);
  return new Parser(tokenize(src), src.length).parseEquation();
}
