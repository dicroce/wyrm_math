import { pinsEnv, restrictionStatus } from "../assumptions.js";
import {
  eq,
  findById,
  int,
  pow,
  product,
  replaceTermRespectingInvariants,
  type Equation,
  type Expr,
  type Fraction,
  type NodeId,
} from "../expr.js";
import { Rational } from "../rational.js";
import {
  idSetDiff,
  RulePreconditionViolation,
  type Location,
  type Rule,
  type RuleApplication,
} from "../rule.js";

export interface QuotientOfPowersParams {
  /** An element of the Fraction's numerator list (bare base or literal power). */
  readonly numTermId: NodeId;
  /** A like-based element of its denominator list. */
  readonly denTermId: NodeId;
}

/** Bare factors count as base^1; literal powers read off; symbolic exponents don't qualify. */
function litBaseExp(e: Expr): { base: Expr; exp: bigint } | undefined {
  if (e.kind !== "pow") return { base: e, exp: 1n };
  if (e.exp.kind !== "int") return undefined;
  return { base: e.base, exp: e.exp.value };
}

interface Resolved {
  readonly frac: Fraction;
  readonly numTerm: Expr;
  readonly denTerm: Expr;
  readonly base: Expr;
  readonly diffExp: bigint; // numerator exponent minus denominator exponent
}

function resolve(
  tree: Equation,
  location: Location,
  params: QuotientOfPowersParams,
): Resolved | undefined {
  const node = findById(tree, location);
  if (node === undefined || node.kind !== "fraction") return undefined;
  const numTerm = node.num.find((c) => c.id === params.numTermId);
  const denTerm = node.den.find((c) => c.id === params.denTermId);
  if (numTerm === undefined || denTerm === undefined) return undefined;
  const a = litBaseExp(numTerm);
  const b = litBaseExp(denTerm);
  if (a === undefined || b === undefined) return undefined;
  if (!eq(a.base, b.base)) return undefined;
  return { frac: node, numTerm, denTerm, base: a.base, diffExp: a.exp - b.exp };
}

/** base^k with id reuse: k = 1 unwraps to the surviving base node. */
function reduced(term: Expr, base: Expr, k: bigint): Expr {
  if (k === 1n) return base;
  if (term.kind === "pow") return { ...term, exp: int(k) };
  return pow(base, int(k));
}

/**
 * The quotient-of-powers law across the bar — like-based powers reduce by
 * subtracting literal exponents:
 *   x³/x² ~> x        x²/x³ ~> 1/x        x/x² ~> 1/x        2³/2² ~> 2
 * A solution-LOSING move (the original is undefined wherever the base is 0),
 * so it emits Restriction(base ≠ 0), discharged on the spot for constants.
 */
export const quotientOfPowers: Rule<QuotientOfPowersParams> = {
  id: "quotient-of-powers",
  description: "Reduce like-based powers across the fraction bar (emits base ≠ 0).",

  precondition(judgment, location, params) {
    const r = resolve(judgment.equation, location, params);
    if (r === undefined) return false;
    const status = restrictionStatus(
      { expr: r.base, value: Rational.zero },
      pinsEnv(judgment.assumptions),
    );
    return status !== "fails";
  },

  apply(judgment, location, params): RuleApplication {
    if (!this.precondition(judgment, location, params)) {
      throw new RulePreconditionViolation(
        this.id,
        "elements are not like-based literal powers (or the base is decidably zero)",
      );
    }
    const tree = judgment.equation;
    const r = resolve(tree, location, params)!;
    const d = r.diffExp;
    // A k=1 reduction can leave a bare Product base; spread it into the list
    // (fraction lists never hold direct Products).
    const spread = (l: Expr[]): Expr[] =>
      l.flatMap((c) => (c.kind === "product" ? c.children : [c]));
    const num = spread(
      d > 0n
        ? r.frac.num.map((c) => (c.id === params.numTermId ? reduced(r.numTerm, r.base, d) : c))
        : r.frac.num.filter((c) => c.id !== params.numTermId),
    );
    const den = spread(
      d < 0n
        ? r.frac.den.map((c) => (c.id === params.denTermId ? reduced(r.denTerm, r.base, -d) : c))
        : r.frac.den.filter((c) => c.id !== params.denTermId),
    );
    const result: Expr = den.length === 0 ? product(num) : { ...r.frac, num, den };
    const tree2 = replaceTermRespectingInvariants(tree, r.frac.id, result);
    const consumed = d >= 0n ? params.denTermId : params.numTermId;
    const mergeTarget = [
      d > 0n ? params.numTermId : d < 0n ? params.denTermId : undefined,
      r.base.id,
      r.frac.id,
      result.id,
    ].find((id) => id !== undefined && findById(tree2, id) !== undefined);
    return {
      equation: tree2,
      emits: [
        { kind: "restriction", expr: r.base, relation: "≠", value: Rational.zero },
      ],
      diff: {
        ...idSetDiff(tree, tree2),
        merged:
          mergeTarget === undefined ? [] : [{ sources: [consumed], target: mergeTarget }],
        moved: [],
      },
    };
  },
};
