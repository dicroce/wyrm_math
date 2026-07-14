import {
  findById,
  int,
  product,
  replaceTermRespectingInvariants,
  type Equation,
  type Expr,
  type Fraction,
  type NodeId,
} from "../expr.js";
import { gcd } from "../rational.js";
import {
  idSetDiff,
  RulePreconditionViolation,
  type Location,
  type Rule,
  type RuleApplication,
} from "../rule.js";
import { literalValue } from "./combineIntegers.js";

export interface ReduceIntegerFractionParams {
  /** An integer literal element of the Fraction's numerator list. */
  readonly numTermId: NodeId;
  /** An integer literal element of its denominator list. */
  readonly denTermId: NodeId;
}

function resolve(
  tree: Equation,
  location: Location,
  params: ReduceIntegerFractionParams,
): { frac: Fraction; va: bigint; vb: bigint; g: bigint } | undefined {
  const node = findById(tree, location);
  if (node === undefined || node.kind !== "fraction") return undefined;
  const numTerm = node.num.find((c) => c.id === params.numTermId);
  const denTerm = node.den.find((c) => c.id === params.denTermId);
  if (numTerm === undefined || denTerm === undefined) return undefined;
  const va = literalValue(numTerm);
  const vb = literalValue(denTerm);
  if (va === undefined || vb === undefined || vb === 0n) return undefined;
  const g = gcd(va < 0n ? -va : va, vb < 0n ? -vb : vb);
  // Reduce is a genuine no-op ONLY when there's no common factor AND the
  // denominator is already a positive non-unit (5/3 stays put). Otherwise there
  // is still work to do even at g = 1: a ±1 denominator collapses the bar
  // (6/1 → 6, −6/−1 → 6) and a negative denominator has its sign canonicalized
  // into the numerator (6/−3 → −2). Gating on g > 1 alone stranded all of those.
  if (g <= 1n && vb > 1n) return undefined;
  return { frac: node, va, vb, g };
}

/**
 * Exact arithmetic across the bar: divide an integer numerator element and
 * an integer denominator element by their gcd.
 *   6/3 ~> 2        6/4 ~> 3/2        6/(3x) ~> 2/x        3/(3x) ~> 1/x
 * Literals that reduce to 1 disappear (an empty list means 1; an empty
 * denominator drops the bar entirely). The denominator is a known nonzero
 * literal and the reduction is exact, so — unlike cancellation — this emits
 * NO assumption.
 */
export const reduceIntegerFraction: Rule<ReduceIntegerFractionParams> = {
  id: "reduce-integer-fraction",
  description: "Reduce an integer over an integer across the fraction bar by their gcd.",

  precondition(judgment, location, params) {
    return resolve(judgment.equation, location, params) !== undefined;
  },

  apply(judgment, location, params): RuleApplication {
    const tree = judgment.equation;
    const r = resolve(tree, location, params);
    if (r === undefined) {
      throw new RulePreconditionViolation(
        this.id,
        "terms are not integer literals with a common factor",
      );
    }
    let a2 = r.va / r.g;
    let b2 = r.vb / r.g;
    if (b2 < 0n) {
      // Canonicalize the sign into the numerator: 6/(−3) reduces to −2, not 2/(−1).
      a2 = -a2;
      b2 = -b2;
    }
    const newNumLit = a2 === 1n ? undefined : int(a2);
    const newDenLit = b2 === 1n ? undefined : int(b2);
    const num = r.frac.num.flatMap((c) =>
      c.id === params.numTermId ? (newNumLit === undefined ? [] : [newNumLit]) : [c],
    );
    const den = r.frac.den.flatMap((c) =>
      c.id === params.denTermId ? (newDenLit === undefined ? [] : [newDenLit]) : [c],
    );
    const result: Expr = den.length === 0 ? product(num) : { ...r.frac, num, den };
    const tree2 = replaceTermRespectingInvariants(tree, r.frac.id, result);
    const mergeTarget = [newNumLit?.id, r.frac.id, result.id].find(
      (id) => id !== undefined && findById(tree2, id) !== undefined,
    );
    return {
      equation: tree2,
      emits: [],
      diff: {
        ...idSetDiff(tree, tree2),
        merged:
          mergeTarget === undefined
            ? []
            : [{ sources: [params.numTermId, params.denTermId], target: mergeTarget }],
        moved: [],
      },
    };
  },
};
