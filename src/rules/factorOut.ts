import {
  eq,
  findById,
  int,
  neg,
  product,
  rebuildNary,
  replaceTermRespectingInvariants,
  sum,
  type Equation,
  type Expr,
  type NodeId,
  type Sum,
} from "../expr.js";
import {
  idSetDiff,
  RulePreconditionViolation,
  survivorMoved,
  type Location,
  type Rule,
  type RuleApplication,
} from "../rule.js";
import { gcd } from "../rational.js";
import { termFromCoeff } from "./splitTerm.js";

export interface FactorOutParams {
  /** A factor INSTANCE inside one term of the Sum at `location`. */
  readonly factorA: NodeId;
  /**
   * An instance inside a different term: structurally equal to factorA, OR
   * an integer literal sharing a common factor (> 1) with factorA's.
   */
  readonly factorB: NodeId;
}

/**
 * The factor positions a term offers for factoring out: the term itself
 * (cofactor 1), a Product's direct factors, a negated term's body (cofactor
 * −1), and a negated product's factors. Shared with move enumeration.
 */
export function factorInstancesOf(term: Expr): readonly Expr[] {
  if (term.kind === "product") return term.children;
  if (term.kind === "neg") {
    if (term.child.kind === "product") return term.child.children;
    return [term.child];
  }
  return [term];
}

/** What remains of `term` when the instance `factorId` is pulled out. */
function cofactorOf(term: Expr, factorId: NodeId): Expr | undefined {
  if (term.id === factorId) return int(1);
  if (term.kind === "product") {
    if (!term.children.some((c) => c.id === factorId)) return undefined;
    return product(term.children.filter((c) => c.id !== factorId));
  }
  if (term.kind === "neg") {
    if (term.child.id === factorId) return int(-1);
    if (term.child.kind === "product" && term.child.children.some((c) => c.id === factorId)) {
      return neg(product(term.child.children.filter((c) => c.id !== factorId)));
    }
  }
  return undefined;
}

/**
 * The instance's integer value with the term's sign folded in: the 3 inside
 * −3x reads as −3. Undefined for non-literal instances.
 */
function signedLiteral(term: Expr, inst: Expr): bigint | undefined {
  if (inst.kind !== "int") return undefined;
  return term.kind === "neg" ? -inst.value : inst.value;
}

/**
 * The term's factors with the instance AND the term's sign removed — the
 * cofactor that pairs with the SIGNED literal (where cofactorOf pairs with
 * the raw instance and keeps the sign). Undefined when the instance is not
 * a direct factor.
 */
function unsignedRest(term: Expr, instId: NodeId): readonly Expr[] | undefined {
  const core = term.kind === "neg" ? term.child : term;
  if (core.id === instId) return [];
  if (core.kind === "product") {
    if (!core.children.some((c) => c.id === instId)) return undefined;
    return core.children.filter((c) => c.id !== instId);
  }
  return undefined;
}

type FactorOutSite = { sum: Sum; termA: Expr; termB: Expr; fa: Expr; fb: Expr } & (
  | { mode: "structural" }
  | { mode: "literal-divisor"; sa: bigint; sb: bigint; divisor: bigint }
);

function resolve(
  tree: Equation,
  location: Location,
  params: FactorOutParams,
): FactorOutSite | undefined {
  const node = findById(tree, location);
  if (node === undefined || node.kind !== "sum") return undefined;
  const owns = (term: Expr, id: NodeId): Expr | undefined =>
    factorInstancesOf(term).find((i) => i.id === id);
  let termA: Expr | undefined;
  let termB: Expr | undefined;
  let fa: Expr | undefined;
  let fb: Expr | undefined;
  for (const t of node.children) {
    const a = owns(t, params.factorA);
    if (a !== undefined) {
      termA = t;
      fa = a;
    }
    const b = owns(t, params.factorB);
    if (b !== undefined) {
      termB = t;
      fb = b;
    }
  }
  if (termA === undefined || termB === undefined || fa === undefined || fb === undefined)
    return undefined;
  if (termA.id === termB.id) return undefined;
  if (eq(fa, fb)) return { mode: "structural", sum: node, termA, termB, fa, fb };
  // Literal factoring. When the grabbed instance, read with its term's sign
  // (the 3 of −3x is −3), divides the other term's literal, pull that SIGNED
  // value out of both — what makes factoring by grouping reach the constant:
  // −3x + 9 ~> (x + −3)·(−3). Otherwise pull the GCF, so the gesture works in
  // BOTH drag directions and when neither literal divides the other:
  // −10 + 2√31 ~> (−5 + √31)·2,  4 + 6y ~> (2 + 3y)·2. A GCF comes out
  // negative only when both terms are negative: −4 − 6y ~> (2 + 3y)·(−2).
  const sa = signedLiteral(termA, fa);
  const sb = signedLiteral(termB, fb);
  if (sa === undefined || sb === undefined || sa === 0n) return undefined;
  const g = gcd(sa < 0n ? -sa : sa, sb < 0n ? -sb : sb);
  if (g === 1n) return undefined; // ±1 factors out as noise
  const divisor = sb % sa === 0n ? sa : sa < 0n && sb < 0n ? -g : g;
  return { mode: "literal-divisor", sum: node, termA, termB, fa, fb, sa, sb, divisor };
}

/** The pulled-out factor and the two cofactors left behind: the result term
 *  is (cofA + cofB)·factor. */
function split(
  r: FactorOutSite,
  params: FactorOutParams,
): { cofA: Expr; cofB: Expr; factor: Expr } {
  if (r.mode === "structural") {
    // (cofA + cofB) · factor — factorA's node carries on by identity.
    return {
      cofA: cofactorOf(r.termA, params.factorA)!,
      cofB: cofactorOf(r.termB, params.factorB)!,
      factor: r.fa,
    };
  }
  // The signed divisor comes out of both terms: cofactors are the
  // sign-stripped rests scaled by sa/divisor and sb/divisor. When the
  // divisor is the grabbed literal itself and positive, it IS factorA's
  // node (identity survives); otherwise it is a fresh canonical literal.
  return {
    cofA: termFromCoeff(r.sa / r.divisor, [...unsignedRest(r.termA, params.factorA)!]),
    cofB: termFromCoeff(r.sb / r.divisor, [...unsignedRest(r.termB, params.factorB)!]),
    factor: r.divisor === r.sa && r.sa > 0n ? r.fa : int(r.divisor),
  };
}

/**
 * What a factor-out would pull out, for captions: the factor, and whether
 * this is COMBINING LIKE TERMS (both cofactors are plain numbers, as in
 * 3x + 2x ~> (3 + 2)·x) rather than factoring (3x² + 10x ~> (3x + 10)·x,
 * −10 + 2√31 ~> (−5 + √31)·2). Undefined when the move doesn't apply.
 */
export function factorOutSummary(
  tree: Equation,
  location: Location,
  params: FactorOutParams,
): { factor: Expr; likeTerms: boolean } | undefined {
  const r = resolve(tree, location, params);
  if (r === undefined) return undefined;
  const { cofA, cofB, factor } = split(r, params);
  const isNumber = (e: Expr): boolean =>
    e.kind === "int" ||
    (e.kind === "neg" && isNumber(e.child)) ||
    (e.kind === "product" && e.children.every(isNumber));
  const factorIsNumber = isNumber(factor);
  return { factor, likeTerms: !factorIsNumber && isNumber(cofA) && isNumber(cofB) };
}

/**
 * Pull a shared factor out of two terms of a Sum — the inverse of
 * distribute, and the move that makes LIKE TERMS work:
 *   3x + 2x ~> (3 + 2)·x        x + 2x ~> (1 + 2)·x        x − 2x ~> (1 + (−2))·x
 * The kept instance (factorA) survives by identity; the dragged-away one
 * merges into it. The cofactor Sum is a real Sum, so combine-integers folds
 * it with the gesture the user already knows.
 */
export const factorOut: Rule<FactorOutParams> = {
  id: "factor-out",
  description: "Factor a shared factor out of two terms of a sum.",

  precondition(judgment, location, params) {
    return resolve(judgment.equation, location, params) !== undefined;
  },

  apply(judgment, location, params): RuleApplication {
    const tree = judgment.equation;
    const r = resolve(tree, location, params);
    if (r === undefined) {
      throw new RulePreconditionViolation(
        this.id,
        "the two ids are not equal factor instances (nor literals sharing a factor) in distinct terms of this sum",
      );
    }
    const { cofA, cofB, factor } = split(r, params);
    const newTerm = product([sum([cofA, cofB]), factor]);
    const children = r.sum.children
      .filter((c) => c.id !== r.termB.id)
      .map((c) => (c.id === r.termA.id ? newTerm : c));
    const rebuilt = rebuildNary(r.sum, children);
    const tree2 = replaceTermRespectingInvariants(tree, r.sum.id, rebuilt);
    const mergeTarget = findById(tree2, factor.id) !== undefined ? factor.id : undefined;
    return {
      equation: tree2,
      emits: [],
      diff: {
        ...idSetDiff(tree, tree2),
        merged:
          mergeTarget === undefined
            ? []
            : [{ sources: [params.factorB], target: mergeTarget }],
        moved: survivorMoved(tree2, rebuilt.id, r.sum.id),
      },
    };
  },
};
