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
import { termFromCoeff } from "./splitTerm.js";

export interface FactorOutParams {
  /** A factor INSTANCE inside one term of the Sum at `location`. */
  readonly factorA: NodeId;
  /**
   * An instance inside a different term: structurally equal to factorA, OR
   * an integer literal that factorA's signed literal value divides.
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
  | { mode: "literal-divisor"; sa: bigint; sb: bigint }
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
  // Literal-divisor factoring: the grabbed instance, read with its term's
  // sign (the 3 of −3x is −3), divides the other term's literal — pull the
  // SIGNED value out of both. This is what makes factoring by grouping
  // reach the constant: −3x + 9 ~> (x + −3)·(−3).
  const sa = signedLiteral(termA, fa);
  const sb = signedLiteral(termB, fb);
  if (sa === undefined || sb === undefined) return undefined;
  if (sa === 1n || sa === -1n || sa === 0n) return undefined; // ±1 factors out as noise
  if (sb % sa !== 0n) return undefined;
  return { mode: "literal-divisor", sum: node, termA, termB, fa, fb, sa, sb };
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
        "the two ids are not equal factor instances (nor a literal divisor pair) in distinct terms of this sum",
      );
    }
    let cofA: Expr;
    let cofB: Expr;
    let factor: Expr;
    if (r.mode === "structural") {
      cofA = cofactorOf(r.termA, params.factorA)!;
      cofB = cofactorOf(r.termB, params.factorB)!;
      // (cofA + cofB) · factor — factorA's node carries on by identity.
      factor = r.fa;
    } else {
      // The signed literal comes out of both terms whole: cofactors are the
      // sign-stripped rests, termB's scaled by sb/sa. A positive divisor IS
      // factorA's node (identity survives); a negative one is a fresh
      // canonical Neg(Integer).
      cofA = product([...unsignedRest(r.termA, params.factorA)!]);
      cofB = termFromCoeff(r.sb / r.sa, [...unsignedRest(r.termB, params.factorB)!]);
      factor = r.sa > 0n ? r.fa : int(r.sa);
    }
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
