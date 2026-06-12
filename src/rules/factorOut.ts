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

export interface FactorOutParams {
  /** A factor INSTANCE inside one term of the Sum at `location`. */
  readonly factorA: NodeId;
  /** A structurally equal instance inside a different term. */
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

function resolve(
  tree: Equation,
  location: Location,
  params: FactorOutParams,
): { sum: Sum; termA: Expr; termB: Expr; fa: Expr; fb: Expr } | undefined {
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
  if (!eq(fa, fb)) return undefined;
  return { sum: node, termA, termB, fa, fb };
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
        "the two ids are not equal factor instances in distinct terms of this sum",
      );
    }
    const cofA = cofactorOf(r.termA, params.factorA)!;
    const cofB = cofactorOf(r.termB, params.factorB)!;
    // (cofA + cofB) · factor — factorA's node carries on by identity.
    const newTerm = product([sum([cofA, cofB]), r.fa]);
    const children = r.sum.children
      .filter((c) => c.id !== r.termB.id)
      .map((c) => (c.id === r.termA.id ? newTerm : c));
    const rebuilt = rebuildNary(r.sum, children);
    const tree2 = replaceTermRespectingInvariants(tree, r.sum.id, rebuilt);
    const mergeTarget = findById(tree2, r.fa.id) !== undefined ? r.fa.id : undefined;
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
