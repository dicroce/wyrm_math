import {
  eq,
  findById,
  findParent,
  int,
  product,
  rebuildNary,
  replaceTermRespectingInvariants,
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
import { literalValue } from "./combineIntegers.js";

export interface AdditiveCancellationParams {
  /** Direct children of the Sum at `location`. */
  readonly termA: NodeId;
  readonly termB: NodeId;
}

/**
 * Integer coefficient and the remaining (non-literal) body of a term:
 *   2x → (2, x);  (−2)x → (−2, x);  −2x → (−2, x);  x → (1, x);  5 → (5, 1).
 */
function splitCoeff(t: Expr): { coeff: bigint; body: Expr } {
  if (t.kind === "neg") {
    const s = splitCoeff(t.child);
    return { coeff: -s.coeff, body: s.body };
  }
  const lit = literalValue(t);
  if (lit !== undefined) return { coeff: lit, body: int(1) };
  if (t.kind === "product") {
    let coeff = 1n;
    const rest: Expr[] = [];
    for (const f of t.children) {
      const v = literalValue(f);
      if (v !== undefined) coeff *= v;
      else rest.push(f);
    }
    return { coeff, body: rest.length === 1 ? rest[0]! : product(rest) };
  }
  return { coeff: 1n, body: t };
}

/**
 * a and b annihilate when they are like terms with OPPOSITE coefficients —
 * c·body and (−c)·body — so a + b = 0. This subsumes the structural a / −a case
 * and also catches 2x + (−2)x, where (−2)x is a product with a negative
 * coefficient (not a Neg node, so it wouldn't match structurally).
 */
function annihilates(a: Expr, b: Expr): boolean {
  const sa = splitCoeff(a);
  const sb = splitCoeff(b);
  return sa.coeff === -sb.coeff && eq(sa.body, sb.body);
}

function resolve(
  tree: Equation,
  location: Location,
  params: AdditiveCancellationParams,
): { sum: Sum; termA: Expr; termB: Expr } | undefined {
  const node = findById(tree, location);
  if (node === undefined || node.kind !== "sum") return undefined;
  if (params.termA === params.termB) return undefined;
  const termA = node.children.find((c) => c.id === params.termA);
  const termB = node.children.find((c) => c.id === params.termB);
  if (termA === undefined || termB === undefined) return undefined;
  return { sum: node, termA, termB };
}

/**
 * Within one Sum, a term and its negation annihilate:
 *   x + a + (-a)  ~>  x        a + (-a)  ~>  0
 */
export const additiveCancellation: Rule<AdditiveCancellationParams> = {
  id: "additive-cancellation",
  description: "A term and its negation in the same sum cancel out.",

  precondition(judgment, location, params) {
    const r = resolve(judgment.equation, location, params);
    return r !== undefined && annihilates(r.termA, r.termB);
  },

  apply(judgment, location, params): RuleApplication {
    const tree = judgment.equation;
    const r = resolve(tree, location, params);
    if (r === undefined || !annihilates(r.termA, r.termB)) {
      throw new RulePreconditionViolation(this.id, "terms do not annihilate");
    }
    const { sum: target } = r;
    const remaining = target.children.filter(
      (c) => c.id !== params.termA && c.id !== params.termB,
    );

    if (remaining.length === 0) {
      // The whole sum annihilates: the pair merges into a fresh 0.
      const zero = int(0);
      const tree2 = replaceTermRespectingInvariants(tree, target.id, zero);
      return {
        equation: tree2,
        emits: [],
        diff: {
          ...idSetDiff(tree, tree2),
          merged: [{ sources: [params.termA, params.termB], target: zero.id }],
          moved: [],
        },
      };
    }

    const rebuilt = rebuildNary(target, remaining);
    const tree2 = replaceTermRespectingInvariants(tree, target.id, rebuilt);
    return {
      equation: tree2,
      emits: [],
      diff: {
        ...idSetDiff(tree, tree2),
        merged: [],
        moved: survivorMoved(tree2, rebuilt.id, target.id),
      },
    };
  },
};
