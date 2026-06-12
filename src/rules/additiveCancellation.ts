import {
  eq,
  findById,
  findParent,
  int,
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

export interface AdditiveCancellationParams {
  /** Direct children of the Sum at `location`. */
  readonly termA: NodeId;
  readonly termB: NodeId;
}

/**
 * a and -a are structural negations of each other. Because double negation
 * never survives the smart constructors, it suffices to unwrap one Neg.
 */
function annihilates(a: Expr, b: Expr): boolean {
  if (a.kind === "neg") return eq(a.child, b);
  if (b.kind === "neg") return eq(a, b.child);
  return false;
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
