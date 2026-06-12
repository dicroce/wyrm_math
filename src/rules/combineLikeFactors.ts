import {
  eq,
  findById,
  int,
  pow,
  rebuildNary,
  replaceTermRespectingInvariants,
  type Equation,
  type Expr,
  type NodeId,
  type Product,
} from "../expr.js";
import {
  idSetDiff,
  RulePreconditionViolation,
  survivorMoved,
  type Location,
  type Rule,
  type RuleApplication,
} from "../rule.js";

export interface CombineLikeFactorsParams {
  /** Direct children of the Product at `location` with structurally equal bases. */
  readonly termA: NodeId;
  readonly termB: NodeId;
}

/**
 * A factor's (base, literal exponent). A bare factor is base^1; a Pow with a
 * literal Integer exponent reads it off. Symbolic exponents return undefined:
 * x^a · x^b ~> x^(a+b) can GAIN solutions when exponents may be negative
 * (x²·x⁻¹ is undefined at 0, x¹ is not), so the symbolic form needs the
 * Extension machinery — deferred until negative exponents exist at all.
 * Literal exponents are non-negative by the AST invariant, where the law
 * holds everywhere (including 0^0 = 1 under our exact evaluator).
 */
function baseAndExp(e: Expr): { base: Expr; exp: bigint } | undefined {
  if (e.kind !== "pow") return { base: e, exp: 1n };
  if (e.exp.kind !== "int") return undefined;
  return { base: e.base, exp: e.exp.value };
}

function resolve(
  tree: Equation,
  location: Location,
  params: CombineLikeFactorsParams,
): { product: Product; termA: Expr; a: { base: Expr; exp: bigint }; b: { base: Expr; exp: bigint } } | undefined {
  const node = findById(tree, location);
  if (node === undefined || node.kind !== "product") return undefined;
  if (params.termA === params.termB) return undefined;
  const termA = node.children.find((c) => c.id === params.termA);
  const termB = node.children.find((c) => c.id === params.termB);
  if (termA === undefined || termB === undefined) return undefined;
  const a = baseAndExp(termA);
  const b = baseAndExp(termB);
  if (a === undefined || b === undefined) return undefined;
  if (!eq(a.base, b.base)) return undefined;
  return { product: node, termA, a, b };
}

/**
 * Two factors with the same base merge by adding exponents — the inverse of
 * expand-power, one pair at a time:
 *   x·x ~> x²        x²·x³ ~> x⁵        x⁰·x ~> x
 * termA's base survives by identity (and termA's Pow node too, when it has
 * one); termB folds into it.
 */
export const combineLikeFactors: Rule<CombineLikeFactorsParams> = {
  id: "combine-like-factors",
  description: "Merge two equal-based factors of a product by adding their exponents.",

  precondition(judgment, location, params) {
    return resolve(judgment.equation, location, params) !== undefined;
  },

  apply(judgment, location, params): RuleApplication {
    const tree = judgment.equation;
    const r = resolve(tree, location, params);
    if (r === undefined) {
      throw new RulePreconditionViolation(
        this.id,
        "factors do not share a base with literal exponents",
      );
    }
    const total = r.a.exp + r.b.exp;
    const result: Expr =
      total === 1n
        ? r.a.base // x^0 · x ~> bare x
        : r.termA.kind === "pow"
          ? { ...r.termA, exp: int(total) }
          : pow(r.a.base, int(total));
    const children = r.product.children
      .filter((c) => c.id !== params.termB)
      .map((c) => (c.id === params.termA ? result : c));
    const rebuilt = rebuildNary(r.product, children);
    const tree2 = replaceTermRespectingInvariants(tree, r.product.id, rebuilt);
    // termA's base lives on inside the result, so only termB (plus termA's
    // replaced exponent literal, if any) merges away.
    const sources = [
      params.termB,
      ...(r.termA.kind === "pow" ? [r.termA.exp.id] : []),
    ];
    // Fallbacks for swallowed results: a Neg result under a Neg parent keeps
    // only its child; failing that, the rebuilt product or nothing.
    const mergeTarget = [
      result.id,
      result.kind === "neg" ? result.child.id : undefined,
      r.product.id,
    ].find((id) => id !== undefined && findById(tree2, id) !== undefined);
    return {
      equation: tree2,
      emits: [],
      diff: {
        ...idSetDiff(tree, tree2),
        merged: mergeTarget === undefined ? [] : [{ sources, target: mergeTarget }],
        moved: survivorMoved(tree2, rebuilt.id, r.product.id),
      },
    };
  },
};
