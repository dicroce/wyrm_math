import { pinsEnv, restrictionStatus } from "../assumptions.js";
import {
  eq,
  findById,
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

export interface MultiplicativeCancellationParams {
  /** An element of the Fraction's numerator list at `location`. */
  readonly numTermId: NodeId;
  /** A structurally equal element of its denominator list. */
  readonly denTermId: NodeId;
}

function resolve(
  tree: Equation,
  location: Location,
  params: MultiplicativeCancellationParams,
): { frac: Fraction; numTerm: Expr; denTerm: Expr } | undefined {
  const node = findById(tree, location);
  if (node === undefined || node.kind !== "fraction") return undefined;
  const numTerm = node.num.find((c) => c.id === params.numTermId);
  const denTerm = node.den.find((c) => c.id === params.denTermId);
  if (numTerm === undefined || denTerm === undefined) return undefined;
  if (!eq(numTerm, denTerm)) return undefined;
  return { frac: node, numTerm, denTerm };
}

/**
 * x/x ~> 1 inside a Fraction — a solution-LOSING move: at points where x = 0
 * the original fraction is undefined while the result pretends it is fine,
 * so the rule emits Restriction(x ≠ 0). The discharge pass settles it
 * immediately when x is decidable (2/2 ~> 1 discharges 2 ≠ 0 on the spot);
 * the precondition rejects cancelling something decidably zero.
 */
export const multiplicativeCancellation: Rule<MultiplicativeCancellationParams> = {
  id: "multiplicative-cancellation",
  description: "Cancel a factor appearing in both numerator and denominator (emits ≠ 0).",

  precondition(judgment, location, params) {
    const r = resolve(judgment.equation, location, params);
    if (r === undefined) return false;
    const status = restrictionStatus(
      { expr: r.denTerm, value: Rational.zero },
      pinsEnv(judgment.assumptions),
    );
    return status !== "fails";
  },

  apply(judgment, location, params): RuleApplication {
    if (!this.precondition(judgment, location, params)) {
      throw new RulePreconditionViolation(
        this.id,
        "factors do not match, or the factor is decidably zero",
      );
    }
    const tree = judgment.equation;
    const r = resolve(tree, location, params)!;
    const num = r.frac.num.filter((c) => c.id !== params.numTermId);
    const den = r.frac.den.filter((c) => c.id !== params.denTermId);
    // An empty denominator list means 1 — drop the bar entirely.
    const result: Expr = den.length === 0 ? product(num) : { ...r.frac, num, den };
    const tree2 = replaceTermRespectingInvariants(tree, r.frac.id, result);
    const mergeTarget = findById(tree2, r.frac.id)
      ? r.frac.id
      : findById(tree2, result.id)
        ? result.id
        : undefined;
    return {
      equation: tree2,
      emits: [
        { kind: "restriction", expr: r.denTerm, relation: "≠", value: Rational.zero },
      ],
      diff: {
        ...idSetDiff(tree, tree2),
        merged: mergeTarget
          ? [{ sources: [params.numTermId, params.denTermId], target: mergeTarget }]
          : [],
        moved: [],
      },
    };
  },
};
