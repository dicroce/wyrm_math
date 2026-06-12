import {
  cloneFresh,
  findById,
  product,
  replaceTermRespectingInvariants,
  type Equation,
  type Pow,
} from "../expr.js";
import {
  idSetDiff,
  RulePreconditionViolation,
  survivorMoved,
  type Location,
  type Rule,
  type RuleApplication,
} from "../rule.js";

/** Expansion takes no parameters: the location says it all. */
export interface ExpandPowerParams {}

function resolve(tree: Equation, location: Location): Pow | undefined {
  const node = findById(tree, location);
  if (node === undefined || node.kind !== "pow") return undefined;
  // Integer literals are non-negative by invariant, so this is n >= 2.
  if (node.exp.kind !== "int" || node.exp.value < 2n) return undefined;
  return node;
}

/**
 * Unroll a literal power into repeated multiplication:
 *   x^3 ~> x·x·x
 * The original base keeps its identity as the first factor (the clones
 * visually peel out of it). Exactly solution-preserving — no assumptions.
 * The inverse is combine-like-factors, applied pairwise.
 */
export const expandPower: Rule<ExpandPowerParams> = {
  id: "expand-power",
  description: "Expand a literal integer power into repeated multiplication.",

  precondition(judgment, location, _params) {
    return resolve(judgment.equation, location) !== undefined;
  },

  apply(judgment, location, _params): RuleApplication {
    const tree = judgment.equation;
    const node = resolve(tree, location);
    if (node === undefined) {
      throw new RulePreconditionViolation(
        this.id,
        "location is not a power with a literal integer exponent >= 2",
      );
    }
    const n = Number((node.exp as { value: bigint }).value);
    const factors = [node.base];
    for (let i = 1; i < n; i++) factors.push(cloneFresh(node.base));
    const expanded = product(factors);
    const tree2 = replaceTermRespectingInvariants(tree, node.id, expanded);
    return {
      equation: tree2,
      emits: [],
      diff: {
        ...idSetDiff(tree, tree2),
        merged: [],
        moved: survivorMoved(tree2, node.base.id, node.id),
      },
    };
  },
};
