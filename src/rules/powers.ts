/**
 * The exponent-law tap rules beyond expand/combine: negative exponents
 * become fractions, nested literal powers multiply out, and literal powers
 * distribute over products. All are exact under the engine's
 * truth-where-both-defined contract (the undefined points of each side
 * coincide), so none emits an assumption.
 */
import {
  cloneFresh,
  findById,
  findParent,
  fraction,
  int,
  pow,
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

type NoParams = Record<string, never>;

function powAt(tree: Equation, location: Location): Pow | undefined {
  const node = findById(tree, location);
  return node !== undefined && node.kind === "pow" ? node : undefined;
}

/**
 * x^(−n) ~> 1/(x^n). The Pow survives (same id) with the negation peeled off
 * its exponent; a fraction bar appears around it. Works for symbolic
 * exponents too (x^(−a) ~> 1/(x^a)) — both sides are undefined at exactly
 * the same points.
 */
export const negativeExponent: Rule<NoParams> = {
  id: "negative-exponent",
  description: "Turn a negative exponent into a reciprocal.",

  precondition(judgment, location, _params) {
    const node = powAt(judgment.equation, location);
    return node !== undefined && node.exp.kind === "neg";
  },

  apply(judgment, location, _params): RuleApplication {
    const tree = judgment.equation;
    const node = powAt(tree, location);
    if (node === undefined || node.exp.kind !== "neg") {
      throw new RulePreconditionViolation(this.id, "location is not a power with a negative exponent");
    }
    const flipped: Pow = { ...node, exp: node.exp.child };
    const result = fraction([], [flipped]);
    const oldParent = findParent(tree, node.id)?.id ?? tree.id;
    const tree2 = replaceTermRespectingInvariants(tree, node.id, result);
    return {
      equation: tree2,
      emits: [],
      diff: {
        ...idSetDiff(tree, tree2),
        merged: [],
        moved: survivorMoved(tree2, node.id, oldParent),
      },
    };
  },
};

/**
 * (x^m)^n ~> x^(m·n) for literal exponents. The inner Pow survives (same id,
 * same base) carrying the folded exponent; the outer Pow and both old
 * exponent literals merge into the new one.
 */
export const powerOfPower: Rule<NoParams> = {
  id: "power-of-power",
  description: "Multiply nested literal exponents.",

  precondition(judgment, location, _params) {
    const node = powAt(judgment.equation, location);
    return (
      node !== undefined &&
      node.base.kind === "pow" &&
      node.exp.kind === "int" &&
      node.base.exp.kind === "int"
    );
  },

  apply(judgment, location, _params): RuleApplication {
    const tree = judgment.equation;
    const node = powAt(tree, location);
    if (
      node === undefined ||
      node.base.kind !== "pow" ||
      node.exp.kind !== "int" ||
      node.base.exp.kind !== "int"
    ) {
      throw new RulePreconditionViolation(this.id, "location is not a literal power of a literal power");
    }
    const folded = int(node.exp.value * node.base.exp.value);
    const result: Pow = { ...node.base, exp: folded };
    const tree2 = replaceTermRespectingInvariants(tree, node.id, result);
    return {
      equation: tree2,
      emits: [],
      diff: {
        ...idSetDiff(tree, tree2),
        merged: [{ sources: [node.exp.id, node.base.exp.id], target: folded.id }],
        moved: [],
      },
    };
  },
};

/**
 * (x·y)^n ~> x^n · y^n for a literal n ≥ 2. The factors survive by identity
 * as the new bases; the exponent survives on the first factor and is cloned
 * onto the rest.
 */
export const distributePower: Rule<NoParams> = {
  id: "distribute-power",
  description: "Distribute a literal power over a product.",

  precondition(judgment, location, _params) {
    const node = powAt(judgment.equation, location);
    return (
      node !== undefined &&
      node.base.kind === "product" &&
      node.exp.kind === "int" &&
      node.exp.value >= 2n
    );
  },

  apply(judgment, location, _params): RuleApplication {
    const tree = judgment.equation;
    const node = powAt(tree, location);
    if (
      node === undefined ||
      node.base.kind !== "product" ||
      node.exp.kind !== "int" ||
      node.exp.value < 2n
    ) {
      throw new RulePreconditionViolation(this.id, "location is not a product raised to a literal power >= 2");
    }
    const factors = node.base.children.map((c, i) =>
      pow(c, i === 0 ? node.exp : cloneFresh(node.exp)),
    );
    const result = product(factors);
    const tree2 = replaceTermRespectingInvariants(tree, node.id, result);
    return {
      equation: tree2,
      emits: [],
      diff: { ...idSetDiff(tree, tree2), merged: [], moved: [] },
    };
  },
};
