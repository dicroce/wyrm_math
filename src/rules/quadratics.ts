/**
 * The disjunctive moves that unlock quadratics, plus the radical cleanup tap.
 *
 * Both branching rules satisfy the UNION property (property-tested): the
 * union of the branches' solution sets equals the original's. Each branch is
 * individually sound (its solutions satisfy the original); together they are
 * complete (every original solution lands in at least one branch — possibly
 * both, e.g. a = b = 0 under zero-product).
 */
import { literalValue } from "./combineIntegers.js";
import {
  findById,
  int,
  neg,
  replaceTermRespectingInvariants,
  sqrt,
  type Equation,
  type Expr,
  type Pow,
  type Product,
} from "../expr.js";
import { sqrtRational } from "../eval.js";
import { Rational } from "../rational.js";
import {
  idSetDiff,
  RulePreconditionViolation,
  type BranchingRule,
  type BranchOutcome,
  type Location,
  type Rule,
  type RuleApplication,
} from "../rule.js";

type NoParams = Record<string, never>;

function squaredLhs(tree: Equation): Pow | undefined {
  const lhs = tree.lhs;
  if (lhs.kind !== "pow") return undefined;
  if (lhs.exp.kind !== "int" || lhs.exp.value !== 2n) return undefined;
  return lhs;
}

/**
 * Undo a square: a² = b branches into a = √b and a = −√b. Sound because a
 * true a² = b forces b to be a perfect square of a rational, where √b is
 * exact; where b is negative the original is false and the branches are
 * undefined — nothing is claimed. Equalities only; gesture: tap the square.
 */
export const sqrtBothSides: BranchingRule<NoParams> = {
  id: "sqrt-both-sides",
  description: "Take square roots of both sides, branching into ± roots.",

  precondition(judgment, location, _params) {
    return (
      location === judgment.equation.id &&
      judgment.equation.relation === "=" &&
      squaredLhs(judgment.equation) !== undefined
    );
  },

  apply(judgment, location, _params): readonly BranchOutcome[] {
    const tree = judgment.equation;
    const squared = location === tree.id ? squaredLhs(tree) : undefined;
    if (squared === undefined || tree.relation !== "=") {
      throw new RulePreconditionViolation(this.id, "left side is not a literal square");
    }
    // Both branches reuse the base and the rhs by identity — they are
    // separate trees, so sharing across siblings is safe and the id-keyed
    // animation tracks them into either branch.
    const positive: Equation = { ...tree, lhs: squared.base, rhs: sqrt(tree.rhs) };
    const negative: Equation = { ...tree, lhs: squared.base, rhs: neg(sqrt(tree.rhs)) };
    return [
      {
        label: "positive root",
        equation: positive,
        emits: [],
        diff: { ...idSetDiff(tree, positive), merged: [], moved: [] },
      },
      {
        label: "negative root",
        equation: negative,
        emits: [],
        diff: { ...idSetDiff(tree, negative), merged: [], moved: [] },
      },
    ];
  },
};

function productEqualsZero(
  tree: Equation,
): { product: Product; flipped: boolean } | undefined {
  if (tree.relation !== "=") return undefined;
  if (tree.lhs.kind === "product" && literalValue(tree.rhs) === 0n) {
    return { product: tree.lhs, flipped: false };
  }
  if (tree.rhs.kind === "product" && literalValue(tree.lhs) === 0n) {
    return { product: tree.rhs, flipped: true };
  }
  return undefined;
}

/**
 * The zero-product property: a·b·… = 0 branches into a = 0, b = 0, …
 * (one branch per factor; rationals form an integral domain). Gesture: tap
 * the product when the other side is zero.
 */
export const zeroProduct: BranchingRule<NoParams> = {
  id: "zero-product",
  description: "A product is zero exactly when one of its factors is.",

  precondition(judgment, location, _params) {
    return (
      location === judgment.equation.id &&
      productEqualsZero(judgment.equation) !== undefined
    );
  },

  apply(judgment, location, _params): readonly BranchOutcome[] {
    const tree = judgment.equation;
    const r = location === tree.id ? productEqualsZero(tree) : undefined;
    if (r === undefined) {
      throw new RulePreconditionViolation(this.id, "not a product equal to zero");
    }
    return r.product.children.map((factor): BranchOutcome => {
      const branch: Equation = { ...tree, lhs: factor, rhs: int(0), relation: "=" };
      return {
        label: `${factorLabel(factor)} = 0`,
        equation: branch,
        emits: [],
        diff: { ...idSetDiff(tree, branch), merged: [], moved: [] },
      };
    });
  },
};

function factorLabel(factor: Expr): string {
  // exprToString would be circular to import here for so little; a compact
  // structural sketch is enough for branch labels.
  switch (factor.kind) {
    case "var":
      return factor.name;
    case "int":
      return `${factor.value}`;
    default:
      return "factor";
  }
}

/** Tap √9 down to 3 — exact perfect squares only. */
export const simplifySqrt: Rule<NoParams> = {
  id: "simplify-sqrt",
  description: "Evaluate the square root of a perfect-square literal.",

  precondition(judgment, location, _params) {
    const node = findById(judgment.equation, location);
    if (node === undefined || node.kind !== "sqrt") return false;
    if (node.child.kind !== "int") return false;
    return sqrtRational(new Rational(node.child.value)) !== undefined;
  },

  apply(judgment, location, _params): RuleApplication {
    if (!this.precondition(judgment, location, _params)) {
      throw new RulePreconditionViolation(this.id, "not a perfect-square literal radical");
    }
    const tree = judgment.equation;
    const node = findById(tree, location)!;
    if (node.kind !== "sqrt" || node.child.kind !== "int") {
      throw new RulePreconditionViolation(this.id, "unreachable");
    }
    const root = sqrtRational(new Rational(node.child.value))!;
    const folded = int(root.num);
    const tree2 = replaceTermRespectingInvariants(tree, node.id, folded);
    return {
      equation: tree2,
      emits: [],
      diff: {
        ...idSetDiff(tree, tree2),
        merged: [{ sources: [location], target: folded.id }],
        moved: [],
      },
    };
  },
};
