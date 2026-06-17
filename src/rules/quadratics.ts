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
import { coeffAndBody } from "./splitTerm.js";
import {
  findById,
  fraction,
  int,
  neg,
  product,
  replaceTermRespectingInvariants,
  sqrt,
  sum,
  variable,
  variablesIn,
  type Equation,
  type Expr,
  type Pow,
  type Product,
} from "../expr.js";
import { exactToExpr, rationalToExpr } from "../eval.js";
import { Rational } from "../rational.js";
import { squareFreeFactor, Surd } from "../surd.js";
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

/** Tap a square root to simplify it: evaluate a perfect square (√9 → 3) or pull
 *  out its largest square factor (√8 → 2√2). Integer radicands only; a
 *  square-free radicand (√7) is already simplest and a negative one has no real
 *  value — neither offers the move. */
export const simplifySqrt: Rule<NoParams> = {
  id: "simplify-sqrt",
  description: "Simplify a square root: evaluate it or pull out its square factor.",

  precondition(judgment, location, _params) {
    const node = findById(judgment.equation, location);
    if (node === undefined || node.kind !== "sqrt" || node.child.kind !== "int") return false;
    const n = node.child.value; // Integer invariant: n ≥ 0
    if (n === 0n) return true; // √0 → 0
    const { coeff, radicand } = squareFreeFactor(n);
    // A perfect square collapses fully (radicand 1 — covers √1 → 1, √49 → 7);
    // otherwise fire only when there's a square factor to pull (√8 → 2√2).
    return radicand === 1n || coeff > 1n;
  },

  apply(judgment, location, _params): RuleApplication {
    if (!this.precondition(judgment, location, _params)) {
      throw new RulePreconditionViolation(this.id, "radical has no square factor to extract");
    }
    const tree = judgment.equation;
    const node = findById(tree, location)!;
    if (node.kind !== "sqrt" || node.child.kind !== "int") {
      throw new RulePreconditionViolation(this.id, "unreachable");
    }
    // n ≥ 0, so Surd.sqrt is defined; exactToExpr renders √9 → 3, √8 → 2√2, …
    const simplified = exactToExpr(Surd.sqrt(new Rational(node.child.value))!);
    const tree2 = replaceTermRespectingInvariants(tree, node.id, simplified);
    return {
      equation: tree2,
      emits: [],
      diff: {
        ...idSetDiff(tree, tree2),
        merged: [{ sources: [location], target: simplified.id }],
        moved: [],
      },
    };
  },
};

/** Read `a·x² + b·x + c = 0` (one side literal 0, the other an expanded
 *  single-variable quadratic with INTEGER coefficients, a ≠ 0). Each term must
 *  be a monomial cx⁰/cx/cx² — a product (factored) or fractional coefficient is
 *  not recognized (zero-product / clearing denominators come first). */
export function readQuadratic(
  eqn: Equation,
): { side: Expr; v: string; a: bigint; b: bigint; c: bigint } | undefined {
  if (eqn.relation !== "=") return undefined;
  let side: Expr;
  if (literalValue(eqn.rhs) === 0n) side = eqn.lhs;
  else if (literalValue(eqn.lhs) === 0n) side = eqn.rhs;
  else return undefined;

  const vars = variablesIn(side);
  if (vars.size !== 1) return undefined;
  const v = [...vars][0]!;

  let a = 0n;
  let b = 0n;
  let c = 0n;
  const terms = side.kind === "sum" ? side.children : [side];
  for (const t of terms) {
    const { coeff, body } = coeffAndBody(t);
    if (body.length === 0) {
      c += coeff;
    } else if (body.length === 1) {
      const part = body[0]!;
      if (part.kind === "var" && part.name === v) {
        b += coeff;
      } else if (
        part.kind === "pow" &&
        part.base.kind === "var" &&
        part.base.name === v &&
        part.exp.kind === "int" &&
        part.exp.value === 2n
      ) {
        a += coeff;
      } else {
        return undefined; // a power other than 2, or a different variable
      }
    } else {
      return undefined; // not a single-variable monomial of degree ≤ 2
    }
  }
  return a === 0n ? undefined : { side, v, a, b, c };
}

/**
 * The quadratic formula: `a·x² + b·x + c = 0` branches into
 * `x = (−b + √D)/(2a)` and `x = (−b − √D)/(2a)`, `D = b² − 4ac`. An exact
 * equivalence over a field (a ≠ 0) — emits nothing. The √D is left UNSIMPLIFIED
 * (a literal radical) so `simplify-sqrt` is the natural follow-up; a perfect
 * square then collapses to rational roots (so this subsumes factoring), and a
 * negative D leaves √(negative) — an undefined point, i.e. "no real solution".
 * Gesture: tap an expanded quadratic that equals zero.
 */
export const quadraticFormula: BranchingRule<NoParams> = {
  id: "quadratic-formula",
  description: "Solve a quadratic a·x² + b·x + c = 0 via x = (−b ± √(b²−4ac)) / 2a.",

  precondition(judgment, location, _params) {
    return location === judgment.equation.id && readQuadratic(judgment.equation) !== undefined;
  },

  apply(judgment, location, _params): readonly BranchOutcome[] {
    const tree = judgment.equation;
    const r = location === tree.id ? readQuadratic(tree) : undefined;
    if (r === undefined) {
      throw new RulePreconditionViolation(this.id, "not an expanded quadratic equal to zero");
    }
    const { v, a, b, c } = r;
    const branch = (positive: boolean, label: string): BranchOutcome => {
      // The discriminant is LEFT UNEVALUATED — `b·b − 4·a·c` with the
      // coefficients substituted — so squaring, multiplying and subtracting are
      // the learner's gestures (the journey, not the destination). Integer
      // products mean the existing fold rules (combine-integer-factors /
      // combine-integers) carry the arithmetic, and simplify-sqrt finishes the
      // √. A negative result leaves √(negative) — "no real solution".
      const disc = sum([product([int(b), int(b)]), neg(product([int(4n), int(a), int(c)]))]);
      const radical = positive ? sqrt(disc) : neg(sqrt(disc));
      const numerator = sum([rationalToExpr(new Rational(-b)), radical]);
      const rhs = fraction([numerator], [rationalToExpr(new Rational(2n * a))]);
      const eqn: Equation = { ...tree, lhs: variable(v), rhs, relation: "=" };
      return { label, equation: eqn, emits: [], diff: { ...idSetDiff(tree, eqn), merged: [], moved: [] } };
    };
    return [branch(true, "+ root"), branch(false, "− root")];
  },
};
