/**
 * Move enumeration: the bridge from "legal moves are possible, illegal moves
 * are impossible" to an interface a finger can use. The UI never invents
 * rule applications — it asks this module what is legal and renders those
 * affordances. Every returned Move passes its rule's precondition against
 * the judgment it was enumerated for (preconditions are the single source of
 * truth; enumerators only generate the candidate space).
 *
 * Two kinds of rule, two kinds of enumeration:
 *  - Id-parameterized rules (cancellations, combine-integers) have a FINITE
 *    candidate space — pairs of children at a site. Enumeration is complete:
 *    every legal application is returned (property-tested).
 *  - Expr-parameterized rules (add/divide/multiply both sides) have an
 *    infinite parameter space. Enumeration returns the gesture-meaningful
 *    instances derived from the tree: drag a term across the equals sign,
 *    drag a factor under the other side, drag a denominator factor across to
 *    clear it. Free-form parameters remain available through Derivation.apply.
 */
import { allNodes, type Expr, type NodeId } from "./expr.js";
import type { Judgment } from "./assumptions.js";
import type { BranchingRule, Location, Rule } from "./rule.js";
import { additiveCancellation } from "./rules/additiveCancellation.js";
import { addToBothSides } from "./rules/addToBothSides.js";
import { combineIntegerFactors } from "./rules/combineIntegerFactors.js";
import { combineIntegers } from "./rules/combineIntegers.js";
import { combineLikeFactors } from "./rules/combineLikeFactors.js";
import { distribute } from "./rules/distribute.js";
import { divideBothSides } from "./rules/divideBothSides.js";
import { expandPower } from "./rules/expandPower.js";
import { factorInstancesOf, factorOut } from "./rules/factorOut.js";
import { dropOneFactor, dropZeroTerm, powerOne, powerZero } from "./rules/identities.js";
import { moveTermAcross } from "./rules/moveTermAcross.js";
import { distributePower, negativeExponent, powerOfPower } from "./rules/powers.js";
import { simplifySqrt, sqrtBothSides, zeroProduct } from "./rules/quadratics.js";
import { quotientOfPowers } from "./rules/quotientOfPowers.js";
import { squareBothSides } from "./rules/squareBothSides.js";
import { swapSides } from "./rules/swapSides.js";
import { multiplicativeCancellation } from "./rules/multiplicativeCancellation.js";
import { multiplyBothSides } from "./rules/multiplyBothSides.js";
import { reduceIntegerFraction } from "./rules/reduceIntegerFraction.js";

// eslint-disable-next-line @typescript-eslint/no-explicit-any
export type AnyRule = Rule<any>;

/** Every rule the engine knows. UI dispatch goes through ruleById. */
export const allRules: readonly AnyRule[] = [
  additiveCancellation,
  addToBothSides,
  combineIntegerFactors,
  combineIntegers,
  combineLikeFactors,
  distribute,
  distributePower,
  divideBothSides,
  dropOneFactor,
  dropZeroTerm,
  expandPower,
  factorOut,
  moveTermAcross,
  multiplicativeCancellation,
  multiplyBothSides,
  negativeExponent,
  powerOfPower,
  powerOne,
  powerZero,
  quotientOfPowers,
  reduceIntegerFraction,
  simplifySqrt,
  squareBothSides,
  swapSides,
];

const registry = new Map(allRules.map((r) => [r.id, r]));

export function ruleById(id: string): AnyRule {
  const rule = registry.get(id);
  if (rule === undefined) throw new Error(`unknown rule ${id}`);
  return rule;
}

// eslint-disable-next-line @typescript-eslint/no-explicit-any
export type AnyBranchingRule = BranchingRule<any>;

/** Disjunctive rules: dispatched through Derivation.applyBranching. */
export const allBranchingRules: readonly AnyBranchingRule[] = [sqrtBothSides, zeroProduct];

const branchingRegistry = new Map(allBranchingRules.map((r) => [r.id, r]));

export function branchingRuleById(id: string): AnyBranchingRule {
  const rule = branchingRegistry.get(id);
  if (rule === undefined) throw new Error(`unknown branching rule ${id}`);
  return rule;
}

/**
 * A concrete legal move: ready to hand to Derivation.apply. `handle` is the
 * node the user grabs; `dropTarget`, when present, is the node the gesture
 * drops it onto (both exist in the current tree, so the UI can resolve them
 * to layout boxes).
 */
export interface Move {
  readonly ruleId: string;
  readonly location: Location;
  readonly params: unknown;
  readonly handle: NodeId;
  readonly dropTarget?: NodeId;
  /** Dispatch through applyBranching/branchingRuleById instead of apply. */
  readonly branching?: boolean;
}

/** All legal moves for this judgment, every one precondition-checked. */
export function enumerateMoves(judgment: Judgment): Move[] {
  const moves: Move[] = [];
  const eqn = judgment.equation;

  const push = (
    rule: AnyRule,
    location: Location,
    params: unknown,
    handle: NodeId,
    dropTarget?: NodeId,
  ): void => {
    if (!rule.precondition(judgment, location, params)) return;
    moves.push(
      dropTarget === undefined
        ? { ruleId: rule.id, location, params, handle }
        : { ruleId: rule.id, location, params, handle, dropTarget },
    );
  };

  const pushBranching = (
    rule: AnyBranchingRule,
    location: Location,
    params: unknown,
    handle: NodeId,
  ): void => {
    if (!rule.precondition(judgment, location, params)) return;
    moves.push({ ruleId: rule.id, location, params, handle, branching: true });
  };

  for (const node of allNodes(eqn)) {
    // Pair moves inside a Sum: cancellation, integer folding, and factoring
    // a shared factor instance out of two terms. Both drag directions.
    if (node.kind === "sum") {
      for (const a of node.children) {
        for (const b of node.children) {
          if (a.id === b.id) continue;
          const params = { termA: a.id, termB: b.id };
          // Term-level moves are ALSO reachable from inside the term (alias
          // handles): grabbing the digit of −1 grabs the signed term, so the
          // gesture resolver's deepest tier can still offer cancellation.
          const handles = new Set([a.id, ...factorInstancesOf(a).map((i) => i.id)]);
          for (const h of handles) {
            push(additiveCancellation, node.id, params, h, b.id);
            push(combineIntegers, node.id, params, h, b.id);
          }
          // Factor-out is reachable from ANY grab point within the term
          // (root or instance) and lands on the WHOLE other term — dragging
          // 3x onto 2x combines like terms without sniper-precision. The
          // params still pin exact instances; with several shared factors
          // the first enumerated pair wins (stable priority sort).
          for (const fa of factorInstancesOf(a)) {
            for (const fb of factorInstancesOf(b)) {
              const params = { factorA: fa.id, factorB: fb.id };
              for (const h of handles) {
                push(factorOut, node.id, params, h, b.id);
              }
            }
          }
        }
        push(dropZeroTerm, node.id, { termId: a.id }, a.id); // tap
      }
    }
    // Pair moves inside a Product: integer folding, like-base merging, and
    // distributing a factor over a Sum sibling.
    if (node.kind === "product") {
      for (const a of node.children) {
        for (const b of node.children) {
          if (a.id === b.id) continue;
          const params = { termA: a.id, termB: b.id };
          push(combineIntegerFactors, node.id, params, a.id, b.id);
          push(combineLikeFactors, node.id, params, a.id, b.id);
          const dParams = { factorId: a.id, sumId: b.id };
          push(distribute, node.id, dParams, a.id, b.id);
          push(distribute, node.id, dParams, b.id, a.id); // drag the sum onto the factor
        }
        push(dropOneFactor, node.id, { termId: a.id }, a.id); // tap
      }
    }
    // Tap moves on powers: expand, unwrap x^1, collapse x^0, flip a
    // negative exponent, fold nested powers, distribute over a product.
    if (node.kind === "pow") {
      push(expandPower, node.id, {}, node.id);
      push(powerOne, node.id, {}, node.id);
      push(powerZero, node.id, {}, node.id);
      push(negativeExponent, node.id, {}, node.id);
      push(powerOfPower, node.id, {}, node.id);
      push(distributePower, node.id, {}, node.id);
    }
    // Tap a perfect-square radical to evaluate it.
    if (node.kind === "sqrt") {
      push(simplifySqrt, node.id, {}, node.id);
    }
    // Pair moves across a fraction bar, in both drag directions.
    if (node.kind === "fraction") {
      for (const n of node.num) {
        for (const d of node.den) {
          const params = { numTermId: n.id, denTermId: d.id };
          push(multiplicativeCancellation, node.id, params, n.id, d.id);
          push(multiplicativeCancellation, node.id, params, d.id, n.id);
          push(reduceIntegerFraction, node.id, params, n.id, d.id);
          push(reduceIntegerFraction, node.id, params, d.id, n.id);
          push(quotientOfPowers, node.id, params, n.id, d.id);
          push(quotientOfPowers, node.id, params, d.id, n.id);
        }
      }
    }
  }

  // Taps on the relation sign: square both sides (equalities; an
  // Extension-emitting move) or swap the sides (any relation; on '=' the
  // square outranks it).
  push(squareBothSides, eqn.id, {}, eqn.id);
  push(swapSides, eqn.id, {}, eqn.id);

  // Disjunctive taps: undo a square (x² = b branches to ±√b; handle is the
  // square itself) and the zero-product property (handle is the product).
  if (eqn.lhs.kind === "pow") {
    pushBranching(sqrtBothSides, eqn.id, {}, eqn.lhs.id);
  }
  for (const side of [eqn.lhs, eqn.rhs]) {
    if (side.kind === "product") {
      pushBranching(zeroProduct, eqn.id, {}, side.id);
    }
  }

  // Both-sides moves, derived from each side's top-level structure.
  const sides: { side: Expr; other: Expr }[] = [
    { side: eqn.lhs, other: eqn.rhs },
    { side: eqn.rhs, other: eqn.lhs },
  ];
  for (const { side, other } of sides) {
    // Drag a top-level term across the equals sign: it MOVES, sign-flipped
    // (the composite of add-to-both-sides + the exact cancellation at the
    // source). The raw add-to-both-sides rule remains available to code via
    // ruleById, but the gesture is the move.
    const terms = side.kind === "sum" ? side.children : [side];
    for (const t of terms) {
      push(moveTermAcross, eqn.id, { termId: t.id }, t.id, other.id);
    }
    // Drag the side (or one of its factors) under the other side.
    const divisors = side.kind === "product" ? [side, ...side.children] : [side];
    for (const f of divisors) {
      push(divideBothSides, eqn.id, { divisor: f }, f.id, other.id);
    }
    // Drag a denominator factor across to clear it.
    const fractions =
      side.kind === "fraction"
        ? [side]
        : side.kind === "product"
          ? side.children.filter((c) => c.kind === "fraction")
          : [];
    for (const f of fractions) {
      for (const d of f.den) {
        push(multiplyBothSides, eqn.id, { factor: d }, d.id, other.id);
      }
    }
  }

  return moves;
}

/** The legal moves that begin by grabbing this node. */
export function movesFrom(judgment: Judgment, handle: NodeId): Move[] {
  return enumerateMoves(judgment).filter((m) => m.handle === handle);
}
