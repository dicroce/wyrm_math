/**
 * wyrm-math — an exact, conditionally-sound symbolic algebra engine for
 * manipulative interfaces.
 *
 * This file IS the public API: every export below is supported surface,
 * grouped by concern. Anything not re-exported here is an internal detail.
 * The groups, top to bottom:
 *
 *   1. Expression trees       — immutable AST, constructors, traversal
 *   2. Exact arithmetic       — Rational (bigint; no floats, ever)
 *   3. Evaluation             — substitute and decide truth, exactly
 *   4. Parsing & printing     — text ⇄ tree
 *   5. Judgments/assumptions  — conditional soundness (the heart)
 *   6. Rules & derivations    — the only mutation paths; the derivation tree
 *   7. Built-in rules         — the algebra
 *   8. Move enumeration       — legal affordances for a UI
 *   9. Layout geometry        — DOM-free boxes/glyphs for rendering
 *  10. Rule-authoring toolkit — helpers for writing new rules soundly
 *
 * The product invariant everything serves: legal moves are possible,
 * illegal moves are impossible, and every reachable state is equivalent to
 * the original equation GIVEN its assumption set.
 */

// ---------------------------------------------------------------------------
// 1. Expression trees
// ---------------------------------------------------------------------------
// Immutable, id-stable AST. Sum/Product are n-ary; there is no subtraction
// or division node (a − b is Sum(a, Neg(b)); division is a Fraction with
// numerator/denominator LISTS). Build only through the smart constructors —
// they maintain the structural invariants (auto-flattening, canonical
// negative literals, no double negation).
export {
  // constructors
  int,
  variable,
  sum,
  product,
  neg,
  fraction,
  pow,
  sqrt,
  equation,
  // traversal & queries
  allNodes,
  childrenOf,
  findById,
  findParent,
  variablesIn,
  // structural equality (commutative for Sum/Product) and printing
  eq,
  exprToString,
  // relations
  flipRelation,
  // copying (fresh ids — ids must stay unique within a tree)
  cloneFresh,
} from "./expr.js";
export type {
  Expr,
  Node,
  NodeId,
  Integer,
  Variable,
  Sum,
  Product,
  Neg,
  Fraction,
  Pow,
  Sqrt,
  Equation,
  RelationKind,
} from "./expr.js";

// ---------------------------------------------------------------------------
// 2. Exact arithmetic
// ---------------------------------------------------------------------------
// All correctness checks are exact: bigint rationals, no floating point.
export { Rational, DivisionByZero, gcd } from "./rational.js";
// Surds extend exact arithmetic past ℚ to quadratic irrationals (q₀ + Σqᵢ√nᵢ);
// evalExpr returns this domain, with Rational as the degenerate element.
export { Surd } from "./surd.js";

// ---------------------------------------------------------------------------
// 3. Evaluation
// ---------------------------------------------------------------------------
// truthValue decides any relation at a sample point, or returns undefined
// where a side is undefined (division by zero, irrational square root):
// the engine never approximates.
export {
  evalExpr,
  truthValue,
  rationalToExpr,
  sqrtRational,
  UnboundVariable,
  NonIntegerExponent,
  InexactSqrt,
} from "./eval.js";
export type { Env } from "./eval.js";

// ---------------------------------------------------------------------------
// 4. Parsing & printing
// ---------------------------------------------------------------------------
// parseEquation("2x + 3 = 11") — relations, fractions, implicit
// multiplication, powers, radicals. Inverse of exprToString (round-trip
// property-tested). Decimals are rejected: the engine is exact.
export { parseEquation, ParseError } from "./parse.js";

// ---------------------------------------------------------------------------
// 5. Judgments and assumptions — conditional soundness
// ---------------------------------------------------------------------------
// The unit of state is a Judgment { assumptions, equation }. The polarity
// distinction is the heart of the design: Restrictions are emitted by moves
// that may LOSE solutions (divide by b ⇒ b ≠ 0); Extensions by moves that
// may GAIN them (multiply, square) and carry the obligation to check
// candidate solutions against the original equation; Pinned are user
// what-ifs. Emission is separate from discharge; discharged assumptions are
// recorded, never deleted.
export {
  mkJudgment,
  checkSolution,
  envSatisfiesAssumptions,
  AssumptionConflict,
} from "./assumptions.js";
export type {
  Judgment,
  Assumption,
  Restriction,
  Extension,
  Pinned,
  AssumptionOrigin,
  CheckVerdict,
  DischargeReason,
} from "./assumptions.js";

// ---------------------------------------------------------------------------
// 6. Rules and derivations — the only mutation paths
// ---------------------------------------------------------------------------
// Equations change only through rules; judgments change only through the
// Derivation's entry points (apply / applyBranching / pinVariable /
// unpinVariable / caseSplit / checkSolution). The derivation log is an
// append-only TREE: undo moves a pointer, abandoned branches stay live, and
// disjunctive rewrites (x² = 9 ⇒ x = ±3) commit all arms as siblings.
export { applyRule, applyBranchingRule, RulePreconditionViolation } from "./rule.js";
export type {
  Rule,
  RuleApplication,
  BranchingRule,
  BranchOutcome,
  AnimationDiff,
  Location,
} from "./rule.js";
export { Derivation } from "./derivation.js";
export type { DerivationNode } from "./derivation.js";

// ---------------------------------------------------------------------------
// 7. Built-in rules
// ---------------------------------------------------------------------------
// Each rule ships with a property test asserting it respects the solution
// set under its assumptions. UIs normally dispatch via ruleById /
// branchingRuleById using Moves from enumerateMoves rather than importing
// rules directly.
export { additiveCancellation } from "./rules/additiveCancellation.js";
export type { AdditiveCancellationParams } from "./rules/additiveCancellation.js";
export { addToBothSides } from "./rules/addToBothSides.js";
export type { AddToBothSidesParams } from "./rules/addToBothSides.js";
export { combineIntegers } from "./rules/combineIntegers.js";
export type { CombineIntegersParams } from "./rules/combineIntegers.js";
export { combineIntegerFactors } from "./rules/combineIntegerFactors.js";
export type { CombineIntegerFactorsParams } from "./rules/combineIntegerFactors.js";
export { combineLikeFactors } from "./rules/combineLikeFactors.js";
export type { CombineLikeFactorsParams } from "./rules/combineLikeFactors.js";
export { distribute } from "./rules/distribute.js";
export type { DistributeParams } from "./rules/distribute.js";
export { divideBothSides } from "./rules/divideBothSides.js";
export type { DivideBothSidesParams } from "./rules/divideBothSides.js";
export { expandPower } from "./rules/expandPower.js";
export type { ExpandPowerParams } from "./rules/expandPower.js";
export { combineFractions } from "./rules/combineFractions.js";
export type { CombineFractionsParams } from "./rules/combineFractions.js";
export { factorOut } from "./rules/factorOut.js";
export type { FactorOutParams } from "./rules/factorOut.js";
export { factorOutNegative } from "./rules/factorOutNegative.js";
export type { FactorOutNegativeParams } from "./rules/factorOutNegative.js";
export { dropZeroTerm, dropOneFactor, powerOne, powerZero } from "./rules/identities.js";
export type { DropTermParams } from "./rules/identities.js";
export { moveTermAcross } from "./rules/moveTermAcross.js";
export type { MoveTermAcrossParams } from "./rules/moveTermAcross.js";
export { multiplicativeCancellation } from "./rules/multiplicativeCancellation.js";
export type { MultiplicativeCancellationParams } from "./rules/multiplicativeCancellation.js";
export { multiplyBothSides } from "./rules/multiplyBothSides.js";
export type { MultiplyBothSidesParams } from "./rules/multiplyBothSides.js";
export { negativeExponent, powerOfPower, distributePower } from "./rules/powers.js";
export { sqrtBothSides, zeroProduct, simplifySqrt } from "./rules/quadratics.js";
export { quotientOfPowers } from "./rules/quotientOfPowers.js";
export type { QuotientOfPowersParams } from "./rules/quotientOfPowers.js";
export { reduceIntegerFraction } from "./rules/reduceIntegerFraction.js";
export type { ReduceIntegerFractionParams } from "./rules/reduceIntegerFraction.js";
export { splitTerm } from "./rules/splitTerm.js";
export type { SplitTermParams } from "./rules/splitTerm.js";
export { squareBothSides } from "./rules/squareBothSides.js";
export { swapSides } from "./rules/swapSides.js";

// ---------------------------------------------------------------------------
// 8. Move enumeration — what a UI renders and dispatches
// ---------------------------------------------------------------------------
// enumerateMoves(judgment) returns every legal affordance, each carrying the
// node the user grabs (handle) and where it drops (dropTarget). Sound for
// all rules; complete for the finite id-parameterized ones. Preconditions
// decide legality, so assumptions automatically prune affordances.
export {
  enumerateMoves,
  movesFrom,
  allRules,
  ruleById,
  allBranchingRules,
  branchingRuleById,
} from "./moves.js";
export type { Move, AnyRule, AnyBranchingRule } from "./moves.js";

// ---------------------------------------------------------------------------
// 9. Layout geometry — DOM-free rendering support
// ---------------------------------------------------------------------------
// layoutNode maps a tree to positioned, id-keyed boxes and glyphs from
// static metric tables (pure Node — render it with anything). hitTest is a
// geometry query. Subtree geometry is context-independent up to translation
// and scale, which is what makes id-keyed animation possible.
export { layoutNode, hitTest, boxCenter, METRICS } from "./layout.js";
export type { Layout, LayoutBox, LayoutRect, PlacedGlyph } from "./layout.js";

// ---------------------------------------------------------------------------
// 10. Rule-authoring toolkit
// ---------------------------------------------------------------------------
// What a new rule needs: id-preserving rebuilds, the invariant-repairing
// splice, diff bookkeeping, lifecycle queries for preconditions, and the
// invariant checker for tests. See ARCHITECTURE.md for the contracts.
export {
  rebuildNary,
  replaceNode,
  replaceTermRespectingInvariants,
  invariantViolations,
} from "./expr.js";
export { idSetDiff, survivorMoved, emptyDiff } from "./rule.js";
export {
  dischargePass,
  materializeAssumption,
  mkPinned,
  pinsEnv,
  restrictionStatus,
  signOf,
} from "./assumptions.js";
export type { EmittedAssumption, RestrictionStatus, Sign } from "./assumptions.js";
export { literalValue } from "./rules/combineIntegers.js";
export { factorInstancesOf } from "./rules/factorOut.js";
