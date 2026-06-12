import {
  AssumptionConflict,
  dischargePass,
  materializeAssumption,
  type EmittedAssumption,
  type Judgment,
} from "./assumptions.js";
import { allNodes, findParent, type Equation, type NodeId } from "./expr.js";

/**
 * Where a rule acts: the id of a node in the current tree. Ids are stable, so
 * the UI's hit testing can hand them straight to the engine.
 */
export type Location = NodeId;

/**
 * Node-level description of what a rule application did, in terms the
 * animation system will consume. `created`/`removed` are exhaustive id sets
 * (every node that appears/disappears); `merged`/`moved` reference subtree
 * roots and carry the rule's animation intent.
 *
 * Defined now, before any UI exists, so that every rule declares its
 * animation semantics from day one.
 */
export interface AnimationDiff {
  /** Nodes that exist only in the result tree (e.g. a folded literal). */
  readonly created: readonly NodeId[];
  /** Nodes that exist only in the input tree (e.g. annihilated terms). */
  readonly removed: readonly NodeId[];
  /** Source nodes visually collapse into the target node. */
  readonly merged: readonly { sources: readonly NodeId[]; target: NodeId }[];
  /** Node survives but is re-parented (e.g. a sum collapsing to one term). */
  readonly moved: readonly { id: NodeId; from: NodeId; to: NodeId }[];
}

export const emptyDiff: AnimationDiff = {
  created: [],
  removed: [],
  merged: [],
  moved: [],
};

export interface RuleApplication {
  readonly equation: Equation;
  readonly diff: AnimationDiff;
  /** Conditions this move depends on, as bare data; the engine stamps origin/status. */
  readonly emits: readonly EmittedAssumption[];
}

/**
 * A solution-set-respecting rewrite under assumptions. EQUATIONS CHANGE ONLY
 * THROUGH RULES; judgments change only through the Derivation's entry points
 * (apply / pin / unpin / caseSplit / checkSolution). UI gestures map to
 * (rule, location, params) triples.
 *
 * Rules operate on Judgments: the precondition sees the assumption set, so a
 * move whose emitted Restriction would decidably FAIL under current Pinned
 * values (divide by x while x is pinned to 0) must return false.
 *
 * `precondition` must be a pure, total predicate: it decides whether the
 * gesture is legal. `apply` may assume the precondition holds and must throw
 * RulePreconditionViolation otherwise (applyRule checks it regardless).
 */
export interface Rule<P> {
  readonly id: string;
  readonly description: string;
  precondition(judgment: Judgment, location: Location, params: P): boolean;
  apply(judgment: Judgment, location: Location, params: P): RuleApplication;
}

/**
 * The single path from a rule application to a new Judgment: checks the
 * precondition, stamps emitted assumptions with their origin (the step id, so
 * any assumption chip can be traced back to the step that spawned it), and
 * runs the discharge pass. A decidably-failing emitted Restriction is a
 * conflict and aborts — preconditions should have rejected it.
 */
export function applyRule<P>(
  judgment: Judgment,
  rule: Rule<P>,
  location: Location,
  params: P,
  stepId = "adhoc",
): { judgment: Judgment; diff: AnimationDiff } {
  if (!rule.precondition(judgment, location, params)) {
    throw new RulePreconditionViolation(rule.id, "rejected by applyRule");
  }
  const { equation, diff, emits } = rule.apply(judgment, location, params);
  const stamped = emits.map((e) =>
    materializeAssumption(e, { kind: "rule", stepId }),
  );
  const { assumptions, conflicts } = dischargePass([
    ...judgment.assumptions,
    ...stamped,
  ]);
  if (conflicts.length > 0) {
    throw new AssumptionConflict(
      `rule ${rule.id} emitted a decidably false restriction`,
    );
  }
  return { judgment: { assumptions, equation }, diff };
}

export class RulePreconditionViolation extends Error {
  constructor(ruleId: string, detail: string) {
    super(`rule ${ruleId}: precondition violated: ${detail}`);
    this.name = "RulePreconditionViolation";
  }
}

/**
 * A DISJUNCTIVE rewrite: the union of the branches' solution sets equals the
 * original's (every solution of the original satisfies at least one branch;
 * every branch solution satisfies the original). x² = 9 branches into
 * x = √9 and x = −√9; ab = 0 branches into a = 0 and b = 0. The derivation
 * tree holds the branches as live siblings — the same shape as a case split.
 */
export interface BranchOutcome {
  readonly label: string;
  readonly equation: Equation;
  readonly diff: AnimationDiff;
  readonly emits: readonly import("./assumptions.js").EmittedAssumption[];
}

export interface BranchingRule<P> {
  readonly id: string;
  readonly description: string;
  precondition(judgment: Judgment, location: Location, params: P): boolean;
  apply(judgment: Judgment, location: Location, params: P): readonly BranchOutcome[];
}

/** The branching counterpart of applyRule: stamp, discharge, per branch. */
export function applyBranchingRule<P>(
  judgment: Judgment,
  rule: BranchingRule<P>,
  location: Location,
  params: P,
  stepId = "adhoc",
): { label: string; judgment: Judgment; diff: AnimationDiff }[] {
  if (!rule.precondition(judgment, location, params)) {
    throw new RulePreconditionViolation(rule.id, "rejected by applyBranchingRule");
  }
  return rule.apply(judgment, location, params).map((outcome) => {
    const stamped = outcome.emits.map((e) =>
      materializeAssumption(e, { kind: "rule", stepId }),
    );
    const { assumptions, conflicts } = dischargePass([
      ...judgment.assumptions,
      ...stamped,
    ]);
    if (conflicts.length > 0) {
      throw new AssumptionConflict(
        `rule ${rule.id} emitted a decidably false restriction`,
      );
    }
    return {
      label: outcome.label,
      judgment: { assumptions, equation: outcome.equation },
      diff: outcome.diff,
    };
  });
}

/**
 * Exhaustive created/removed id sets between two trees — the bookkeeping half
 * of an AnimationDiff. Rules add their own merged/moved intent on top.
 */
export function idSetDiff(
  before: Equation,
  after: Equation,
): { created: NodeId[]; removed: NodeId[] } {
  const beforeIds = new Set<NodeId>();
  for (const n of allNodes(before)) beforeIds.add(n.id);
  const afterIds = new Set<NodeId>();
  for (const n of allNodes(after)) afterIds.add(n.id);
  return {
    created: [...afterIds].filter((id) => !beforeIds.has(id)),
    removed: [...beforeIds].filter((id) => !afterIds.has(id)),
  };
}

/**
 * Best-effort "re-parented survivor" moved entry: present when an n-ary node
 * collapsed and its survivor now hangs somewhere else; absent when the node
 * survived in place or the splice point swallowed the survivor (e.g. a
 * double-negation collapse).
 */
export function survivorMoved(
  after: Equation,
  survivorId: NodeId,
  oldParentId: NodeId,
): { id: NodeId; from: NodeId; to: NodeId }[] {
  if (survivorId === oldParentId) return [];
  const newParent = findParent(after, survivorId);
  if (newParent === undefined || newParent.id === oldParentId) return [];
  return [{ id: survivorId, from: oldParentId, to: newParent.id }];
}
