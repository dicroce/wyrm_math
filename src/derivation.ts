import {
  AssumptionConflict,
  checkSolution as checkSolutionJudgment,
  dischargePass,
  mkJudgment,
  mkPinned,
  type CheckVerdict,
  type Judgment,
} from "./assumptions.js";
import type { Env } from "./eval.js";
import type { Equation } from "./expr.js";
import type { Rational } from "./rational.js";
import {
  applyBranchingRule,
  applyRule,
  type AnimationDiff,
  type BranchingRule,
  type Location,
  type Rule,
} from "./rule.js";

let nodeCounter = 0;
function freshNodeId(): string {
  return `s${++nodeCounter}`;
}

interface NodeBase {
  readonly id: string;
  readonly parentId: string | null;
  /** The full state AFTER this operation. */
  readonly judgment: Judgment;
  /** Append-only; mutated only by Derivation.commit. */
  readonly children: string[];
}

/**
 * One committed operation in the derivation tree. Rule applications are the
 * common case; pins, case-split branches, and solution checks are first-class
 * log entries too, so the whole story of a derivation is replayable and every
 * assumption's origin step is a real node.
 */
export type DerivationNode = NodeBase &
  (
    | { readonly kind: "root" }
    | {
        readonly kind: "rule";
        readonly ruleId: string;
        readonly location: Location;
        readonly params: unknown;
        readonly diff: AnimationDiff;
        readonly viaCaseSplit?: boolean;
      }
    | {
        /** Branch B of a case split: the move was NOT applied; the variable is pinned instead. */
        readonly kind: "case-pin";
        readonly forRuleId: string;
        readonly variable: string;
        readonly value: Rational;
      }
    | {
        /** One arm of a disjunctive rewrite; its siblings are the other arms. */
        readonly kind: "branch";
        readonly ruleId: string;
        readonly location: Location;
        readonly params: unknown;
        readonly label: string;
        readonly diff: AnimationDiff;
      }
    | { readonly kind: "pin"; readonly variable: string; readonly value: Rational }
    | { readonly kind: "unpin"; readonly variable: string }
    | { readonly kind: "check-solution"; readonly candidate: Env; readonly verdict: CheckVerdict }
  );

/**
 * The derivation log: an append-only TREE of judgments. "Current state" is a
 * pointer into the tree; undo moves the pointer to the parent, and applying a
 * new operation while elsewhere simply grows a new branch — abandoned
 * branches stay live and navigable (goto). Nothing is ever rewritten.
 */
export class Derivation {
  private readonly nodes = new Map<string, DerivationNode>();
  readonly rootId: string;
  private currentId: string;

  constructor(initial: Equation | Judgment) {
    const judgment = "assumptions" in initial ? initial : mkJudgment(initial);
    const root: DerivationNode = {
      kind: "root",
      id: freshNodeId(),
      parentId: null,
      judgment,
      children: [],
    };
    this.nodes.set(root.id, root);
    this.rootId = root.id;
    this.currentId = root.id;
  }

  node(id: string): DerivationNode {
    const n = this.nodes.get(id);
    if (n === undefined) throw new Error(`unknown derivation node ${id}`);
    return n;
  }

  get currentNode(): DerivationNode {
    return this.node(this.currentId);
  }

  get current(): Judgment {
    return this.currentNode.judgment;
  }

  childrenOf(id: string): readonly string[] {
    return this.node(id).children;
  }

  /** Nodes from the root to the current pointer, inclusive. */
  get path(): DerivationNode[] {
    const out: DerivationNode[] = [];
    for (let n: DerivationNode | null = this.currentNode; n !== null; ) {
      out.push(n);
      n = n.parentId === null ? null : this.node(n.parentId);
    }
    return out.reverse();
  }

  private commit(node: DerivationNode, moveTo = true): DerivationNode {
    this.nodes.set(node.id, node);
    if (node.parentId !== null) this.node(node.parentId).children.push(node.id);
    if (moveTo) this.currentId = node.id;
    return node;
  }

  /** Apply a rewrite rule at the current pointer; illegal moves throw and leave no node. */
  apply<P>(rule: Rule<P>, location: Location, params: P): DerivationNode {
    const stepId = freshNodeId();
    const { judgment, diff } = applyRule(this.current, rule, location, params, stepId);
    return this.commit({
      kind: "rule",
      id: stepId,
      parentId: this.currentId,
      judgment,
      children: [],
      ruleId: rule.id,
      location,
      params,
      diff,
    });
  }

  canUndo(): boolean {
    return this.currentNode.parentId !== null;
  }

  /** Move the pointer to the parent. The abandoned node stays in the tree. */
  undo(): Judgment {
    const parent = this.currentNode.parentId;
    if (parent === null) throw new Error("nothing to undo");
    this.currentId = parent;
    return this.current;
  }

  canRedo(): boolean {
    return this.currentNode.children.length > 0;
  }

  /** Move to the most recently created child; use goto() to pick a branch. */
  redo(): Judgment {
    const kids = this.currentNode.children;
    if (kids.length === 0) throw new Error("nothing to redo");
    this.currentId = kids[kids.length - 1]!;
    return this.current;
  }

  /** Jump anywhere in the tree — every committed state stays live. */
  goto(id: string): Judgment {
    this.currentId = this.node(id).id;
    return this.current;
  }

  /**
   * User what-if: assume variable = value. Rejected (both directions of the
   * conflict check) when it decidably violates an existing Restriction.
   */
  pinVariable(variable: string, value: Rational): DerivationNode {
    const existing = this.current.assumptions.find(
      (a) => a.kind === "pinned" && a.variable === variable,
    );
    if (existing !== undefined) {
      throw new AssumptionConflict(`${variable} is already pinned`);
    }
    const pin = mkPinned(variable, value, { kind: "user" });
    const { assumptions, conflicts } = dischargePass([
      ...this.current.assumptions,
      pin,
    ]);
    if (conflicts.length > 0) {
      throw new AssumptionConflict(
        `pinning ${variable} = ${value} violates restriction ${conflicts[0]!.id}`,
      );
    }
    return this.commit({
      kind: "pin",
      id: freshNodeId(),
      parentId: this.currentId,
      judgment: { assumptions, equation: this.current.equation },
      children: [],
      variable,
      value,
    });
  }

  /**
   * Remove a user pin. Restrictions that were discharged by this pin become
   * active again (the discharge pass re-decides them). Case-split pins are
   * structural to their branch and cannot be unpinned.
   */
  unpinVariable(variable: string): DerivationNode {
    const pin = this.current.assumptions.find(
      (a) => a.kind === "pinned" && a.variable === variable,
    );
    if (pin === undefined) throw new Error(`${variable} is not pinned`);
    if (pin.origin.kind !== "user") {
      throw new AssumptionConflict(
        `${variable} was pinned by a case split; navigate to another branch instead`,
      );
    }
    const remaining = this.current.assumptions.filter((a) => a !== pin);
    const { assumptions } = dischargePass(remaining);
    return this.commit({
      kind: "unpin",
      id: freshNodeId(),
      parentId: this.currentId,
      judgment: { assumptions, equation: this.current.equation },
      children: [],
      variable,
    });
  }

  /**
   * Apply a DISJUNCTIVE rewrite: all branches are committed as live sibling
   * children (the union of their solution sets equals the original's) and
   * the pointer lands on the first. Navigate the rest via goto.
   */
  applyBranching<P>(
    rule: BranchingRule<P>,
    location: Location,
    params: P,
  ): DerivationNode[] {
    const parentId = this.currentId;
    const stepId = freshNodeId();
    const outcomes = applyBranchingRule(this.current, rule, location, params, stepId);
    const nodes = outcomes.map((o, i) =>
      this.commit(
        {
          kind: "branch",
          id: i === 0 ? stepId : freshNodeId(),
          parentId,
          judgment: o.judgment,
          children: [],
          ruleId: rule.id,
          location,
          params,
          label: o.label,
          diff: o.diff,
        },
        false,
      ),
    );
    this.currentId = nodes[0]!.id;
    return nodes;
  }

  /**
   * Fork the current node on a Restriction-producing move whose restriction
   * targets a bare variable v ≠ c:
   *   - branch A ("restricted") applies the move and carries Restriction(v ≠ c);
   *   - branch B ("pinned") does NOT apply the move and pins v = c instead.
   * Both branches stay live; the pointer moves to branch A.
   */
  caseSplit<P>(
    rule: Rule<P>,
    location: Location,
    params: P,
  ): { restricted: DerivationNode; pinned: DerivationNode } {
    const parentId = this.currentId;
    const parentJudgment = this.current;
    const stepId = freshNodeId();
    const { judgment: judgmentA, diff } = applyRule(
      parentJudgment,
      rule,
      location,
      params,
      stepId,
    );
    const emitted = judgmentA.assumptions.filter(
      (a) =>
        a.kind === "restriction" &&
        a.origin.kind === "rule" &&
        a.origin.stepId === stepId,
    );
    if (emitted.length !== 1 || emitted[0]!.kind !== "restriction") {
      throw new Error("case split requires a move emitting exactly one Restriction");
    }
    const restriction = emitted[0]!;
    if (restriction.expr.kind !== "var") {
      throw new Error(
        "case split currently requires the restriction to target a bare variable",
      );
    }
    const v = restriction.expr.name;
    if (parentJudgment.assumptions.some((a) => a.kind === "pinned" && a.variable === v)) {
      throw new AssumptionConflict(`${v} is already pinned; the split is vacuous`);
    }
    // Validate branch B before committing anything.
    const pin = mkPinned(v, restriction.value, { kind: "case-split", stepId });
    const { assumptions: bAssumptions, conflicts } = dischargePass([
      ...parentJudgment.assumptions,
      pin,
    ]);
    if (conflicts.length > 0) {
      throw new AssumptionConflict(
        `the ${v} = ${restriction.value} branch violates an existing restriction`,
      );
    }
    const restricted = this.commit(
      {
        kind: "rule",
        id: stepId,
        parentId,
        judgment: judgmentA,
        children: [],
        ruleId: rule.id,
        location,
        params,
        diff,
        viaCaseSplit: true,
      },
      false,
    );
    const pinned = this.commit(
      {
        kind: "case-pin",
        id: freshNodeId(),
        parentId,
        judgment: { assumptions: bAssumptions, equation: parentJudgment.equation },
        children: [],
        forRuleId: rule.id,
        variable: v,
        value: restriction.value,
      },
      false,
    );
    this.currentId = restricted.id;
    return { restricted, pinned };
  }

  /**
   * Check a candidate solution against the original equation(s) carried by
   * the judgment's Extensions. Verified candidates discharge the Extensions;
   * extraneous ones are condemned in the log (the node records the verdict)
   * and change nothing else.
   */
  checkSolution(candidate: Env): { verdict: CheckVerdict; node: DerivationNode } {
    const { verdict, judgment } = checkSolutionJudgment(this.current, candidate);
    const node = this.commit({
      kind: "check-solution",
      id: freshNodeId(),
      parentId: this.currentId,
      judgment,
      children: [],
      candidate,
      verdict,
    });
    return { verdict, node };
  }
}
