/**
 * Identity cleanup taps: tiny, exactly-preserving rules that clear the
 * residue other moves leave behind (a stranded 0 in a sum, a 1 in a
 * product, x^1, x^0). All are tap gestures — no drop target.
 *
 * Note on definedness: like additive-cancellation, these can erase a
 * subexpression's undefinedness hole (x^0 ~> 1 is defined even where x is
 * not). The engine-wide soundness contract is truth-where-both-defined,
 * which these preserve exactly.
 */
import {
  findById,
  int,
  neg,
  rebuildNary,
  replaceTermRespectingInvariants,
  sum,
  type Equation,
  type Expr,
  type NodeId,
} from "../expr.js";
import {
  idSetDiff,
  RulePreconditionViolation,
  survivorMoved,
  type Location,
  type Rule,
  type RuleApplication,
} from "../rule.js";
import { literalValue } from "./combineIntegers.js";

export interface DropTermParams {
  readonly termId: NodeId;
}

function dropChild(
  tree: Equation,
  location: Location,
  termId: NodeId,
  kind: "sum" | "product",
): { equation: Equation; removedFrom: NodeId; rebuiltId: NodeId } | undefined {
  const node = findById(tree, location);
  if (node === undefined || node.kind !== kind) return undefined;
  if (!node.children.some((c) => c.id === termId)) return undefined;
  const rebuilt = rebuildNary(node, node.children.filter((c) => c.id !== termId));
  return {
    equation: replaceTermRespectingInvariants(tree, node.id, rebuilt),
    removedFrom: node.id,
    rebuiltId: rebuilt.id,
  };
}

/** x + 0 ~> x (also accepts the canonical −0, Neg(Integer 0)). */
export const dropZeroTerm: Rule<DropTermParams> = {
  id: "drop-zero-term",
  description: "Remove a zero term from a sum.",

  precondition(judgment, location, params) {
    const node = findById(judgment.equation, location);
    if (node === undefined || node.kind !== "sum") return false;
    const term = node.children.find((c) => c.id === params.termId);
    return term !== undefined && literalValue(term) === 0n;
  },

  apply(judgment, location, params): RuleApplication {
    if (!this.precondition(judgment, location, params)) {
      throw new RulePreconditionViolation(this.id, "term is not a literal zero in this sum");
    }
    const r = dropChild(judgment.equation, location, params.termId, "sum")!;
    return {
      equation: r.equation,
      emits: [],
      diff: {
        ...idSetDiff(judgment.equation, r.equation),
        merged: [],
        moved: survivorMoved(r.equation, r.rebuiltId, r.removedFrom),
      },
    };
  },
};

/** x · 1 ~> x (strictly the literal 1; −1 is not an identity). */
export const dropOneFactor: Rule<DropTermParams> = {
  id: "drop-one-factor",
  description: "Remove a factor of 1 from a product.",

  precondition(judgment, location, params) {
    const node = findById(judgment.equation, location);
    if (node === undefined || node.kind !== "product") return false;
    const term = node.children.find((c) => c.id === params.termId);
    return term !== undefined && term.kind === "int" && term.value === 1n;
  },

  apply(judgment, location, params): RuleApplication {
    if (!this.precondition(judgment, location, params)) {
      throw new RulePreconditionViolation(this.id, "factor is not the literal 1");
    }
    const r = dropChild(judgment.equation, location, params.termId, "product")!;
    return {
      equation: r.equation,
      emits: [],
      diff: {
        ...idSetDiff(judgment.equation, r.equation),
        merged: [],
        moved: survivorMoved(r.equation, r.rebuiltId, r.removedFrom),
      },
    };
  },
};

function powWithLiteralExp(tree: Equation, location: Location, value: bigint) {
  const node = findById(tree, location);
  if (node === undefined || node.kind !== "pow") return undefined;
  if (node.exp.kind !== "int" || node.exp.value !== value) return undefined;
  return node;
}

/** x^1 ~> x; the base survives by identity. */
export const powerOne: Rule<Record<string, never>> = {
  id: "power-one",
  description: "Unwrap a first power.",

  precondition(judgment, location, _params) {
    return powWithLiteralExp(judgment.equation, location, 1n) !== undefined;
  },

  apply(judgment, location, _params): RuleApplication {
    const tree = judgment.equation;
    const node = powWithLiteralExp(tree, location, 1n);
    if (node === undefined) {
      throw new RulePreconditionViolation(this.id, "location is not a power with exponent 1");
    }
    const tree2 = replaceTermRespectingInvariants(tree, node.id, node.base);
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

/** x^0 ~> 1 (0^0 = 1 under the exact evaluator). */
export const powerZero: Rule<Record<string, never>> = {
  id: "power-zero",
  description: "Collapse a zeroth power to 1.",

  precondition(judgment, location, _params) {
    return powWithLiteralExp(judgment.equation, location, 0n) !== undefined;
  },

  apply(judgment, location, _params): RuleApplication {
    const tree = judgment.equation;
    const node = powWithLiteralExp(tree, location, 0n);
    if (node === undefined) {
      throw new RulePreconditionViolation(this.id, "location is not a power with exponent 0");
    }
    const one = int(1) as Expr;
    const tree2 = replaceTermRespectingInvariants(tree, node.id, one);
    return {
      equation: tree2,
      emits: [],
      diff: {
        ...idSetDiff(tree, tree2),
        merged: [{ sources: [node.id], target: one.id }],
        moved: [],
      },
    };
  },
};

/** 0 · x ~> 0: a product with a literal-zero factor is zero. (Unconditionally
 *  exact — 0·anything is 0 — like the other identity cleanups.) Pairs with
 *  drop-zero-term to clear a vanished term, e.g. after 2x + (−2)x folds to 0x. */
export const multiplyByZero: Rule<Record<string, never>> = {
  id: "multiply-by-zero",
  description: "A product with a zero factor is zero.",

  precondition(judgment, location, _params) {
    const node = findById(judgment.equation, location);
    return (
      node !== undefined &&
      node.kind === "product" &&
      node.children.some((c) => literalValue(c) === 0n)
    );
  },

  apply(judgment, location, _params): RuleApplication {
    const tree = judgment.equation;
    const node = findById(tree, location);
    if (
      node === undefined ||
      node.kind !== "product" ||
      !node.children.some((c) => literalValue(c) === 0n)
    ) {
      throw new RulePreconditionViolation(this.id, "not a product with a zero factor");
    }
    const zero = int(0);
    const tree2 = replaceTermRespectingInvariants(tree, node.id, zero);
    return {
      equation: tree2,
      emits: [],
      diff: {
        ...idSetDiff(tree, tree2),
        merged: [{ sources: node.children.map((c) => c.id), target: zero.id }],
        moved: [],
      },
    };
  },
};

/**
 * Pull a single negative factor out in front of a product: (−20)·x → −(20·x),
 * 20·(−y) → −(20·y). An exact identity (−a·b = −(a·b)) that tidies the clunky
 * parenthesized form into standard notation. Gated to products with EXACTLY one
 * negative factor (two cancel via cancel-negatives) AND at least one non-numeric
 * factor — a pure numeric product like 4·(−8) is evaluated by
 * combine-integer-factors instead, which outranks this on a tap.
 */
const isNumericLit = (e: Expr): boolean =>
  e.kind === "int" || (e.kind === "neg" && e.child.kind === "int");

export const pullOutNegative: Rule<Record<string, never>> = {
  id: "pull-out-negative",
  description: "Pull the negative sign out in front of the product.",

  precondition(judgment, location, _params) {
    const node = findById(judgment.equation, location);
    if (node === undefined || node.kind !== "product") return false;
    const negCount = node.children.filter((c) => c.kind === "neg").length;
    return negCount === 1 && node.children.some((c) => !isNumericLit(c));
  },

  apply(judgment, location, _params): RuleApplication {
    if (!this.precondition(judgment, location, _params)) {
      throw new RulePreconditionViolation(this.id, "needs exactly one negative factor and a non-numeric factor");
    }
    const tree = judgment.equation;
    const node = findById(tree, location);
    if (node === undefined || node.kind !== "product") {
      throw new RulePreconditionViolation(this.id, "unreachable");
    }
    const negIndex = node.children.findIndex((c) => c.kind === "neg");
    const negChild = node.children[negIndex]!;
    if (negChild.kind !== "neg") throw new RulePreconditionViolation(this.id, "unreachable");
    // Un-negate that one factor, rebuild the product (keeps its id), wrap in Neg.
    const children = node.children.map((c, i) => (i === negIndex ? negChild.child : c));
    const negated = neg(rebuildNary(node, children));
    const tree2 = replaceTermRespectingInvariants(tree, node.id, negated);
    return {
      equation: tree2,
      emits: [],
      diff: { ...idSetDiff(tree, tree2), merged: [], moved: [] },
    };
  },
};

/** (−a)·(−b) ~> a·b: two negative factors in a product cancel. Exact and
 *  unconditional. Common after distributing a negative over a difference, e.g.
 *  (−2)(x − y) → (−2)x + (−2)(−y), where the second term is (−2)(−y) → 2y. */
export const cancelNegatives: Rule<Record<string, never>> = {
  id: "cancel-negatives",
  description: "Two negative factors in a product make a positive.",

  precondition(judgment, location, _params) {
    const node = findById(judgment.equation, location);
    return (
      node !== undefined &&
      node.kind === "product" &&
      node.children.filter((c) => c.kind === "neg").length >= 2
    );
  },

  apply(judgment, location, _params): RuleApplication {
    const tree = judgment.equation;
    const node = findById(tree, location);
    if (
      node === undefined ||
      node.kind !== "product" ||
      node.children.filter((c) => c.kind === "neg").length < 2
    ) {
      throw new RulePreconditionViolation(this.id, "needs two negative factors");
    }
    let flipped = 0;
    const children = node.children.map((c) => {
      if (c.kind === "neg" && flipped < 2) {
        flipped++;
        return c.child; // un-negate; two sign flips cancel
      }
      return c;
    });
    const rebuilt = rebuildNary(node, children);
    const tree2 = replaceTermRespectingInvariants(tree, node.id, rebuilt);
    return {
      equation: tree2,
      emits: [],
      diff: { ...idSetDiff(tree, tree2), merged: [], moved: [] },
    };
  },
};

/** −(a + b) ~> −a + (−b): distribute a negation across a sum. Exact and
 *  unconditional. Needed by elimination's subtract step, where α·A + (−1)·B
 *  produces −(B's sum) — e.g. (x + y) − (x − y) has the −(x − y) term. */
export const distributeNegation: Rule<Record<string, never>> = {
  id: "distribute-negation",
  description: "Distribute a negative across a sum: −(a + b) = −a − b.",

  precondition(judgment, location, _params) {
    const node = findById(judgment.equation, location);
    return node !== undefined && node.kind === "neg" && node.child.kind === "sum";
  },

  apply(judgment, location, _params): RuleApplication {
    const tree = judgment.equation;
    const node = findById(tree, location);
    if (node === undefined || node.kind !== "neg" || node.child.kind !== "sum") {
      throw new RulePreconditionViolation(this.id, "not a negation of a sum");
    }
    // neg() collapses double negation, so −(x − y) becomes −x + y cleanly.
    const distributed = sum(node.child.children.map((c) => neg(c)));
    const tree2 = replaceTermRespectingInvariants(tree, node.id, distributed);
    return {
      equation: tree2,
      emits: [],
      diff: { ...idSetDiff(tree, tree2), merged: [], moved: [] },
    };
  },
};
