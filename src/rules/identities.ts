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
  rebuildNary,
  replaceTermRespectingInvariants,
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
