import {
  cloneFresh,
  findById,
  int,
  neg,
  product,
  rebuildNary,
  replaceNode,
  type Equation,
  type Expr,
  type NodeId,
  type Sum,
} from "../expr.js";
import {
  idSetDiff,
  RulePreconditionViolation,
  type Location,
  type Rule,
  type RuleApplication,
} from "../rule.js";

export interface SplitTermParams {
  /** A direct child of the Sum at `location` with an integer coefficient. */
  readonly termId: NodeId;
  /** Coefficient of the first part; the second part gets (coeff − first). */
  readonly first: bigint;
}

/**
 * A term read as coeff·body: the integer literal factor (sign folded in from
 * a wrapping Neg) and the remaining factors. A bare literal has empty body;
 * a term with no literal factor has coefficient 1. Shared with move
 * enumeration, which uses it to spot the a·B² + b·B + c trinomial pattern.
 */
export function coeffAndBody(term: Expr): { coeff: bigint; body: readonly Expr[] } {
  if (term.kind === "neg") {
    const inner = coeffAndBody(term.child);
    return { coeff: -inner.coeff, body: inner.body };
  }
  if (term.kind === "int") return { coeff: term.value, body: [] };
  if (term.kind === "product") {
    const lit = term.children.find((c) => c.kind === "int");
    if (lit !== undefined && lit.kind === "int") {
      return { coeff: lit.value, body: term.children.filter((c) => c.id !== lit.id) };
    }
    const nlit = term.children.find((c) => c.kind === "neg" && c.child.kind === "int");
    if (nlit !== undefined && nlit.kind === "neg" && nlit.child.kind === "int") {
      return { coeff: -nlit.child.value, body: term.children.filter((c) => c.id !== nlit.id) };
    }
    return { coeff: 1n, body: term.children };
  }
  return { coeff: 1n, body: [term] };
}

/** coeff·body as a canonical term (Neg outside, no 1· prefix). */
export function termFromCoeff(coeff: bigint, body: readonly Expr[]): Expr {
  const mag = coeff < 0n ? -coeff : coeff;
  const core = mag === 1n ? product([...body]) : product([int(mag), ...body]);
  return coeff < 0n ? neg(core) : core;
}

function resolve(
  tree: Equation,
  location: Location,
  params: SplitTermParams,
): { sum: Sum; term: Expr; coeff: bigint; body: readonly Expr[] } | undefined {
  if (typeof params.first !== "bigint") return undefined;
  const node = findById(tree, location);
  if (node === undefined || node.kind !== "sum") return undefined;
  const term = node.children.find((c) => c.id === params.termId);
  if (term === undefined) return undefined;
  const { coeff, body } = coeffAndBody(term);
  // Splitting a bare literal is combine-integers' inverse, not this rule;
  // zero parts would plant 0·x noise.
  if (body.length === 0) return undefined;
  if (params.first === 0n || params.first === coeff) return undefined;
  return { sum: node, term, coeff, body };
}

/**
 * Split one integer-coefficient term of a Sum into two adjacent parts —
 * the inverse of factor-out + combine-integers, and the step that unlocks
 * factoring by grouping:
 *   −6x ~> −3x + −3x        x ~> 3x + −2x        5x ~> 2x + 3x
 * An exact identity: emits nothing. The first part keeps the original body
 * nodes (and so their ids); the second part's body is a fresh clone.
 */
export const splitTerm: Rule<SplitTermParams> = {
  id: "split-term",
  description: "Split an integer-coefficient term into two parts whose coefficients sum to it.",

  precondition(judgment, location, params) {
    return resolve(judgment.equation, location, params) !== undefined;
  },

  apply(judgment, location, params): RuleApplication {
    const tree = judgment.equation;
    const r = resolve(tree, location, params);
    if (r === undefined) {
      throw new RulePreconditionViolation(
        this.id,
        "term is not an integer-coefficient child of this sum, or the split is degenerate",
      );
    }
    const firstPart = termFromCoeff(params.first, r.body);
    const secondPart = termFromCoeff(r.coeff - params.first, r.body.map(cloneFresh));
    const children = r.sum.children.flatMap((c) =>
      c.id === params.termId ? [firstPart, secondPart] : [c],
    );
    // The sum GROWS, so it survives as a Sum with its id; no splice repair.
    const rebuilt = rebuildNary(r.sum, children);
    const tree2 = replaceNode(tree, r.sum.id, rebuilt);
    return {
      equation: tree2,
      emits: [],
      diff: {
        ...idSetDiff(tree, tree2),
        merged: [],
        moved: [],
      },
    };
  },
};
