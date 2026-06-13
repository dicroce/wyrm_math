import {
  findById,
  fraction,
  rebuildNary,
  replaceNode,
  replaceTermRespectingInvariants,
  type Equation,
  type Expr,
  type Fraction,
  type NodeId,
  type Product,
} from "../expr.js";
import {
  idSetDiff,
  RulePreconditionViolation,
  survivorMoved,
  type Location,
  type Rule,
  type RuleApplication,
} from "../rule.js";
import { coeffAndBody, termFromCoeff } from "./splitTerm.js";

export interface CombineIntegerFactorsParams {
  /**
   * Two factors of the Product at `location`, or two elements of the SAME
   * factor list (num or den) of the Fraction there (the lists are implicit
   * products). At least one must be a bare integer literal — it is absorbed
   * into the other factor's integer coefficient.
   */
  readonly termA: NodeId;
  readonly termB: NodeId;
}

interface Site {
  readonly container: Product | Fraction;
  /** The bare integer literal that dissolves into the target. */
  readonly multId: NodeId;
  /** The factor that survives, carrying the merged coefficient. */
  readonly targetId: NodeId;
  readonly resultCoeff: bigint;
  /** The target's non-coefficient factors, by identity. */
  readonly targetRest: readonly Expr[];
}

/** A bare integer literal (int or canonical Neg(int)) has an empty body. */
function asBareInteger(e: Expr): bigint | undefined {
  const { coeff, body } = coeffAndBody(e);
  return body.length === 0 ? coeff : undefined;
}

function resolve(
  tree: Equation,
  location: Location,
  params: CombineIntegerFactorsParams,
): Site | undefined {
  const node = findById(tree, location);
  if (node === undefined || (node.kind !== "product" && node.kind !== "fraction")) {
    return undefined;
  }
  if (params.termA === params.termB) return undefined;
  const lists = node.kind === "product" ? [node.children] : [node.num, node.den];
  // Ids are unique, so finding both terms in one list means the SAME list —
  // a num/den integer pair is reduce-integer-fraction territory.
  for (const list of lists) {
    const termA = list.find((c) => c.id === params.termA);
    const termB = list.find((c) => c.id === params.termB);
    if (termA === undefined || termB === undefined) continue;
    const aInt = asBareInteger(termA);
    const bInt = asBareInteger(termB);
    // Pick the multiplier (a bare integer) and the target. When BOTH are
    // bare integers (the classic fold), keep the result in termA's slot to
    // preserve the long-standing 3·2·x ~> 6x animation/position.
    let multId: NodeId;
    let target: Expr;
    let multVal: bigint;
    if (aInt !== undefined && bInt !== undefined) {
      multId = termB.id;
      target = termA;
      multVal = bInt;
    } else if (aInt !== undefined) {
      multId = termA.id;
      target = termB;
      multVal = aInt;
    } else if (bInt !== undefined) {
      multId = termB.id;
      target = termA;
      multVal = bInt;
    } else {
      return undefined;
    }
    const { coeff, body } = coeffAndBody(target);
    // Fire only where it actually simplifies: two integers fold (empty body),
    // a real coefficient absorbs the integer (coeff ≠ 1), or a ±1 multiplier
    // folds its sign in (x·(−1) ~> −x). A bare 3·x ~> 3x is a no-op — skip it.
    if (body.length !== 0 && coeff === 1n && multVal !== -1n && multVal !== 1n) {
      return undefined;
    }
    return {
      container: node,
      multId,
      targetId: target.id,
      resultCoeff: multVal * coeff,
      targetRest: body,
    };
  }
  return undefined;
}

/**
 * Absorb a bare integer factor into another factor of the same product (or
 * fraction list), multiplying it into that factor's coefficient — the
 * multiplicative twin of combine-integers, generalized to reach a coefficient
 * through a Neg wrapper:
 *   3 · 2 · x  ~>  6x        −3 · −2x  ~>  6x        x · (−1)  ~>  −x
 */
export const combineIntegerFactors: Rule<CombineIntegerFactorsParams> = {
  id: "combine-integer-factors",
  description: "Absorb an integer factor into another factor's coefficient (product or fraction list).",

  precondition(judgment, location, params) {
    return resolve(judgment.equation, location, params) !== undefined;
  },

  apply(judgment, location, params): RuleApplication {
    const tree = judgment.equation;
    const r = resolve(tree, location, params);
    if (r === undefined) {
      throw new RulePreconditionViolation(
        this.id,
        "neither factor is a bare integer to absorb, or the fold is a no-op",
      );
    }
    const folded = termFromCoeff(r.resultCoeff, r.targetRest);
    // The folded factor takes the target's slot; the multiplier disappears.
    const mergeInto = (list: readonly Expr[]): Expr[] =>
      list
        .filter((c) => c.id !== r.multId)
        .map((c) => (c.id === r.targetId ? folded : c));
    let tree2: Equation;
    let moved: RuleApplication["diff"]["moved"];
    if (r.container.kind === "product") {
      const rebuilt = rebuildNary(r.container, mergeInto(r.container.children));
      tree2 = replaceTermRespectingInvariants(tree, r.container.id, rebuilt);
      moved = survivorMoved(tree2, rebuilt.id, r.container.id);
    } else {
      // The bar always survives (two list elements became one, never zero);
      // keep the fraction's id.
      const rebuilt: Expr = {
        ...fraction(mergeInto(r.container.num), mergeInto(r.container.den)),
        id: r.container.id,
      };
      tree2 = replaceNode(tree, r.container.id, rebuilt);
      moved = [];
    }
    // If the product collapsed under a Neg parent, the double-negation repair
    // swallowed `folded`'s root; merge onto its surviving child.
    const mergeTarget =
      findById(tree2, folded.id) !== undefined
        ? folded.id
        : folded.kind === "neg"
          ? folded.child.id
          : folded.id;
    return {
      equation: tree2,
      emits: [],
      diff: {
        ...idSetDiff(tree, tree2),
        merged: [{ sources: [r.multId, r.targetId], target: mergeTarget }],
        moved,
      },
    };
  },
};
