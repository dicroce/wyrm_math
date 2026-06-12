/**
 * fast-check generators and shared assertion helpers for the property tests.
 * Everything here builds trees exclusively through the smart constructors, so
 * generated trees satisfy the structural invariants by construction.
 */
import fc from "fast-check";
import { expect } from "vitest";
import {
  childrenOf,
  envSatisfiesAssumptions,
  equation,
  fraction,
  int,
  neg,
  pow,
  product,
  sqrt,
  sum,
  truthValue,
  variable,
  Rational,
  type Env,
  type Equation,
  type Expr,
  type Judgment,
  type Node,
} from "../src/index.js";

export const VAR_POOL = ["x", "y", "z"] as const;

const arbLeaf: fc.Arbitrary<Expr> = fc.oneof(
  { arbitrary: fc.integer({ min: -9, max: 9 }).map(int), weight: 2 },
  { arbitrary: fc.constantFrom(...VAR_POOL).map(variable), weight: 2 },
);

function arbExprDepth(depth: number): fc.Arbitrary<Expr> {
  if (depth <= 0) return arbLeaf;
  const sub = arbExprDepth(depth - 1);
  return fc.oneof(
    { arbitrary: arbLeaf, weight: 4 },
    {
      arbitrary: fc.array(sub, { minLength: 2, maxLength: 4 }).map(sum),
      weight: 2,
    },
    {
      arbitrary: fc.array(sub, { minLength: 2, maxLength: 3 }).map(product),
      weight: 2,
    },
    { arbitrary: sub.map(neg), weight: 1 },
    {
      arbitrary: fc
        .tuple(
          fc.array(sub, { minLength: 1, maxLength: 2 }),
          fc.array(sub, { minLength: 1, maxLength: 2 }),
        )
        .map(([n, d]) => fraction(n, d)),
      weight: 1,
    },
    {
      // Exponents stay small non-negative integer literals so that exact
      // rational evaluation is always possible.
      arbitrary: fc
        .tuple(sub, fc.integer({ min: 0, max: 3 }))
        .map(([b, e]) => pow(b, int(e))),
      weight: 1,
    },
    {
      // Radicals are mostly inexact under random substitution (those sample
      // points evaluate as undefined and are skipped), but they exercise
      // structure, ids, layout, and cloning everywhere.
      arbitrary: sub.map(sqrt),
      weight: 1,
    },
  );
}

export const arbExpr: fc.Arbitrary<Expr> = arbExprDepth(3);

export const arbEquation: fc.Arbitrary<Equation> = fc
  .tuple(arbExpr, arbExpr)
  .map(([lhs, rhs]) => equation(lhs, rhs));

export const arbRational: fc.Arbitrary<Rational> = fc
  .tuple(fc.integer({ min: -9, max: 9 }), fc.integer({ min: 1, max: 9 }))
  .map(([n, d]) => new Rational(BigInt(n), BigInt(d)));

/** Assignment for every variable in the pool. */
export const arbEnv: fc.Arbitrary<Env> = fc
  .tuple(arbRational, arbRational, arbRational)
  .map(([x, y, z]) => new Map([["x", x], ["y", y], ["z", z]]));

/** A batch of sample points for solution-set comparison. */
export const arbEnvs: fc.Arbitrary<Env[]> = fc.array(arbEnv, {
  minLength: 10,
  maxLength: 20,
});

/**
 * THE rule-soundness property: at every sample point where both equations are
 * defined, their truth values agree — i.e. the rewrite preserved the solution
 * set. Sample points where either side is undefined (division by zero) are
 * skipped.
 */
export function assertSolutionSetPreserved(
  before: Equation,
  after: Equation,
  envs: readonly Env[],
): void {
  for (const env of envs) {
    const tb = truthValue(before, env);
    const ta = truthValue(after, env);
    if (tb === undefined || ta === undefined) continue;
    expect(ta, `truth value changed under ${[...env].map(([k, v]) => `${k}=${v}`).join(", ")}`).toBe(tb);
  }
}

/**
 * The CONDITIONAL form of the soundness property: rejection-sample the
 * substitutions down to those satisfying the result judgment's Restrictions
 * and Pinned values, and require truth preservation only there. This is the
 * revised core invariant: every reachable state is equivalent to the original
 * GIVEN its assumption set.
 */
export function assertConditionallyPreserved(
  before: Equation,
  after: Judgment,
  envs: readonly Env[],
): void {
  assertSolutionSetPreserved(
    before,
    after.equation,
    envs.filter((env) => envSatisfiesAssumptions(after, env)),
  );
}

/**
 * Strict identity of two subtrees: same ids, same structure, same order.
 * Used to assert untouched subtrees survive a rule application byte-for-byte.
 */
export function subtreeIdenticalWithIds(a: Node, b: Node): boolean {
  if (a.kind !== b.kind || a.id !== b.id) return false;
  if (a.kind === "int" && a.value !== (b as typeof a).value) return false;
  if (a.kind === "var" && a.name !== (b as typeof a).name) return false;
  const ac = childrenOf(a);
  const bc = childrenOf(b);
  if (ac.length !== bc.length) return false;
  return ac.every((c, i) => subtreeIdenticalWithIds(c, bc[i]!));
}

/**
 * Embeds a sum into an equation in one of several shapes so rules get
 * exercised at depth, not just at the top of a side. Returns the equation;
 * the sum keeps its id wherever it lands.
 */
export type Wrap = "top" | "neg" | "product" | "fraction";
export const arbWrap: fc.Arbitrary<Wrap> = fc.constantFrom(
  "top",
  "neg",
  "product",
  "fraction",
);

export function embed(
  target: Expr,
  wrap: Wrap,
  other: Expr,
  targetOnLhs: boolean,
): Equation {
  let side: Expr;
  switch (wrap) {
    case "top":
      side = target;
      break;
    case "neg":
      side = neg(target);
      break;
    case "product":
      side = product([target, int(3)]);
      break;
    case "fraction":
      // Fraction lists spread direct Product elements (ctor invariant), so a
      // Product target rides inside a Neg to stay intact at depth.
      side = fraction([target.kind === "product" ? neg(target) : target], [int(5)]);
      break;
  }
  return targetOnLhs ? equation(side, other) : equation(other, side);
}
