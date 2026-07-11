/**
 * Random practice-problem generator.
 *
 * Problems are built BACKWARD from a chosen integer solution: pick the answer
 * first, then assemble an equation around it. This guarantees three things the
 * "generate then hope" approach can't — the problem is solvable, the answer is
 * clean, and difficulty is exactly the templates and coefficient ranges we draw
 * from. Every generated problem returns its solution(s), so a practice loop can
 * check the learner and serve the next one.
 *
 * The engine stays pure: randomness is an injected `Rng` (a `() => number` in
 * [0, 1)), never ambient `Math.random`. Callers pass `Math.random` (or a seeded
 * PRNG in tests).
 */
import { type Equation } from "./expr.js";
import { parseEquation } from "./parse.js";
import { Rational } from "./rational.js";

export type Difficulty = "easy" | "medium" | "hard";

export type ProblemTopic =
  | "linear-one-step"
  | "linear-two-step"
  | "linear-both-sides"
  | "quadratic";

export interface ProblemSpec {
  readonly topic: ProblemTopic;
  readonly difficulty: Difficulty;
}

export interface GeneratedProblem {
  readonly equation: Equation;
  /** The intended value(s) of the variable — one for linear, up to two for
   *  quadratics (distinct roots deduped). */
  readonly solutions: readonly Rational[];
  readonly topic: ProblemTopic;
  readonly difficulty: Difficulty;
}

/** Uniform random in [0, 1) — inject `Math.random` or a seeded PRNG. */
export type Rng = () => number;

/** Topics with display labels, for building a picker. */
export const PROBLEM_TOPICS: readonly { readonly id: ProblemTopic; readonly label: string }[] = [
  { id: "linear-one-step", label: "One-step" },
  { id: "linear-two-step", label: "Two-step" },
  { id: "linear-both-sides", label: "Variables on both sides" },
  { id: "quadratic", label: "Quadratic" },
];

export const DIFFICULTIES: readonly Difficulty[] = ["easy", "medium", "hard"];

interface Range {
  readonly coeffMax: number; // largest coefficient magnitude
  readonly solMax: number; // largest |solution| / |root|
  readonly allowNeg: boolean; // negatives in coefficients and answers
}

const RANGES: Record<Difficulty, Range> = {
  easy: { coeffMax: 5, solMax: 9, allowNeg: false },
  medium: { coeffMax: 9, solMax: 9, allowNeg: true },
  hard: { coeffMax: 12, solMax: 15, allowNeg: true },
};

// --- random integer helpers (selection only — never correctness arithmetic) ---

/** Integer in [min, max] inclusive. */
function randInt(rng: Rng, min: number, max: number): number {
  return min + Math.floor(rng() * (max - min + 1));
}

/** A nonzero integer with magnitude in [minMag, maxMag], sign per allowNeg. */
function signedInt(rng: Rng, minMag: number, maxMag: number, allowNeg: boolean): number {
  const mag = randInt(rng, Math.max(1, minMag), maxMag);
  return allowNeg && rng() < 0.5 ? -mag : mag;
}

// --- equation string assembly ---
// Building a natural string and re-parsing sidesteps hand-canonicalizing the
// AST (subtraction is Sum+Neg, negative literals, dropped 1-coefficients …);
// parseEquation produces exactly the tree a typed problem would.

type Kind = "x^2" | "x" | "";
interface Term {
  readonly c: number;
  readonly v: Kind;
}

function renderTerms(terms: readonly Term[]): string {
  const nz = terms.filter((t) => t.c !== 0);
  if (nz.length === 0) return "0";
  return nz
    .map((t, i) => {
      const mag = Math.abs(t.c);
      const body = t.v !== "" && mag === 1 ? t.v : `${mag}${t.v}`;
      if (i === 0) return t.c < 0 ? `-${body}` : body;
      return t.c < 0 ? ` - ${body}` : ` + ${body}`;
    })
    .join("");
}

interface Built {
  readonly lhs: readonly Term[];
  readonly rhs: readonly Term[];
  readonly solutions: readonly number[];
}

// --- templates (backward from the answer) ---

function linearOneStep(rng: Rng, r: Range): Built {
  const s = signedInt(rng, 1, r.solMax, r.allowNeg);
  if (rng() < 0.5) {
    // additive: x + b = s + b
    const b = signedInt(rng, 1, r.coeffMax, r.allowNeg);
    return { lhs: [{ c: 1, v: "x" }, { c: b, v: "" }], rhs: [{ c: s + b, v: "" }], solutions: [s] };
  }
  // multiplicative: a·x = a·s  (|a| ≥ 2 so it's a real step)
  const a = signedInt(rng, 2, r.coeffMax, r.allowNeg);
  return { lhs: [{ c: a, v: "x" }], rhs: [{ c: a * s, v: "" }], solutions: [s] };
}

function linearTwoStep(rng: Rng, r: Range): Built {
  const s = signedInt(rng, 1, r.solMax, r.allowNeg);
  const a = signedInt(rng, 2, r.coeffMax, r.allowNeg);
  const b = signedInt(rng, 1, r.coeffMax, r.allowNeg);
  return {
    lhs: [{ c: a, v: "x" }, { c: b, v: "" }],
    rhs: [{ c: a * s + b, v: "" }],
    solutions: [s],
  };
}

function linearBothSides(rng: Rng, r: Range): Built {
  const s = signedInt(rng, 1, r.solMax, r.allowNeg);
  const a = signedInt(rng, 2, r.coeffMax, r.allowNeg);
  let c = signedInt(rng, 1, r.coeffMax, r.allowNeg);
  while (c === a) c = signedInt(rng, 1, r.coeffMax, r.allowNeg); // a ≠ c or x cancels out
  const b = signedInt(rng, 1, r.coeffMax, r.allowNeg);
  const d = a * s + b - c * s; // a·s + b = c·s + d
  return {
    lhs: [{ c: a, v: "x" }, { c: b, v: "" }],
    rhs: [{ c: c, v: "x" }, { c: d, v: "" }],
    solutions: [s],
  };
}

function quadratic(rng: Rng, r: Range): Built {
  const rootMax = Math.min(r.solMax, 9);
  const r1 = signedInt(rng, 1, rootMax, r.allowNeg);
  const r2 = signedInt(rng, 1, rootMax, r.allowNeg);
  // (x − r1)(x − r2) = x² − (r1+r2)x + r1·r2
  return {
    lhs: [
      { c: 1, v: "x^2" },
      { c: -(r1 + r2), v: "x" },
      { c: r1 * r2, v: "" },
    ],
    rhs: [{ c: 0, v: "" }],
    solutions: r1 === r2 ? [r1] : [r1, r2],
  };
}

function build(topic: ProblemTopic, rng: Rng, r: Range): Built {
  switch (topic) {
    case "linear-one-step":
      return linearOneStep(rng, r);
    case "linear-two-step":
      return linearTwoStep(rng, r);
    case "linear-both-sides":
      return linearBothSides(rng, r);
    case "quadratic":
      return quadratic(rng, r);
  }
}

/**
 * Generate a random problem for the given topic and difficulty. The returned
 * equation is guaranteed well-formed and solvable, with `solutions` its exact
 * integer answer(s). `rng` supplies randomness — pass `Math.random` in the app,
 * a seeded PRNG in tests.
 */
export function generateProblem(spec: ProblemSpec, rng: Rng): GeneratedProblem {
  const built = build(spec.topic, rng, RANGES[spec.difficulty]);
  const source = `${renderTerms(built.lhs)} = ${renderTerms(built.rhs)}`;
  return {
    equation: parseEquation(source),
    solutions: built.solutions.map((n) => new Rational(BigInt(n))),
    topic: spec.topic,
    difficulty: spec.difficulty,
  };
}
