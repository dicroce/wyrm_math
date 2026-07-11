/**
 * Random practice-problem generator.
 *
 * Problems are built BACKWARD from a chosen integer answer: pick the solution
 * first, then assemble an equation around it. This guarantees the problem is
 * solvable, the answer is clean, and difficulty is exactly the templates and
 * coefficient ranges we draw from. Every problem returns its solution(s) so a
 * practice loop can check the learner and serve the next one.
 *
 * The engine stays pure: randomness is an injected `Rng` (a `() => number` in
 * [0, 1)), never ambient `Math.random`. Callers pass `Math.random` (or a seeded
 * PRNG in tests).
 *
 * Single-variable topics go through `generateProblem`; two-variable systems
 * (two equations) go through `generateSystem`.
 */
import { type Equation } from "./expr.js";
import { truthValue } from "./eval.js";
import { parseEquation } from "./parse.js";
import { gcd, Rational } from "./rational.js";

export type Difficulty = "easy" | "medium" | "hard";

export type ProblemTopic =
  | "linear-one-step"
  | "linear-two-step"
  | "linear-both-sides"
  | "distribution"
  | "fractions"
  | "power"
  | "inequality"
  | "quadratic";

export interface ProblemSpec {
  readonly topic: ProblemTopic;
  readonly difficulty: Difficulty;
}

export interface GeneratedProblem {
  readonly equation: Equation;
  /** Value(s) of the variable that solve it — two for a distinct-root
   *  quadratic; for an inequality, a witness point inside the solution set. */
  readonly solutions: readonly Rational[];
  readonly topic: ProblemTopic;
  readonly difficulty: Difficulty;
}

export interface SystemProblem {
  readonly equations: readonly [Equation, Equation];
  readonly x: Rational;
  readonly y: Rational;
  readonly difficulty: Difficulty;
}

/** Uniform random in [0, 1) — inject `Math.random` or a seeded PRNG. */
export type Rng = () => number;

/** Topics with display labels, for building a picker. */
export const PROBLEM_TOPICS: readonly { readonly id: ProblemTopic; readonly label: string }[] = [
  { id: "linear-one-step", label: "One-step" },
  { id: "linear-two-step", label: "Two-step" },
  { id: "linear-both-sides", label: "Variables on both sides" },
  { id: "distribution", label: "Distribution" },
  { id: "fractions", label: "Fractions" },
  { id: "power", label: "Powers" },
  { id: "inequality", label: "Inequalities" },
  { id: "quadratic", label: "Quadratic" },
];

export const DIFFICULTIES: readonly Difficulty[] = ["easy", "medium", "hard"];

interface Range {
  readonly coeffMax: number;
  readonly solMax: number;
  readonly allowNeg: boolean;
}

const RANGES: Record<Difficulty, Range> = {
  easy: { coeffMax: 5, solMax: 9, allowNeg: false },
  medium: { coeffMax: 9, solMax: 9, allowNeg: true },
  hard: { coeffMax: 12, solMax: 15, allowNeg: true },
};

// --- random integer helpers (selection only — never correctness arithmetic) ---

function randInt(rng: Rng, min: number, max: number): number {
  return min + Math.floor(rng() * (max - min + 1));
}

/** A nonzero integer with magnitude in [minMag, maxMag], sign per allowNeg. */
function signedInt(rng: Rng, minMag: number, maxMag: number, allowNeg: boolean): number {
  const mag = randInt(rng, Math.max(1, minMag), Math.max(Math.max(1, minMag), maxMag));
  return allowNeg && rng() < 0.5 ? -mag : mag;
}

function pick<T>(rng: Rng, arr: readonly T[]): T {
  return arr[Math.floor(rng() * arr.length)]!;
}

// --- equation string assembly ---
// Building a natural string and re-parsing sidesteps hand-canonicalizing the
// AST (subtraction is Sum+Neg, negative literals, dropped 1-coefficients …);
// parseEquation produces exactly the tree a typed problem would.

type Kind = "x^2" | "x" | "y" | "";
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

const num = (c: number): string => renderTerms([{ c, v: "" }]);

interface Built {
  readonly source: string;
  readonly solutions: readonly number[];
}

const R = (n: number): Rational => new Rational(BigInt(n));

// --- single-variable templates (backward from the answer) ---

function linearOneStep(rng: Rng, r: Range): Built {
  const s = signedInt(rng, 1, r.solMax, r.allowNeg);
  if (rng() < 0.5) {
    const b = signedInt(rng, 1, r.coeffMax, r.allowNeg); // x + b = s + b
    return { source: `${renderTerms([{ c: 1, v: "x" }, { c: b, v: "" }])} = ${num(s + b)}`, solutions: [s] };
  }
  const a = signedInt(rng, 2, r.coeffMax, r.allowNeg); // a·x = a·s
  return { source: `${renderTerms([{ c: a, v: "x" }])} = ${num(a * s)}`, solutions: [s] };
}

function linearTwoStep(rng: Rng, r: Range): Built {
  const s = signedInt(rng, 1, r.solMax, r.allowNeg);
  const a = signedInt(rng, 2, r.coeffMax, r.allowNeg);
  const b = signedInt(rng, 1, r.coeffMax, r.allowNeg);
  return {
    source: `${renderTerms([{ c: a, v: "x" }, { c: b, v: "" }])} = ${num(a * s + b)}`,
    solutions: [s],
  };
}

function linearBothSides(rng: Rng, r: Range): Built {
  const s = signedInt(rng, 1, r.solMax, r.allowNeg);
  const a = signedInt(rng, 2, r.coeffMax, r.allowNeg);
  let c = signedInt(rng, 1, r.coeffMax, r.allowNeg);
  while (c === a) c = signedInt(rng, 1, r.coeffMax, r.allowNeg); // a ≠ c or x cancels
  const b = signedInt(rng, 1, r.coeffMax, r.allowNeg);
  const d = a * s + b - c * s;
  return {
    source: `${renderTerms([{ c: a, v: "x" }, { c: b, v: "" }])} = ${renderTerms([{ c, v: "x" }, { c: d, v: "" }])}`,
    solutions: [s],
  };
}

function distribution(rng: Rng, r: Range): Built {
  const s = signedInt(rng, 1, r.solMax, r.allowNeg);
  const a = randInt(rng, 2, r.coeffMax); // positive multiplier, keeps "a(x ± b)" clean
  const b = signedInt(rng, 1, r.coeffMax, r.allowNeg);
  return {
    source: `${a}(${renderTerms([{ c: 1, v: "x" }, { c: b, v: "" }])}) = ${num(a * (s + b))}`,
    solutions: [s],
  };
}

function fractions(rng: Rng, r: Range): Built {
  if (rng() < 0.5) {
    // x/a = q  ⇒  x = a·q
    const a = randInt(rng, 2, Math.min(r.coeffMax, 6));
    const q = signedInt(rng, 1, Math.min(r.solMax, 6), r.allowNeg);
    return { source: `x/${a} = ${num(q)}`, solutions: [a * q] };
  }
  // x/a + x/b = c  with a≠b, solution a multiple of lcm so c is a clean integer
  const a = randInt(rng, 2, 4);
  let b = randInt(rng, 2, 4);
  while (b === a) b = randInt(rng, 2, 4);
  const lcm = (a * b) / Number(gcd(BigInt(a), BigInt(b)));
  const s = lcm * randInt(rng, 1, 3);
  return { source: `x/${a} + x/${b} = ${num(s / a + s / b)}`, solutions: [s] };
}

function power(rng: Rng, r: Range): Built {
  const n = randInt(rng, 2, r.allowNeg ? 4 : 3);
  const base = randInt(rng, 2, Math.min(r.solMax, 6)); // positive; even powers add ±
  const c = base ** n;
  return { source: `x^${n} = ${c}`, solutions: n % 2 === 0 ? [base, -base] : [base] };
}

function inequality(rng: Rng, r: Range): Built {
  const s = signedInt(rng, 1, r.solMax, r.allowNeg);
  const a = signedInt(rng, 1, r.coeffMax, r.allowNeg); // may be negative → relation flips
  const b = signedInt(rng, 1, r.coeffMax, r.allowNeg);
  const rel = pick(rng, ["<", "<=", ">", ">="]);
  const source = `${renderTerms([{ c: a, v: "x" }, { c: b, v: "" }])} ${rel} ${num(a * s + b)}`;
  // The "solution" of an inequality is a half-line; report a witness point that
  // actually satisfies it (near the boundary s), found by evaluating truth.
  const eqn = parseEquation(source);
  let witness = s;
  for (const cand of [s, s - 1, s + 1, s - 2, s + 2, s - 3, s + 3]) {
    if (truthValue(eqn, new Map([["x", R(cand)]])) === true) {
      witness = cand;
      break;
    }
  }
  return { source, solutions: [witness] };
}

function quadratic(rng: Rng, r: Range): Built {
  const rootMax = Math.min(r.solMax, 9);
  const r1 = signedInt(rng, 1, rootMax, r.allowNeg);
  const r2 = signedInt(rng, 1, rootMax, r.allowNeg);
  // (x − r1)(x − r2) = x² − (r1+r2)x + r1·r2
  const source = renderTerms([
    { c: 1, v: "x^2" },
    { c: -(r1 + r2), v: "x" },
    { c: r1 * r2, v: "" },
  ]);
  return { source: `${source} = 0`, solutions: r1 === r2 ? [r1] : [r1, r2] };
}

function build(topic: ProblemTopic, rng: Rng, r: Range): Built {
  switch (topic) {
    case "linear-one-step":
      return linearOneStep(rng, r);
    case "linear-two-step":
      return linearTwoStep(rng, r);
    case "linear-both-sides":
      return linearBothSides(rng, r);
    case "distribution":
      return distribution(rng, r);
    case "fractions":
      return fractions(rng, r);
    case "power":
      return power(rng, r);
    case "inequality":
      return inequality(rng, r);
    case "quadratic":
      return quadratic(rng, r);
  }
}

/**
 * Generate a random single-variable problem. The equation is guaranteed
 * well-formed and solvable, with `solutions` its exact answer(s) (a witness
 * point for inequalities). `rng` supplies randomness — `Math.random` in the
 * app, a seeded PRNG in tests.
 */
export function generateProblem(spec: ProblemSpec, rng: Rng): GeneratedProblem {
  const built = build(spec.topic, rng, RANGES[spec.difficulty]);
  return {
    equation: parseEquation(built.source),
    solutions: built.solutions.map(R),
    topic: spec.topic,
    difficulty: spec.difficulty,
  };
}

/**
 * Generate a random 2×2 linear system with a unique integer solution (x, y).
 * The coefficient matrix is non-singular by construction, so it solves by
 * substitution or elimination.
 */
export function generateSystem(difficulty: Difficulty, rng: Rng): SystemProblem {
  const r = RANGES[difficulty];
  const cMax = Math.min(r.coeffMax, 5);
  const sMax = Math.min(r.solMax, 8);
  const sx = signedInt(rng, 1, sMax, r.allowNeg);
  const sy = signedInt(rng, 1, sMax, r.allowNeg);
  let a1 = 0;
  let b1 = 0;
  let a2 = 0;
  let b2 = 0;
  do {
    a1 = signedInt(rng, 1, cMax, r.allowNeg);
    b1 = signedInt(rng, 1, cMax, r.allowNeg);
    a2 = signedInt(rng, 1, cMax, r.allowNeg);
    b2 = signedInt(rng, 1, cMax, r.allowNeg);
  } while (a1 * b2 - a2 * b1 === 0); // non-singular → unique solution
  const line = (a: number, b: number, c: number): Equation =>
    parseEquation(`${renderTerms([{ c: a, v: "x" }, { c: b, v: "y" }])} = ${num(c)}`);
  return {
    equations: [line(a1, b1, a1 * sx + b1 * sy), line(a2, b2, a2 * sx + b2 * sy)],
    x: R(sx),
    y: R(sy),
    difficulty,
  };
}
