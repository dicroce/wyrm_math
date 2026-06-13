# wyrm-math — roadmap & TODO

A living sketch of where the engine is, how it climbs, and where it
deliberately stops. See `ARCHITECTURE.md` for the invariants and `CLAUDE.md`
for contribution rules; this file is the *direction*.

---

## What this engine is (the one axis)

An **exact, conditionally-sound, gesture-driven symbolic manipulation
engine**. Its whole job is to rewrite an expression tree through legal,
reversible, assumption-tracked rules — and an enormous amount of mathematics
*is* exactly that. The runway along this one axis is long; we climb it by
adding **rule families** (cheap, nearly unlimited) and, at the gates between
levels, by **enriching the number tower** (real projects, but bounded).

A guiding observation from building it: adding a rule never strains the
architecture (split-term, factor-out-negative, combine-fractions all just
slotted in). The *only* thing that ever forces an architectural pause is a
**missing number** (the quadratic formula needs irrationals). So:

> Floors are rules. Gates are number systems.

And the hardest-won feature — **conditional soundness** (assumptions surface
as visible chips) — gets *more* valuable as we climb, because higher math is
a minefield of conditions (zero denominators, even roots, logs of negatives,
domains). The engine is, if anything, better suited to the subtleties of
Algebra 2 and calculus than to the tidy cases we started with.

---

## Where we are (2026-06)

The **Algebra 1 manipulation core is solid** — verified end-to-end through
real gestures by the coverage harness in the app repo
(`wyrm/packages/ui/bank/` + `test/coverage.test.ts`; keep it honest — add a
bank problem for every new capability):

- Linear: all forms (one/multi-step, variables both sides, distribution,
  fractions).
- Inequalities: basic linear, including the sign-flip on dividing by a
  negative.
- Exponent rules: expand, combine like factors, quotient, power-of-power,
  distribute-power, negative exponents.
- Factoring: GCF, **trinomials incl. leading-coefficient ≠ 1**, perfect
  squares, difference of squares (via square roots).
- Quadratics: by factoring and by square roots.
- Rational/fractions: clear denominators, cancel, **add over a common
  denominator** (combine-fractions).

Known boundaries the harness flags today: irrational roots (`x² = 5`,
`x² + x − 1 = 0`), no-real-root quadratics (`x² + 4 = 0`), completing the
square. All three trace to one wall — see the number tower below.

---

## The climb (rungs, roughly in dependency order)

### 1. Finish Algebra 1 manipulation
- [ ] **Systems of equations** — multi-equation state; substitution &
  elimination as gestures. (The biggest structural addition: today the engine
  is single-equation.)
- [ ] **Compound inequalities** — an interval / conjunction representation
  (today a judgment carries a single relation).

### 2. The number tower (the gates)
The recurring wall. Each rung keeps the exactness discipline — we never
approximate in *reasoning*.
- [ ] **Quadratic irrationals** `p + q√d` as first-class exact values —
  carry them through arithmetic and through `truthValue` checking. Unlocks
  the **quadratic formula**, **completing the square**, `x² = 5`, and every
  quadratic that doesn't factor rationally. Seed already exists: the `Sqrt`
  node + exact perfect-square evaluation.
- [ ] **Complex numbers** `a + bi` — unlocks no-real-root quadratics and is
  the honest answer to `x² + 4 = 0`.
- [ ] (Further out) general **algebraic numbers**.

### 3. Algebra 2 manipulation
- [ ] **Rational expressions** — full add / subtract / multiply / divide
  (combine-fractions started this).
- [ ] **Exponentials & logarithms** as symbolic objects + their laws.
- [ ] **General polynomial arithmetic & factoring** beyond the quadratic
  patterns.

### 4. Calculus — the engine's natural habitat
Differentiation rules are *literally* rewrite rules; this is what the engine
was born for, and it should feel like it.
- [ ] **Symbolic differentiation** — power, sum, product, quotient, chain.
- [ ] **Symbolic integration** — elementary / table cases.
- [ ] **Limits** — the algebraic ones.

### 5. The grapher (a view, not part of the core)
**Key principle — exactness guards *reasoning*, not *rendering*.** The
invariant exists to decide move legality soundly; it says nothing about
drawing pixels. A grapher reads exact expressions and *samples* them — it
never feeds back into the engine, so it may approximate freely. It lives in
the view layer, downstream, like `layout.ts` / `svg.ts`.

- [ ] **Function grapher** — expression in one variable + range → sample via
  the existing `evalExpr` at rational points → SVG path. Undefined points
  (division by zero, etc.) become honest gaps in the curve. A *display-only*
  numerical fallback covers irrational values without touching the engine.
  - Buildable **today** on the existing evaluator; needs nothing from the
    number tower.
  - Most valuable **after calculus**: graph the *exact symbolic* `f'` (not a
    numerical-derivative approximation), show the tangent line whose slope is
    the derivative, shade the area an integral measures. A combination almost
    nothing in school math offers.

---

## Deliberately out of scope (identity, not backlog)

These aren't unbuilt features; they're a different kind of tool. The wise
version of this project goes *vertical* through the curriculum it's shaped
for rather than chasing these.

- **Numerical reasoning / floating point as answers** — numerical
  root-finding, evaluating transcendentals to N digits, anything where the
  *answer* is approximate. (A grapher may approximate for *display* only — see
  rung 5 — because it never decides a move.)
- **Statistics & probability** — inherently data/approximate.
- **Graphing-as-core, function-as-graph pedagogy, word-problem translation** —
  other modalities (coordinate geometry, NLP). The engine can be the
  manipulation *brain behind* such tools, not the tool itself.
- **Research / CAS-scale computation** — the gesture UI caps practical
  complexity at expressions a hand can drive one step at a time, which is
  exactly the pedagogical band (school → early college), not 40-term machine
  algebra.

---

## Invariants to preserve while climbing
- No floating point in anything correctness-related — exact `Rational`
  (bigint) only; undefined points stay undefined.
- Every new rule gets a property test: it respects the solution set under its
  assumptions (extension-emitting rules weaken one direction; branching rules
  satisfy the union property).
- New public surface goes through the curated, grouped `src/index.ts`.
- Each new capability earns a problem in the app-repo coverage bank, driven at
  the gesture layer — so "what Algebra 1 / Algebra 2 / calculus do we cover?"
  always has a runnable answer.

---

## The throne (why the ceiling is worth climbing)

Every mainstream tool computes *answers*. This one teaches *manipulation*,
with a guarantee nothing else offers: **illegal moves cannot happen**. Nobody
owns "the rigorous manipulative tutor for exact symbolic math, K-12 through
early college." Climbing the number tower toward calculus, with a view-layer
grapher hung off the side, is how this engine could.
