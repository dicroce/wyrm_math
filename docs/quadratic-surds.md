# Design: quadratic surds (exact irrational values)

Status: **accepted** (2026-06-17) — implementing on branch `quadratic-surds`.
Deferred pieces are tracked as next steps in [todo.md](todo.md).

## Why

The engine lives entirely in ℚ. `evalExpr` returns a `Rational`; `truthValue`
decides relations via `Rational.compare`; the property tests substitute random
exact rationals. The `Sqrt` node can *represent* √n, but per ARCHITECTURE.md
"√v is defined only when v is a perfect rational square — otherwise the point is
UNDEFINED."

Consequence: `√2` is not a *value*, it's an **undefined point**. So `x² = 2`
"solves" to `x = √2` in the UI (variable isolated) but that answer is
semantically empty — the engine can't evaluate it, verify it with
`checkSolution`, or compare it. Every quadratic whose discriminant isn't a
perfect square has the same problem. To make those answers **real** (verifiable,
comparable, simplifiable) the exact-value domain must grow past ℚ — staying
**exact** (the "no floats, ever" rule is non-negotiable).

## Scope of this branch

**In:**
- Exact **surd values** in the evaluator: numbers `q₀ + Σ qᵢ·√nᵢ`
  (qᵢ ∈ ℚ, nᵢ distinct square-free integers > 1). Multi-radicand so `√2 + √3`
  is robust; a quadratic-formula answer only ever uses one radicand.
- **Equality** of surd values (clean — see below). Enough for `=`.
- **Radical simplification** rewrite rules: `√(k²·m) → k√m`, `√a·√b → √(ab)`,
  combine like radicals `q√n + r√n → (q+r)√n`, rationalize a surd denominator.
- A **`quadratic-formula`** branching rule. It *subsumes* trinomial factoring —
  it closes the three quadratics Guide Me / Solution Search currently can't
  (`x²−5x+6=0`, `x²−6x+9=0`, `2x²+5x−3=0`), factorable or not.

**Out (deferred / separate efforts):**
- **Negative discriminant** → report "no real solution"; defer ℂ.
- **Order** comparison of surds (`<,>` with irrational bounds) — only needed for
  *inequalities* with surd terms. Decidable but heavier (exact sign of
  Σqᵢ√nᵢ); see Open Questions. Equalities ship first.
- **Nested radicals / general algebraic numbers** — a different representation
  (minimal polynomial, or radical towers). Out of scope by design.
- **Transcendentals** (π, e) — a separate axis (symbolic constants), later.

## Core change: an `ExactValue` domain in the evaluator

Today: `evalExpr(e, env): Rational` (with undefined points). Generalize to an
exact-value abstraction the evaluator returns:

```
evalExpr(e, env): ExactValue | undefined
```

- `ExactValue` is the surd-closed exact domain; a `Rational` is the degenerate
  element (no radical part), so all current behavior is preserved for rational
  inputs (regression bar: every existing test stays green).
- `truthValue` compares `ExactValue`s (equality always; order where decidable).
- `rationalToExpr` → `exactToExpr`: rebuild a canonical tree from an
  `ExactValue` using the existing **smart constructors** (so AST invariants
  hold automatically).
- Genuine undefined points (1/0, √ of a negative, **nested** radical that
  escapes the field) stay UNDEFINED — never approximated.

This is the central refactor. The exhaustive `kind` switch in `evalExpr` (the
`sqrt` case especially) is where it concentrates; the compiler surfaces any
other site that assumed `Rational`.

## Representation (`surd.ts`, new pure module)

A value = rational `c` plus a map `{ squareFreeInt n → rational coeff }`.

- **Closed under** `+ − ×`; `÷` via rationalization in the multiquadratic field
  ℚ(√n₁,…). `√` only when the result lands back in the field (e.g. √ of a
  perfect square times a known radical); otherwise it's a **nested radical →
  treated as an undefined point** (honest: out of scope, never approximated).
- **Equality is clean:** the √ of distinct square-free integers are ℚ-linearly
  independent, so `q₀ + Σ qᵢ√nᵢ = 0` iff every coefficient is 0. Structural,
  exact, no numerics.
- **Sign/order** (needed only for surd inequalities): exact sign of `Σ qᵢ√nᵢ`
  via conjugate/interval refinement over rational bounds. Heavier — see Open
  Questions; may land in a follow-up.

No floats anywhere. Pure, DOM-free — passes `boundary.test.ts`.

## Rules

- **`simplify-sqrt`** (extend): currently collapses perfect squares only
  (√9→3). Extend to pull the perfect-square factor: `√(k²·m) → k·√m`. Pure
  rewrite, exactly sound for k ≥ 0.
- **`multiply-radicals`** `√a·√b → √(ab)`, **`combine-like-radicals`**
  `q√n + r√n → (q+r)√n`, **`rationalize-denominator`** — each a rewrite rule
  with a solution-set property test, each wired into `enumerateMoves`.
- **`quadratic-formula`** (BranchingRule): recognize `a·x² + b·x + c (= 0)` on a
  side; branch into `x = (−b + √D)/(2a)` and `x = (−b − √D)/(2a)`,
  `D = b² − 4ac`. Satisfies the **UNION property** (both directions), like
  `sqrt-both-sides`/`zero-product`.
  - `D` a perfect square → `simplify-sqrt` collapses → rational roots
    (so it also handles factorable quadratics — one rule, whole chapter).
  - `D < 0` → branch RHS is √(negative) = undefined → empty → "no real
    solution".

## Soundness & tests (the soul)

The property harness substitutes random **rational** x-values and checks
`truthValue` is preserved on the domain. With `ExactValue` eval, a branch like
`x = (−b+√D)/2a` evaluates its RHS to an exact surd, and substituting a rational
x compares `rational == surd` **exactly** — so the existing framework extends
naturally; no approximation enters.

- `quadratic-formula`: UNION property test (every rational root of the original
  lands in a branch; every branch value satisfies the original), mirroring the
  existing branching-rule tests.
- New `gen.ts` scenarios: quadratics with rational *and* irrational roots.
- Keep enforcing: structural invariants of results, bystander id stability,
  diff sanity, **no-DOM / no-float** boundary, and "result offers the expected
  follow-up moves" (e.g. `simplify-sqrt` available on the produced √D).

## AST / invariant impact

Likely **no new node** — reuse `Sqrt` + `Sum`/`Product`/`Fraction`. The change
is in the *value domain* (evaluator) plus rules. Any canonical surd display is
produced by `exactToExpr` via smart constructors, so flattening / canonical
negatives / fraction-list invariants are maintained for free. Radical layout
already exists.

## Phased implementation

1. **`surd.ts`** — the `ExactValue` type + arithmetic (`+ − × ÷`, √-into-field),
   equality. Unit + property tests for the field laws. (Order/sign optional,
   gated behind Open Questions.)
2. **Thread through** `evalExpr` / `truthValue` / `exactToExpr`. Rational inputs
   behave identically — **all existing tests must stay green**.
3. **Radical simplification rules** (+ property tests + `enumerateMoves`).
4. **`quadratic-formula`** branching rule (+ union property test + enumeration
   as a tap on the quadratic + follow-up-moves check).
5. **App side** (separate `wyrm` repo, later): `solver.ts` / search pick up
   `quadratic-formula` automatically; add a Guide Me caption; confirm the three
   trinomials now solve end-to-end.

## Decisions (agreed 2026-06-17)

1. **Surd order for inequalities** — **deferred.** Equalities cover the
   quadratics goal; exact ordering of surds (the heavy part) is a next step.
2. **Multi- vs single-radicand** — **design the type for multi-radicand**
   (robust for `√2+√3`); implement pragmatically, growing from single-radicand
   if field division/sign proves heavy.
3. **Negative discriminant** — **report "no real solution"** for now; complex
   numbers are a next step.
4. **Quadratic formula vs complete-the-square** — **formula now** (one clean
   branching rule); complete-the-square is a later pedagogical alternative.

### Deferred — available next steps (tracked in todo.md)

- **NEXT: "no real solution" detection** (app side). The engine correctly
  leaves a negative discriminant as `√(negative)` (an undefined point), but the
  app's `isSolved` is structural, so `x = √(−1)` reads as "isolated → solved"
  and the app cheerfully celebrates an imaginary value. Fix: when a solved form
  contains a negative radical (or its value side fails to evaluate to a real —
  `evalExpr` throws InexactSqrt), report **"no real solution"** instead of a
  win. Unblocks adding `x² + 1 = 0` to the examples honestly; on-ramp to ℂ.
- **Radical arithmetic rules** beyond `simplify-sqrt`: `√a·√b → √(ab)`, combine
  like radicals `q√n + r√n → (q+r)√n`, rationalize a surd denominator. Not on
  the quadratic-formula path, so split out of Phase 3 into a focused pass.
- Exact surd **ordering** → inequalities with irrational bounds.
- **Complex numbers** → honest answers for negative discriminants.
- **Complete-the-square** as a shown-work alternative to the formula.
- **Nested radicals / general algebraic numbers** (different representation).
- **Transcendentals** (π, e) — the separate symbolic-constant axis.
```
