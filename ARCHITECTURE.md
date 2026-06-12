# @wyrm/core architecture

The engine behind Wyrm's one product invariant: **legal moves are possible,
illegal moves are impossible.** Equations are never validated; they are only
ever transformed by rewrite rules. Soundness is CONDITIONAL: **every reachable
state is equivalent to the original equation GIVEN its assumption set.** Real
algebra includes moves that are only valid under conditions (dividing by b
needs b ≠ 0) or that can introduce extraneous solutions (multiplying both
sides); Wyrm does not forbid them — it makes the conditions first-class
visible objects. This document explains the invariants that make that work
and that every future contribution must preserve.

## The expression tree (`expr.ts`)

Immutable AST with a `kind`-discriminated union. Mutating in place is never
allowed — every operation returns a new tree, and old trees stay alive in the
derivation log for undo/replay.

Node types: `Integer`, `Variable`, `Sum`, `Product`, `Neg`, `Fraction`, `Pow`,
and `Equation` (only ever at the root). Adding a node type later (radicals,
functions) means adding a union member and extending the exhaustive switches —
the compiler will point at every site.

Deliberate representation choices:

- **No subtraction, no division.** `a - b` is `Sum(a, Neg(b))`; division is a
  `Fraction` whose numerator/denominator are *expression lists* (implicit
  products). These match what the user sees and drags, which is the whole
  point of the product.
- **`Sum`/`Product` are n-ary**, not binary chains, so "the terms of this sum"
  is a flat list a finger can pick from.

### Structural invariants

Every reachable tree satisfies (see `invariantViolations`, property-tested):

1. A `Sum` never contains a direct `Sum` child; same for `Product`
   (auto-flattened by the constructors).
2. No `Neg(Neg(x))`.
3. `Sum`/`Product` have ≥ 2 children — 0 children collapse to the identity
   literal (0 / 1), 1 child collapses to the child itself.
4. `Integer.value >= 0`; negative literals are canonically `Neg(Integer)`
   (`int(-5)` builds that for you). One canonical form means structural
   equality is enough to decide "is this the negation of that".
5. Fraction num/den lists never contain a direct `Product` element (lists
   ARE implicit products; the constructor flattens, keeping child ids).
6. Node ids are unique within a tree.

How to stay inside the invariants:

- Build nodes ONLY through the smart constructors (`int`, `variable`, `sum`,
  `product`, `neg`, `fraction`, `pow`, `equation`).
- Rebuild nodes ONLY through `rebuildNary` (keeps the original id when the
  node survives) and `replaceNode` / `replaceTermRespectingInvariants`.
- `replaceTermRespectingInvariants` exists because a structurally valid
  replacement can still break an invariant *at the splice point*: a sum that
  collapses to its last term can put a `Neg` under a `Neg` parent, or a
  `Product` under a `Product` parent. The helper repairs exactly that — it
  collapses the double negation (which may *swallow* the replacement's root
  node) or flattens into the parent. One level of repair is always enough
  because the rest of the tree already satisfies the invariants.

### Stable ids

Every node has a stable id, the future currency of hit testing and animation
diffing. The contract: **operations preserve the ids of untouched subtrees**
(property-tested per rule as "bystander stability"). Ancestors of an edit keep
their ids too; only nodes the rule actually consumed/created appear in the
diff. `cloneFresh` is the only way to duplicate a subtree — ids must stay
unique within a tree, so inserting the "same" term twice means two clones.

### Structural equality

`eq(a, b)` ignores ids and compares `Sum`/`Product` children (and `Fraction`
lists) as **multisets** — commutativity is baked into equality, so `x + 2` and
`2 + x` are the same expression as far as rules are concerned. Equation sides
are ordered. Greedy multiset matching is correct because `eq` is an
equivalence relation.

## Judgments and assumptions (`assumptions.ts`)

The unit of state is a **Judgment**:

```ts
Judgment = { assumptions: Assumption[], equation: Equation }
```

All rules operate on Judgments, and the conditional invariant is stated over
them: the judgment's equation has the same solutions as the original equation
*wherever the assumptions hold*.

### The polarity distinction — read this twice

`Assumption` has three species, and the first two differ in the DIRECTION the
solution set can move. This polarity is the heart of the design:

- **Restriction** `{ expr, relation: '≠', value, origin }` — emitted by moves
  that may **LOSE** solutions. Dividing both sides by `b` says nothing about
  the points where `b = 0`, so the result is only equivalent on the domain
  `b ≠ 0`. A Restriction *narrows* where the judgment speaks. Nothing further
  is owed: the state is fully sound, just conditional.
- **Extension** `{ description, originalEquation, origin }` — emitted by
  moves that may **GAIN** solutions. Multiplying both sides by `(x - 5)`
  makes `x = 5` satisfy the new equation whether or not it satisfied the old
  one. An Extension *widens* what the equation admits, so it carries an
  **obligation**: candidate solutions must be checked against the original
  equation — which the Extension itself carries — before the derivation is
  settled. `checkSolution(judgment, candidate)` substitutes into the carried
  original, evaluates exactly, and returns `verified` (Extensions discharge)
  or `extraneous` (the candidate is condemned in the log).
- **Pinned** `{ variable, value, origin }` — a user what-if ("assume x = 2").
  Never emitted by rewrite rules; added/removed only through
  `pinVariable`/`unpinVariable` on the Derivation. Case splits also create
  pins, marked with a `case-split` origin and not removable by the pin API.

Every assumption records its **origin** — the step id of the rule application
or the user action that created it — so a UI chip can always be traced back to
the move that spawned it.

### Lifecycle: emission is separate from discharge

Rules emit assumptions unconditionally, as bare data (`emits` on the rule
result). The engine (`applyRule`) stamps origins and then runs the **discharge
pass** (`dischargePass`):

- A Restriction decidable right now — a constant (`2 ≠ 0`), or decidable
  under current Pinned values — is marked **discharged**. Discharged
  assumptions are recorded, never deleted: the log shows they existed.
- A Restriction that decidably FAILS is a **conflict**. Rule preconditions
  check this (dividing by `x` while `x` is pinned to 0 is rejected), and the
  pin API checks the reverse direction (pinning `x = 0` against an active
  `x ≠ 0` throws `AssumptionConflict`). Both directions are tested.
- Pin-discharged Restrictions are re-decided on every pass, so removing the
  pin reactivates them. Constant and solution-check discharges are permanent.
- Extensions discharge only through `checkSolution`.

## Branching: disjunction is first-class

A `BranchingRule` returns SEVERAL outcomes whose solution sets UNION to the
original's (property-tested both directions: every original solution lands
in at least one branch; every branch solution satisfies the original).
`Derivation.applyBranching` commits all arms as live sibling children —
the same tree shape as a case split — and the pointer lands on the first.
This is what unlocks quadratics:

- `sqrt-both-sides` (tap the square): x² = b branches into x = √b and
  x = −√b. Sound under exact semantics: when a² = b is true, b is a perfect
  rational square and √b is exact; where b is negative the original is
  false and the branches are undefined — nothing is claimed.
- `zero-product` (tap the product when the other side is 0): a·b·… = 0
  branches into one a = 0 per factor (rationals form an integral domain).

The `Sqrt` node is the first AST addition since day one (the exhaustive
`kind` switches surfaced every site). Exact evaluation only: √v is defined
when v is a perfect rational square, otherwise the point is UNDEFINED (the
same skip semantics as division by zero — Wyrm never approximates).
`simplify-sqrt` taps √9 down to 3. Layout renders a stretched radical with
a vinculum bar over the radicand.

## Relations: inequalities are first-class

`Equation` carries a `relation: "=" | "<" | "≤" | ">" | "≥"` (default `=`).
`truthValue` decides every relation exactly via `Rational.compare`. Local
rewrites and `move-term-across` carry the relation through untouched (the
immutable spread preserves it for free). The relation-sensitive moves:

- `divide-both-sides` / `multiply-both-sides` on an inequality require a
  DECIDABLE sign (`signOf` under the pins): positive keeps the relation,
  negative FLIPS it, unknown is not offered (symbolic sign analysis is
  future work — a sign case split would fit the assumption machinery).
  A decidably-signed nonzero multiply on an inequality is exact, so the
  Extension obligation is emitted only for equalities.
- `square-both-sides` is refused on inequalities (not monotone).
- `swap-sides` (tap on the relation glyph) flips: a R b ⇔ b flip(R) a.

## Rules (`rule.ts`, `rules/`)

```ts
Rule<P> = {
  id, description,
  precondition(judgment, location, params) -> boolean,
  apply(judgment, location, params) -> { equation, diff, emits },
}
```

- **Equations change only through rules; judgments change only through the
  Derivation's entry points** (apply / pinVariable / unpinVariable /
  caseSplit / checkSolution). `applyRule` is the single path from a rule
  application to a new Judgment: precondition check, origin stamping,
  discharge pass.
- Preconditions see the whole Judgment, so assumption-aware legality (the
  pinned-zero divisor case) lives in the same place as structural legality.
- `location` is a node id (what hit testing naturally produces); `params` are
  rule-specific and also mostly node ids.
- `apply` returns an `AnimationDiff` — `created`/`removed` are exhaustive id
  sets, `merged`/`moved` carry the rule's animation intent. Consumer
  learnings (the UI's transition planner, `animate.ts`): stable-id glyph
  matching across the before/after layouts re-derives created/removed/moved
  on its own, so `merged` is the one field doing real work — it directs
  removed glyphs to fly into their merge target. Keep populating all fields
  (they're cheap and serve tests/tooling), but design new rules' diffs with
  `merged` as the part that matters.
- Rules that span both sides of the equals sign are ONE atomic application.
  The transactional drag gesture is a UI concern; the engine never exposes an
  unbalanced intermediate state.

`move-term-across` is the drag-across gesture: a term moves to the other
side sign-flipped in ONE move (2x = 10 − 3x ~> 2x + 3x = 10) — semantically
add-to-both-sides plus the exact structural cancellation at the source, so
it emits nothing. The term's body travels by identity (the minus is consumed
or created in transit). `add-to-both-sides` remains the free-form engine
rule but is no longer the enumerated gesture.

Current rules: `additive-cancellation`, `add-to-both-sides`,
`combine-integers`, `combine-integer-factors`, `reduce-integer-fraction`,
`expand-power`, `combine-like-factors`, `distribute`, `factor-out`, the
identity taps `drop-zero-term`, `drop-one-factor`, `power-one`,
`power-zero`, and the power laws `negative-exponent` (x⁻ⁿ ~> 1/xⁿ),
`power-of-power` ((xᵐ)ⁿ ~> xᵐⁿ, literal exponents), `distribute-power`
((xy)ⁿ ~> xⁿyⁿ, literal n ≥ 2), `swap-sides`, `move-term-across` (emit
nothing); `divide-both-sides`, `multiplicative-cancellation`,
`quotient-of-powers` (xᵐ/xⁿ ~> x^(m−n) across the bar, emits base ≠ 0)
(emit Restrictions); `multiply-both-sides` (equalities only) and
`square-both-sides` (emit Extensions — squaring is a tap on the equals
sign; x = 2 squared admits −2 and checkSolution condemns it).

Distribution: `distribute` pushes one factor over a Sum sibling
(2·(x+3) ~> 2x + 2·3; the factor survives by identity in the first term,
the Sum and every term keep their ids). `factor-out` is the inverse and is
what makes LIKE TERMS work: drag a factor instance in one term onto a
matching instance in another — 3x + 2x ~> (3+2)·x, with bare terms getting
cofactor 1 (x + 2x ~> (1+2)·x) and negated terms negative cofactors
(x − 2x ~> (1 + (−2))·x). The cofactor Sum is a real Sum, so
combine-integers folds it with a known gesture. Factor instances are one
level deep (term itself, Product factors, Neg body, Neg(Product) factors).

Exponents: `expand-power` unrolls a literal power (x³ ~> x·x·x; the base
keeps its identity as the first factor) and `combine-like-factors` is its
pairwise inverse (x·x ~> x², x²·x³ ~> x⁵, x⁰·x ~> x). Combining is
restricted to LITERAL exponents: literals are non-negative by the AST
invariant, where aᵐ·aⁿ = a^(m+n) holds everywhere (0⁰ = 1 under the exact
evaluator). The symbolic form x^a·x^b can GAIN solutions once negative
exponents exist (x²·x⁻¹ is undefined at 0, x¹ is not) and will need the
Extension machinery. Nested-pow bases ((y²)³ next to a bare y²) decompose
greedily and don't combine yet.

**Result states must offer the follow-up moves the gesture implies** (found
twice via playtesting; guarded by the x/2=3 and 3x=6 end-to-end tests in
`test/moves.test.ts`):
- `multiply-both-sides` absorbs the factor into a Fraction side's NUMERATOR
  — (x·2)/2 rather than (x/2)·2 — so multiplicative-cancellation can reach
  it.
- `divide-both-sides` spreads a Product side's factors into the numerator
  LIST — (3·x)/3 with separate elements, not one lump — so the divisor can
  cancel against the factor it came from. (Trade-off: dividing a product
  side by the whole product no longer leaves a whole-product cancellation
  pair; acceptable until a factor-grouping gesture exists.)
- `reduce-integer-fraction` is exact gcd arithmetic across the bar
  (6/3 ~> 2, 6/4 ~> 3/2, sign canonicalized into the numerator); the
  denominator is a known nonzero literal, so unlike cancellation it emits no
  assumption.

## Derivation log (`derivation.ts`): an append-only TREE

`Derivation` owns an append-only node store; each node is
`{ id, parentId, children, judgment, kind, ... }` and "current state" is a
pointer into the tree. **Undo moves the pointer to the parent; applying an
operation while elsewhere grows a new branch.** Abandoned branches are never
truncated — they stay live and navigable (`goto`, `childrenOf`; `redo` follows
the most recently created child). Pins, unpins, case-split branches, and
solution checks are first-class node kinds alongside rule applications, so
the entire story of a derivation is in the log.

**Case split** is a derivation operation, not a rewrite rule. Given a
Restriction-producing move whose restriction targets a bare variable
(`divide by b`), it forks the current node into two children:

- branch A ("restricted") applies the move and carries `Restriction(b ≠ 0)`;
- branch B ("pinned") does NOT apply the move and pins `b = 0` instead.

Both branches remain live states; every solution of the original equation
lands in exactly one of them (property-tested). Restrictions over compound
expressions can't case-split yet — that needs an `Equal`-style assumption
species (future work).

## Move enumeration (`moves.ts`)

The bridge from "legal moves are possible, illegal moves are impossible" to
an interface a finger can use. The UI never invents rule applications — it
asks `enumerateMoves(judgment)` (or `movesFrom(judgment, handleId)` for a
grabbed node) and renders the returned affordances:

```ts
Move = { ruleId, location, params, handle, dropTarget? }
```

`handle` is the node the user grabs; `dropTarget` is where the gesture drops
it. Both resolve to layout boxes. Dispatch is
`derivation.apply(ruleById(move.ruleId), move.location, move.params)`.

Two kinds of rule, two enumeration guarantees (both property-tested in
`test/moves.props.test.ts`):

- **Id-parameterized rules** (cancellations, combine-integers) have a finite
  candidate space — pairs of children at a site. Enumeration is SOUND (every
  returned move passes its precondition and applies cleanly) and COMPLETE
  (every legal application is returned). Pair moves are emitted in both drag
  directions.
- **Expr-parameterized rules** (add/divide/multiply both sides) have an
  infinite parameter space, so enumeration is sound but deliberately curated
  to the gesture-meaningful instances derived from the tree: drag a top-level
  term across the equals sign, drag a side or product factor under the other
  side, drag a denominator factor across to clear it. Free-form parameters
  remain available through `Derivation.apply`.

Because enumerators only generate candidate spaces and **preconditions decide
legality**, assumption-awareness comes for free: pin `x = 0` and every
divide-by-x affordance disappears from the same query the UI was already
making.

## Parsing (`parse.ts`)

`parseEquation(src)` turns typed input into an Equation: relations
(= < <= >= ≤ ≥), fractions via `/` (lists absorb Product parts), implicit
multiplication (2x, x(x+1)), `^` (right-assoc, x^-2 works), `sqrt(...)`/√,
unary minus, integers only (decimals are rejected with a hint to write an
exact fraction). The load-bearing test is the ROUND-TRIP property:
`eq(parseEquation(exprToString(e)), e)` for every generated equation —
printer and parser are pressure-tested as a pair. That property forced two
fixes: exprToString now parenthesizes Neg/Pow bases of powers, and the
fraction smart constructor gained the invariant that lists never contain a
direct Product element (they auto-flatten, like Sum-in-Sum) — which in turn
exposed that the Neg(Neg(x)) collapse repair must CASCADE (the surfaced
child may need splicing at its new parent; the repair recurses).

## Layout geometry (`layout.ts`)

A PURE function from a tree to positioned, id-keyed geometry — no DOM, no
font measurement, just static metric tables (`METRICS`). The UI package
projects the result onto SVG; it never computes positions itself.

```ts
layoutNode(node) -> { boxes: Map<NodeId, LayoutBox>, glyphs: PlacedGlyph[], width, height }
hitTest(layout, x, y) -> NodeId | undefined   // deepest box containing the point
```

Display decisions the AST deliberately does not encode live here:

- `Sum(a, Neg(b))` renders as binary subtraction `a − b`. The minus glyph is
  **owned by the Neg node**, so the draggable box of the signed term includes
  its sign; the Sum contributes only `+` separators and spacing.
- Parentheses are **owned by the parent that requires them** (Sum factor in a
  Product, Sum under Neg, compound Pow bases, Neg factors); products
  juxtapose (`3x`) with `·` inserted only where digits would glue to digits;
  fraction lists render as centered rows (empty list ⇒ implicit `1`);
  exponents are raised and scaled.

Geometry invariants (property-tested in `test/layout.props.test.ts`):

1. Every tree node has exactly one box (hit testing is total over the tree).
2. Child boxes nest inside their parent's box.
3. Sibling boxes never overlap — so "deepest containing box" is unambiguous
   and `hitTest` needs no tie-breaking.
4. Glyphs stay inside their owner's box (the visual is inside the draggable
   region).
5. **A subtree's internal geometry is context-independent** up to translation
   and uniform scale. This is the property that makes id-keyed animation
   work: when a rule moves an untouched subtree, the UI can move its boxes
   rigidly instead of re-discovering their shape.

## Testing rules (`test/`)

Vitest + fast-check. **Every rule must ship with a property test asserting it
respects the solution set under its assumptions** — this is the proof the
design is sound:

- Ordinary and Restriction-emitting rules: random equations are built around
  an applicable site, random exact-`Rational` assignments (never floats —
  `rational.ts`) are substituted, **rejection-sampled down to those satisfying
  the result judgment's Restrictions and Pinned values**, and the equation's
  truth value at every surviving sample point must be unchanged
  (`assertConditionallyPreserved` in `test/gen.ts`; `truthValue` returns
  `undefined` at division-by-zero points and those samples are skipped).
- Extension-emitting rules weaken to ONE DIRECTION: every substitution
  satisfying the original equation still satisfies the new one — solutions
  are never lost; gaining is permitted and `checkSolution` is property-tested
  to catch it (extraneous candidates are manufactured by multiplying both
  sides by `(x - k)`).
- Case splits: every substitution satisfying the original lands in exactly
  one live branch and satisfies that branch's judgment.
- Conflicts: pinning against an existing Restriction and restricting against
  an existing Pin both reject, in both orders.

Also property-tested: structural invariants of every result, bystander id
stability, and diff sanity. `test/gen.ts` holds the generators — they build
trees exclusively through the smart constructors, and `embed` plants the
rule's target at depth (under `Neg`, inside a `Product`, inside a `Fraction`),
which is exactly how the splice-point edge cases above were found.

`test/boundary.test.ts` mechanically enforces "no DOM, no @wyrm/ui in core",
backing up the tsconfig (`lib: ES2022`, `types: []`).
