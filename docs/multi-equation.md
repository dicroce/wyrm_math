# Multiple live items — engine design (Phase 0)

Status: **design**, not yet implemented. The foundation for systems of
equations, the "quadratic formula as a draggable tool," and (later) calculus's
side-by-side work. The engine half only; the consuming UI plan lives in the app
repo (`wyrm/tech_docs/multi-equation-ui.md`).

## Two orthogonal axes

Almost everything in this engine advances along one of two independent axes.
Keeping them separate is what makes this design future-proof.

1. **Expression richness** — what a single tree can *be*: new number systems
   (surds, ℂ), new operator nodes (derivative, integral, limit, Σ), and the
   rewrite rules over them. The roadmap's "floors are rules, gates are number
   systems" axis. **Most of the road to calculus rides here** —
   differentiation, integration, and limits are new operator nodes + rewrite
   rules on a *single* expression, the engine's core competency.

2. **Workspace multiplicity** — how many related items live at once, and how
   they relate. *This* is what the present design adds.

They **compose without interfering**: a system can involve derivatives; an
integral can be worked beside its function. As long as axis 2 never assumes its
items are "simple algebra," each axis advances on its own — calculus happens on
axis 1, *inside* the items axis 2 holds.

## Three relationships between items — keep them distinct

Items on screen can relate in three ways, with different solution-set
semantics, so they get different treatment. Collapsing them into one mechanism
would be the wrong abstraction.

| | Relationship | Solution set | Status |
|---|---|---|---|
| **Branches** (`x² = 9` → `x = 3` ∨ `x = −3`) | disjunction | **union** | exists (`kind: "branch"`) |
| **Systems** (`2x + y = 5` ∧ `x − y = 1`) | conjunction | **intersection** over the variable tuple | new |
| **Auxiliary** (the quadratic-formula card, a side computation, `let u = …`) | not a constraint — *derives* something | n/a | new |

Branches already live as sibling nodes in the derivation tree. Systems and
auxiliary items are what this design adds.

## State model: a workspace of typed items

Two options were considered:

- **A — generalize `Judgment.equation` → `equations[]`.** Rejected: every rule,
  `evalExpr`, `truthValue`, `assumptions`, and `moves` references `.equation`.
  Maximal blast radius, high risk.
- **B — a workspace layer above the existing machinery.** Chosen.

The unit a `Derivation` node stores becomes a **workspace of typed items**:

```ts
type Relationship = "constraint" | "auxiliary" | "definition"; // extensible

interface Item {
  readonly node: Node;            // an Equation/relation OR a bare Expr
  readonly relationship: Relationship;
}

interface Workspace {
  readonly assumptions: readonly Assumption[]; // shared by constraint+auxiliary
  readonly items: readonly Item[];
}
```

Why an **item is a `Node`, not an `Equation`**: a bare `Expr` ("simplify this")
is then first-class — common in algebra *and* in every calculus simplification —
and `Equation` already carries a `relation` field, so inequalities and compound
inequalities come for free. A **conjunctive `System`** is simply the
specialization where every item's relationship is `constraint`; it is the *first*
use of this model, not the whole of it.

- **Single-equation rules are reused unchanged.** They still act on ONE item; a
  move carries *which* item (an index). `applyRule` builds a transient
  `{ assumptions: ws.assumptions, equation: ws.items[i].node }`, applies, and
  writes the result back. The rule library and its property tests are untouched.
- **Assumptions follow the relationship.** `constraint` and `auxiliary` items in
  one workspace state **share** the assumption set (same variable space — a
  `Restriction(a ≠ 0)` from the quadratic card, or `Restriction(x ≠ 0)` from a
  division, constrains the whole workspace). **Branches stay separate**
  derivation nodes with their own assumptions, exactly as today (disjunction
  diverges).
- **`Derivation` holds `Workspace` snapshots.** Undo, redo, goto, branch, pin,
  case-split keep their current shape; only the payload per node widens.
- **Degenerate cases are free.** Today's single equation is `items = [one
  constraint]`; a lone "simplify this" is `items = [one bare Expr]`.

> Naming is an implementation detail to settle in Phase 3: keep `Judgment` as the
> single-item unit rules operate on, with `Workspace` (and a `System` alias when
> all items are constraints) as the new top-level state.

## Solution-set semantics

- **Constraints** are conjunctive: the workspace is true at an assignment iff
  *every* constraint item is true there (`truthValue` AND-folded; undefined at a
  point ⇒ skipped, as today). The soundness contract is unchanged in spirit —
  moves preserve the **intersection** solution set over the variable tuple.
- **Auxiliary / definition** items are not constraints; they don't tighten the
  solution set, they *derive* new items (a formula instance, a substituted
  integral). Soundness for them is "the derived item is a consequence under the
  shared assumptions."
- **checkSolution**: a candidate must satisfy all *constraint* items and the
  assumptions.

## Cross-item rules (new)

Operate on the `Workspace`, not a single item:

- **Substitution** — solve one item for a variable (or use it as-is if already
  `v = …` / `u = g(x)`), replace `v` in another item. This single rule serves
  **systems** (substitute one equation into another) *and*, later,
  **u-substitution / change of variables** in calculus — the same machinery.
- **Elimination** — replace a constraint with a linear combination `αA + βB`
  (exact rationals) chosen to cancel a variable.

Each gets a property test in the existing style: random workspaces around an
applicable site, random exact-rational tuple substitutions, rejection-sampled to
the result's restrictions/pins, **intersection** truth preserved at every
surviving sample point.

## Move enumeration over a workspace

`enumerateMoves(workspace)` returns:
- **intra-item** moves — the existing per-item enumeration, tagged with the item
  index.
- **inter-item** moves — substitution/elimination, referencing two item indices.

## The quadratic-formula tool (auxiliary)

UX (app side): leave `2x² + 5x − 3 = 0` in place and add the formula as a
separate `auxiliary` item the learner works.

- Filling `a, b, c` instantiates the theorem
  `ax² + bx + c = 0 ⟺ x = (−b ± √(b² − 4ac))/2a` (for `a ≠ 0`), so the result is
  **sound by construction** and lands as the existing `±` **branches** — derived
  *beside* the original rather than replacing it.
- **Fidelity ladder** (matches UI phasing):
  1. **Pre-filled card** — `a, b, c` already read from the source; learner
     simplifies by hand. No new node kind.
  2. **Placeholders** — a template with holes the learner fills by dragging
     coefficients in. Likely needs a **placeholder node kind** (a legal tree with
     a typed hole). Identifying `a, b, c` is the key learning step, so this is the
     richer target.

## What this serves later (why axis 2 is high-leverage, not a one-off)

- **u-substitution / change of variables** — auxiliary `definition` item +
  the substitution rule above. Same machinery as systems.
- **Working a derivative/integral off to the side** — `auxiliary` item beside
  the function (the calculus version of the quadratic card).
- **Optimization & related rates** — solving `∇f = 0` / rate relations is a
  conjunctive system.
- **Compound inequalities** (`1 ≤ x < 5`) — conjunction of relation items.
- **Solutions as unions of intervals** — disjunction, i.e. the existing
  branches.

## Phasing

- **Phase 0** — this doc. Lock the two-axes framing and the workspace model.
- **Phase 1** — no engine change (UI renders N independent derivations;
  pre-filled quadratic card is a derived equation). Engine stays single-item.
- **Phase 2** — placeholder node kind + a "fill" rule (sound substitution into
  the quadratic-formula theorem). First cross-item engine work.
- **Phase 3** — the `Workspace`/`System` state, substitution/elimination with
  intersection-preserving property tests, workspace-wide move enumeration.

## Open questions

- Naming: `Judgment` (single item) + `Workspace`/`System` — final shape.
- Placeholders as a first-class node kind vs a UI-only overlay that commits a
  whole substitution at once.
- The `Relationship` taxonomy: is `definition` distinct from `auxiliary`, or a
  flavor of it?
- Elimination parameters: how much is enumerated (gesture-meaningful
  combinations) vs left to free-form `Derivation` calls.
