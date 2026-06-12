# wyrm-math

An exact, **conditionally-sound symbolic algebra engine** for building
manipulative math interfaces — the kind where users solve equations by
dragging terms across the equals sign, tapping a power to expand it, or
pulling a shared factor out of two terms.

The core invariant: **legal moves are possible, illegal moves are
impossible.** Equations are never validated — they are only ever transformed
by rewrite rules, so every reachable state is sound by construction. And
soundness is *conditional*: moves that are only valid under a condition
(dividing by `b` requires `b ≠ 0`) or that can introduce extraneous solutions
(multiplying both sides, squaring) are not forbidden — their conditions
become first-class, visible **Assumptions** that travel with the equation.

Pure TypeScript, zero dependencies, zero DOM — runs in Node, browsers,
workers, native webviews, anywhere.

```ts
import {
  parseEquation, Derivation,
  enumerateMoves, ruleById, layoutNode, exprToString,
} from "wyrm-math";

const d = new Derivation(parseEquation("2x + 3 = 11"));

// What can the user legally do right now?
const moves = enumerateMoves(d.current);

// Drag the 3 across the equals sign (the UI picks a Move; the engine
// guarantees it is legal — enumeration is precondition-checked):
const move = moves.find((m) => m.ruleId === "move-term-across")!;
d.apply(ruleById(move.ruleId), move.location, move.params);

console.log(exprToString(d.current.equation)); // 2x = 11 + -3

// Render it however you like: layoutNode gives positioned, id-keyed boxes
// and glyphs from static metric tables (no font measurement needed).
const layout = layoutNode(d.current.equation);
```

## What's inside

The public API is `src/index.ts`, organized into ten documented groups — it
reads as a table of contents:

| Group | What it gives you |
| --- | --- |
| **Expression trees** | Immutable AST with stable node ids. N-ary `Sum`/`Product`; no subtraction or division nodes (`a − b` is `Sum(a, Neg(b))`; division is a `Fraction` with numerator/denominator lists). Smart constructors maintain the structural invariants. |
| **Exact arithmetic** | `Rational` over `bigint`. No floating point anywhere — `√2` is an *undefined point*, not 1.4142. |
| **Evaluation** | `truthValue(equation, env)` decides any relation (`= < ≤ > ≥`) at a sample point, exactly, or returns `undefined` where a side is undefined. |
| **Parsing & printing** | `parseEquation("2x + 3 = 11")` ⇄ `exprToString` — round-trip property-tested. Implicit multiplication, fractions, powers, radicals; decimals rejected (the engine is exact). |
| **Judgments & assumptions** | The unit of state is `{ assumptions, equation }`. **Restrictions** (moves that may LOSE solutions: `b ≠ 0`), **Extensions** (moves that may GAIN them: carry the original equation as an obligation, settled by `checkSolution`), **Pinned** (user what-ifs). Discharged assumptions are recorded, never deleted. |
| **Rules & derivations** | `Rule.apply` is the only way an equation changes. The derivation log is an append-only **tree**: undo moves a pointer, abandoned branches stay live, case splits and disjunctions fork into live siblings. |
| **Built-in rules** | ~25 rules covering linear equations, like terms, distribution, fractions, exponent laws, inequalities (sign-aware, relation-flipping), and quadratics (`x² = 9` branches to `x = ±3`; zero-product). Every rule ships with a property test that it respects the solution set under its assumptions. |
| **Move enumeration** | `enumerateMoves(judgment)` returns every legal affordance with gesture anchors (`handle`, `dropTarget`). Sound for all rules, complete for the finite ones. Pin `x = 0` and every divide-by-x affordance disappears automatically. |
| **Layout geometry** | `layoutNode` maps trees to positioned, id-keyed boxes and glyphs (fraction stacking, superscripts, radicals) from static metric tables. `hitTest` is a geometry query. Subtree geometry is context-independent up to translation+scale — which is what makes id-keyed animation possible. |
| **Rule-authoring toolkit** | Id-preserving rebuilds, the invariant-repairing splice, diff bookkeeping, and assumption-lifecycle queries for writing new rules. |

`ARCHITECTURE.md` explains the invariants and contracts in depth.

## Design commitments

- **Exactness.** All arithmetic is `bigint` rationals. Points where an
  expression is undefined (division by zero, irrational roots) are treated
  as undefined, never approximated. The engine-wide soundness contract is
  *truth-where-both-defined*.
- **Stable ids.** Every node has an id; operations preserve the ids of
  untouched subtrees. This is the currency of hit testing and animation:
  a renderer can match nodes across a rewrite and move them rigidly.
- **Conditional soundness.** For ordinary and Restriction-emitting rules,
  property tests rejection-sample substitutions to those satisfying the
  result judgment's assumptions and assert truth preservation. For
  Extension-emitting rules the check weakens to one direction (solutions
  are never lost), with `checkSolution` covering the gain obligation.
- **Disjunction.** Branching rules return several outcomes whose solution
  sets union to the original's (`x² = 9` ⇒ `x = 3` *or* `x = −3`); the
  derivation tree holds all arms as live, navigable states.

## Development

```sh
pnpm install
pnpm test        # vitest + fast-check (property tests are the soul of this project)
pnpm typecheck
pnpm build       # emits dist/ (ESM + d.ts)
```

The engine must stay DOM-free: `tsconfig.json` has no DOM lib and
`test/boundary.test.ts` scans the sources for browser globals.

## License

MIT
