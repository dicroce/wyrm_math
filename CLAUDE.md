# wyrm-math

An exact, conditionally-sound symbolic algebra engine for manipulative math
interfaces. Pure TypeScript, ZERO dependencies, ZERO DOM — must run in plain
Node. See README.md for the API tour and ARCHITECTURE.md for the invariants
in depth.

**The core invariant: legal moves are possible, illegal moves are
impossible.** Equations are never validated — only ever mutated through
rewrite rules. Soundness is CONDITIONAL: every reachable state is equivalent
to the original equation GIVEN its assumption set.

## Hard rules for changes

- **No DOM, no browser imports, no dependencies, ever.** `tsconfig.json` has
  `"lib": ["ES2022"]` and `"types": []`; `test/boundary.test.ts` scans the
  sources and fails on browser globals.
- **No floating point in anything correctness-related.** Exact `Rational`
  (bigint) arithmetic only. Undefined points (division by zero, irrational
  roots) stay undefined — never approximate.
- **Immutability.** Every operation returns a new tree; old trees live on in
  the derivation log. Never mutate a node.
- **Build nodes only through the smart constructors** (`int`, `sum`,
  `product`, `neg`, `fraction`, `pow`, `sqrt`, `equation`) and rebuild only
  through `rebuildNary` / `replaceNode` / `replaceTermRespectingInvariants`.
  They maintain the structural invariants (flattening, canonical negatives,
  fraction-list product spreading, no double negation, unique ids).
- **Stable ids.** Operations must preserve the ids of untouched subtrees
  (property-tested as "bystander stability"). `cloneFresh` is the only way
  to duplicate a subtree.
- **Equations change only through rules; judgments only through the
  Derivation entry points** (apply / applyBranching / pinVariable /
  unpinVariable / caseSplit / checkSolution).
- **The public API is `src/index.ts`** — explicit, grouped, documented
  exports. New surface goes in the right group with a comment; internals are
  not re-exported.

## Testing is the soul of this project

Vitest + fast-check. **Every rule MUST have a property test asserting it
respects the solution set under its assumptions**: random equations around
an applicable site, random exact-rational substitutions, rejection-sampled
to the result judgment's Restrictions/Pinned values, truth preserved at
every surviving sample point (`truthValue` returns undefined at undefined
points; those are skipped). Extension-emitting rules weaken to one
direction (solutions never lost); branching rules satisfy the UNION
property (original true ⇒ some branch true; branch true ⇒ original true).

Recurring test patterns to respect (learned the hard way):
- "X survives by identity" assertions need the splice exceptions: a Product
  dissolves into a flattening parent or fraction list; a Neg gets swallowed
  under a Neg (and that repair CASCADES — see
  `replaceTermRespectingInvariants`).
- New rules must leave RESULT states that offer the follow-up moves a user
  expects — check `enumerateMoves` on the output, not just soundness.
- `test/gen.ts` holds the generators; build scenarios exclusively through
  smart constructors and `embed` (which plants targets at depth).

## Commands

```sh
pnpm install
pnpm test             # vitest, run mode
pnpm test:watch
pnpm typecheck        # src (DOM-free) and tests
pnpm build            # dist/ (ESM + d.ts)
```
