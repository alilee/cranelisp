# exemplar/

Exemplar project for Cranelisp: a Sudoku Solver. Owned by `/port` skill.

The **committed showcase target is the stdio CLI** — `user.cl` tells the full
story end-to-end. The web platform is a designed-but-unbuilt future stretch
(FIXME 0405, `/platform`); see `plan-exemplar.md`.

## Current State (Sprint 92 Phase 6b — parallel divide-and-conquer search)

The solver's backtracking search is now a **parallel divide-and-conquer** over
the candidate digits (FIXME 0408, *contained half* — the parallel-search
**expression**). The sequential `try-digits` early-exit loop in `solver.cl` is
retired and replaced by three new functions (~40 lines, all in `solver.cl`,
`grid.cl` untouched):

- `mask-to-digits` — enumerate the set digits (1-9) of a candidate mask → `(Vec Int)`;
- `first-success a b` — `(match a (Success s) (Success s) _ b)`: take `a` if it
  solved, else `b`; correct even when `b` was computed speculatively (pure
  branches — the loser's work is discarded);
- `solve-range g idx digits lo hi` — copy-free index-range D&C: base `hi-lo==1`
  commits the digit and `solve`s; else split at `mid` and combine the two
  **independent expensive recursive solves** with `first-success`.

The two `solve-range` calls are the independent expensive **apply-arguments** of
`first-success`, which **slice-1 lenient eval (S92) auto-sparks** — the search
tree parallelises with **zero `spark`/`par` in the source**, and the
spark-budget create-gate bounds over-sparking (over budget → serial arm). See
`design/backend/lenient-eval.md` §2.5. (A `vec-map`-style cons-walk does **not**
parallelise — one expensive arg per node; only the two-expensive-arg D&C shape
does, which is why the reshape is D&C.) `solve`/`solve-range` are mutually
recursive; `solve`'s guess arm calls `solve-range` over the candidate Vec.

**Validation.** Full easy 9×9 solves end-to-end (`user.cl`). The exemplar suite
is **40/40 green** (added `solver/test-solve-parallel-equiv`, a
backtracking-requiring puzzle pinned to its unique solution) under **both**
default (parallel) and `CRANELISP_NO_LENIENT=1` (serial) — the **parallel ≡
serial** equivalence guard for the reshape. **Net wall-clock speedup is not yet
observable**: the copy-per-guess grid representation (quadratic, allocation-
dominated) masks the parallel gain — that is the **carried perf half** of FIXME
0408 (persistent/structural-share Vec or in-place candidate masks + a Phase-H
release backend). S92 delivers the parallel **expression**; the perf carry
stays open, and `test-hard-puzzle` stays excluded.

The Wave-4 "inherently sequential / counterexample" verdict in
`plan-exemplar.md` is superseded (constraint *propagation* is sequential, but
backtracking *search* is embarrassingly parallel — Sudoku is a showcase of
**budget-bounded speculative parallel search**).

## Current State (Sprint 91 Phase 6 — `grid.cl` bit layer on native primitives)

Five Cranelisp files: four pure-core modules (`grid`, `solver`, `html`,
`form`), the headline `user.cl` entry, plus a free-standing `tests.cl` runner.
All compile cleanly under the reimplementation compiler and run through the
stdio platform.

**S91 Phase 6 swap (this sprint).** S91 landed native bitwise primitives
(`bit-and`/`bit-or`/`bit-xor`/`bit-not`/`shl`/`shr`/`popcount`; FIXME 0416
RESOLVED) and `stdlib/num/bits.cl` was rewritten as a thin curated layer over
them — **dropping** the pre-S91 arithmetic-sim helpers `pow2`/`full-mask`/
`width`/`bit-at`. The S88 `grid.cl` adapters delegated to those dropped names
(`num.bits/pow2`, etc.) via FQ module-qualified calls, so the exemplar was
broken against the S91 stdlib. `grid.cl` now imports the live `num.bits`
primitives **by name** (`bit-shift-left`/`bit-test`/`bit-and`/`bit-or`/
`bit-not`/`popcount`) and its digit-domain adapters use them directly:
`pow2 n` → `(bit-shift-left 1 n)`, `bit-set? mask d` → `(bit-test mask (- d 1))`,
`bit-clear`/`bit-set` composed locally (avoiding the `num.bits` name collision),
`bit-count` → `popcount`; `bit-lowest` keeps its 1-9 scan. Behaviour verified
identical to the old arithmetic sim across all 512 masks × 9 digits (0
mismatches). Full 9×9 solve + 39/39 tests stay green. This is the end-to-end
validation that FIXME 0416 achieved its purpose.

## Current State (Sprint 88 Phase 5 Wave 4 / Stage D — stdlib-adoption refresh)

Five Cranelisp files: four pure-core modules (`grid`, `solver`, `html`,
`form`), the headline `user.cl` entry, plus a free-standing `tests.cl` runner.
All compile cleanly under the reimplementation compiler and run through the
stdio platform.

**S88 adoption swaps applied** (the S87 stdlib-adequacy review's adoption half;
see `notes-stdlib-adequacy-s87.md §FULL` G1–G10):

- **G2 — `vec-push` → `conj`.** Every heap-ADT (`Cell`) accumulator now uses
  the curated `collections.vec/conj` (`grid.cl` peers + make-grid, `solver.cl`
  + `html.cl` test grid builders). The DEF-2 carve-out is **RETIRED** — S88
  Step 3.1 confirmed `conj` is RC-identical to the bare `vec-push` (the earlier
  corruption was the collateral-fixed 0417 defect). Full 9×9 solve + 39/39 tests
  stay green.
- **G1-adoption — `grid.cl` bit layer → `num.bits`** *(refreshed S91 Phase 6 —
  see the top section)*. The ~55-line hand-rolled 9-bit mask simulation
  (`pow2`/`bit-set?`/`bit-clear`/`bit-set`/`bit-count`/`bit-lowest`) is replaced
  by thin *digit-1-9* domain adapters over `num.bits` — which is now the thin
  curated layer over the S91 native bitwise primitives (the S88-era delegation
  to the old arithmetic-sim `num.bits/pow2`/etc. is gone; those names were
  dropped in the S91 rewrite). The solver and tests are unchanged at grid's
  boundary.
- **G6 — `solver.cl` `digit-string`** 10-arm `if` → `(if (= v 0) "."
  (text.string/digit-to-char v))`.
- **G8 — `form.cl` `make-dots`** recursive loop → `(repeat-str "." 81)`.
- **G10 — `user.cl` `field-name`** reuses `grid/row-of`·`col-of` (col-of itself
  routes through `rem-i64`) instead of the inline idx → row/col duplication.

Not adopted (deliberate, flagged below): **G7** (`rem-i64` inline domain alias),
**G9** (`str` macro — the exemplar keeps the nested `str-concat` to avoid
show-dispatch overhead).

## Current State (Sprint 86 Phase 6b — idiom pass + headline entry)

Five Cranelisp files: four pure-core modules (`grid`, `solver`, `html`,
`form`), the headline `user.cl` entry, plus a free-standing `tests.cl` runner.
All compile cleanly under the reimplementation compiler and run through the
stdio platform.

**The full 9×9 grid solves end-to-end** (exit 0, valid solution) on the current
binary — `--run exemplar/solver.cl` and `--run exemplar/user.cl` both print the
puzzle and its complete solution. The earlier "segfaults on full grids" note is
**obsolete and removed** (resolved in the S80 full-grid-solve milestone).

**Idiom pass (S86):** the modules now consume the **curated surface** produced
by the S86 prelude de-leak — arithmetic and comparison go through the prelude's
trait operators (`+ - * / = != < <= >`), string equality through `=` (Eq on
String), and Vec access through the curated Clojure verbs `count`/`get`/`assoc`
imported from `collections.vec`. The ~190 raw `*-i64`/`str-eq`/`vec-*` call
sites are gone. Genuine domain helpers (`rem-i64`, `pow2`, the bitmask ops) are
kept but route their arithmetic through the operators. String primitives
(`char-at`, `str-concat`, `substring`, `split`, `replace`, `contains?`,
`int-to-string`) and boolean `not` are imported by name from `primitives`.

| File | Purpose | Status |
|------|---------|--------|
| `grid.cl` | Grid/Cell types, bitmask ops, index helpers, peers, make-grid, is-solved | Complete; idiomatic |
| `solver.cl` | eliminate, propagate, solve, board formatting, stdio `main` | Complete; idiomatic |
| `html.cl` | HTML generation (form page, solution page, error page) | Complete (10 tests) |
| `form.cl` | URL-encoded form body parsing | Complete (8 tests) |
| `user.cl` | **Headline entry** — full pipeline through stdio IO | Complete |
| `tests.cl` | Free-standing test runner (exit code = pass count) | Complete (40/40 green; parallel ≡ serial) |
| `main.cl` | Web routing + IO models | Not started (FIXME 0405, `/platform`) |

## Headline entry

`user.cl` is the showcase command. It wires all four modules together exactly
as the web platform would:

```
form body  --parse-form-body-->  puzzle string
puzzle     --make-grid-------->  Grid
Grid       --solve------------>  SolveResult
solution   --format-board----->  ASCII board (terminal view)
solution   --solution-page---->  HTML page   (browser view)
```

```bash
CRANELISP_PLATFORM_PATH=target/debug CRANELISP_LIB=stdlib \
  cargo run -- --run exemplar/user.cl
```

It encodes a known puzzle as a URL-encoded form body, round-trips it through
`form/parse-form-body`, solves it, and prints the input board, the ASCII
solution, and the byte-size of the rendered HTML solution page (exit 0).

`solver.cl` also has its own `main` (a simpler solve-and-print of a hard-coded
puzzle) for a quick smoke test.

## Tests

`tests.cl` is a **free-standing runner** following the `examples/` convention —
NO `(mod test)` submodules, NO `discover-tests` (those paths are blocked by
carried defects D3/D4/D5; the in-language runner is REPL-only). It imports each
module's `test-*` function (each returns `(Option String)`: `None` = pass), runs
them directly, and returns the number of passes as the process exit code.

```bash
CRANELISP_PLATFORM_PATH=target/debug CRANELISP_LIB=stdlib \
  cargo run -- --run exemplar/tests.cl
echo $?   # => 40  (all green)
```

The suite is green **40/40 under both default (parallel) and
`CRANELISP_NO_LENIENT=1` (serial)** — that two-mode green run is the
parallel ≡ serial equivalence guard for the S92 D&C search reshape
(`solver/test-solve-parallel-equiv`, a backtracking-requiring puzzle pinned to
its unique solution; ~8-9s, the carried copy-per-guess cost).

`solver/test-hard-puzzle` is still excluded from the runner (kept in
`solver.cl` as documentation): it is *correct* but the genuinely-hard
backtracking copies the whole 81-cell Vec on every guess, so it runs for
minutes. The easy puzzle, the `test-solve-parallel-equiv` search guard, and the
`eliminate`/`unsolvable` tests cover the solver path in the runner.

## Known Issues

- **Platform path**: `CRANELISP_PLATFORM_PATH=target/debug` is needed because
  `exemplar/` is not the project root where the stdio DLL lives. Without it,
  `(platform stdio)` fails with "platform not found".
- **DEF-2 — RETIRED (S88 Stage D).** The curated `collections.vec/conj` is now
  used for every heap-ADT (`Cell`) accumulator (grid cells, peer lists, test
  grid builders). The historical corruption (a Vec of `Cell` built via `conj`
  came out wrong, so the solver reported "No solution found") was the
  collateral-fixed **0417** defect; S88 Step 3.1 confirmed `conj` is
  RC-identical to the bare `vec-push` (full 9×9 solve + 39/39 tests green with
  `conj`). The exemplar no longer reaches for the bare `vec-push` primitive.
- **Hard-puzzle backtracking is quadratic** (performance, not correctness) —
  **the carried perf half of FIXME 0408**. `set-cell`/`assoc` copy the full
  81-cell Vec per guess; deep backtracking on hard puzzles is slow, and this
  copy cost dominates so heavily it **masks the parallel-search speedup** (the
  S92 D&C reshape parallelises structurally but shows no net wall-clock gain
  until this is fixed). A future representation (persistent/structural-share
  Vec, or in-place candidate masks) would fix it, alongside a Phase-H
  release/Tier-2 backend. Not blocking the showcase. `test-hard-puzzle` stays
  excluded from the runner until then; `test-solve-parallel-equiv` (a
  shallower-search puzzle, ~8-9s) is the in-suite search guard.

## Design Decisions

- **Bitmask representation**: Candidates stored as a 9-bit integer mask (bits
  0-8 for digits 1-9), not a `(Vec Int)`. Avoids heap allocation for candidate
  tracking; operations are O(1).
- **Bitwise via `num.bits` (stdlib, native-primitive-backed)** *(S91 Phase 6;
  was S88 "Bitwise via num.bits", originally "No bitwise primitives")*:
  **Cranelisp now HAS native bitwise primitives** (S91, FIXME 0416 RESOLVED:
  `bit-and`/`bit-or`/`bit-xor`/`bit-not`/`shl`/`shr`/`popcount`, each lowering
  1:1 to a CLIF op — spec appendix-a-builtins §A.3). The stdlib `num.bits`
  module is now a thin curated layer over those primitives (full surface:
  `bit-and`/`bit-or`/`bit-xor`/`bit-not`/`bit-shift-left`/`bit-shift-right`/
  `bit-test`/`bit-set`/`bit-clear`/`bit-flip`/`popcount`/`bit-count`). `grid.cl`
  imports `bit-shift-left`/`bit-test`/`bit-and`/`bit-or`/`bit-not`/`popcount`
  by name and keeps only thin *digit-1-9* domain adapters
  (`pow2`/`bit-set?`/`bit-clear`/`bit-set`/`bit-count`/`bit-lowest`) over the
  *bit-position-0-8* primitives. The earlier inline ~55-line arithmetic
  simulation is gone (the S88 adapters that delegated to the old
  arithmetic-sim `num.bits` are gone too — that module was retired in S91).
  **Width note:** the native ops are full **64-bit two's-complement** (no WIDTH
  cap; `bit-not 0 = -1`, the sign bit participates). The Sudoku candidate masks
  are always **9-bit (bits 0-8, positive)**, so the sign bit never participates.
  Verified behaviour-identical to the old arithmetic sim across the entire
  domain — all **512 masks × 9 digits** plus `pow2 0..8`: **0 mismatches**.
  Grid's `bit-clear`/`bit-set` are composed locally
  (`(bit-and mask (bit-not (shl 1 (- d 1))))` / `(bit-or mask (shl 1 (- d 1)))`)
  rather than imported, because `num.bits`'s position-domain `bit-clear`/
  `bit-set` names would collide with grid's digit-domain ones.
- **No `mod`/`rem` operator — `rem-i64` kept inline (G7, deliberate
  non-adoption)**: `num.int/rem` exists with identical semantics, but `rem-i64`
  is kept as a documented domain helper, defined inline as
  `(- a (* (/ a b) b))`. Routing the index helpers (`col-of`/`box-of`) through
  a single local domain name reads cleaner than a cross-module import for one
  arithmetic identity; the S87 adequacy review (G7) flagged this as
  "flag, don't force."
- **`char-at` dependency**: `make-grid` parses strings character-by-character
  using `char-at`. Available via the string primitives.
- **String building via `str-concat` — `str` macro NOT adopted (G9, deliberate
  non-adoption)**: `html.cl` builds HTML purely through nested `str-concat`. The
  `text.string/str` macro exists and would flatten the pyramids, but the
  exemplar avoids it to keep no `str`-macro / `show`-dispatch overhead in
  production. The S87 adequacy review (G9) flagged this as "list as available,
  do not force."
- **Form parsing via `split`**: `form.cl` uses `split` on `&`/`=` and `char-at`
  for field names; reconstructs the puzzle string with `substring`+`str-concat`.

## Conventions

- The exemplar MAY depend on stdlib (root CLAUDE.md §Stdlib separation — only
  `exemplar/` and `src/main.rs` may); it uses the curated prelude surface.
- Idiomatic surface: trait operators bare via prelude; curated Vec verbs
  (`count`/`get`/`assoc`/`conj`) imported from `collections.vec`; bitwise via
  `num.bits`; `digit-to-char`/`repeat-str` from `text.string`; string
  primitives + `not` imported by name from `primitives`. (The S88 Stage D
  adoption refresh applied G2/G1-adoption/G6/G8/G10; G7/G9 left as deliberate
  non-adoptions.)
- Test functions are top-level `test-*` defns returning `(Option String)`
  (`None` = pass, `(Some why)` = fail) per `repl/spec.md §16.1`. They are run by
  the free-standing `tests.cl` runner — NOT `(mod test)` / `discover-tests`
  (Decision 30 deadlock + REPL-only discovery).
- Every batch `main` returns `(IO _)` via `(Pure n)` or a `bind` chain; the
  inner Int is the exit code.
