# exemplar/

Exemplar project for Cranelisp: a Sudoku Solver. Owned by `/port` skill.

The **committed showcase target is the stdio CLI** — `user.cl` tells the full
story end-to-end. The web platform is a designed-but-unbuilt future stretch
(FIXME 0405, `/platform`); see `plan-exemplar.md`.

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
| `tests.cl` | Free-standing test runner (exit code = pass count) | Complete (39/39 green) |
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
echo $?   # => 39  (all green)
```

`solver/test-hard-puzzle` is excluded from the runner (kept in `solver.cl` as
documentation): it is *correct* but the genuinely-hard backtracking copies the
whole 81-cell Vec on every guess, so it runs for minutes. The easy puzzle plus
the `eliminate`/`unsolvable` tests cover the solver path in the runner.

## Known Issues

- **Platform path**: `CRANELISP_PLATFORM_PATH=target/debug` is needed because
  `exemplar/` is not the project root where the stdio DLL lives. Without it,
  `(platform stdio)` fails with "platform not found".
- **DEF-2 — curated `conj` corrupts heap-ADT elements (carried defect; repro
  queued for `/qa`).** The exemplar uses the bare `vec-push` primitive instead
  of the curated `collections.vec/conj` wrapper everywhere it accumulates a Vec
  of heap ADTs (grid cells, peer lists). The `conj` wrapper
  (`(defn conj [v x] (vec-push v x))`) mis-manages the refcount of a heap-ADT
  element passed through its call frame: a Vec of `Cell` values built via `conj`
  in an accumulator loop comes out **corrupted**, so the solver finds spurious
  contradictions and reports "No solution found". `count`/`get`/`assoc` are
  unaffected and ARE used idiomatically. Int-valued `conj` is also unaffected.
  Minimal repro: accumulate a `(Vec Box)` (ADT) via `conj` vs `vec-push` in a
  30-iteration loop and compare element sums — they differ. This is a
  wrapper-RC / consuming-calling-convention bug, distinct from DEF-1 (which is
  about re-exported `defn` bodies never reaching codegen — `conj` here DOES run,
  just wrong). Swap `vec-push`→`conj` once it lands.
- **Hard-puzzle backtracking is quadratic** (performance, not correctness).
  `set-cell`/`assoc` copy the full 81-cell Vec per guess; deep backtracking on
  hard puzzles is slow. A future representation (persistent Vec, or in-place
  candidate masks) would fix it. Not blocking the showcase.

## Design Decisions

- **Bitmask representation**: Candidates stored as a 9-bit integer mask (bits
  0-8 for digits 1-9), not a `(Vec Int)`. Avoids heap allocation for candidate
  tracking; operations are O(1).
- **No bitwise primitives**: Cranelisp lacks `bit-and`/`bit-or`/`bit-shift`, so
  bitmask operations are simulated via `/`, `*`, `-` and a `pow2` helper. Works
  for 9-bit masks.
- **No `mod`/`rem` operator**: `rem-i64` is a genuine domain helper, defined
  inline as `(- a (* (/ a b) b))`.
- **`char-at` dependency**: `make-grid` parses strings character-by-character
  using `char-at`. Available via the string primitives.
- **String building via `str-concat`**: `html.cl` builds HTML purely through
  nested `str-concat`. No `str`-macro / `show`-dispatch overhead in production.
- **Form parsing via `split`**: `form.cl` uses `split` on `&`/`=` and `char-at`
  for field names; reconstructs the puzzle string with `substring`+`str-concat`.

## Conventions

- The exemplar MAY depend on stdlib (root CLAUDE.md §Stdlib separation — only
  `exemplar/` and `src/main.rs` may); it uses the curated prelude surface.
- Idiomatic surface: trait operators bare via prelude; curated Vec verbs
  (`count`/`get`/`assoc`) imported from `collections.vec`; string primitives +
  `not` imported by name from `primitives`. (See the DEF-2 `conj` carve-out.)
- Test functions are top-level `test-*` defns returning `(Option String)`
  (`None` = pass, `(Some why)` = fail) per `repl/spec.md §16.1`. They are run by
  the free-standing `tests.cl` runner — NOT `(mod test)` / `discover-tests`
  (Decision 30 deadlock + REPL-only discovery).
- Every batch `main` returns `(IO _)` via `(Pure n)` or a `bind` chain; the
  inner Int is the exit code.
