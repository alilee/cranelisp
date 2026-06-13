# exemplar/

Exemplar project for Cranelisp: a Sudoku Solver with Web Platform. Owned by `/port` skill.

## Current State (Sprint 81)

Four pure-core modules implemented, solver.cl has IO output. Validated under the
reimplementation compiler — all four modules compile cleanly and the entry
module runs through IO to print the puzzle board **and the full solution**.
The full 9×9 grid solves end-to-end (exit 0, valid solution) on the current
binary; this is locked by the S80 full-grid-solve milestone and re-verified in
S81 (`--run exemplar/solver.cl`). The earlier solve-step segfault is resolved —
no longer an issue.

Post-Sprint-57 updates applied to the exemplar:
- Added explicit `(import [primitives [*]])` to each module. The current prelude
  does not re-export primitives like `eq-i64`/`add-i64`/`not` — modules that use
  primitive names directly must import them.
- Converted `(const full-mask 511)` to `(defn full-mask [] 511)` and updated all
  call sites to `(full-mask)`. The `const` macro creates a compile-time bare-symbol
  expansion that is not visible through cross-module glob imports.
- Disabled the inline `(mod test ...)` submodules in all four files via FIXME
  comment. These exercised `(import [super [*]])` which deadlocks against the
  v4 form-by-form scheduler per Decision 30 (see `design/arch/CLAUDE.md`).
  Wave 0's super-rewrite lands correctly at the frontend boundary, but the
  full pipeline cannot typecheck parent-child inline submodule pairs because
  the child's super-import blocks on the parent, and the parent blocks on
  `(mod test)` until the child is typechecked. Re-enable the test submodules
  once the scheduler supports sibling super-import, or migrate them to the
  `discover-tests` / `run-test` builtin pattern per spec §8.3.7 warning.



| File | Purpose | Status |
|------|---------|--------|
| `grid.cl` | Grid/Cell types, bitmask ops, index helpers, peers, make-grid, is-solved | Complete |
| `solver.cl` | eliminate, propagate, solve, board formatting, IO main | Complete (IO added) |
| `html.cl` | HTML generation (form page, solution page, error page) | Complete (10 tests) |
| `form.cl` | URL-encoded form body parsing | Complete (8 tests) |
| `main.cl` | Request routing, IO models | Not started (Ring 4) |

## IO Output

`solver.cl` has a `main` function that uses IO to print a formatted Sudoku board and its solution. Run with:

```bash
CRANELISP_PLATFORM_PATH=target/debug CRANELISP_LIB=stdlib cargo run -- --run exemplar/solver.cl
```

The puzzle input board displays correctly, the solve step runs to completion, and the solved board prints. The whole run exits 0 with a valid solution. The IO plumbing (`platform stdio`, `print`, `bind`, `Pure`) and the solver (`eliminate`/`propagate`/`solve`) are all verified working end-to-end on the full 81-cell grid.

## Known Issues

- **Platform path**: The `CRANELISP_PLATFORM_PATH` env var is needed because `exemplar/` is not the project root where the stdio DLL lives. Without it, `(platform stdio)` fails with "platform not found".

## Design Decisions

- **Bitmask representation**: Candidates stored as a 9-bit integer mask (bits 0-8 for digits 1-9), not a `(Vec Int)`. This avoids heap allocation for candidate tracking and makes operations O(1).
- **No bitwise primitives**: Since Cranelisp lacks `bit-and`/`bit-or`/`bit-shift`, bitmask operations are simulated via `div-i64`/`mul-i64`/`sub-i64` and a `pow2` helper. Works correctly for 9-bit masks.
- **No `mod`/`rem` primitive**: `rem-i64` defined inline as `a - b * (a / b)`.
- **`char-at` dependency**: `make-grid` parses strings character-by-character using `char-at`. Now available via F2 string primitives (Sprint 14).
- **String building via `str-concat`**: `html.cl` builds HTML purely through nested `str-concat` calls. No `str` macro usage in production code (avoids `show` trait dispatch overhead), only in tests if needed.
- **Form parsing via `split`**: `form.cl` uses `split` to break URL-encoded body on `&` and `=`, then `char-at` for field name parsing. Reconstructs puzzle string using `substring` + `str-concat`.

## Conventions

- Uses prelude (exemplar is allowed to depend on stdlib, unlike tests/examples)
- Prelude macros used: `const` (for `full-mask`), `cond` (in form.cl for digit parsing)
- All functions use monomorphic named primitives (`add-i64`, `eq-i64`, etc.) for clarity and to avoid trait dispatch overhead in tight loops
- Test submodules use `(mod test ...)` inline syntax with `(import [super [*]])`
- Test main functions return sum of test results (1 per passing test)
