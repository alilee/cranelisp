# exemplar/

Exemplar project for Cranelisp: a Sudoku Solver with Web Platform. Owned by `/port` skill.

## Current State (Sprint 14)

Four pure-core modules implemented:

| File | Purpose | Status |
|------|---------|--------|
| `grid.cl` | Grid/Cell types, bitmask ops, index helpers, peers, make-grid, is-solved | Complete |
| `solver.cl` | eliminate, propagate, find-min-candidates, solve (backtracking) | Complete |
| `html.cl` | HTML generation (form page, solution page, error page) | Complete (10 tests) |
| `form.cl` | URL-encoded form body parsing | Complete (8 tests) |
| `main.cl` | Request routing, IO models | Not started (Ring 4) |

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
