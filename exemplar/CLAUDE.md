# exemplar/

Exemplar project for Cranelisp: a Sudoku Solver. Owned by `/port` skill.

The **committed showcase target is the stdio CLI** — `user.cl` tells the full
story end-to-end. The web platform is now built (S96) and is the marquee for
**inferred concurrency**; see the S96 Phase 6 note below and `plan-exemplar.md`.

## Current State (Sprint 98 Phase 6 — exemplar adopts the v9 ctx-vtable handle model + marquee replays GREEN)

The web exemplar is now on the **v9 ctx-vtable handle model** (S97 model pivot;
`design/platform/poll-support.md` §3.5, `design/arch/effect-concurrency.md`
§4.1.1). Scheduling state (token/capacity) **never rides on a value** — it flows
through a trampoline-owned `ctx` vtable the platform's poll-fns call. Concretely:

- **`web/Connection` is a slim OPAQUE handle** carrying only the platform's `r`
  in a GENUINE `fd` field (`(deftype Connection [:primitives/Int fd])`); the
  platform reads `fd` back and PROJECTS the per-direction token from it. No
  `token`/`capacity` fields (the dead v8 leading-pair shape), no header slot, no
  user-visible descriptor.
- **`serve.cl` wrappers are near-trivial pass-throughs** — no leading
  `(token, capacity)` pair to thread, no descriptor to read/write. `read`/`send`
  take the opaque handle directly; `accept` takes the `Listener` directly.
- **`web.cl` / `serve.cl` are byte-identical to the v9 reference fixture**
  `tests/fixtures/web_fanout/` (the S97-cutover reference). `main.cl` is the full
  Sudoku-over-HTTP showcase (differs from the reduced fixture `main.cl` only in
  routes: `/solve` parse→solve→render vs the fixture's `/fault` witness) and uses
  the v9 imports (`[serve [listen accept]]` + raw `[platform.web [read-conn
  send-conn]]`) and the v9 serve-loop (opaque `conn` threaded directly into the
  Consume poll leaves). The one stale v8 comment in `main.cl` (wrappers "supply
  the poll leading (token, capacity) pair") was reconciled to v9.

**Marquee replays GREEN — and this is the real-showcase validation that bug #2
(0494) holds.** `tests/exemplar_web.rs` (both tests un-ignored after 0494,
`5ca6ef2`):

- `exemplar_web_server_serves_form_solution_and_not_found_over_http` — spawns the
  live `--run exemplar/main.cl` server, POSTs a puzzle, and asserts the rendered
  solution page is a COMPLETE VALID sudoku (30 given + 51 solved cells) across the
  host↔DLL boundary. This is the end-to-end proof the 0494 launched-strand
  borrowed-`conn` double-free fix holds in the full showcase (not just the reduced
  `launch_grid_corrupt` guard).
- `exemplar_web_server_fans_out_concurrent_requests_overlap` — the no-`spawn`
  marquee: K=4 concurrent `/slow` requests OVERLAP (≈1·D) instead of serialising
  (≈K·D).

Both are process-managed + killed on drop, bounded by a 20 s readiness deadline —
safe under nextest (the idle-armed-server S98 `0479` survive-forever caveat is why
a bare foreground `--run` on a server hangs; these tests never wait on exit).
Full `cargo nextest run`: **1795 passed, 1 skipped, 0 failed** (the skip is the
`concurrency_spark` perf benchmark, `#[ignore]`'d). The non-web Sudoku showcase
(`user.cl`/`solver.cl`/`tests.cl`) is untouched by this sprint.

Doc-only residue filed to `/qa` (FIXME 0498): `tests/exemplar_web.rs`'s header
still reads "STILL IGNORED/QUARANTINED" though the tests are un-ignored + green.

## Current State (Sprint 96 Phase 6 — web server adopts the inferred concurrent fan-out)

The exemplar **`web` server (`main.cl`) now genuinely fans out** — a "server
with no `spawn`". The serve loop INFERS launch-and-continue concurrency: the
per-connection handler is inlined as a sub-tree of DIRECT poll/timer leaves
(`read-conn` → `(sleep (slow-ms req))` → `send-conn`), its result DISCARDED (the
`do`) and its footprint disjoint from the continuation's `listener`, so /int's
bind-chain analysis (`effect-concurrency.md §4.1` E1/E2/E3) infers a detached
launch — one supervised strand per connection. There is **NO `spawn`/`go`/`async`
in the source**. This mirrors the reference fixture
`tests/fixtures/web_fanout/main.cl` (byte-identical `web.cl`/`serve.cl`).

**The direct-leaf discipline (why the launch fires):** every EFFECT POSITION in
the handler sub-tree is a direct launchable leaf — `read-conn`/`send-conn`
(ResourceSerial poll over the fresh connection token) or `sleep` (the
resource-free timer leaf, §4.1 timer refinement). The pure helpers `slow-ms`
(`Request -> Int`, the per-request delay) and `safe-handle` (`Request ->
Response`, the 500-safe router) only compute leaf ARGUMENTS — they are never
themselves placed in an effect position. A user function returning IO in an
effect position (the retired `handle-conn` wrapper, or a `(slow-delay req)`
returning `(IO _)`) is an opaque footprint the eligibility analysis REFUSES (E3),
silently serialising the server — that was the S96 0470 wall, now avoided here.

**500-on-fault preserved:** `safe-handle` runs the pure router under
`catch-runtime-error` → a faulting request yields a 500 page for THAT request,
the serve loop keeps living (reactor.md §2.12, the application-layer 500).

**Proof:** `tests/exemplar_web.rs` — two green e2e:
`exemplar_web_server_serves_form_solution_and_not_found_over_http` (serves the
form / a valid solved grid / 404, all through the launched handler) and
`exemplar_web_server_fans_out_concurrent_requests_overlap` (K=4 concurrent
`/slow` requests OVERLAP ≈1·D ≈110ms, NOT serialise ≈K·D ≈440ms — the ratio
assertion; deterministic, 5/5 green). The harness is now port-parametrized
(ephemeral port via `CRANELISP_PORT`), retiring the fixed-8080 collision. The
exemplar-scale counterpart of `tests/concurrency_fanout_web.rs`.

Demonstration endpoint: `GET /slow` returns a plain 200 after a deterministic
100 ms `(sleep …)` — the concurrency witness. All real routes (`/`, `/solve`,
404) stay instantaneous (`slow-ms` returns 0). The Sudoku core
(`handle`/`solve-route`/`solution-page`/`parse-form-body`) is unchanged and
pure. The non-web Sudoku showcase (`user.cl`/`solver.cl`/`tests.cl`) is
untouched by this sprint.

## Current State (Sprint 95 Phase 6a — assessment: exemplar untouched, web rewrite is S96)

**No S95 exemplar work — confirmed read-only.** S95 advanced only the
**Concurrency axis** (token-capacity `Semaphore` pool + two-pool routing,
`concurrency-runtime`-gated, default build byte-identical). The pool was proven
on the **BLOCKING carrier** using a synthetic `pool-demo` fixture *inside*
`cranelisp-platform` — **not** the exemplar. The exemplar's `web` platform
(`exemplar/platforms/web/src/lib.rs`) is **still v6 blocking**, verified:
`declare_platform!` (not `declare_concurrent_platform!`), three
`SchedulingClass::Sequential` effects (`listen`/`accept`/`send`), single
in-flight accepted stream, no poll-shape / token / capacity. The S94 parallel
Sudoku solver (0424 spark substrate, `par-map-reduce` search) is **unchanged**
by S95 — the perf carry (FIXME 0408 perf half: copy-per-guess contention) is a
**Parallelism-axis** problem re-scoped to **S97** (the floor/atomic-RC knot),
with raw-speed numbers still wanting `--release` (Phase H).

**The exemplar's capacity/web work is entirely S96** — the natural consumer of
the capacity-on-token model is the web platform's reactor **connection pool**,
which needs three things S95 explicitly deferred: (1) **poll-shape live capacity
supply + acquire-around-poll** (the permit wrapping the `EffectPoll`
establish→ready arc), (2) the **`poll_support` ergonomics** suite (typed env
accessor, fd-readiness/timer scaffold, converged platform macro), and (3)
**slice 5** (launch-and-continue + supervisor) so the "server with no `spawn`"
demo can exercise it. All three are S96; co-scheduling the web rewrite with
slice 5 is deliberate (a server demo is only meaningful on real poll
`accept`/`read` leaves). No S95-surfaced gap to file — the S96 web-rewrite
milestone is already in `sprints/ROADMAP.md`, and the only open FIXME targeting
`/port` is **0408** (perf half, deferred Phase H).

### S96 Phase 6b plan (the web v7 rewrite)

Rewrite `exemplar/platforms/web/` from a v6 blocking `declare_platform!`
platform into a **model v7 concurrent platform**: replace the single-stream
blocking `accept`/`send` with **poll-shape `accept` and `read`** leaves (over
the `poll_support` env-accessor + host/waker vtable extracted evidence-first in
S96), introduce a **reactor connection-pool token of capacity N** so up to N
in-flight connections overlap on the one reactor thread while the (N+1)th parks
(the real **capacity-on-poll** consumer that lights up S95's deferred
acquire-around-poll half), and wire it to the **slice-5 server-with-no-`spawn`**
demo (a panicking handler → 500 while the server survives) so the existing pure
core (`handle`/`solution-page`/`parse-form-body`, already complete and tested)
drives a genuinely concurrent server — validating the capacity-on-token model at
the §10/§16 reference workload end-to-end, with the v6 path coexisting via the
additive ABI (no version flip). Owner: `/port` + `/platform`.

## Current State (Sprint 94 Phase 6 — parallel search via stdlib `par-map-reduce`)

The parallel backtracking search is now expressed with the **stdlib
`collections.parallel/par-map-reduce`** instead of the hand-rolled
`solve-range` divide-and-conquer. The Sudoku search *is* a map-reduce over the
candidate digits: **map** each candidate `d` to its recursive solve
`(solve (set-cell g2 idx (Solved d)))`, **reduce** the per-digit results with
the associative `first-success` (identity `Unsolvable`). The `solve` guess arm
(`solver.cl`) now reads:

```
(par-map-reduce
  (fn [d] (solve (set-cell g2 idx (Solved d))))
  first-success
  Unsolvable
  digits)
```

`par-map-reduce` splits the digit Vec at its midpoint into two **independent
`let` bindings** that the sparkability analysis auto-sparks (lenient-eval §2.1)
— so the search tree still parallelises with **no `spark`/`par` in the
source**, and the create-gate still bounds in-flight sparks. `solve-range` is
**retired**; `mask-to-digits` and `first-success` stay (now the map collection
and the associative reducer). This adopts the canonical library the substrate
shipped this sprint and is the cleaner showcase ("search = parallel map-reduce
over candidates"). `grid.cl` untouched.

**Correctness floor re-verified.** Exemplar suite **40/40 green under both
default (parallel) and `CRANELISP_NO_LENIENT=1` (serial)**; `solver.cl` and
`user.cl` produce the **identical** solution to the pre-change baseline (the
parallel ≡ serial equivalence guard, `solver/test-solve-parallel-equiv`).

**Perf finding (the carried half of FIXME 0408, now QUANTIFIED as a floor
violation).** A/B timing shows the parallel search is currently ~**10× SLOWER**
than serial on the debug backend, not merely "no speedup": the full suite runs
~20 s parallel vs ~1.9 s serial, and the slowdown is **sys-time dominated**
(~21 s sys parallel vs ~0.05 s serial; user ~43 s = many cores busy). This is
**not** introduced by the `par-map-reduce` reshape — the retired `solve-range`
shape measured identically (~19.5 s / ~1.7 s). Root cause, isolated with a
free-standing repro ladder (pure compute → int-Vec copy → ADT-Vec copy): the
**copy-per-guess + heap-`Cell` allocation** generates **allocator-lock and
atomic-RC contention** that scales the parallel penalty (pure compute: parallel
≈ serial, sys≈0; ADT-Vec copy: parallel 1.4× slower, 9× user CPU, elevated
sys; Sudoku: 10× slower, sys-saturated). The create-gate bounds spark *count*
but not the *shared-resource contention each sparked branch generates*, so
allocation-dominated parallel work violates the never-slower-than-serial floor.
The fix is unchanged (FIXME 0408 perf half): a non-copying grid representation
(persistent / structural-share Vec, or in-place candidate masks) + a Phase-H
release backend. Repro handed to `/qa` (see report); `test-hard-puzzle` stays
excluded.

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
