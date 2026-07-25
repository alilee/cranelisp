# exemplar/

Exemplar project for Cranelisp: a **Sudoku Solver**. Owned by the `/port` skill.

Two coexisting showcases share one pure core:

- **stdio CLI — the committed showcase.** `user.cl` tells the full story
  end-to-end: parse a form body → build a grid → solve → render both an ASCII
  board and an HTML solution page. This is the canonical "does the language
  work for a real program" demonstration.
- **web server — the concurrency marquee.** `main.cl` serves Sudoku over HTTP
  and is a *server with no `spawn`*: the per-connection fan-out is **inferred**
  by the compiler, not written by hand (see Current State).

The exemplar is one of only two trees permitted to depend on `stdlib/` (the
other is `src/main.rs`; root CLAUDE.md §"Stdlib separation").

## Current State

**Sources on disk (all tracked, all compile under the reimplementation
compiler):**

| File | Purpose |
|------|---------|
| `grid.cl` | Grid/Cell ADTs, 9-bit candidate bitmask ops, index helpers, peers, `make-grid`, `is-solved` |
| `solver.cl` | `eliminate`/`propagate`/`solve` (constraint prop + parallel backtracking search), board formatting, stdio `main` |
| `html.cl` | HTML generation (form page, solution page, error page) |
| `form.cl` | URL-encoded form-body parsing |
| `user.cl` | **Headline stdio entry** — full pipeline through stdio IO |
| `tests.cl` | Free-standing test runner (exit code = pass count) |
| `web.cl` / `serve.cl` / `main.cl` | Web showcase: opaque `Connection`/`Listener` types, serve-loop wrappers, HTTP router + serve loop |
| `platforms/web/` | The `web` platform DLL (Rust): HTTP parse + poll-shape leaves |

The `collections/`, `compare/`, `fn/`, `num/`, `text/` trees hold
module-mirroring `test.cl` fixtures that assert stdlib surfaces via
`testing.assertions` — separate from the Sudoku showcase.

**stdio showcase runs end-to-end.** `--run user.cl` prints the parsed board,
the ASCII solution, and a rendered HTML solution page, exit 0. Run with:

```bash
CRANELISP_PLATFORM_PATH=target/debug CRANELISP_LIB=stdlib \
  cargo run -- --run exemplar/user.cl
```

`solver.cl` also carries its own simpler `main` (solve-and-print a hard-coded
puzzle) for a quick smoke test.

**S115 Phase-6a re-verification.** `--run` and `--link` are **byte-identical**
on the headline entry; `tests.cl` is **40/40 under both** the default (parallel)
and `CRANELISP_NO_LENIENT=1` (serial) toggles; the sprint's language rulings had
**zero impact** on exemplar source — no line changed. The exemplar's one open
finding at S115 is the solve-path leak below, which is a compiler defect, not an
exemplar one.

**S117 Phase-6b verification.** The headline `--run` exits 0 from both cold and
warm cache with byte-identical stdout. `tests.cl` remains 40/40 under both
default parallel and `CRANELISP_NO_LENIENT=1` serial execution; this includes
all eight form tests, so the real `form.cl` pipeline exercises R-3-backed
`split` on both `=` and `&`. A proposed showcase adoption of
`(impl text.display/Display Cell …)` was reverted: fresh compilation succeeds,
but an explicit warm-cache `(show (Given 5))` probe loses the sibling-written
impl with `no impl of trait text.display/Display for type grid/Cell`, exactly
the open FIXME 0869 defect. The exemplar retains its established bare spelling
and takes no cache workaround.

Standalone Link parity could not be re-established in this environment:
isolated cold-cache linking fails before producing an executable because the
rebuilt stdio/web platform archives contain unresolved Rust/platform symbols.
This is not the FIXME 0869 face and no exemplar source workaround was made.
W3b REPL introspection, deferred W3c presentation, and design-only Byte-backed
text have no exemplar impact.

**Parallel search (no `spark`/`par` in the source).** The backtracking search
in `solver.cl` is expressed as `collections.parallel/par-map-reduce` over the
candidate digits at each guess node — **map** each candidate to its recursive
solve, **reduce** with the associative `first-success` (identity `Unsolvable`).
`par-map-reduce` splits the digit Vec into independent `let` bindings that the
sparkability analysis auto-sparks (lenient eval), so the search tree
parallelises structurally with no concurrency keyword in the source. This is
*budget-bounded speculative parallel search*: the loser branch's work is pure
and simply discarded, and `first-success` is correct regardless of evaluation
order. The design write-up (with the "constraint propagation is sequential but
search is embarrassingly parallel" correction) lives in `plan-exemplar.md`
§"Wave 4 Parallelism Opportunities Assessment" — do not restate it here.

**web marquee runs concurrently with no `spawn`.** `main.cl` serves Sudoku over
HTTP. The serve loop INFERS launch-and-continue concurrency: the per-connection
handler is inlined as a sub-tree of DIRECT poll/timer leaves (`read-conn` →
`sleep` → `send-conn`), its result discarded and its footprint disjoint from
the continuation's `listener`, so the compiler's bind-chain analysis
(`design/arch/effect-concurrency.md` §4.1) infers a detached launch — one
supervised strand per connection. The platform DLL uses `declare_platform!`
(mixed shape): `bind-listener` is `SchedulingClass::Sequential`, while
`accept-conn`/`read-conn`/`send-conn` are poll-shape leaves (Produce/Consume
descriptors). `web/Connection` is a slim OPAQUE handle carrying only the socket
`fd` (the v9 ctx-vtable handle model — scheduling state never rides on a value;
`design/arch/effect-concurrency.md` §4.1.1). A faulting request yields a 500
for THAT request while the serve loop keeps living. Run:

```bash
CRANELISP_PLATFORM_PATH=target/debug CRANELISP_LIB=stdlib \
  cargo run -- --run exemplar/main.cl   # serves until killed
```

**Performance carry (FIXME 0408 → backlog).** The hard-puzzle backtracking is
quadratic: `set-cell`/`assoc` copy the whole 81-cell Vec per guess, and this
allocation-dominated copy generates allocator-lock + atomic-RC contention that
masks the parallel-search speedup (parallel is not yet faster than serial on
allocation-heavy hard puzzles). This is a **performance** finding, not a
correctness defect. FIXME 0408 was consolidated into the perf backlog at S106;
the durable record is `design/arch/backlog/performance.md` §"0408 — Sudoku
exemplar copy-per-guess allocator/atomic-RC contention". A non-copying grid
representation (persistent/structural-share Vec or in-place masks) plus a
Phase-H release backend is the fix. `test-hard-puzzle` stays excluded from the
runner until then.

**Solve-path never-freed leak (FIXME 0810 + 0782; distinct from 0408).**
A full serial solve leaks ~11.8k objects. All numbers below are `--run
exemplar/solver.cl` with `CRANELISP_NO_LENIENT=1 CRANELISP_RC_STATS=1`, warm
cache (a cold cache adds a constant ~1,042 compile-session objects — always
compare warm to warm):

| Measurement | allocs / deallocs | residue |
|---|---|---|
| Full serial solve, HEAD | 26457 / 14637 | **11,820** |
| Full serial solve, `4d20cea1` (pre-S115 RC wave) | — | 11,823 |
| Propagation-only probe (no closure, no `par-map-reduce`, no guessing) | — | 11,765 |
| Full solve with the `Option` wrappers ablated off the propagation path | 14771 / 13459 | **1,312** |

**The S114 attribution is FALSIFIED.** S114 blamed `set-cell`'s match-extract →
COW → re-wrap → supersede shape ("2 objects/iteration × ~5.9k supersedes").
`set-cell` is **exonerated by measurement**: in isolation, a tail loop of N
`set-cell` calls is exact and non-scaling (N=100 → 1278/1277, N=1100 →
4278/4277 — residue 1, slope 0). So is `peers` (N=1100 → 23101/23101, exact).
The S115 RC wave moved the total by **3 objects (0.025%)**, which is why the
"fixed S115 in one RC-release sweep" expectation never landed.

**The real mechanism is FIXME 0810** — `match` over an **owned ADT temporary**
under a constructor pattern, which has two faces and no correct spelling:

- **Face A (leak)** — the scrutinee spelled INLINE never releases the wrapper
  box: `(match (eliminate g peer-idx d) [None … (Some g2) …])`. Slope is exactly
  1 object/iteration; with a heap payload the box AND its field strand together
  (slope 2).
- **Face B (over-release)** — the SAME program with the scrutinee LET-BOUND
  frees the wrapper while the extracted payload is still live: SIGBUS in
  `--run`, heap-corruption abort in `--link`, from **N=1**. RC *balances* on this
  face, so a balance-only check cannot see it.

FIXME 0782 is the var-pattern sibling of the same seam (double release). Both
are pinned by `tests/match_owned_temporary_scrutinee_0810.rs` (14 cells, 10 RED
/ 4 GREEN controls, both modes, both ownership toggles) — that file, not this
paragraph, is the durable record and the trigger.

**How much of the exemplar's residue is 0810 — measured, not inferred.**
Ablating the `Option` wrapper off the propagation path (`eliminate`,
`eliminate-from-peers`, `propagate-pass-helper`, `propagate` return a `Grid`
directly; the easy puzzle still solves, exit 0) drops the residue from 11,820 to
**1,312** — **10,508 objects, 88.9%, is 0810 and nothing else**. Of that,
~9,945 is `eliminate` alone: an alloc-counter probe shows **11,120 `eliminate`
calls** per solve (556 `eliminate-from-peers` × 20 peers), each returning one
`(Some g)` box that is never released.

**Acceptance criterion for the fix: the warm-cache serial-solve residue must
drop from 11,820 to ≈1,300 — not to zero.** Landing materially above ~2,000
means the fix is partial.

**The remaining ~1,300 is a SEPARATE, smaller, work-scaling leak** (FIXME
0840), not the wrapper mechanism and not a constant: 81 `eliminate-from-peers`
calls with zero `set-cell`s leave residue 83 (≈1.0/call), while 556 calls with
392 `set-cell`s leave 1,256 (≈1.0/call + ≈1.8/set-cell). Neither component
reproduces in isolation — `peers` and `set-cell` are each exact on their own —
so it only appears in **composition**, where a `Gr` box owning a cells `Vec` is
carried alongside a peer-list `Vec` through a tail loop.

**Both of these are the same class as FIXME 0837** (`/arch`): *ownership of heap
that owns further heap — exact at depth 1, wrong at depth ≥ 2*. The exemplar's
residue is the application-scale instance of it. 0810's heap-payload face
strands the box AND its field; the ~1,300 residual is only visible once a
heap-owning ADT and a heap loop parameter compose. If 0837 is ruled one class,
the exemplar is the measurement that says how much the class costs in a real
program: **89% of every object a Sudoku solve leaks.**

This is a **correctness leak** and is **distinct from 0408** — 0408's copy-churn
*performance* framing (the quadratic whole-Vec copy per guess) stands unchanged.
A solve is *correct*, just leaky, so **no exemplar source change is warranted**:
`(Some g)`-returning `eliminate` is idiomatic and correct, the defect is the
compiler's, and rewriting the exemplar around it would destroy the sentinel
value of the measurement.

## Headline entry

`user.cl` is the showcase command. It wires all four pure modules exactly as
the web platform does:

```
form body  --parse-form-body-->  puzzle string
puzzle     --make-grid-------->  Grid
Grid       --solve------------>  SolveResult
solution   --format-board----->  ASCII board  (terminal view)
solution   --solution-page---->  HTML page    (browser view)
```

It encodes a known puzzle as a URL-encoded form body, round-trips it through
`form/parse-form-body`, solves it, and prints the input board, the ASCII
solution, and the rendered HTML solution page (exit 0).

## Design Decisions

- **Bitmask candidate representation.** Candidates are a 9-bit integer mask
  (bits 0–8 for digits 1–9), not a `(Vec Int)` — no heap allocation for
  candidate tracking; ops are O(1).
- **Bitwise via `num.bits` (stdlib, native-primitive-backed).** Cranelisp has
  native bitwise primitives (`bit-and`/`bit-or`/`bit-xor`/`bit-not`/`shl`/`shr`/
  `popcount`, each lowering 1:1 to a CLIF op). `stdlib/num/bits.cl` is a thin
  curated layer over them. `grid.cl` imports `bit-shift-left`/`bit-test`/
  `bit-and`/`bit-or`/`bit-not`/`popcount` by name and keeps only thin
  *digit-1-9* domain adapters (`pow2`/`bit-set?`/`bit-clear`/`bit-set`/
  `bit-count`/`bit-lowest`) over the *bit-position-0-8* primitives. The native
  ops are full 64-bit two's-complement, but the Sudoku masks are always 9-bit
  (bits 0–8, positive), so the sign bit never participates. Grid's
  `bit-clear`/`bit-set` are composed locally rather than imported, because
  `num.bits`'s position-domain `bit-clear`/`bit-set` names would collide with
  grid's digit-domain ones.
- **`rem-i64` kept inline (deliberate non-adoption).** `num.int/rem` exists with
  identical semantics, but `rem-i64` is kept as a documented domain helper
  defined inline as `(- a (* (/ a b) b))`: routing the index helpers
  (`col-of`/`box-of`) through one local name reads cleaner than a cross-module
  import for a single arithmetic identity.
- **`char-at` dependency.** `make-grid` parses strings character-by-character
  using the `char-at` string primitive.
- **String building via `str-concat` (deliberate non-adoption of the `str`
  macro).** `html.cl` builds HTML through nested `str-concat`. The
  `text.string/str` macro would flatten the pyramids but the exemplar avoids it
  to keep no `str`-macro / `show`-dispatch overhead in production output.
- **Form parsing via `split`.** `form.cl` uses `split` on `&`/`=` and `char-at`
  for field names, reconstructing the puzzle string with `substring`+`str-concat`.

## Conventions

- **Idiomatic surface.** Arithmetic/comparison go through the prelude's trait
  operators (`+ - * / = != < <= >`); Vec access through the curated Clojure
  verbs `count`/`get`/`assoc`/`conj` imported from `collections.vec`; bitwise
  via `num.bits`; `digit-to-char`/`repeat-str` from `text.string`; string
  primitives (`char-at`, `str-concat`, `substring`, `split`, …) and boolean
  `not` imported by name from `primitives`.
- **Test functions** are top-level `test-*` defns returning `(Option String)`
  (`None` = pass, `(Some why)` = fail; `repl/spec.md` §16.1). They are run by
  the free-standing `tests.cl` runner — NOT `(mod test)` / `discover-tests`
  (in-language discovery is REPL-only).
- **Every batch `main` returns `(IO _)`** via `(Pure n)` or a `bind` chain; the
  inner Int is the process exit code.

## Tests

`tests.cl` is a **free-standing runner** following the `examples/` convention —
no `(mod test)` submodules, no `discover-tests`. It imports each module's
`test-*` function, runs them directly, and returns the number of passes as the
process exit code. The runner imports **40** tests (15 grid, 7 solver, 10 html,
8 form); a full green run exits 40.

```bash
CRANELISP_PLATFORM_PATH=target/debug CRANELISP_LIB=stdlib \
  cargo run -- --run exemplar/tests.cl
echo $?   # => 40  (all green)
```

Running the suite under both default (parallel) and `CRANELISP_NO_LENIENT=1`
(serial) and getting the same 40 is the **parallel ≡ serial equivalence guard**
for the search reshape (`solver/test-solve-parallel-equiv`, a
backtracking-requiring puzzle pinned to its unique solution).

`solver/test-hard-puzzle` is excluded from the runner (kept in `solver.cl` as
documentation): it is *correct* but the genuinely-hard backtracking copies the
whole 81-cell Vec on every guess, so it runs for minutes (the 0408 perf carry
above). The easy puzzle, the parallel-equivalence guard, and the
`eliminate`/`unsolvable` tests cover the solver path in the runner.

The web marquee has its own end-to-end proof in `tests/exemplar_web.rs`: one
test serves the form / a valid solved grid / a 404 over HTTP, and one asserts
that K concurrent `/slow` requests OVERLAP (≈1·D on the one reactor) instead of
serialising (≈K·D).

## Known Issues

- **Platform path.** `CRANELISP_PLATFORM_PATH=target/debug` is required because
  `exemplar/` is not the project root where the platform DLLs live; without it
  `(platform stdio)` / `(platform web)` fail with "platform not found".
- **Do not run bare REPL sessions with `exemplar/` as cwd.** A REPL `user`
  module uses `./user.cl` as its regenerated backing file and shares the `user`
  cache slot in `./.cranelisp-cache/` — a session here can rewrite the
  exemplar's `user.cl` and poison the cache for the next session. Use a scratch
  directory with copies of the modules for REPL work.
- **Hard-puzzle backtracking is quadratic** (performance, not correctness) — the
  0408 perf carry; see Current State.
- **`--link` requires a consistent workspace build.** Before an exemplar
  `--link`, the workspace must be built coherently: `cargo build` plus
  `tests/scripts/build-link-prereqs.sh`. A piecemeal build (some crates stale,
  some fresh) yields spurious `undefined reference to cranelisp_platform::…` at
  the link step. This is the documented build-skew gotcha (Linux VM baseline),
  **not a compiler defect** — a coherent rebuild clears it.
