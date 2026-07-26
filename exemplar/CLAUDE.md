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
(**S118 Phase 6: that Link symptom no longer reproduces** — see below.)

**S118 Phase-6 verification (HEAD `501e701f`).** `tests.cl` is **40/40 under
both** toggles (default parallel and `CRANELISP_NO_LENIENT=1`). The headline
`--run exemplar/user.cl` exits 0 from both cold and warm cache with
byte-identical stdout (659 bytes, empty stderr), and the in-tree run is
byte-identical to a scratch-copy run. The sprint's drop-glue mechanism
collapse, the program-result owner and the RE-1 marshal fix changed **no line
of exemplar source** and moved no observable output.

**Standalone Link parity RE-ESTABLISHED (FIXME 0875 symptom gone).** After the
documented coherent build (`cargo build` + `tests/scripts/build-link-prereqs.sh`),
an isolated **cold-cache** `--link user.cl` in a scratch copy of the sources
produces the executable (exit 0, the only stderr line being the `cc` command
echo), and running it gives stdout **byte-identical to `--run`**, exit 0. No
unresolved Rust/platform symbols. 0875 is updated with this reproduction; its
attribution was never dispatched and the symptom is no longer observable here.

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

**Solve-path never-freed leak — CURRENT STATE (S118 Phase 6, FIXME 0917).**
The leak survived S118's 0810/0782/0726 fixes. It is now measured, reduced to a
free-standing 30-line repro, and re-attributed; **the S115 attribution below is
retained as history and is discharged** — read this block first.

*Per-solve, not per-session.* A driver loop that solves the SAME easy puzzle N
times in one process (`CRANELISP_NO_LENIENT=1`, warm cache, `CRANELISP_RC_STATS=1`):

| N solves | allocs / deallocs | residue | residue / N |
|---:|---|---:|---:|
| 0 | 1 / 1 | 0 | — |
| 1 | 25517 / 13141 | 12,376 | 12,376 |
| 2 | 51033 / 26281 | 24,752 | 12,376 |
| 4 | 102065 / 52561 | 49,504 | 12,376 |
| 8 | 204129 / 105121 | 99,008 | 12,376 |
| 64 | — | 792,064 | 12,376 |
| 128 | — | 1,584,128 | 12,376 |

**Exactly linear, intercept exactly 0**, over two orders of magnitude, and
identical in the default parallel lane. There is no per-session component: the
retention is 12,376 blocks (~1.13 MB RSS) **per solve, permanently**. RSS grows
1.13 MB/solve (59.1 MB at N=8 → 195.3 MB at N=128, marginal constant to three
digits). Correctness is unaffected (every solve is right) and throughput is
near-flat (marginal 32.5 ms/solve at N≤32, 39 ms at N=128 — a mild second-order
allocator-pressure cost, not degradation).

*It is observable at the marquee.* The web server (`main.cl`) serving real
`POST /solve` requests grows **~1.17 MB per request**, monotonically, never
reclaimed: 55.3 MB after 1 request → 125.2 MB after 61. Every response is
correct (HTTP 200, identical 2,886-byte solution page). Extrapolated, the
server crosses +1 GB at roughly 900 requests. **This is the finding that
matters for scheduling: the leak is not a hygiene number on a batch program,
it bounds the lifetime of the long-running showcase.**

*Where it is.* 100% of it is in constraint propagation, none in parsing or
search: `make-grid` alone is exactly balanced (978/978, residue 0);
`make-grid` + `propagate` alone reproduces the whole 12,376. (The easy puzzle
is solved by propagation, so the backtracking search never runs.)

*The discriminator, reduced.* `eliminate` retains **4 objects per call and the
loop frees nothing at all** (deallocs frozen at 898 across N=100 and N=1100),
while every neighbouring operation is exact in isolation — `cell-at`,
`set-cell`, `(Some g)` over a parameter, `(Some (set-cell …))`, mixed
alias/fresh arms, and the same shape called cross-module are all balanced at
both N. Stripping `eliminate` arm by arm isolates one ingredient: **a match
arm returning the NULLARY constructor `None` beside an arm returning a boxed
`(Some …)`, over a let-bound owned heap ADT temporary.** Remove the nullary
arm and the identical program balances exactly; the nullary arm is never taken
at runtime. Free-standing repro (PrimitivesOnly prelude, zero stdlib,
`--no-cache`, subject/control differing only in the arms' return values):
subject 4406 allocs / **4** deallocs, control 4406 / 4406 at N=1100; slope 4
objects/iteration; same in `--link`. Filed as **FIXME 0917** with the program.

This face survives every landed guard: `match_owned_temporary_scrutinee_0810`
(14/14), `mixed_arm_match_forward_0726` (4/4) and the `gen_ownership_flows`
eliminator axis are all GREEN at this HEAD.

*What it is NOT.* The `Grid.cells` synthetic accessor — the FIXME 0903 family-1
witness the S118 golden re-baseline blessed and `tests/plan/s118-test-plan.md`
§11.3 named as the lead for cell #21 — **is never called by the exemplar**.
Every Grid field read is `(match g [(Grid cells) …])`; `cell-at` and `set-cell`
both destructure. Spelling the field type (`(deftype Grid [:(Vec Cell) cells])`,
which is legal and which the exemplar could adopt) flips that accessor's
emitted CLIF from the shallow non-glue release to the canonical colocated glue
call — and moves **zero** runtime blocks (26457/14026 either way, byte-identical
at N=1 and N=4). Evidence appended to FIXME 0903.

---

*History (S115, retained; the attribution below is discharged).* A full serial
solve leaked ~11.8k objects. All numbers `--run exemplar/solver.cl` with
`CRANELISP_NO_LENIENT=1 CRANELISP_RC_STATS=1`, warm cache (a cold cache adds a
constant compile-session term — always compare warm to warm; at S118 HEAD warm
is ambient-free and cold adds 1,143):

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

**Acceptance criterion (S118-current):** the warm-cache serial-solve residue —
12,431 for `solver.cl`, 12,376 per solve for the driver loop — must go to **0**
per solve, and the driver loop's residue must be **flat in N**, not merely
smaller. The ≤1400 bound of cell #21
(`tests/exemplar_ownership_residue_s116.rs`) is the committed guard; a value
materially above zero after FIXME 0917 lands means the fix is partial.
(The S115-era "drop to ≈1,300" criterion assumed the 0810 wrapper mechanism was
the whole story; it is superseded — the residual it reserved slack for is the
same 0917 shape.)

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
value of the measurement. (That judgement is re-affirmed at S118: the same
argument applies to spelling `Grid`'s field type or dropping the `None`
contradiction arm — both would hide the defect and neither is what an
application author should have to know.)

*End of history block.*

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
