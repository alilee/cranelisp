# Exemplar Project: Sudoku Solver

Selected exemplar project for the Cranelisp reimplementation. This document is owned by the `/port` skill, updated from the Sprint 0 candidate evaluation.

## Showcase target (S86 Phase 6b rebaseline)

> **The committed showcase is the stdio CLI.** `exemplar/user.cl` is the
> headline entry: it drives the full pipeline — `form/parse-form-body` →
> `grid/make-grid` → `solver/solve` → ASCII board (`solver/format-board`) +
> HTML page (`html/solution-page`) — end-to-end through `(platform stdio)`,
> exit 0. The four pure modules (`grid`, `solver`, `html`, `form`) are complete
> and idiomatic (S86 curated-surface idiom pass), and `tests.cl` runs 39/39
> green as a free-standing runner.
>
> **The web platform below is a designed-but-unbuilt future stretch**, NOT the
> committed target. The pure handler, HTML generation, and form parsing it
> needs are already implemented and tested — only the Rust platform DLL
> (`exemplar/platforms/web/`) and the IO wiring (`exemplar/main.cl`, routing)
> are missing. Building it needs `/platform` to author a `cdylib`; it is
> preserved as **FIXME 0405** (`target: /platform`). Everything in the
> "Web Platform DLL", "Two IO Models", and "Request Routing" sections is the
> design for that stretch — read it as the spec for 0405, not as shipped work.
>
> The original title was "Sudoku Solver with Web Platform"; the web half is now
> explicitly future. The rest of this document (architecture, data types,
> algorithms, test strategy, ring assessments) remains the authoritative design
> record for the pure core, which is built.

## Wave 4 Parallelism Opportunities Assessment

Assessment by `/port` — 2026-03-24. Evaluates the Sudoku solver exemplar for
parallelism opportunities: lenient evaluation, commutative IO, and operators
as values.

> **SUPERSEDED IN PART — S92 (FIXME 0408), `/port`.** The §1 "inherently
> sequential / no measurable benefit" verdict and the Summary's "useful
> *counterexample*" framing were **wrong for the search dimension** and are
> superseded below (see "### 1bis"). The original §1 text reasoned only about
> constraint **propagation** (`propagate`/`eliminate`/`find-min`), which *is*
> genuinely sequential — each step depends on the prior grid. But it conflated
> propagation with the whole solver and never examined the backtracking
> **search**, which is **embarrassingly parallel**: at a guess node the
> candidate-digit branches are fully independent (each tries a different digit
> on its own grid). Sudoku is therefore a showcase of **budget-bounded
> speculative parallel search**, not a parallelism counterexample. §2
> (commutative IO) and §3 (operators-as-values) verdicts **stand** — with one
> reframing: §2's "Model B" web concurrency is now the **effect-concurrency
> track** (`design/arch/effect-concurrency.md`; control-half combinators
> `race`/`select`/`timeout` + supervised launch-and-continue), a distinct axis
> from the inferred dataflow parallelism the search now exercises. The original
> §1–§3 prose is retained below as the historical record.

### 1bis. Lenient Evaluation — CORRECTED: backtracking search is parallel (S92)

**Corrected finding: the backtracking search auto-parallelises; propagation is
the sequential half.** The original §1 (below) is right that the *propagation*
hot path is sequential and that the *formatting* `let` bindings are
asymmetric/cheap. What it missed: the **search** is the exemplar's real parallel
opportunity.

Two language facts make it land with **zero `spark`/`par` in the source**:

1. **Slice-1 lenient eval (S92)** widened automatic sparking from independent
   `let` bindings to independent **apply-arguments** (`design/backend/lenient-eval.md`
   §2.5): the two individually-expensive, independent arguments of a function
   application are sparked. A `vec-map`-style cons-walk does **not** qualify
   (one expensive arg per node); only a **divide-and-conquer** shape (two
   independent expensive recursive calls at a node) does.
2. The candidate branches at a guess node are independent and pure, so a D&C
   split over the candidate digits exposes exactly that two-expensive-arg shape.

**The reshape (S92, `solver.cl`).** The sequential digit loop (`try-digits`)
is replaced by:
- `mask-to-digits` — enumerate the set digits of a candidate mask → `(Vec Int)`;
- `first-success a b` — `(match a (Success s) (Success s) _ b)`: take `a` if it
  solved, else `b`; **correct even when `b` was computed speculatively** (pure
  branches — the loser's work is discarded);
- `solve-range g idx digits lo hi` — copy-free index-range D&C: base
  `hi-lo == 1` commits the one digit and `solve`s; else split at `mid` and
  `(first-success (solve-range … lo mid) (solve-range … mid hi))`. **The two
  `solve-range` calls are the independent expensive apply-args** that slice-1
  sparks. `solve`'s guess arm calls `solve-range` over the candidate Vec;
  `solve`/`solve-range` are mutually recursive.

The **spark-budget create-gate** (`lenient-eval.md` §3.6) makes this degrade
gracefully: over budget → the apply takes its serial (direct) arm, so the
exponential search tail runs at ≈ serial cost rather than sparking `O(2ⁿ)`
IVars.

**Mechanism + baseline (measured S92, debug backend, this VM).**
- *Equivalence verified:* a backtracking-requiring puzzle solves to its unique
  solution **identically** under default (parallel) and `CRANELISP_NO_LENIENT=1`
  (serial). Guarded by `solver/test-solve-parallel-equiv` (pinned full solution)
  + the whole 40-test suite passing **40/40 in both modes**.
- *Baseline (the carried perf half):* the search puzzle solves in ~8.5 s; the
  earlier easy-9×9 web baseline was ~3.3 s (FIXME 0408). **Net wall-clock
  speedup is not yet observable** because the **copy-per-guess** grid
  representation (`set-cell`/`assoc` copy the full 81-cell Vec per guess —
  quadratic, allocation-dominated: `sys`≈`real`, `user`>`real` from
  allocator/runtime threads in *both* modes) masks the parallel gain. Removing
  that quadratic copy (FIXME 0408 perf half — persistent/structural-share Vec
  or in-place candidate masks) + a release/Tier-2 backend (Phase H) is what will
  let the parallel search *show* a speedup number. S92 delivers the parallel
  **expression**; the perf carry remains open.

### 1. Lenient Evaluation (Independent Let Bindings) — original 2026-03-24 (superseded by 1bis for the search dimension)

**Finding: minimal benefit for hot paths; some benefit in formatting/IO code.**

The solver's hot path is `propagate` -> `eliminate` -> `eliminate-from-peers`.
These functions are fundamentally sequential — each step depends on the grid
state produced by the previous step. Specifically:

- `eliminate` (solver.cl:35): The `let` binding `[cell (cell-at g idx)]` is a
  single binding — nothing to parallelize. The nested `let [new-mask ...]` depends
  on `cell`, so it is also sequential.
- `eliminate-from-peers-helper` (solver.cl:57): Iterates peers one at a time;
  each iteration's grid `g2` feeds the next. Inherently sequential.
- `propagate-pass-helper` (solver.cl:72): Same pattern — cell-by-cell iteration
  where each step may modify the grid.
- `find-min-helper` (solver.cl:127): Scans all 81 cells maintaining `best-idx`
  and `best-count` — sequential fold with carried state.

The formatting code has marginally better candidates:

- `build-output` (solver.cl:265): `[header ..., input-board ..., solution-str ...]`
  — `header` is a constant, `input-board` depends only on `puzzle-str`, and
  `solution-str` depends only on `puzzle-str`. So `input-board` and `solution-str`
  are independent and could be evaluated in parallel. However, `solution-str`
  dominates the cost (it runs the solver), while `input-board` is trivial string
  formatting. A cost heuristic would correctly identify only `solution-str` as
  expensive enough to warrant parallelization, but since nothing else is similarly
  expensive, there is no beneficial parallel pair.
- `parse-field-index` (form.cl:58): `[row ..., col ...]` — `row` and `col` are
  independent (`char-at` on different indices). But they are trivially cheap
  (single character lookup each). A cost heuristic should correctly skip these.

**Verdict**: Lenient evaluation would not measurably improve solver performance.
The algorithm's data-flow is inherently sequential — each constraint propagation
step depends on the previous grid state. The formatting/IO code has independent
bindings but they are either too cheap to parallelize or asymmetrically costly.
This is a useful *negative* finding for the exemplar: it demonstrates that
lenient evaluation is not a universal win, and that the cost heuristic matters.

### 2. Commutative IO Scheduling

**Finding: no current opportunities; Model B callback provides concurrency instead.**

The exemplar's IO usage in `main` (solver.cl:287) is a linear `bind` chain:
print puzzle, then solve, then print solution. These `print` calls are
`Sequential` (they must appear in order on stdout). There are no data-independent
IO pairs.

Looking ahead to the web platform (main.cl, not yet implemented):

- **Model A** (explicit loop): `accept` -> `handle` -> `send` is inherently
  sequential per request. No commutative pairs.
- **Model B** (callback): Concurrency comes from the platform's thread pool
  calling the pure handler in parallel. This is not IO scheduling — it is the
  platform managing threads. The compiler does not need to detect parallelism
  because the handler is pure and the platform does the dispatch.

The one hypothetical commutative opportunity would be if the exemplar made
multiple independent platform calls per request (e.g., fetching data from two
sources). The Sudoku solver does not — it is a self-contained computation with
no external dependencies per request.

**Verdict**: No commutative IO opportunities exist in the exemplar. This is
expected for a compute-bound application. The exemplar demonstrates concurrency
through platform-level parallelism (Model B) rather than through automatic IO
scheduling. This is a valid architectural pattern: not every application needs
the compiler to find parallelism in IO.

### 3. Operators as Values

**Finding: not currently used; limited natural opportunities.**

The exemplar exclusively uses monomorphic named primitives (`add-i64`, `eq-i64`,
`mul-i64`, etc.) rather than trait-dispatched operators (`+`, `=`, `*`). This
is a deliberate design choice documented in `exemplar/CLAUDE.md` — avoiding
trait dispatch overhead in tight loops.

Places where operators-as-values could apply:

- `bit-count-helper` (grid.cl:85): Counts set bits by iterating digits 1-9 and
  incrementing `acc` with `add-i64`. This is essentially `fold` with `+`, but
  the function already works and using operator values would add trait dispatch
  overhead without improving clarity.
- `count-determined-helper` (solver.cl:310, test module): Counts cells matching
  a predicate. Could use `filter` + `count` with operators if collection
  operations existed over the grid, but the grid is a Vec accessed by index.
- The test `main` functions sum test results via nested `add-i64` — this is
  boilerplate that `reduce` with `+` would clean up, but these are test-only
  functions, not production code.

The deeper issue is that the exemplar operates on `Vec Int` via index arithmetic,
not on sequences via higher-order traversals. Operators-as-values shine when
passed to `map`, `filter`, `reduce` — functions that abstract iteration. The
exemplar's tail-recursive-with-accumulator style does not create demand for
operator values.

**Verdict**: Operators as values would not improve the exemplar in its current
form. The exemplar intentionally uses monomorphic primitives for performance.
If the grid were refactored to use collection-level operations (map over cells,
fold over peers), operator values would become relevant, but that refactoring
is not motivated by the current architecture.

### Summary

**S92 correction (see §1bis):** the row below is the original 2026-03-24
assessment; the lenient-evaluation row is **superseded** — the backtracking
search *is* exploitable parallelism.

| Feature | Applicable? | Impact | Notes |
|---|---|---|---|
| ~~Lenient evaluation~~ → **Lenient eval (search)** | ~~Marginal~~ → **Yes** | ~~None measurable~~ → **parallel search (perf gated on copy-per-guess carry)** | ~~Algorithm is inherently sequential~~ → propagation is sequential; **search is embarrassingly parallel** (D&C over candidate digits, slice-1 apply-arg sparking, S92) |
| Commutative IO | No (current); web → effect-concurrency track | None (current) | Compute-bound; per-request web concurrency is the effect-concurrency track (`design/arch/effect-concurrency.md`), not commutative-IO scheduling |
| Operators as values | No | None | Uses monomorphic primitives by design |

~~The exemplar is a useful *counterexample* for Wave 4 parallelism features.~~
**Superseded (S92).** The exemplar is now a **showcase of budget-bounded
speculative parallel search**: the backtracking search auto-parallelises via
slice-1 apply-arg sparking with zero `spark`/`par` in the source (the D&C shape
in `solver.cl`'s `solve-range`/`first-success`), while constraint propagation
stays correctly sequential. The original "no exploitable parallelism /
counterexample" conclusion was an artefact of examining only the propagation
half. The conservative-cost-heuristic observation still holds (and is now
enforced by the create-gate's budget): the *vec-map cons-walk* shape genuinely
does **not** parallelise — only the two-independent-expensive-args D&C shape
does, which is exactly why the reshape uses D&C.

## Sprint 24 HKT/Lazy Evaluation: Exemplar Impact Assessment

Assessment by `/port` — 2026-03-23. Evaluates whether Sprint 24's HKT (Functor/Monad)
and lazy sequences would benefit the Sudoku solver exemplar.

**Functor/fmap over Option**: Moderate benefit. The solver has ~15 `match` expressions
on `(Option Grid)` that extract a value, transform it, and re-wrap. For example,
`eliminate` and `propagate-pass-helper` both match `(Some g2)` just to call the next
step. With `fmap`, some of these could become `(fmap next-step result)`. However, many
of the Option matches also handle `None` with distinct logic (contradiction detection),
so they cannot be replaced by fmap — they need the full match. Estimate: 3-5 matches
could simplify, the rest must stay.

**Monad/bind over Option**: Stronger benefit. The solver chains Option-returning
operations: eliminate -> eliminate-from-peers -> propagate. Each step matches
`[None None, (Some g2) (next-step g2)]` — this is exactly monadic bind (`>>=`).
`eliminate-from-peers-helper` is a fold over peers with Option short-circuiting,
which is `foldM`. If `(Option a)` had a Monad instance, several helper functions
could shrink significantly. The IO `main` already uses `bind` for IO chaining, so
the pattern is familiar to the codebase.

**Lazy sequences**: Minimal benefit. The solver operates on a fixed 81-cell Vec with
index arithmetic — there are no list traversals, stream processing, or unbounded
iteration that would benefit from laziness. The HTML and form modules iterate over
fixed ranges (0-8 rows, 0-8 cols) via tail-recursive helpers, which are already
efficient. Lazy sequences would add overhead without improving clarity or performance.

**Verdict**: Option Monad would be the single most impactful addition — it would
eliminate ~40 lines of mechanical `match [None None, (Some x) ...]` boilerplate
in solver.cl. Functor alone is less useful because most Option matches need the
None branch. Lazy sequences are not applicable to this problem domain. No changes
recommended until Monad for Option is available; when it is, solver.cl should be
the first adoption target.

## Decision

**Selected**: Sudoku Solver. **Committed IO layer: stdio CLI** (`user.cl`).
**Future stretch: custom web platform** (HTTP server) — FIXME 0405.

**Rationale**: The Sudoku solver hits the best balance across all nine selection criteria: algorithm-rich (constraint propagation + backtracking), universally familiar domain, clean pure/IO split, moderate and predictable scope. The pure core is deployed today over stdio; the web platform would replace stdio as the IO layer, adding a compelling demo experience (browser-based puzzle input and solution display) and deeply validating the platform model. That stretch is preserved for `/platform` (the pure core already supplies everything it needs to wire).

**Key insight**: The platform DLL is part of the exemplar, not separate infrastructure. Writing a platform is something application developers do — the web stretch would demonstrate that this is not an impossible ask. (Until then, the stdio CLI already validates the platform model via `(platform stdio)`.)

## What It Demonstrates

1. **Algorithm**: constraint propagation + recursive backtracking — exercises recursion, pattern matching, higher-order functions
2. **ADTs**: `Cell`, `Grid`, `SolveResult`, `PropResult` — domain-specific sum types, not toy wrappers
3. **Platform authoring**: a custom web platform DLL written in Rust, showing the full `declare_platform!` workflow
4. **Two IO models**: the same pure handler deployed with both a Cranelisp-side loop and a platform-side callback — demonstrates why purity matters
5. **Server-side HTML**: pure string building for HTML generation, no JavaScript
6. **Module decomposition**: 7+ modules with clear responsibilities

---

## Architecture

### The Pure Core

The handler function is pure: `Request → Response`. No IO, no side effects. The solver, HTML generation, and form parsing are all pure computation.

```
handle :: (Fn [Request] Response)     ; pure
```

This purity is the key architectural property. It means:
- The handler is trivially testable (no IO mocking)
- The platform can call it from multiple threads safely (no data races)
- The same handler works with both IO models

### Two IO Models

The exemplar implements both, demonstrating the tradeoffs:

**Model A — Loop in Cranelisp** (explicit, single-threaded):

```clojure
(defn main []
  (bind! [_ (listen 8080)]
    (serve-loop)))

(defn serve-loop []
  (bind! [req  (accept)
          _    (send (handle req))]
    (serve-loop)))
```

- Cranelisp controls the loop — easy to reason about, add logging, modify behavior
- TCO on `serve-loop` means no stack growth
- Single-threaded: one request at a time
- Platform provides simple primitives: `listen`, `accept`, `send`

**Model B — Loop in platform** (callback, concurrent):

```clojure
(defn main []
  (serve 8080 (fn [req] (Some (handle req)))))
```

- Platform owns the loop and manages threads
- Handler is called from multiple threads — safe because it's pure
- `(Option Response)` return: `None` signals clean shutdown
- Platform provides one higher-level primitive: `serve`

Both models use the same `handle` function. The difference is where the loop lives.

### The Roundtrip

```
Browser GET /           → form page: 9×9 grid of input fields
Browser POST /solve     → parse 81 form values, solve, render solution HTML
```

No JavaScript. Standard HTML form POST. Server-side rendering only. The form submits known digits; empty cells are left blank. The solution page shows the completed grid with given vs solved cells visually distinguished.

---

## Web Platform DLL

The platform is a Rust shared library that embeds a small HTTP server (e.g. `tiny_http`). It exports functions via the standard `declare_platform!` macro and C-ABI contract.

### Platform Functions

**Loop model primitives** (for Model A):

| CL Name | JIT Name | Type | Scheduling | Purpose |
|---|---|---|---|---|
| `listen` | `cranelisp_web_listen` | `(Fn [Int] (IO Int))` | Sequential | Bind to port, start server |
| `accept` | `cranelisp_web_accept` | `(Fn [] (IO Request))` | Sequential | Block until request arrives, return it |
| `send` | `cranelisp_web_send` | `(Fn [Response] (IO Int))` | Sequential | Send HTTP response for current request |

**Callback primitive** (for Model B):

| CL Name | JIT Name | Type | Scheduling | Purpose |
|---|---|---|---|---|
| `serve` | `cranelisp_web_serve` | `(Fn [Int (Fn [Request] (Option Response))] (IO Int))` | Sequential | Start server, call handler per request, stop on None |

**Data accessors** (pure — no IO):

| CL Name | JIT Name | Type | Purpose |
|---|---|---|---|
| `request-method` | `cranelisp_web_request_method` | `(Fn [Request] String)` | HTTP method ("GET", "POST") |
| `request-path` | `cranelisp_web_request_path` | `(Fn [Request] String)` | URL path ("/", "/solve") |
| `request-body` | `cranelisp_web_request_body` | `(Fn [Request] String)` | POST body (URL-encoded form data) |
| `response` | `cranelisp_web_response` | `(Fn [Int String String] Response)` | Construct response (status, content-type, body) |

### Implementation Notes

- `Request` and `Response` are opaque heap values at the Cranelisp level (allocated via `HostCallbacks.alloc`, pointer passed as `i64`)
- The accessor functions read fields from the heap object — same pattern as ADT field access
- `serve` receives a Cranelisp function pointer as `i64`, calls it via transmute for each request (same mechanism as `run-tests` GOT function calls)
- `accept`/`send` share state via thread-local or `Arc<Mutex>` within the DLL — the DLL manages request/response pairing internally
- The HTTP server is a dependency of the DLL, not of Cranelisp itself — the compiler has no knowledge of HTTP

### Concurrency Story

- **Model A**: Single-threaded. `accept` blocks until a request arrives. The platform buffers incoming connections. For a Sudoku solver (microsecond solves), this is fine.
- **Model B**: The platform calls the pure handler from its own thread pool. No data races possible because the handler is pure. Concurrency is a property of the deployment model, not the application code.

This is the exemplar's teaching moment: *purity enables concurrency without language-level concurrency primitives*.

### Termination

- **Model A**: `serve-loop` runs forever. Ctrl+C kills the process. This is normal for dev servers.
- **Model B**: `serve` runs until the handler returns `None`. For the exemplar, no route returns `None` — Ctrl+C. But the type makes clean shutdown possible without a special mechanism.

---

## Module Decomposition

```
exemplar/
  main.cl              ; (platform web), routes, both serve models
  grid.cl              ; Grid and Cell types, construction, accessors
  grid/test.cl         ; grid model unit tests
  solver.cl            ; constraint propagation + backtracking
  solver/test.cl       ; solver tests with known puzzles
  html.cl              ; HTML generation (form page, solution page, error page)
  html/test.cl         ; HTML output tests
  form.cl              ; URL-encoded form body parsing
  form/test.cl         ; form parsing tests
  platforms/
    web/               ; Rust crate: the web platform DLL
      Cargo.toml
      src/lib.rs
```

**7 Cranelisp modules** + 4 test submodules + 1 Rust platform crate = the complete exemplar.

---

## Key Data Types

```clojure
;; grid.cl

;; A cell is either given (fixed in the puzzle) or has remaining candidates
(deftype Cell
  (Given [:Int value])
  (Solved [:Int value])
  (Candidates [candidates]))       ; :(Vec Int) — remaining possible values

;; A Sudoku grid: 81 cells stored as a flat Vec
(deftype Grid [cells])              ; :(Vec Cell)

;; Result of a solve attempt
(deftype SolveResult
  (Success [grid])                  ; :(Grid) — solved grid
  Unsolvable)
```

```clojure
;; solver.cl

;; Result of constraint propagation on a single cell
(deftype PropResult
  Unchanged
  Reduced                           ; candidates were eliminated
  Determined                        ; cell reduced to one candidate → Solved
  Contradiction)                    ; no candidates remain → backtrack
```

**Trait usage**:
- `derive [Eq Display]` on `Cell`, `SolveResult`, `PropResult`
- Custom `Display` impl on `Grid` (for debugging — the real output is HTML)
- `Eq` on `Cell` for test assertions

**Note**: `Given` vs `Solved` distinction lets the HTML renderer style them differently (bold given digits, normal solved digits).

---

## Core Algorithms

### Grid Construction (`grid.cl`)

- `make-grid :: (Fn [String] (Option Grid))` — parse 81-char string (digits and dots) into Grid. Digits become `Given`, dots become `Candidates [1..9]`.
- `cell-at :: (Fn [Grid Int] Cell)` — access cell by flat index (0–80)
- `set-cell :: (Fn [Grid Int Cell] Grid)` — return new grid with updated cell (functional update via `vec-set`)
- `row-of :: (Fn [Int] Int)` — `(/ idx 9)`
- `col-of :: (Fn [Int] Int)` — `(mod idx 9)`
- `box-of :: (Fn [Int] Int)` — `(+ (* (/ (row-of idx) 3) 3) (/ (col-of idx) 3))`
- `peers :: (Fn [Int] (Vec Int))` — all indices sharing row, column, or box with given index
- `is-solved :: (Fn [Grid] Bool)` — all cells are `Given` or `Solved`

### Constraint Propagation (`solver.cl`)

- `eliminate-from-peers :: (Fn [Grid Int Int] Grid)` — for a fixed cell at index with value, remove that value from all peers' candidate lists
- `propagate :: (Fn [Grid] (Option Grid))` — iterate elimination until fixed point; return `None` on contradiction (any cell has empty candidates)
- `naked-singles :: (Fn [Grid] Grid)` — if a candidate appears in only one cell of a row/col/box, fix it

### Backtracking Search (`solver.cl`) — parallel divide-and-conquer (S92)

- `find-min-candidates :: (Fn [Grid] (Option Int))` — index of unfixed cell with fewest candidates (MRV heuristic)
- `mask-to-digits :: (Fn [Int] (Vec Int))` — enumerate the set digits (1-9) of a candidate mask
- `first-success :: (Fn [SolveResult SolveResult] SolveResult)` — `(match a (Success s) (Success s) _ b)`; take `a` if solved else `b` (correct even when `b` was computed speculatively — pure branches)
- `solve-range :: (Fn [Grid Int (Vec Int) Int Int] SolveResult)` — copy-free index-range D&C over the candidate-digit Vec: base `hi-lo==1` commits one digit and `solve`s; else split at `mid` and combine the two **independent expensive recursive solves** with `first-success` (the two `solve-range` calls are the apply-args slice-1 lenient eval sparks — `design/backend/lenient-eval.md` §2.5)
- `solve :: (Fn [Grid] SolveResult)` — propagate, then if unsolved: pick min-candidate cell (MRV), `solve-range` over its candidate digits; `solve`/`solve-range` mutually recursive. The earlier sequential `try-digits` early-exit loop is retired (S92, FIXME 0408)

### HTML Generation (`html.cl`)

- `form-page :: (Fn [] String)` — full HTML page with 9×9 grid of `<input>` fields in a `<form method="POST" action="/solve">`
- `solution-page :: (Fn [Grid Grid] String)` — solved grid rendered as HTML table; given cells bold, solved cells normal; original grid passed for comparison
- `error-page :: (Fn [String] String)` — error message with link back to form
- `css :: (Fn [] String)` — inline CSS for grid styling (borders for 3×3 boxes, font sizing)

### Form Parsing (`form.cl`)

- `parse-form-body :: (Fn [String] String)` — extract 81-char puzzle string from URL-encoded POST body (`c00=5&c01=&c02=3&...`). Empty fields become dots.
- `url-decode :: (Fn [String] String)` — decode percent-encoded characters (minimal: `+` → space, `%XX` → char)

### Request Routing (`main.cl`)

```clojure
(defn handle [req]
  (match (request-method req)
    ["GET"
     (match (request-path req)
       ["/"  (response 200 "text/html" (form-page))]
       [_    (response 404 "text/plain" "Not found")])]
    ["POST"
     (match (request-path req)
       ["/solve"
        (let [puzzle (parse-form-body (request-body req))
              grid   (make-grid puzzle)]
          (match grid
            [(Some g)
             (match (solve g)
               [(Success solution) (response 200 "text/html" (solution-page solution g))]
               [Unsolvable         (response 200 "text/html" (error-page "No solution exists"))])]
            [None (response 200 "text/html" (error-page "Invalid puzzle input"))]))]
       [_    (response 404 "text/plain" "Not found")])]
    [_ (response 405 "text/plain" "Method not allowed")]))
```

---

## Test Strategy

### Unit Tests (pure, Ring 3)

```clojure
;; grid/test.cl
(defn test-make-grid-valid []
  (assert-true (match (make-grid "530070000600195000098000060800060003400803001700020006060000280000419005000080079")
    [(Some _) true
     None false])))

(defn test-cell-at []
  (let [g (make-grid known-puzzle)]
    (match g
      [(Some grid) (assert-eq (Given 5) (cell-at grid 0))])))

(defn test-peers-count []
  (assert-eq 20 (vec-len (peers 0))))
```

```clojure
;; solver/test.cl
(defn test-easy-puzzle []
  (match (make-grid easy-puzzle)
    [(Some g) (match (solve g)
               [(Success _) (assert-true true)]
               [_ (assert-true false)])]))

(defn test-hard-puzzle []
  (match (make-grid hard-puzzle)
    [(Some g) (match (solve g)
               [(Success _) (assert-true true)]
               [_ (assert-true false)])]))

(defn test-unsolvable []
  (match (make-grid invalid-puzzle)
    [(Some g) (assert-eq Unsolvable (solve g))]))
```

```clojure
;; html/test.cl
(defn test-form-page-contains-inputs []
  (assert-true (str-contains (form-page) "<input")))

(defn test-solution-page-contains-digits []
  (let [solved-grid (... known solved grid ...)]
    (assert-true (str-contains (solution-page solved-grid original-grid) "5"))))
```

```clojure
;; form/test.cl
(defn test-parse-form-body []
  (assert-eq "5.3......" (parse-form-body "c00=5&c01=&c02=3&c03=&...")))
```

### Integration Tests (with platform, Ring 4)

- Start the web server programmatically
- Construct request values
- Verify response status and body content
- Verify round-trip: form → parse → solve → render

### Coverage

| Layer | Module | What's Tested |
|---|---|---|
| Grid model | `grid/test.cl` | Construction, accessors, peer calculation |
| Solver | `solver/test.cl` | Easy/medium/hard puzzles, unsolvable detection |
| HTML gen | `html/test.cl` | Form page structure, solution page content |
| Form parse | `form/test.cl` | URL-encoded body → puzzle string |
| Routing | integration | Full request → response pipeline |
| Platform | manual | Browser-based verification |

---

## Feature Coverage

| Feature | How Exercised |
|---------|---------------|
| ADTs (variety) | `Cell` (3 ctors), `Grid` (product), `SolveResult` (2 ctors), `PropResult` (4 ctors) |
| Pattern matching | Cell dispatch, solve result, request routing, option handling |
| Traits | `Display` on all types, `Eq` on Cell and SolveResult, `derive` |
| Higher-order functions | `fold` over cells, `filter` candidates, `map` grid transformations |
| Closures | Predicate closures for filtering, row/col/box extractors |
| Macros | `do`, `bind!`, `match`, `->`, `let` |
| Modules | 7 user modules + 4 test submodules |
| IO model | Both loop and callback patterns demonstrated |
| Strings | HTML generation (heavy), form parsing, URL decoding |
| Vecs | Grid (81 cells), candidate lists, peer indices |
| Platform authoring | Custom web DLL with `declare_platform!`, 7 exported functions |
| Testing | Unit tests per module, integration tests for roundtrip |

---

## Stdlib Requirements for `/stdlib`

| Function | Type | Priority | Notes |
|----------|------|----------|-------|
| `mod` (or `rem`) | `(Fn [Int Int] Int)` | **Blocking** | Box index: `(mod idx 9)`, `(mod col 3)` |
| `char-at` | `(Fn [String Int] Int)` | **Blocking** | Parse input string character by character |
| `str-len` | `(Fn [String] Int)` | **Blocking** | Validate input length, string iteration |
| `vec-filter` | `(Fn [(Fn [a] Bool) (Vec a)] (Vec a))` | Important | Candidate elimination |
| `int-to-string` | `(Fn [Int] String)` | Important | Digit display in HTML |
| `str-contains` | `(Fn [String String] Bool)` | Important | Test assertions, URL decoding |
| `str-split` | `(Fn [String String] (Vec String))` | Important | Form body parsing (split on `&`) |
| `vec-contains` | `(Fn [(Vec a) a] Bool)` | Nice-to-have | Can build from `vec-reduce` |
| `vec-concat` | `(Fn [(Vec a) (Vec a)] (Vec a))` | Nice-to-have | Peer union |

---

## Ring Readiness

### Ring 0 Assessment (Sprint 1)

**Ring 0 features available**: `Int`, `Float`, `Bool` types. 19 monomorphic primitives (`add-i64`, `sub-i64`, `mul-i64`, `div-i64`, `eq-i64`, `lt-i64`, `gt-i64`, `le-i64`, `ge-i64`, `add-f64`, `sub-f64`, `mul-f64`, `div-f64`, `eq-f64`, `lt-f64`, `gt-f64`, `le-f64`, `ge-f64`, `not`). `defn`, `let`, `if`, `fn` (lambda), `match`. Enum ADTs (no fields). Pattern matching on enums and wildcards. TCO for self-recursion.

**Ring 0 features NOT available**: Strings, closures, heap allocation, collections (`Vec`, `List`), modules, imports, traits, macros, IO, ADTs with fields, `derive`.

**Component-by-component assessment**:

| Component | Ring 0 viable? | Blocking gaps |
|---|---|---|
| `grid.cl` — Grid/Cell types | No | `Cell` is a sum ADT with fields (Ring 1). `Grid` wraps `Vec Cell` (Ring 1). `make-grid` parses a `String` (Ring 1). |
| `solver.cl` — constraint propagation, backtracking | No | Operates on `Grid`/`Cell` (Ring 1). Candidate elimination uses `Vec` operations (Ring 1). `PropResult` is an enum ADT — but only useful if it can be returned from functions that manipulate `Grid`. |
| `html.cl` — HTML generation | No | Entirely `String`-based (Ring 1). |
| `form.cl` — URL form parsing | No | Entirely `String`-based (Ring 1). |
| `main.cl` — routing, IO models | No | IO model (Ring 4). Platform DLL (Ring 4). `String` matching for routes (Ring 1+). |
| `solver/test.cl`, etc. — test submodules | No | Modules (Ring 2). `run-tests` infrastructure (Ring 3+). |
| `platforms/web/` — Rust DLL | No | Platform system (Ring 4). |

**What CAN be done with Ring 0 features**:

Very little of the Sudoku Solver itself, but two small algorithmic building blocks can be validated as standalone functions using only `Int`, `Bool`, `if`, and recursion:

1. **Index arithmetic** — `row-of`, `col-of`, `box-of` are pure `Int -> Int` functions using `div-i64` and `mul-i64`. These can be written and tested at Ring 0 (they don't depend on grids or collections). However, `mod` (remainder) is not a Ring 0 primitive — `col-of` and `box-of` would need to be expressed as `(sub-i64 idx (mul-i64 (div-i64 idx 9) 9))` in place of `(mod idx 9)`.

2. **`PropResult` enum** — This is a pure enum (all nullary constructors: `Unchanged`, `Reduced`, `Determined`, `Contradiction`). It can be defined and pattern-matched at Ring 0. But it has no practical use without the grid infrastructure that produces and consumes it.

3. **`is-solved` recursion pattern** — A recursive traversal over a flat array index range `0..80` could be expressed as a self-recursive function taking an index, if the grid were representable. But it isn't (needs `Vec`).

**Verdict**: Ring 0 unlocks **zero implementable Sudoku Solver components**. The solver fundamentally requires heap-allocated data structures (`Vec`, `String`, ADTs with fields) which arrive in Ring 1. The only Ring-0-expressible pieces (index arithmetic, `PropResult` enum) are isolated fragments with no useful composition at this ring.

This is expected and confirms the exemplar plan's original assessment that the bulk of the work begins at Ring 3. The gap between Ring 0 and the exemplar's needs is:

| Need | Arrives at |
|---|---|
| ADTs with fields (`Cell`, `Grid`, `SolveResult`) | Ring 1 |
| `String` (HTML, form parsing, input) | Ring 1 |
| `Vec` (grid cells, candidate lists, peer indices) | Ring 1 |
| Closures (predicates for filtering, extractors) | Ring 1 |
| Modules and imports | Ring 2 |
| Traits (`Eq`, `Display`, `derive`) | Ring 2 |
| Macros (`do`, `bind!`, `match` sugar, `list`) | Ring 3 |
| IO model, platform DLLs | Ring 4 |

**Ring 1 is the first ring where meaningful exemplar work becomes possible** — specifically, prototyping the `Grid`/`Cell` data model and basic solver logic in a single-file program without modules or traits. **Ring 3 is where the exemplar becomes fully implementable** as a multi-module pure computation. **Ring 4 completes it** with the web platform.

### Ring 1 Assessment (Sprint 2)

**Ring 1 features available** (Chunks A+B+C; 738 tests, 2 ignored):
- **Strings**: literals, `str-concat`, `str-eq`, `str-len`, `string-identity`, `int-to-string`, `float-to-string`, `bool-to-string`. `parse-int` is defined but its return type is still `Int` (placeholder — needs `Option` ADT return support, hence the 2 ignored tests).
- **ADTs with fields**: Product types (`(deftype Point [:Int x :Int y])`), sum types with data constructors (`(deftype (Option a) None (Some [:a val]))`), polymorphic type parameters, shortcut syntax (`(deftype Pair [first second])`). Constructor patterns with field bindings in `match`. Exhaustiveness checking (panics at runtime for non-exhaustive). Multiple ADT definitions in the same compilation unit.
- **Closures**: Lambda with variable capture (single and multiple captures). Closures returned from functions. Higher-order functions (functions as arguments and return values). Named functions as values. Nested closures. Function composition. Zero-param closures.
- **RC**: Heap allocation with reference counting. Consuming calling convention with last-use optimization. Drop glue for strings, ADTs with heap fields, and closure environments. Balanced inc/dec verified by 35 RC tests.
- **Still NOT available**: `Vec` (deferred to Sprint 3), modules/imports, traits (`Eq`, `Display`, `derive`), macros, IO, platform DLLs, `char-at`, `str-split`, `str-contains`, `str-sub`, `mod`/`rem` primitive.

**Component-by-component assessment**:

| Component | Ring 1 viable? | Assessment |
|---|---|---|
| `grid.cl` — Grid/Cell types | **Partially** | `Cell` ADT can now be fully defined: `(deftype Cell (Given [:Int value]) (Solved [:Int value]) (Candidates [candidates]))`. However, `Candidates` wraps a `:(Vec Int)` which does not exist yet. `Grid` wraps `:(Vec Cell)` — also blocked. Individual `Cell` values can be constructed, passed through functions, and pattern-matched. But no collection to hold 81 of them. |
| `solver.cl` — constraint propagation, backtracking | **No** | The solver traverses and transforms a grid (Vec-based). Candidate elimination requires `Vec` filtering. Even with `Cell` definable, the algorithms cannot operate without `Vec`. `PropResult` (pure enum) and `SolveResult` (sum with field) are both expressible, but useless without the grid. |
| `html.cl` — HTML generation | **Partially** | String concatenation (`str-concat`) and conversion (`int-to-string`) are available. A function like `(defn wrap-tag [tag content] (str-concat (str-concat "<" (str-concat tag ">")) (str-concat content (str-concat "</" (str-concat tag ">")))))` works. But building the 9x9 grid HTML requires iterating over 81 cells — which requires `Vec` or a recursive data structure. Individual string-building helpers (tag wrapping, CSS embedding) are expressible. |
| `form.cl` — URL form parsing | **No** | Requires `str-split` (to split on `&` and `=`), `char-at` (to inspect individual characters), and iteration over a collection of key-value pairs. None of these are available. `str-eq` is available, which would help compare keys, but without string splitting/indexing, parsing is impossible. |
| `main.cl` — routing, IO models | **No** | IO model (Ring 4), platform DLL (Ring 4). String matching for routes (`str-eq` on method and path) is now possible in principle, but without IO the routing logic has no context. |
| `test submodules` | **No** | Modules (Ring 2). Testing infrastructure (`run-tests`, `assert-eq`) (Ring 3+). |
| `platforms/web/` — Rust DLL | **No** | Platform system (Ring 4). |

**What CAN be done with Ring 1 features**:

Ring 1 unlocks meaningful prototyping of isolated data model fragments and string-building helpers. Specifically:

1. **Cell ADT (without Vec-based Candidates)** — The `Cell` type can be defined in a simplified form that uses an `Int` bitset instead of `Vec Int` for candidates:
   ```clojure
   ;; Ring 1 workaround: candidates as bitmask (bits 1-9)
   (deftype Cell
     (Given [:Int value])
     (Solved [:Int value])
     (Candidates [:Int bitmask]))
   ```
   This is a legitimate and possibly even *better* representation for a Sudoku solver (bitwise operations on a 9-bit mask are faster than Vec filtering). All Cell operations — construction, pattern matching, field extraction — work at Ring 1. The design can keep this representation even when Vec arrives.

2. **SolveResult and PropResult ADTs** — Both are expressible. `PropResult` is a pure enum (Ring 0). `SolveResult` is now meaningful because `Grid` can be wrapped as a field:
   ```clojure
   (deftype SolveResult (Success [grid]) Unsolvable)
   ```
   However, `grid` would need a `Grid` type that is itself a product — and without Vec, `Grid` cannot hold 81 cells.

3. **String-building helpers for HTML** — Functions like `wrap-tag`, `css` (a constant string), and individual table cell rendering can be written and tested:
   ```clojure
   (defn td [content css-class]
     (str-concat "<td class=\"" (str-concat css-class (str-concat "\">" (str-concat content "</td>")))))
   ```
   These compose via `str-concat` chaining. Deeply nested `str-concat` is verbose but functional.

4. **Higher-order patterns** — Closures enable the callback and predicate patterns that the solver uses. A `map-opt` function that transforms the value inside an `Option` works:
   ```clojure
   (deftype (Option a) None (Some [:a val]))
   (defn map-opt [opt f]
     (match opt
       [(Some x) (Some (f x))
        None None]))
   ```
   The `apply-fn`, `compose`, and `apply-twice` patterns all work. These are building blocks for the solver's functional style.

5. **Index arithmetic (enhanced)** — Still no `mod` primitive, but the workaround `(sub-i64 idx (mul-i64 (div-i64 idx 9) 9))` works for `col-of` and `box-of`. With closures, helper functions can be composed more naturally:
   ```clojure
   (defn rem-i64 [a b] (sub-i64 a (mul-i64 (div-i64 a b) b)))
   (defn row-of [idx] (div-i64 idx 9))
   (defn col-of [idx] (rem-i64 idx 9))
   (defn box-of [idx]
     (add-i64 (mul-i64 (div-i64 (row-of idx) 3) 3)
              (div-i64 (col-of idx) 3)))
   ```

6. **Option-based error handling** — `(Option a)` is now fully functional. `make-grid` could return `(Option Grid)` once `Grid` exists. The pattern of `match (some-fn ...) [(Some x) ... None ...]` works throughout.

**Critical blocker: Vec**

The single most impactful missing feature for the Sudoku Solver is `Vec`. Nearly every component depends on it:
- `Grid` stores 81 cells as `:(Vec Cell)`
- Candidate lists are `:(Vec Int)` (or bitmask alternative)
- `peers` returns `:(Vec Int)` (20 peer indices per cell)
- The solver iterates over cells, filters candidates, and builds new grids
- HTML generation iterates over cells to build the table
- Form parsing produces a collection of parsed values

Without `Vec`, the exemplar cannot compose its pieces into working modules. However, the bitmask alternative for candidates suggests that a creative encoding could reduce some Vec dependencies.

**Design adjustment: bitmask candidates**

Based on Ring 1 analysis, the exemplar plan should adopt `Int` bitmasks for candidate sets instead of `:(Vec Int)`. This is:
- More performant (bitwise AND/OR vs Vec allocation and filtering)
- Ring-1-compatible for the `Cell` type itself
- Idiomatic for Sudoku solvers (the constraint propagation literature uses bitmasks)

The `Grid` type still needs Vec to hold 81 cells. No reasonable alternative exists — 81 named fields in a product type would be absurd, and a linked list (definable at Ring 1 via recursive ADT) would have O(n) random access for `cell-at` and `set-cell`, making the solver impractical.

**Revised gap table**:

| Need | Status at Ring 1 | Arrives at |
|---|---|---|
| ADTs with fields (`Cell`, `SolveResult`) | **Available** | Ring 1 (current) |
| `String` (HTML, form parsing, input) | **Partially available** — concat, eq, len, to-string. Missing: split, char-at, contains, substring | Ring 1 has basics; string manipulation arrives with stdlib (Ring 2–3) |
| Closures (predicates, callbacks, composition) | **Available** | Ring 1 (current) |
| `Option` type | **Available** (user-defined) | Ring 1 (current) |
| `Vec` (grid cells, peer indices) | **Not available** — single most impactful gap | Sprint 3 (Chunk D) |
| `parse-int` with `Option` return | **Blocked** — 2 ignored tests | Needs ADT return type support from extern functions |
| `mod`/`rem` primitive | **Not available** — workaround exists | Ring 2 stdlib or explicit primitive |
| Modules and imports | Not available | Ring 2 |
| Traits (`Eq`, `Display`, `derive`) | Not available | Ring 2 |
| Macros (`do`, `bind!`, threading) | Not available | Ring 3 |
| IO model, platform DLLs | Not available | Ring 4 |

**Verdict**: Ring 1 moves the exemplar from "zero implementable components" (Ring 0) to "**data model prototypable, algorithms blocked**". The `Cell`, `SolveResult`, and `PropResult` ADTs are now expressible. String-building helpers for HTML work. Closures enable the functional patterns the solver relies on. `Option` provides error handling.

But **Vec is the critical gate**. Without it, the `Grid` type cannot exist, and therefore the solver, HTML generation (grid iteration), and form parsing (value collection) cannot be composed. Vec arrives in Sprint 3 (Chunk D). Once Vec is available — even without modules, traits, or macros — a single-file prototype of the complete pure solver core becomes feasible.

**Estimated Ring at which the exemplar becomes implementable**:
- **Sprint 3 (Vec)**: Single-file proof-of-concept — Grid + Cell + solver + string output, all in one compilation unit, using monomorphic primitives. No modules, no traits, no macros. Verbose but functional.
- **Ring 2**: Multi-module decomposition. Trait-based equality for test assertions. `Display` for debugging.
- **Ring 3**: Full exemplar core with macros, prelude, stdlib, `run-tests`. This is the target for implementing the pure computation modules (`grid.cl`, `solver.cl`, `html.cl`, `form.cl`).
- **Ring 4**: Web platform DLL, IO wiring, integration tests. Exemplar complete.

### Sprint 12 Assessment (Ring 3)

**Ring 3 features available** (Sprint 11; 1551 tests):
- **ADTs with fields**: Sum and product types, polymorphic type parameters, pattern matching with field bindings.
- **Traits**: `deftrait`, `impl`, constrained polymorphism with monomorphisation. Prelude provides `Num`, `Eq`, `Ord`, `Display` with implementations for `Int`, `Float`, `Bool`, `String`.
- **Operators via traits**: `+`, `-`, `*`, `/`, `=`, `<`, `>` work in `defn` bodies via trait dispatch.
- **Vecs**: `vec-get`, `vec-set`, `vec-push`, `vec-len`. Functional update via `vec-set`.
- **Strings**: `str-concat`, `str-eq`, `str-len`, `int-to-string`, `show` (Display).
- **TCO**: Self-recursive tail calls optimized to loops.
- **Macros**: `defmacro`, quasiquote, prelude macros.
- **Modules**: `mod`, `import`, qualified names.

**What was demonstrated** (see `repl/demos/exemplar-progress.demo`):

A working 4x4 mini-Sudoku solver was implemented entirely in the REPL, exercising:

1. **Domain ADTs**: `Cell` (Given/Solved/Unknown), `PropResult` (pure enum), defined and pattern-matched.
2. **Display trait**: Custom `impl Display PropResult` showing match-based string conversion.
3. **Grid index arithmetic**: `row-of`, `col-of`, `box-of` — pure Int functions for 9x9 Sudoku geometry.
4. **Backtracking solver**: Recursive `solve` function with constraint checking (`no-conflict`), backtracking on failure, using `vec-set` for functional grid updates.
5. **Grid display**: `format-grid`/`format-row`/`format-cell` — recursive string-building to pretty-print boards.
6. **Two puzzles solved**: From given digits to complete valid solutions, with correct constraint propagation.

**Findings and blockers**:

| Finding | Severity | Skill | Description |
|---|---|---|---|
| Vec in polymorphic ADT display | Important | `/backend` | `(Solved [1 2 3])` displays as `(SolveResult.Solved [])` — the Vec field shows empty in ADT display, though data is correct when extracted via `match`. Prevents wrapping solution Vec in a `SolveResult` ADT for the demo. |
| Trait operators in closures | Important | `/backend` | `(fn [x] (* x x))` fails with "no GOT slot for function: *". Trait-dispatched operators work in `defn` but not inside anonymous `fn` closures. Workaround: use monomorphic primitives (`mul-i64`) in closures. |
| `!=` operator parse error | Minor | `/frontend` | `(!= 3 4)` → "unexpected character: '\'". The `!` character is not accepted as an operator character. Workaround: `(not (= 3 4))`. |
| No `mod`/`rem` primitive | Important | `/stdlib` | Index arithmetic for `col-of` and `box-of` requires remainder. Workaround: `(- idx (* (/ idx 9) 9))`. |
| No `char-at` / `str-split` | Blocking | `/stdlib` | Parsing puzzle input strings requires character-level access. Cannot implement `make-grid :: (Fn [String] Grid)`. |
| No mutual recursion | Important | `/backend` | Solver `solve`/`try-each` pattern requires mutual recursion or workaround (combined into one function with extra `guess` parameter). |
| Constrained poly GOT slots in REPL | Minor | `/backend` | Second call to a constrained polymorphic function in the same REPL session sometimes fails with "no GOT slot". Workaround: use monomorphic versions. |
| IO / platform system | Blocking | Ring 4 | Web platform DLL and IO model not yet available. |



**Revised gap table (Sprint 12)**:

| Need | Status | Arrives at |
|---|---|---|
| ADTs with fields | **Available** | Ring 1 |
| Pattern matching | **Available** | Ring 1 |
| Traits (Display, Eq) | **Available** | Ring 2 |
| Vec operations | **Available** | Ring 1 |
| Operators via traits | **Available in defn** — broken in closures | Needs fix |
| Strings (concat, show) | **Available** | Ring 1 |
| Recursive algorithms | **Available** — self-recursion with TCO | Ring 0 |
| `mod`/`rem` | **Not available** — workaround exists | stdlib |
| `char-at`, `str-split` | **Not available** — blocks input parsing | stdlib |
| Modules | **Available** — not exercised in demo | Ring 2 |
| Macros | **Available** — not exercised in demo | Ring 3 |
| IO / Platform DLLs | **Not available** | Ring 4 |

**Verdict**: Ring 3 moves the exemplar from "data model prototypable" to "**core algorithm demonstrable**". A working backtracking solver (4x4 scale) runs in the REPL with ADTs, pattern matching, Vec operations, recursive constraint checking, and string-based grid display. The 9x9 solver is algorithmically identical — only the constants change.

The remaining blockers for a full exemplar implementation are:
1. **String manipulation** (`char-at`, `str-split`) for input parsing — stdlib work
2. **IO / platform system** for the web server — Ring 4
3. **Operator closures** and **Vec-in-ADT display** — compiler fixes needed for idiomatic code

**Risk assessment updates**:

1. **Vec dependency confirmed as the critical path** (no change from Ring 0 assessment, but now quantified: 5 of 7 modules depend on Vec). Mitigation: bitmask encoding for candidates reduces Vec surface area slightly.
2. **String primitive set is narrower than expected**. Ring 1 has `str-concat`, `str-eq`, `str-len`, and type-to-string conversions, but NOT `char-at`, `str-split`, `str-contains`, or `str-sub`. The form parser (`form.cl`) depends on `str-split` and character-level access. These are either stdlib functions (Ring 2–3) or new primitives. Risk is moderate — these are straightforward to add but may not be prioritized for Ring 2.
3. **`parse-int` returning `Option`** is blocked on extern function ADT return type support. This is a known issue (2 ignored tests). The form parser needs `parse-int` to convert form field values. Low risk — the mechanism exists, just needs wiring.
4. **No `mod`/`rem` primitive** remains a minor annoyance. The `(sub-i64 a (mul-i64 (div-i64 a b) b))` workaround is adequate but verbose. Should be added as a Ring 0 primitive or Ring 2 stdlib function.
5. **Deeply nested `str-concat` is painful**. Without macros (Ring 3) for string interpolation or threading (`->`), building HTML strings requires 5+ levels of nesting for a single element. This is a usability concern, not a blocker — it works, it's just ugly. Threading macros at Ring 3 will help significantly.

### Sprint 3 Assessment — Vec Available (resolves U1.10)

**Vec primitives now available**: `vec-len`, `vec-get`, `vec-set`, `vec-push`. Vec is polymorphic (`Vec(a)`), supports COW (copy-on-write when shared, mutate-in-place when unique), and works with all element types (Int, String, ADTs, closures). 32 integration tests passing, 4 REPL Vec tests passing. Vec literal syntax `[1 2 3]` works.

**Vec RC status**: Vec allocation and operations are functionally correct, but scope-level dec (freeing Vec temporaries at scope exit) is deferred to Ring 2. This means Vec values leak in the current implementation. 10 RC balance tests are `#[ignore]`. This is acceptable for prototyping but means any long-running exemplar code (e.g., solving many puzzles) would accumulate memory. Not a blocker for algorithm validation.

**Still NOT available**: Modules/imports, traits (`Eq`, `Display`, `derive`), macros (`do`, `bind!`, `->`, `cond`), IO, platform DLLs, `char-at`, `str-split`, `str-contains`, `str-sub`, `mod`/`rem` primitive, higher-order Vec functions (`vec-filter`, `vec-map`, `vec-fold`/`vec-reduce`).

**Component-by-component assessment**:

| Component | Sprint 3 viable? | Assessment |
|---|---|---|
| `grid.cl` — Grid/Cell types | **Yes (core)** | `Grid` can now be defined as `(deftype Grid [cells])` wrapping `:(Vec Cell)`. `Cell` uses bitmask candidates (Ring 1 design decision). `make-grid` can parse a string character-by-character using index arithmetic + `char-at` (blocked — see below). `cell-at` is `(vec-get (cells grid) idx)`. `set-cell` is `(deftype Grid [(vec-set (cells grid) idx cell)])`. `peers` returns `:(Vec Int)` — can be constructed via `vec-push` chains. `row-of`, `col-of`, `box-of` all work (Int arithmetic, workaround for missing `mod`). **Blocker**: `char-at` is needed for `make-grid` to parse input strings. Without it, grid construction from string input is impossible. Grid construction from a pre-built `Vec Cell` works. |
| `solver.cl` — constraint propagation, backtracking | **Mostly yes** | With bitmask candidates and Vec-based grid, the core algorithm is expressible. `eliminate-from-peers`: iterate peer indices (recursive loop over Vec), clear candidate bit in each peer cell. `propagate`: iterate cells 0..80, apply elimination, detect fixed point. `naked-singles`: iterate units, bitwise analysis. `find-min-candidates`: iterate cells, track minimum. `solve`: recursive backtracking with TCO on the search loop. All of these use `vec-get`, `vec-set`, `vec-len`, and recursive index loops. **No higher-order functions needed** — the solver can use explicit recursion over indices. Without `vec-filter`/`vec-map`, code is more verbose but fully functional. |
| `html.cl` — HTML generation | **Partially** | String building with `str-concat` works (Ring 1). Iterating over 81 cells via recursive index loop + `vec-get` works. Individual cell rendering, table row construction, CSS embedding — all expressible. **Pain point**: deeply nested `str-concat` (U1.11) makes HTML building verbose. No threading macro (`->`) or variadic `str` yet. Functional but ugly. **Blocker**: no `int-to-string` for digit display... wait, `int-to-string` IS available (Ring 1). So digit rendering works. |
| `form.cl` — URL form parsing | **No** | Requires `str-split` (to split on `&` and `=`), `char-at` (character inspection), and `str-contains`/`str-sub` (substring operations). None of these exist as primitives yet (U1.1). `str-eq` and `str-len` are available but insufficient for parsing. **Hard blocker**: no character-level or substring string operations. |
| `main.cl` — routing, IO models | **No** | IO model (Ring 4), platform DLL (Ring 4). String matching for routes (`str-eq`) works, but without IO the routing logic has no context. |
| `test submodules` | **No** | Modules (Ring 2). Testing infrastructure (`run-tests`, `assert-eq`) (Ring 3+). |
| `platforms/web/` — Rust DLL | **No** | Platform system (Ring 4). |

**What CAN be implemented now (single-file, no modules/traits/macros)**:

1. **Grid data model** — `Cell` ADT (bitmask candidates), `Grid` wrapping `Vec Cell`. Construction from a pre-built Vec (not from string parsing — blocked on `char-at`). All grid accessors: `cell-at`, `set-cell`, `row-of`, `col-of`, `box-of`. Peer calculation returning `Vec Int`.

2. **Complete solver algorithm** — Constraint propagation (eliminate value from peers, detect contradictions, find naked singles), backtracking search (find minimum-candidate cell, try each candidate, recurse). The entire algorithm uses only: Int arithmetic, Bool logic, `if`, pattern matching on `Cell`/`PropResult`/`SolveResult`, `vec-get`/`vec-set`/`vec-len`, and self-recursive functions (TCO). No higher-order functions, closures, or stdlib needed.

3. **Basic text output** — Given a solved grid, render it as a text string using `str-concat` and `int-to-string`. Not HTML (that needs iteration helpers for ergonomics) but sufficient to verify correctness. Example: render each row as "5 3 4 | 6 7 8 | 9 1 2".

4. **Solver validation** — Hard-code a known puzzle as a Vec of Cell values (bypassing string parsing), solve it, verify the result. This is the single-file proof-of-concept that validates the core algorithm.

**Proof-of-concept scope**: A single-file program (~300-400 lines) containing:
- `Cell`, `Grid`, `PropResult`, `SolveResult` ADT definitions
- `rem-i64`, `row-of`, `col-of`, `box-of` index arithmetic
- `make-peers` peer index calculation
- `eliminate`, `propagate`, `find-min-candidates`, `solve` — full solver
- `make-test-grid` hard-coded puzzle (bypasses `char-at` blocker)
- `grid-to-string` text rendering
- `main` that constructs, solves, and returns a checksum value

This would validate: ADTs with fields in Vec, Vec random access and functional update, recursive algorithms over Vec, bitmask operations, TCO in the search, and composition of all these features at realistic scale (~81-cell grid, ~20 peers per cell, recursive backtracking).

**Blocking issues for full exemplar**:

| Issue | Severity | Blocks | Arrives at |
|---|---|---|---|
| `char-at` primitive | **Blocking** | `make-grid` (string→Grid parsing), `form.cl` | Ring 2 stdlib or new primitive (U1.1) |
| `str-split` primitive | **Blocking** | `form.cl` (URL form parsing) | Ring 2 stdlib or new primitive (U1.1) |
| `str-contains` primitive | Important | `html/test.cl` assertions, `form.cl` | Ring 2 stdlib or new primitive (U1.1) |
| `str-sub` (substring) | Important | `form.cl`, `url-decode` | Ring 2 stdlib or new primitive (U1.1) |
| `mod`/`rem` primitive | Important | `col-of`, `box-of` (workaround exists) | Ring 2 stdlib |
| Vec scope-level dec | Important | Long-running solver sessions (memory leak) | Ring 2 |
| Modules/imports | **Blocking** (for decomposition) | Multi-file exemplar | Ring 2 |
| Traits (`Eq`, `Display`) | Important | Test assertions, debug output, `derive` | Ring 2 |
| Macros (`do`, `->`, `cond`) | Important | Ergonomics, especially HTML building | Ring 3 |
| IO, platform DLLs | **Blocking** (for web) | `main.cl`, web server | Ring 4 |

**Revised timeline**:

| Milestone | Ring | What becomes possible |
|---|---|---|
| **Sprint 3 (now)** | 1 (complete) | Single-file proof-of-concept: Grid + solver + text output. Validates core algorithm and data model. ~300-400 lines. |
| **Ring 2** | 2 | Multi-module decomposition. String primitives (`char-at`, `str-split`) enable `make-grid` and `form.cl`. Traits enable `Eq`-based test assertions and `Display` for debugging. Vec RC balanced. |
| **Ring 3** | 3 | Full exemplar core with macros, prelude, stdlib, `run-tests`. All pure modules implementable: `grid.cl`, `solver.cl`, `html.cl`, `form.cl` with test submodules. Ergonomic string building with threading macros. |
| **Ring 4** | 4 | Web platform DLL, IO wiring, `main.cl` with both serve models, integration tests. Exemplar complete. |

**Risk updates**:

1. **Vec confirmed functional** — 32 integration tests + 4 REPL tests passing. COW works. Polymorphic element types work. The critical-path blocker (U1.10) is resolved.
2. **String primitive gap is now the critical path** — With Vec available, the next blocker is string manipulation primitives (`char-at`, `str-split`, `str-contains`, `str-sub`). These are needed for `make-grid` and `form.cl`. Filed as U1.1, expected at Ring 2.
3. **Bitmask candidate design validated** — The decision to use Int bitmasks instead of `Vec Int` for candidate sets (made at Ring 1) is confirmed as the right call. It eliminates nested Vec complexity and is more performant.
4. **Higher-order Vec functions not needed for solver** — The solver can use explicit recursive index loops over Vec. `vec-filter`/`vec-map`/`vec-fold` would improve ergonomics but are not blockers. They arrive with `/stdlib` at Ring 2-3.
5. **Vec memory leak is acceptable for prototyping** — Scope-level dec deferred to Ring 2. The proof-of-concept solver runs once and exits, so leaks don't accumulate. Long-running web server (Ring 4) will need balanced RC.

### Ring 2A Assessment (Sprint 4) — Trait Dispatch

**Ring 2A features available**: Trait declarations (`deftrait`), trait implementations (`impl`), operator dispatch via `Num`/`Eq`/`Ord` traits with impls for `Int`, `Float`, `Bool`, `String`. Constrained polymorphism (`(defn add [x y] (+ x y))` infers `Num a => (Fn [a a] a)`, monomorphised at call sites). Default methods (`<=`, `>=`, `!=`). ADT trait impls (concrete and polymorphic). Type annotations with trait constraints.

**Ring 2A does NOT deliver**: Modules/imports, multi-sig dispatch, auto-curry, stdlib files, platform DLLs, `derive`. These are Sprint 5 (Ring 2B).

**Component-by-component trait assessment**:

| Component | Trait impact | Assessment |
|---|---|---|
| `grid.cl` — index arithmetic | **Direct benefit** | `row-of`, `col-of`, `box-of` can use `+`, `-`, `*`, `/` via `Num` instead of `add-i64`, `sub-i64`, `mul-i64`, `div-i64`. Code becomes readable: `(/ idx 9)` instead of `(div-i64 idx 9)`. The `rem-i64` workaround `(- a (* (/ a b) b))` becomes `(- a (* (/ a b) b))` — same logic, cleaner syntax. |
| `grid.cl` — Cell comparison | **Partially available** | `Eq` could be manually implemented for `Cell` via `(impl Eq Cell ...)`, enabling `(= cell1 cell2)` in test assertions. However, `derive [Eq]` is not yet available (Sprint 5), so each constructor case must be hand-written in the `impl`. For the bitmask-candidate `Cell` (3 constructors, each with one `Int` field), this is ~15 lines — tedious but feasible. |
| `solver.cl` — constraint propagation | **Direct benefit** | All arithmetic in the solver (candidate bitmask operations, index calculations, counting) now uses clean operator syntax. `(> count 0)` instead of `(gt-i64 count 0)`. This is the biggest ergonomic win — the solver has dozens of arithmetic/comparison expressions. |
| `solver.cl` — PropResult/SolveResult comparison | **Partially available** | `PropResult` is a pure enum (4 nullary constructors). `(impl Eq PropResult ...)` is straightforward — compare tags. `SolveResult` has a data constructor `(Success [grid])` — `Eq` impl would need to compare grids, which requires `Eq` on `Vec Cell`. Not practical without `derive` or Vec equality. Pattern matching remains the primary dispatch mechanism for these types. |
| `html.cl` — grid display | **Limited** | `Display` trait with `show :: (Fn [a] String)` could be implemented for `Cell` to produce digit strings. But the HTML renderer needs structured output (CSS classes, table cells), not just `show`. `Display` on `Cell` is useful for debugging (`(show cell)`) but not for HTML generation. `int-to-string` remains the practical choice for digit rendering. |
| `html.cl` — string building | **Minor benefit** | `str-concat` is already available; trait dispatch does not change string building. The real ergonomic improvement for HTML comes from threading macros (`->`) at Ring 3. |
| `form.cl` — form parsing | **No change** | Still blocked on string manipulation primitives (`char-at`, `str-split`, `str-contains`, `str-sub`). Trait dispatch does not address these gaps. |
| `main.cl` — routing | **No change** | Still blocked on IO model and platform DLLs (Ring 4). |
| Test assertions | **Available** | With `Eq` impls on `Cell` and `PropResult`, test assertions can use `(= actual expected)` instead of pattern-matching each case. This is a significant testing ergonomic win, though `assert-eq` infrastructure itself needs `run-tests` (Ring 3). |

**What can be done now that could not before**:

1. **Clean operator syntax throughout** — Every `add-i64`/`sub-i64`/`mul-i64`/`div-i64`/`eq-i64`/`lt-i64`/`gt-i64`/`le-i64`/`ge-i64` call in the proof-of-concept can be replaced with `+`/`-`/`*`/`/`/`=`/`<`/`>`/`<=`/`>=`. This is the single biggest readability improvement.

2. **Constrained polymorphic helpers** — Generic utility functions like `(defn max [x y] (if (> x y) x y))` get inferred as `Ord a => (Fn [a a] a)`. Useful for `find-min-candidates` which needs to compare candidate counts.

3. **Manual `Eq` on Cell** — Enables equality-based test assertions for the grid data model. Not blocked on `derive`.

4. **`Display` for debugging** — `(impl Display Cell (show [c] ...))` can produce a text representation. Useful for REPL-based debugging of the solver, even though the real output is HTML.

**What still needs later rings**:

| Need | Blocked on | Arrives at |
|---|---|---|
| `derive [Eq Display]` on ADTs | `derive` macro infrastructure | Ring 3 (macros) |
| Multi-module decomposition | Module system | Sprint 5 (Ring 2B) |
| `char-at`, `str-split`, `str-contains` | String primitives in stdlib | Sprint 5+ (stdlib) |
| `vec-filter`, `vec-map`, `vec-fold` | Higher-order Vec functions | Sprint 5+ (stdlib) |
| `mod`/`rem` as operator | Stdlib or new primitive | Sprint 5+ |
| IO model, platform DLLs | Platform system | Ring 4 |
| Threading macros (`->`, `->>`) | Macro system | Ring 3 |

**Risks and concerns**:

1. **Manual `Eq` impls are fragile** — Without `derive`, any change to an ADT requires updating the corresponding `Eq` impl. For the exemplar this is manageable (3-4 types), but it means the exemplar code written now will need updating when `derive` arrives. Acceptable for prototyping.

2. **No `Display`-based print** — The `show` method returns a `String`, but there is no `print` or `println` that dispatches on `Display`. Printing a value still requires calling `show` explicitly and then using an IO primitive. This is fine for the exemplar (HTML output is string-based anyway) but worth noting.

3. **Proof-of-concept rewrite opportunity** — If a Sprint 3 proof-of-concept exists using `add-i64`-style primitives, it should be rewritten with operator syntax to validate trait dispatch at realistic scale. This is a good validation exercise for Ring 2A.

**Verdict**: Ring 2A is a **significant ergonomic improvement** for the exemplar but does not unlock new components. The solver algorithm and grid model were already expressible (Sprint 3). What changes is readability: operator syntax replaces verbose primitive names throughout. Manual `Eq` impls enable equality-based assertions. `Display` provides debug output. The exemplar remains blocked on modules (Sprint 5) for multi-file decomposition and on string primitives for `make-grid` and `form.cl`.

**Recommended action**: If a single-file proof-of-concept was built at Sprint 3, rewrite it with trait-based operators as a Ring 2A validation exercise. Otherwise, wait for Sprint 5 (modules + stdlib) before beginning serious exemplar implementation.

### Ring 3+

Grid model, solver, HTML generation, form parsing — all pure computation. Testable with `run-tests`. This is the bulk of the Cranelisp code.

### Ring 4

Web platform DLL, request routing, IO wiring (`main`, `serve-loop`, `serve`). Integration tests.

The clean pure/IO split means most exemplar work can begin at Ring 3, before the platform exists.

---

## Estimated Scale

| Component | Lines (est.) |
|---|---|
| `grid.cl` + tests | ~150 |
| `solver.cl` + tests | ~200 |
| `html.cl` + tests | ~250 |
| `form.cl` + tests | ~80 |
| `main.cl` (both models) | ~60 |
| **Cranelisp total** | **~740** |
| `platforms/web/src/lib.rs` | ~200 |
| **Overall total** | **~940** |

Comfortably within the 500–2000 line target.

---

## Ring 3 Readiness Assessment (Sprint 9)

Analysis of which exemplar patterns depend on macros vs IO, and what becomes implementable at Ring 3.

### Macro Dependencies by Module

| Module | Macros used | IO required? | Ring 3 viable? |
|--------|------------|--------------|----------------|
| `grid.cl` | `derive [Eq Display]`, `list` (if candidate sets use lists), `cond` (multi-way dispatch) | no | **yes** |
| `solver.cl` | `cond` (multi-way propagation results), `->` (pipeline compositions), `case` (optional) | no | **yes** |
| `html.cl` | `str` (string building), `->` (threading for string pipelines), `cond` (conditional rendering) | no | **yes** |
| `form.cl` | `cond` or `case` (dispatch on parsed values), `->` (threading) | no | **yes** |
| `main.cl` | `do`, `bind!` | **yes** (platform, `listen`/`accept`/`send`/`serve`) | **no** — Ring 4 |
| `**/test.cl` | `do` (sequencing assertions), testing macros | no (uses `run-tests`) | **yes** |

### Pattern Analysis

**Pure computation patterns (Ring 3)**:
- **`derive [Eq Display]`** on `Cell`, `SolveResult`, `PropResult`, `Color` — requires the `derive` macro infrastructure (multi-form expansion, per-trait helper macros). This is a Ring 3 feature.
- **`cond` multi-way conditional** — used in solver for propagation result dispatch, in HTML for conditional rendering, in routing for method/path dispatch. Pure syntactic rewriting to nested `if`.
- **`->` thread-first** — used in HTML string building pipelines and solver data transformations. Pure syntactic rewriting.
- **`str` variadic string concatenation** — heavily used in `html.cl` for building HTML strings. Depends on `show` (Display trait, Ring 2) and `str-concat` (primitive, Ring 1).
- **`list` construction** — used if candidate sets are represented as List values (current plan uses bitmask Int, so this is optional).
- **`case` value dispatch** — optional; `cond` with explicit `=` comparisons is equivalent.

**IO patterns (Ring 4 only)**:
- **`do` sequencing** — used in `main.cl` for IO action sequencing. Also appears in test modules for assertion sequencing, but test modules can use `let [_ ...]` chains instead.
- **`bind!` monadic bind** — used exclusively in `main.cl` for IO binding (`listen`, `accept`, `send`, `serve`, `read-line`). Not needed in any pure module.
- **`platform` declaration** — only in `main.cl`. All other modules are platform-independent.

### What Becomes Possible at Ring 3

1. **Full `grid.cl` module** — With `derive [Eq Display]`, the Cell/Grid/SolveResult/PropResult types get automatic equality and display. With `cond`, multi-way dispatch reads naturally. With string primitives from stdlib (`char-at`, `str-split`), `make-grid` can parse puzzle strings.

2. **Full `solver.cl` module** — The entire constraint propagation + backtracking algorithm is pure computation. `cond` for multi-way result dispatch, `->` for pipeline-style transformations. No IO dependency.

3. **Full `html.cl` module** — HTML generation is pure string building. `str` macro for concatenation, `->` for threading through string transformations, `cond` for conditional rendering. Heavily macro-dependent for ergonomics but functionally possible without macros (just verbose).

4. **Full `form.cl` module** — URL form parsing is pure string manipulation. Depends on string primitives (`str-split`, `char-at`, `str-contains`) and `cond`/`case` for dispatch.

5. **All test submodules** — `grid/test.cl`, `solver/test.cl`, `html/test.cl`, `form/test.cl` can use `run-tests` infrastructure with `assert-eq`, `assert-true`. Test assertions use `Eq` trait (Ring 2). Test discovery uses `run-tests` (Ring 3+).

6. **NOT `main.cl`** — Routing and IO wiring depend on the platform system (Ring 4). However, the pure `handle` function (request routing to response) can be written and tested at Ring 3 using mock Request/Response values.

### Blocking Dependencies

| Dependency | Status | Blocks |
|-----------|--------|--------|
| `derive` macro | Ring 3 | `Eq`/`Display` impls on all ADTs |
| `cond` macro | Ring 3 | Multi-way dispatch in solver, HTML, routing |
| `->` macro | Ring 3 | Pipeline-style string building in HTML |
| `str` macro | Ring 3 | Ergonomic string concatenation in HTML |
| `char-at` primitive | Ring 3 stdlib | `make-grid` string parsing |
| `str-split` primitive | Ring 3 stdlib | `form.cl` URL parsing |
| `str-contains` primitive | Ring 3 stdlib | Test assertions, URL decoding |
| `mod`/`rem` | Ring 3 stdlib or primitive | `col-of`, `box-of` (workaround exists) |
| Platform DLL system | Ring 4 | `main.cl`, web server |
| `do`, `bind!` macros | Definable at Ring 3, usable at Ring 4 | IO sequencing in `main.cl` |

### Verdict

**Ring 3 unlocks 5 of 7 Cranelisp modules** (grid, solver, html, form, plus all test submodules). Only `main.cl` and the platform DLL require Ring 4. The exemplar's pure/IO split means that approximately 85% of the Cranelisp code (~630 of ~740 estimated lines) can be implemented and tested at Ring 3. The critical macro dependencies are `derive`, `cond`, `->`, and `str` — all of which are in the prelude macro set and have no IO dependency.

## Ring 3 Macro Usage Map (Sprint 10 Refinement)

Module-level macro dependency matrix, refined from the Sprint 9 readiness assessment.

| Module | `cond` | `case` | `->` / `->>` | `str` | `vec` | `when` | `list` | `def`/`const` | `do`/`bind!` |
|--------|--------|--------|---------------|-------|-------|--------|--------|---------------|--------------|
| `grid.cl` | x | | | | x | | | x | |
| `solver.cl` | x | | x | | | x | | | |
| `html.cl` | x | | x | x | | | | x | |
| `form.cl` | x | x | x | | | | | | |
| `main.cl` | | | | | | | | | x |
| `**/test.cl` | | | | | x | | | x | |

**Implementable after Sprint 11 prelude macros** (pure computation, no IO):
- `grid.cl` — ADTs, `cond`, `vec` literal, `def` constants. Needs `char-at`/`str-split` from stdlib.
- `solver.cl` — core algorithm uses `cond`, `->`, `when`. Fully self-contained once macros land.
- `html.cl` — heaviest macro user (`str`, `->`, `cond`, `def`). String-building ergonomics depend on `str` macro.
- `form.cl` — `cond`/`case`/`->` for parsing logic. Needs string primitives from stdlib.
- `**/test.cl` — all four test submodules use `run-tests`, `vec` literals, `def` for test data.

**Requires Ring 4 IO** (~15% of Cranelisp code, as identified in Sprint 9):
- `main.cl` (~60 lines) — `do`/`bind!` for IO sequencing, `(platform web)` declaration.
- `platforms/web/` — Rust DLL, entirely Ring 4.

**Sprint 11 /port task**: Implement `grid.cl` and `solver.cl` first (lowest stdlib dependency, highest algorithm value), then `html.cl` and `form.cl` (heavier stdlib/string dependency). All four test submodules follow their parent module. Defer `main.cl` and platform DLL to Ring 4 sprint.

---

## Current Status (Sprint 17)

**Exemplar fails in reimplementation with**: `error: parse error at 1328..1349: unknown top-level form: const`

**Root cause**: `run_file()` in `src/main.rs` previously set `project_root` to `file_path.parent()`. When the entry file is `exemplar/solver.cl`, project_root became `exemplar/`, so `assemble_lib_dirs` looked for `exemplar/stdlib/` (doesn't exist) and `resolve_prelude` looked for `exemplar/prelude.cl` (doesn't exist). The prelude was never loaded, and `(const full-mask 511)` in `grid.cl` — a prelude macro — failed as an unrecognized form.

**FIXME resolved (Sprint 25)**: `run_file()` in `src/main.rs` now uses `std::env::current_dir()` for `project_root`, matching the REPL's behavior. This ensures prelude/stdlib resolution works correctly for files in subdirectories.

**Pure core status in sketch**: grid.cl, solver.cl, html.cl, form.cl all work in the prototype compiler. The reimplementation has the pipeline machinery (module graph, prelude loading, macro expansion) and the project_root derivation is now correct.

---

## Next Skills

- `/stdlib` — String primitives (`char-at`, `str-split`, `str-contains`, `str-sub`) remain the critical path for the exemplar (U1.1). Also: `mod`/`rem`, `vec-filter`, `vec-map`, `vec-fold`. Consider a variadic `str` function for string building ergonomics (U1.11).
- `/platform` — Review the web platform API above. Confirm that `declare_platform!` can handle: (a) a function receiving a function pointer callback (`serve`), (b) opaque heap values for Request/Response. Flag if the platform ABI needs extension for callbacks.
- `/examples` — The exemplar's ADT patterns (sum types with data, enum types with derive) should align with the learning sequence.
- `/docs` — The exemplar will serve as the capstone tutorial/walkthrough. The web platform authoring is a natural "advanced topic" chapter.
- `/port` — At Sprint 5 (Ring 2B, post-modules, post-string-primitives): decompose into multi-module structure, implement `make-grid` (needs `char-at`). At Ring 3: implement full exemplar core with macros, `derive`, and testing. At Ring 4: web platform DLL and IO wiring.
