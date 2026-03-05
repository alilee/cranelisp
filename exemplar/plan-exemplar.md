# Exemplar Project: Sudoku Solver with Web Platform

Selected exemplar project for the Cranelisp reimplementation. This document is owned by the `/port` skill, updated from the Sprint 0 candidate evaluation.

## Decision

**Selected**: Sudoku Solver with a custom web platform (HTTP server).

**Rationale**: The Sudoku solver hits the best balance across all nine selection criteria: algorithm-rich (constraint propagation + backtracking), universally familiar domain, clean pure/IO split, moderate and predictable scope. The web platform replaces stdio as the IO layer, adding a compelling demo experience (browser-based puzzle input and solution display) and deeply validating the platform model.

**Key insight**: The platform DLL is part of the exemplar, not separate infrastructure. Writing a platform is something application developers do — the exemplar demonstrates that this is not an impossible ask.

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

### Backtracking Search (`solver.cl`)

- `find-min-candidates :: (Fn [Grid] (Option Int))` — index of unfixed cell with fewest candidates (MRV heuristic)
- `solve :: (Fn [Grid] SolveResult)` — propagate, then if unsolved: pick min-candidate cell, try each candidate recursively, backtrack on contradiction

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

## Next Skills

- `/platform` — Review the web platform API above. Confirm that `declare_platform!` can handle: (a) a function receiving a function pointer callback (`serve`), (b) opaque heap values for Request/Response. Flag if the platform ABI needs extension for callbacks.
- `/stdlib` — Prioritize `mod`/`rem`, `char-at`, `str-len`, `vec-filter`, `str-split` — these are blocking or important for the exemplar.
- `/arch` — Review whether the platform callback mechanism (function pointer passed to DLL, DLL calls back into JIT code) requires architectural support or is already covered by the existing GOT/function-pointer model.
- `/examples` — The exemplar's ADT patterns (sum types with data, enum types with derive) should align with the learning sequence.
- `/docs` — The exemplar will serve as the capstone tutorial/walkthrough. The web platform authoring is a natural "advanced topic" chapter.
