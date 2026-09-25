# Sudoku exemplar design

Owner: `dev`, narrow-deployed to `exemplar/`. This document states the current
design of the built Sudoku Solver exemplar and its open obligations. Entry
guidance, run commands and evidence navigation are in the
[exemplar memory](CLAUDE.md). Language behaviour is specified in `spec/`, and
this document does not restate it.

## Purpose

The exemplar shows that Cranelisp handles a real multi-module program:

- constraint propagation and backtracking search over domain ADTs
- module decomposition around one pure core
- server-side HTML and form parsing without JavaScript
- an application-authored platform DLL (`platforms/web/`)
- parallel search and concurrent serving that the compiler infers, with no
  `spark`, `par` or `spawn` in the source

## Architecture

One pure core serves two IO entries.

| Module | Responsibility |
|---|---|
| `grid.cl` | Data model, candidate-bitmask adapters, index geometry, peers, `make-grid`, `is-solved` |
| `solver.cl` | `eliminate`, `propagate`, MRV (`find-min-candidates`), `solve`, board formatting |
| `html.cl` | Form, solution, error and not-found pages |
| `form.cl` | URL-encoded form body → 81-character puzzle string |
| `user.cl` | Stdio entry (the headline showcase) |
| `main.cl`, `serve.cl`, `web.cl` | Web entry: router, serve loop, and the `web` platform's language-side types |

`user.cl` drives the same pipeline the web route uses:

```text
form body  --parse-form-body-->  puzzle string
puzzle     --make-grid-------->  Grid
Grid       --solve------------>  SolveResult
solution   --format-board----->  ASCII board
solution   --solution-page---->  HTML page
```

### Data model

- `Cell` is `Given`, `Solved` or `Candidates`. Candidates is a 9-bit mask
  where digit *d* is bit *d*−1 and `full-mask` is 511.
- `(Grid cells-type)` holds the 81 cells as a flat Vec.
  `(SolveResult grid-type)` is `Success` or `Unsolvable`.
- `Grid` and `SolveResult` are deliberately explicit generics (spec §5.2.4).
  Spelling the field as `(Vec Cell)` is legal, but it would force the
  element type and sidestep the inference that the
  [multi-sig obligation](#multi-sig-vec-helper-showcase) must demonstrate.

### Solving

- `eliminate` and `propagate` return `(Option Grid)`, where `None` means a
  contradiction. Propagation repeats until the grid stops changing. Each step
  depends on the previous grid, so propagation is sequential.
- When propagation stalls, `solve` picks the unfixed cell with the fewest
  candidates (MRV). It then maps each candidate digit to a recursive solve
  with `collections.parallel/par-map-reduce` and reduces the results with the
  associative `first-success` (identity `Unsolvable`).
- `par-map-reduce` splits the digits into independent `let` bindings. Lenient
  evaluation sparks those bindings, and the spark budget falls back to serial
  evaluation ([lenient evaluation](../design/backend/lenient-eval.md) §2.1,
  §3.6). The search is speculative: losing branches are discarded.
- Correctness is the contract. The parallel and serial
  (`CRANELISP_NO_LENIENT=1`) searches must produce the same result, because a
  valid puzzle has one solution. Parallel search is not yet faster than serial
  (see
  [copy-per-guess performance](#copy-per-guess-performance)).

### Web server

- Routes: `GET /` form, `POST /solve` solution or error page, `GET /slow`
  a page served after a fixed delay for the fan-out demonstration. Any other
  path gets 404, and any other method gets 405.
- `handle` is pure (`Request → Response`). `safe-handle` wraps it in
  `catch-runtime-error`, so a faulting request gets a 500 while the server
  keeps running.
- **Concurrency is inferred, not written.** `serve-loop` binds the next
  connection and discards a per-connection sub-tree
  (`read-conn` → `sleep` → `send-conn`). That sub-tree's footprint is disjoint
  from the continuation's `listener`, so bind-chain analysis infers a detached
  launch: one supervised strand per connection
  ([effect concurrency](../design/arch/effect-concurrency.md) §4.1).
- **Keep every effect position a direct leaf.** A user function that returns
  IO in the handler sub-tree has an opaque footprint. Eligibility analysis must
  refuse it, so the server silently serialises. Pure helpers such as
  `slow-ms` and `safe-handle` may compute leaf arguments only.
- The `web` platform uses the mixed `declare_platform!` shape.
  `bind-listener` is `Sequential`. `accept-conn`, `read-conn` and `send-conn`
  are poll leaves. `web/Connection` is an opaque handle carrying only the
  socket `fd`; scheduling state never rides on the value
  ([effect concurrency](../design/arch/effect-concurrency.md) §4.1.1).
  `CRANELISP_PORT` overrides the default port 8080.

## Design decisions

- **Bitmask candidates.** Candidate tracking needs no heap allocation, and each
  mask operation is O(1).
- **Digit-domain adapters over `num.bits`.** `grid.cl` imports the
  bit-position verbs by name. It defines its own digit-domain
  `pow2`/`bit-set?`/`bit-clear`/`bit-set`/`bit-count`/`bit-lowest`, because
  importing the position-domain `bit-clear`/`bit-set` would collide with them.
  The native operations are 64-bit two's-complement; the masks never use the
  sign bit.
- **`rem-i64` stays inline.** `num.int/rem` has the same semantics. One local
  arithmetic identity reads more clearly in `col-of` than a cross-module import.
- **HTML is built with `str-concat`, not the `str` macro.** This keeps
  `show`-dispatch overhead out of production output. For the same reason, the
  `Display Cell` implementation is a REPL and debug affordance that the
  formatting path does not use.
- **Form parsing** splits on `&` and `=` with the `split` primitive, then
  rebuilds the puzzle with `substring` and `str-concat`.
- **Source is idiomatic, not defect-shaped.** Do not rewrite exemplar source
  around a compiler defect, for example by annotating to force inference or by
  removing the contradiction arm of `eliminate`. The exemplar is valuable
  because it measures what an ordinary application author writes. File the
  defect instead.

## Open obligations

### Multi-sig Vec-helper showcase

`is-solved` is one multi-signature `defn`: the 1-argument clause seeds the
scan. `make-grid`/`make-grid-helper` and `peers`/`peers-helper` remain
two-function pairs. Collapsing either pair makes a multi-signature Vec result
reach a separately monomorphised consumer through a bound parameter. That
currently fails with a located carrier-gate type error.

- **Trigger:** collapse both pairs when
  `tests/mc_x4_consume_at_distance_0719.rs::multi_sig_return_through_wrapper_indirection_infers`
  passes. Spec §5.1.2 requires the multi-sig form to infer like its
  two-function equivalent.
- The green MC-X4 battery (`tests/mc_x4_multi_sig_return_consumer.rs`) is not
  the trigger. It consumes the result in the same expression, not through a
  parameter.
- Do not force the collapse by annotating the seed or the ADT field.

### Copy-per-guess performance

`set-cell`/`assoc` copy the 81-cell Vec on every guess. That makes hard-puzzle
search quadratic, and under parallel evaluation it causes allocator and
atomic-RC contention, so parallel search is slower than serial.
`solver/test-hard-puzzle` stays out of `tests.cl` until a hard puzzle solves in
fast-test time. The analysis, proposed fix and re-entry trigger are in the
[performance backlog](../design/arch/backlog/performance.md) under 0408.

### Stdlib adoption

The S87 adequacy review's stdlib verbs now exist. The exemplar has adopted
`conj`, `num.bits`, `digit-to-char` and `repeat-str`, and it reuses
`row-of`/`col-of`. It has not yet adopted three verbs:

- `text.string/char-to-digit` for `form.cl` `parse-digit-char` and the
  digit ladder in `grid.cl` `make-grid-helper`
- `text.string/replace-at` for `form.cl` `set-char-at`
- `collections.vec/range` with `vec-reduce`/`vec-map` for the hand-threaded
  0..9 and 0..81 index loops (`*-helper` functions) across the four pure
  modules

Adopt each verb only where it reads better. Do not reshape `eliminate` or the
propagation path.

### Qualified `Display Cell` spelling

`grid.cl` uses the bare `(impl Display Cell …)` head. The S117 attempt to use
the qualified `text.display/Display` head was reverted, because warm-cache
dispatch lost the implementation. That failure is guarded by
`tests/cache.rs::cache_restores_sibling_written_trait_impls_for_dispatch`.
Re-attempt the qualified head only after that guard passes.
