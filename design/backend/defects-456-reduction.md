# Sprint 59 Wave 1 — Defects 4+5 and 6 Reduction Report

**Workstream**: Sprint 59 Wave 1 follow-on (co-owner mode `/backend` + `/qa`)
**Status**: Phase 4 — D4/5 reduced to ≤25 LOC html + 14 LOC grid, pinned to tail-recursive row loop over 2-grid `cell-at` + `match` + `str-concat`. No fix applied.
**Tests**: `tests/sprint59_defects456_repro.rs`

Per root `CLAUDE.md` §"Usability Findings and Defects", these reductions join the suite as small, failing, un-ignored regression guards. The **original** demo-level reproductions in `tests/wave6_demo_repros.rs` stay in place unchanged.

---

## Runs used

4 of 6 `cargo nextest run` invocations, all against `--test sprint59_defects456_repro` only.

---

## Defect 4+5 — `/run-tests` batched invocation SIGSEGV

### Failing reduction committed

**`tests/sprint59_defects456_repro.rs::d45_real_exemplar_html_run_tests_no_crash`** — imports one test-* fn from the real exemplar `html.cl`, then runs `/run-tests html`. Child process dies by signal.

### Passing reductions (ruled-out negative controls)

All of these PASS (no signal crash), together forming a tight diagnostic fence:

| Test | Shape | Passing tells us |
|---|---|---|
| `d45_baseline_trivial_run_tests_no_crash` | Synthetic module, 1 `(defn test-none-ok [] None)`. | `/run-tests` dispatch itself is NOT the defect. |
| `d45_single_str_concat_contains_run_tests_no_crash` | 1 synthetic test doing `(if (contains? (str-concat "a" "b") "a") None ...)`. | Single test body with `str-concat` + `contains?` is NOT the defect. |
| `d45_wrap_tag_html_verbatim_run_tests_no_crash` | 1 test copying html.cl's `test-wrap-tag` verbatim (5-deep nested `str-concat` + `str-eq`) but in an isolated synthetic module. | The body shape in isolation is NOT the defect. |
| `d45_multiple_tests_with_contains_run_tests_no_crash` | 3 tests in a batch with `contains?`. | Short batched dispatch of similar bodies is NOT the defect. |
| `d45_form_shaped_body_run_tests_no_crash` | `str-eq` + `Some`-with-string return. | `Some (string)` boxing in a test return-value is NOT the defect. |
| `d45_two_trivial_tests_run_tests_no_crash` | 2 trivial tests returning `None`. | Batch-size-of-2 is NOT the defect. |
| `d45_ten_str_bodies_run_tests_no_crash` | 10 tests with `str-concat` + `contains?` bodies, same module. | Batch-size-of-10 with string work is NOT the defect. |
| `d45_real_exemplar_html_single_run_test_no_crash` | Real `html.cl` loaded + `(run-test "html/test-wrap-tag")` (NOT `/run-tests`). | **Individual** `run-test` call on a real html test is NOT the defect (confirms /port Wave 6 finding). |

### Diagnosis — narrowed

The defect is NOT in any of:
- `/run-tests` command dispatch
- Dispatching multiple test bodies (up to 10 in a synthetic module works)
- Individual test body shape (str-concat, contains?, wrap-tag nesting)
- `Option` (None/Some) return values from test bodies
- A single `(run-test ...)` call against the real html module

The defect **IS** something that needs ALL of:
- The real `exemplar/html.cl` loaded into the session (with its `grid.cl` cross-module dependency chain)
- `/run-tests <module>` batched dispatch (not individual `(run-test ...)`)

Two plausible remaining hypotheses (neither ruled in nor out by these reductions):

1. **Cross-module ADT RC**: html.cl imports `Grid`, `Cell`, `Given`, `Solved`, `Candidates`, `cell-at`, `cell-value` from `grid`. html's `make-all-ones-grid` builds a `Grid (Vec Cell)` value. When a test like `test-solution-page-has-digits` uses it, the cross-module-ADT flow through `run_test_by_name` may not cleanly decrement the inner Vec of Cells on return. Synthetic reductions have no cross-module ADT dependency.
2. **Symbol-table / discovery interaction**: `/run-tests html` discovers test-* names via `discover_test_names` on the `html` module's symbol table. The batch dispatches via `run_test_by_name`. If the GOT lookup for a test whose body transitively reaches a `grid/*` symbol resolves to a stale or not-yet-finalised code pointer, `run_test_by_name`'s call could return to junk. Synthetic modules have no external GOT slots.

### CLIF-level observation

Could not obtain CLIF inspection for the crashing path in this session — `/clif <defn>` in the REPL requires the module to load successfully first and the child dies on `/run-tests html`, so there is no interactive CLIF capture. Recommend `/backend` re-run with `CRANELISP_CODEGEN_TRACE=1 cargo nextest run --test sprint59_defects456_repro d45_real_exemplar_html_run_tests_no_crash` and inspect the CLIF emitted for `test-wrap-tag` and the test-dispatch trampoline.

---

## Phase 4 — Minimal repro pair reached

### Further reductions (Phase 4 session, +13 tests)

Probed the "cross-module 2-file" axis the prior agent had not isolated. Progressively added html-ness to a synthetic 2-file pair, then switched to stripping the real html.cl paired with a hand-trimmed 14-line grid.cl fixture.

| Test | Outcome | Axis isolated |
|---|---|---|
| `d45_cross_module_adt_basic_no_crash` | PASS | Cross-module ADT ctor + match alone — NOT enough |
| `d45_cross_module_import_but_no_use_no_crash` | PASS | Importing Grid-ADT symbols without using them — NOT enough |
| `d45_cross_module_grid_build_in_test_no_crash` | PASS | Building Grid (Vec Cell) via cross-module ctor in one test — NOT enough |
| `d45_cross_module_html_like_batch_no_crash` | PASS | 4-test batch with Grid-build + deep str-concat + match — NOT enough |
| `d45_cross_module_html_full_10_tests_no_crash` | PASS | 10-test synthetic batch mirroring html.cl's shape — NOT enough |
| `d45_real_html_with_trimmed_grid_no_crash` | **FAIL** | Real html.cl + 14-line trimmed grid.cl. **CRASH REPRODUCED** — pinned away from rest of grid.cl. |
| `d45_html_no_css_no_crash` | **FAIL** | Real html.cl minus `css` fn — CSS is not load-bearing. |
| `d45_html_solution_tests_only_no_crash` | **FAIL** | Only the 3 solution-page tests — non-solution tests are not load-bearing. |
| `d45_html_one_test_no_crash` | PASS | 1 simplified solution-cell test (1-arg signature). Signature simplification changed something. |
| `d45_html_two_tests_no_crash` | PASS | Same 1-arg signature, 2 tests. Batch size alone was not it. |
| `d45_html_three_tests_mixed_no_crash` | PASS | Adds build-mixed-helper + third test. Mixed-grid still insufficient with 1-arg solution-cell. |
| `d45_html_two_arg_solution_no_crash` | **FAIL** | **2 grid params (`original solved idx`) + 2 `cell-at` calls + `wrap-tag`/`td` nesting.** |
| `d45_html_min_v1_no_crash` | **FAIL** | Strip wrap-tag/td, keep 2-grid-param solution-cell, 9-cell row loop, 1 test. **~25 LOC.** |
| `d45_html_min_v2_no_crash` | PASS | Remove the 9-cell row loop; 1 cell + 1 solution-cell call. Loop is load-bearing. |

### Minimal repro — current floor

**`d45_html_min_v1_no_crash`** reproduces the SIGSEGV/SIGTRAP.

**`grid.cl`** (14 LOC):
```lisp
(import [primitives [*]])

(deftype Cell
  (Given [:Int value])
  (Solved [:Int value])
  (Candidates [:Int bitmask]))

(deftype Grid [cells])

(defn cell-at [g idx]
  (match g [(Grid cells) (vec-get cells idx)]))

(defn cell-value [c]
  (match c
    [(Given v) v
     (Solved v) v
     (Candidates _) 0]))
```

**`html.cl`** (25 LOC):
```lisp
(import [primitives [*]])
(import [grid [Grid Cell Given Solved Candidates cell-at cell-value]])

(defn solution-cell [original solved idx]
  (let [orig-cell (cell-at original idx)
        solved-cell (cell-at solved idx)
        digit (int-to-string (cell-value solved-cell))]
    (match orig-cell
      [(Given _) (str-concat "g:" digit)
       _ (str-concat "s:" digit)])))

(defn row-helper [original solved col acc]
  (if (eq-i64 col 9) acc
    (row-helper original solved (add-i64 col 1)
      (str-concat acc (solution-cell original solved col)))))

(defn page [original solved]
  (row-helper original solved 0 ""))

(defn build-helper [v i]
  (if (eq-i64 i 9) v
    (build-helper (vec-push v (Given 1)) (add-i64 i 1))))

(defn make-grid [] (Grid (build-helper [] 0)))

(defn test-page []
  (let [g (make-grid)]
    (if (contains? (page g g) "g:1") None (Some "no g:1"))))
```

Driven via `/run-tests html` on a freshly-imported session.

### Load-bearing features (each reduction step removed one and crash went away)

All of these must be present:
1. **Tail-recursive loop** (`row-helper`) over multiple cells. 1 cell (V2) passes; 9 cells (V1) crashes. Single-shot `solution-cell` call doesn't crash.
2. **Two grid parameters** to the helper called inside the loop (`solution-cell original solved idx`), with two `cell-at` calls against the SAME grid passed twice. 1-grid-param version doesn't crash.
3. **`match` arm** in `solution-cell` that returns a freshly-allocated string via `str-concat` (the result is consumed by the caller's `str-concat` in the loop).
4. **Cross-module ADT extraction** (`cell-at` → `match (Grid cells) (vec-get cells idx)` crossing module boundary). Synthetic same-file ADTs never crashed.
5. **`/run-tests` batched dispatch.** Individual `(run-test "html/test-page")` does not crash (the earlier passing test `d45_real_exemplar_html_single_run_test_no_crash` confirmed this).

### Phase 2 — RC trace observations

<!-- FIXME(/backend): CLIF dump infrastructure gap — `CRANELISP_CODEGEN_TRACE=1`
is documented in `tests/CLAUDE.md` §"Diagnostic Logging" as dumping "CLIF IR
before/after optimization", but is currently wired only for error paths in
`src/worker.rs` and `src/session_v4.rs`, not for normal codegen paths. Sprint
59 Wave 1 defect hunting was forced to use `CRANELISP_RC_TRACE=1` as a proxy
because CODEGEN_TRACE doesn't dump IR. The missing infrastructure: add CLIF
emission hooks to the per-defn codegen path in `cranelisp-backend` gated on
the env var, so small-repro debugging can read compiled IR by eye (per the
discipline in root `CLAUDE.md` §"Usability Findings and Defects" paragraph
"Keep reductions as small as possible — small tests aid debugging"). S60
candidate — small infrastructure task; target: one block-per-function dump
with instruction numbers and RC op sites visible. Remove this FIXME when the
env var is wired to actually dump IR. -->

`CRANELISP_CODEGEN_TRACE=1` is only wired for error paths (not full CLIF dumps) in `src/worker.rs` and `src/session_v4.rs` — it does NOT dump IR. `CRANELISP_RC_TRACE=1` was used instead. Invoked on the minimal repro:

```
CRANELISP_RC_TRACE=1 cranelisp  # with stdin "(import [html [test-page]])\n/run-tests html\n"
```

Exit code: **133 (SIGTRAP — `debug_assert!` fired, most likely `rc_underflow_check` in `crates/cranelisp-runtime/src/rc.rs:107`).** 71 lines of RC trace before the child dies.

Observed pattern in the trace tail (excerpt — the crash is in `row-helper`'s iterations):

```
[RC] alloc 0xb91c6d340 rc=1     ;; allocation freshly made
[RC]   dec 0xb91c6d320 rc=0
[RC]  free 0xb91c6d320 rc=0
[RC]   dec 0xb91c6d340 rc=1     ;; dec of a rc=2 value
[RC]  free 0xb91c6d340 rc=0     ;; another dec on the same pointer — now rc=0 + freed
[RC] alloc 0xb91c6d340 rc=1     ;; ALLOCATOR REUSES THE SAME SLOT
[RC]   dec 0xb91c6d140 rc=1
[RC]   dec 0xb91c6d300 rc=2     ;; dec lands on 0xb91c6d300 which is still live at rc=3 then 2
```

Observe that after a pointer is freed (`0xb91c6d340 rc=0`), the **same slot is reallocated** and given out to a subsequent operation. This is standard allocator reuse behavior. But some scope cleanup on the previous loop iteration may hold a cached pointer to that slot, and on iteration 2 emits a `dec` against the old pointer's value — now a DIFFERENT live allocation with a different rc count. That is exactly the pattern of the observed `dec ... rc=N` with N≥1 (not reaching 0) followed by further decs against the same slot.

`inc` is only traced from `string.rs` (string-sharing inc), not from heap ADT inc. So the "alloc vs dec" count from the trace is not directly meaningful; only the *sequence* is.

### Fix hypothesis (not applied)

**The tail-recursive `row-helper`'s TCO scope cleanup decrements a value that is ALSO being passed as a tail-call argument.**

In the crashing shape:
```
(defn row-helper [original solved col acc]
  (if (eq-i64 col 9) acc
    (row-helper original solved (add-i64 col 1)
      (str-concat acc (solution-cell original solved col)))))   ;; tail call
```

At the tail call site:
- `acc` goes out of scope (the outgoing argument `(str-concat acc ...)` *consumes* it).
- `original`, `solved` are re-passed as the same parameter slots.
- The new `acc'` is `(str-concat acc (solution-cell original solved col))` — a freshly-allocated string.

The hypothesis: when self-TCO jumps to the loop header, the scope-cleanup step for `row-helper`'s parameters (`original`, `solved`, `acc`) decrements `original` / `solved` — but the jump then re-assigns those same slots with the same values. If the cleanup `dec` fires BEFORE the re-assignment `inc`, the pointer might transiently hit rc=0 and get freed between frames, then reallocated and overwritten. If it fires AFTER, all is well.

The 2-grid-param signature (passing `original solved` unchanged on every iteration) is load-bearing — the 1-param version doesn't crash, probably because there's only one path to inc/dec, not two. The `match` projecting `(Grid cells)` + `vec-get` on EACH iteration against BOTH `original` and `solved` (which point to the same allocation under `g g` calls) means the same Grid allocation is repeatedly read in a way that races with the scope cleanup.

Compare with the non-crashing `d45_html_one_test_no_crash` which used 1-arg `solution-cell [g idx]` — only one `cell-at` per iteration, only one grid param re-passed. No crash.

### Recommended next steps for `/backend`

1. Inspect `crates/cranelisp-backend/src/compiler/control_flow.rs` (search for `emit_scope_cleanup_for_tco` / self-recursive jump emission). Verify that when a tail-call argument is IDENTICAL to an incoming parameter (i.e., "pass through"), the dec+inc is elided or safely ordered.
2. Specifically: what happens at the tail call when the SAME value is used as BOTH `original` and `solved` argument slots? If the scope cleanup emits a `dec` per parameter slot (2 decs for `original` and `solved`), but the value is the same underlying allocation (rc only inc'd by 2 on entry), a net-zero dec-inc-dec-inc could transiently drive rc=0 and free it.
3. Add a narrower unit test inside `cranelisp-backend`: tail-recursive fn `(defn f [x y acc i] (if (= i N) acc (f x y (consume x y acc) (+ i 1))))` where the first two params are passed-through on every iteration and also read on every iteration. If this crashes, the reduction is crate-local and fixable without the cross-module dependency.

### Budget

| Run | Test(s) | Result |
|---|---|---|
| 1 | `d45_real_exemplar_html_run_tests_no_crash` | FAIL (baseline confirmed) |
| 2 | `d45_cross_module*` (3 tests) | all PASS |
| 3 | `d45_cross_module_html_like_batch` | PASS |
| 4 | `d45_cross_module_html_full_10_tests` | PASS |
| 5 | `d45_real_html_with_trimmed_grid` | FAIL |
| 6 | `d45_html_no_css` | FAIL |
| 7 | `d45_html_solution_tests_only` | FAIL |
| 8 | `d45_html_one_test` | PASS |
| 9 | `d45_html_two_tests` | PASS |
| 10 | `d45_html_three_tests_mixed` | PASS |
| 11 | `d45_html_two_arg_solution` | FAIL |
| 12 | `d45_html_min_v1` | FAIL |
| 13 | `d45_html_min_v2` | PASS |
| 14 | `d45_html_min_v1` with `CRANELISP_RC_TRACE` (via direct subprocess, not nextest) | FAIL + trace captured |

**14 of 15 runs used.** LLDB not attempted.

---

## Defect 6 — exemplar solver SIGSEGV on puzzles

### Failing reductions committed

Three reductions of increasing narrowness, all failing:

| Test | What it calls | What this pins |
|---|---|---|
| `d6_exemplar_solve_minimal_puzzle_no_io_does_not_segv` | `(solve g)` on real puzzle, no IO trampoline. | Defect is not in the IO trampoline path. |
| `d6_exemplar_solve_all_dots_does_not_segv` | `(solve g)` on maximally-empty puzzle. | Defect is not dependent on the specific Sprint 19 puzzle string. |
| `d6_exemplar_propagate_only_does_not_segv` | `(propagate g)` once — no backtracking, no `try-digits`, no `solve` recursion. | Defect is NOT in `solve`'s backtracking. It's already present in one call to `propagate`. |

### Passing reductions (ruled-out negative controls)

| Test | Shape | Passing tells us |
|---|---|---|
| `d6_vec_cow_int_loop_does_not_segv` | 400 `vec-set` updates on an 81-element `(Vec Int)`. | Plain Vec COW with Int elements is NOT the defect. |
| `d6_vec_cow_adt_loop_does_not_segv` | Same but elements are `Cell` (3-variant ADT). | Vec COW of ADT elements is NOT the defect. |
| `d6_grid_wrapper_cow_does_not_segv` | Wraps Vec in `Grid` ADT; `set-cell` unwraps/wraps. | `Grid` wrapper + `match` is NOT the defect. |
| `d6_solve_recursive_adt_does_not_segv` | Recursive `solve`-shaped fn with 30 levels of match on `SolveResult`. | Deep recursive match-over-SolveResult is NOT the defect. |
| `d6_exemplar_make_grid_only_does_not_segv` | Just `(make-grid "...")`, no propagate. | Grid construction from puzzle string is NOT the defect. |
| `d6_exemplar_eliminate_from_peers_does_not_segv` | One `(eliminate-from-peers g 2 3)` call. | One eliminate-from-peers call is NOT the defect. |
| `d6_exemplar_propagate_single_pass_does_not_segv` | One `(propagate-pass-helper g 0)` call — NO fixpoint loop. | A single full-grid pass is NOT the defect. |

### Diagnosis — narrowed

The defect is NOT in any of:
- IO trampoline / `bind` / `Pure`
- The specific puzzle string (all-dots crashes too; Sprint 19 puzzle crashes too)
- `solve`'s backtracking recursion or `try-digits`
- `make-grid` / `Grid` construction
- A single `eliminate-from-peers` call
- A single `propagate-pass-helper` call (one full-grid scan with peer elimination)
- Vec COW on ADT values (40 operations) or Grid ADT COW (40 operations)

The defect **IS** in the interaction between:
- `propagate` (defined in `exemplar/solver.cl:113-121`) which recursively calls itself after one pass,
- `grids-differ-helper` which walks both grids in lock-step to decide whether to recurse, and
- the fact that propagate calls itself `N` times until fixpoint — N is 1-5 in practice but each call allocates a new `Grid (Vec Cell)`.

### Suspect code — propagate body

```lisp
(defn propagate [g]
  (match (propagate-pass-helper g 0)
    [None None
     (Some g2)
       (if (grids-differ-helper g g2 0)
         (propagate g2)              ;; <-- recursive call, g2 is new Grid
         (Some g2))]))               ;; <-- fixpoint return
```

### Likely root cause (hypothesis — not applied)

**Self-TCO + `match`-bound fresh ADT value.** `propagate` is self-recursive in tail position. The reimplementation's loop-based self-TCO (per `MEMORY.md` §"Tail Call Optimization") rebinds the loop header's parameter to `g2`. The crash hypothesis:

- `g2` is bound from a `match` arm (`(Some g2)`). Inside that arm, the RC-transfer semantics for a match-extracted ADT field are subtle — the outer `Some` wrapper gets decref'd but `g2` is a projected field that was just incref'd to escape the arm.
- When TCO jumps to the loop header, the old `g` parameter should be decref'd and `g2` should take its slot. If the "emit scope cleanup for TCO" does NOT correctly handle the case where the new argument (`g2`) was **itself** projected out of a value bound in the scope being cleaned, the decref runs on `g2`'s backing allocation before the loop-header-slot assignment takes ownership.
- On iteration 2, the Vec of Cells inside g2 (now the loop-header `g`) has a corrupted RC or is outright dangling. The `vec-get`/`match` at the top of the next `propagate-pass-helper` reads a free'd allocation → SIGSEGV.

This matches the RC-trace imbalance `/backend` originally recorded (20875 allocs vs 18396 frees, delta +2479): many intermediate Grids allocated, fewer freed, because the TCO cleanup dropped ownership of the new parameter's backing allocation but the allocator still sees it as live — until a subsequent allocator access hits the corrupted header and segfaults.

### Next step for resolution (not performed in this phase)

Resolver should:
1. Inspect `src/codegen/` for the self-TCO path's scope cleanup (search for `emit_scope_cleanup_for_tco` / loop header block param rebind).
2. Verify what happens when the new-argument-value is a `match`-projected field of an old-argument-value still in scope. The old value is about to be decref'd (scope cleanup) — does that decref correctly preserve the still-live projected child?
3. A sharper narrow test: a synthetic `(defn f [g] (if (pred g) (f (extract-g2 g)) g))` shape where `extract-g2` returns a cell of `g`. If that crashes, TCO + projected-arg is confirmed.

Note: my synthetic `d6_solve_recursive_adt_does_not_segv` did NOT reproduce the crash, but its recursion argument was `(set-cell g ...)` — a freshly-allocated Grid, not a child extracted from `g` by `match`. That's the missing axis. A future reduction should put `propagate`'s shape (recursive call with `match`-extracted argument and a binary decision to recurse) into a synthetic module without `grid.cl`/`solver.cl` dependency. If it crashes, the reduction is crate-local.

### CLIF-level observation

Not captured in this session — the `--run` path finalizes and invokes the JIT'd `main` before CLIF is easily dumped interactively. Recommend `/backend` re-run with `CRANELISP_CODEGEN_TRACE=1` and grep the emitted CLIF for `propagate`'s function body — specifically look for:
- Block param count at the loop-header block (should be 1 for `g`)
- Jump to loop-header — what value is passed? If it's a value previously consumed by scope cleanup, the issue is visible in CLIF.
- Presence/absence of `call runtime/dec` for the old `g` before the jump.

---

## FIXMEs filed in test file

Each reduction test carries an inline `FIXME(/backend)` comment stating what the reduction rules in and rules out. These FIXMEs are resolved when `/backend` applies a fix that makes the failing tests pass.

No documentation-only FIXMEs were filed on spec/design files — the failing tests ARE the record per the principle codified in root `CLAUDE.md` §"Usability Findings and Defects".

---

## Summary

| Defect | Before this work | After this work |
|---|---|---|
| 4+5 | One large test importing html.cl and running `/run-tests html` | **8 ruled-out reductions** + 1 minimal-real-module failure; single `(run-test)` proven benign; defect localised to "batched dispatch of real html.cl tests" — requires html's cross-module context. |
| 6 | One large test `--run exemplar/solver.cl` (stack-overflow hypothesis) | **7 ruled-out reductions** + 3 failing reductions; solve→propagate→propagate-pass-helper ruled in; IO, backtracking, single-pass, make-grid, eliminate-from-peers ruled out. Defect localised to `propagate`'s tail-recursive call. |

**No fix applied in this phase** (per the task boundary). The reductions are the deliverable.

---

## Resolution — Sprint 60 continuation (/backend, Pass 2)

**Status**: **Partial — one real double-inc bug fixed in `protect_return_value`; bare-REPL reproduction of `(solution-cell g g 0)` now passes deterministically, but the import-time reproduction (html/grid cross-module) still crashes intermittently (~75% rate) with raw SIGTRAP (exit 133) and no stderr output. The crash is machine-level (Cranelift-emitted trap, not a Rust `debug_assert!`). Further work needed — see §"Still to resolve" below.**

### New minimal reproductions found (Pass 2)

- `d45_solution_cell_single_call_no_rc_underflow` (in `tests/sprint59_defects456_repro.rs`). The repro is:
  ```
  (import [html [make-grid solution-cell]])
  (let [g (make-grid)] (solution-cell g g 0))
  (let [g (make-grid)] (solution-cell g g 0))
  ```
  Second invocation reliably SIGTRAPs. Tighter still: **single** `(solution-cell g g 0)` with imports crashes intermittently (~75%). The import path is load-bearing — the identical definitions typed directly at the REPL execute cleanly 5/5 runs.
- A bare-REPL equivalent that types the grid/html definitions directly (no `import`) does **not** crash, confirming the bug is in how cross-module constrained-polymorphic dispatch is assembled.

### Pass-2 CLIF evidence

CLIF for `solution-cell` (entered at REPL so `/clif` works) captured twice — pre-fix and post-fix. `cell-at` is called through an auto-curry-shaped closure trampoline even though 2 args are supplied for 2 params (`fn3(env) -> v13; fn4(v13); call fn10(v13)`). This is the constrained-polymorphic dispatch path laid on top of a partial-application wrapper, and it is what makes the bug specific to imported polymorphic functions.

In `cell-at`'s own CLIF, **two guarded `rc_inc`s** fire on the same value `v22` (the vec-get element): one from `vec_codegen.rs:201` (`emit_guarded_rc_inc`) and one from `protect_return_value` in `compiler/mod.rs:1109`. Match-arm scope contains only the borrowed `cells` binding; `protect_return_value` was inc'ing anyway because its "has heap bindings" check did not exclude borrowed/consumed vars.

### Mechanism fixed

`protect_return_value` used to emit `rc_inc` on the return value whenever the current scope frame contained *any* heap-typed binding — including borrowed pattern-extracted fields (`cells` in `(Grid cells)`) and consumed vars (arguments already transferred to a callee). But `pop_scope_with_cleanup` skips exactly those two classes, so the protective `rc_inc` could not actually balance any future dec — it was a pure leak for return values where the only heap binding in scope was a borrow.

The fix scopes the "has heap bindings" check to exclude `borrowed_vars` and `consumed_vars`, matching the `pop_scope_with_cleanup` discipline.

### Files changed

- `crates/cranelisp-backend/src/compiler/mod.rs` — `protect_return_value` now checks only non-borrowed/non-consumed heap bindings when deciding whether to emit the protective `rc_inc`.

### Prior agent's TCO "fix" status

**Not present in the working tree** — already reverted (or never committed). `git grep emit_scope_cleanup_for_tco` returns only the plan doc. No revert action needed.

### Test outcomes after Pass-2 fix

| Test | Status |
|---|---|
| `cargo check -p cranelisp-backend` | Clean — no new warnings. |
| `cargo nextest run -p cranelisp-backend` | 161/161 pass (including `test_mono_defn_self_recursive_tco`). |
| bare-REPL `(let [g (make-grid)] (solution-cell g g 0))` × 5 runs | 5/5 PASS (pre-fix: intermittent). |
| Imported `(solution-cell g g 0)` × 20 runs | 15/20 SIGTRAP (pre-fix: similar). Fix did not repair this path. |
| `d45_html_min_v1_no_crash` | Still FAIL. |
| `d45_solution_cell_single_call_no_rc_underflow` | Still FAIL. |
| `d6_exemplar_propagate_only_does_not_segv` | Still FAIL. |
| `exemplar_solver_does_not_stack_overflow_on_small_puzzle` | Still FAIL. |
| `run_tests_batched_invocation_no_crash` | Still FAIL. |
| Regression sentinels (`persist_import_survives_restart`, `v4_cache_hit_dependency`, `cache_repl_loads_on_startup`, `display_defn_with_docstring_uses_dash_separator`) | 4/4 PASS. |

### Still to resolve — architectural shape

**The core finding is the invariant violation itself, independent of which hypothesis below is correct.** The Pass-2 fix flipped REPL-entered defns green 5/5 but left module-imported defns failing ~75% — **same source, different code**. That is an architectural red flag: JIT finalization and `.o`-emission + link-loading should produce **byte-identical code**, differing only in the fixup mechanism (JIT direct-finalize-then-invoke vs relocation-then-link-load). If they differ, the codegen paths have diverged; that is a correctness bug in its own right, independent of any specific RC/closure/page-reclaim symptom. S61 should begin by auditing this invariant (same source → same code bytes) before root-causing any specific symptom.

The crash is intermittent, leaves no stderr (no Rust panic backtrace), and reproduces only for imported polymorphic functions. Three architectural hypotheses (ALL of which may trace back to the same root — divergent codegen between paths):

1. **Monomorphised defn codegen context divergence**: When `cell-at` is imported, it is monomorphised to `cell-at$grid.Cell` (or similar mangled name) in a second codegen pass. If that pass reads `variable_types` / `borrowed_vars` / `consumed_vars` through a partially-populated or stale state (e.g., the AST's `inferred_type` annotations are not fully propagated across module boundaries when mono'd), the same fix above would not apply. The REPL-typed version works because the defn is compiled in a single pass with full state.

2. **Auto-curry closure over polymorphic dispatch**: The CLIF shows `cell-at` being called via a 2-capture auto-curry closure that wraps a second trampoline call (`fn4(fn3(env))`). When both args match the full param count, AutoCurry should not fire — unless the polymorphic `a` return requires a curry level to stall monomorphisation until return context is known. If that's the shape, the closure env's inc+drop pattern has to balance with the caller's consuming convention — and it may not be, specifically when the closure is freed before the return value's RC stabilises.

3. **Cross-module GOT indirection with a racy drop-glue pointer**: GOT slot for `cell-at$grid.Cell` is filled when the mono'd defn is jitted; if the imported wrapper's drop glue (stored at `v7+24`) is a pointer into a code page that gets re-mapped/reclaimed between REPL evals, calling it dereferences freed executable memory → raw trap. The intermittency matches this profile. 

The raw-trap-no-stderr signature strongly implicates (3): Rust `debug_assert!` always flushes stderr before abort; a JIT-emitted trap does not.

### Recommendation for S61

- Before further RC-ABI work, dump CLIF for the imported `cell-at$grid.Cell` and its drop-glue wrapper. The FIXME at the top of §Phase 2 — wire `CRANELISP_CODEGEN_TRACE=1` to dump full post-codegen CLIF — is load-bearing. Without it the investigation is guesses.
- Check whether the closure env's drop-glue `func_addr` survives cross-eval JIT page reclamation (Decision 31 territory). If not, that's the architectural fix: drop-glue addresses MUST be stable across evals, or the closure env must hold an indirection through a stable symbol table.
- Keep the Pass-2 fix. It eliminates a real double-inc (confirmed in cell-at's CLIF) and is a strict improvement.

### Budget used (Pass 2)

- `cargo nextest run`: 5 (well under the 15 cap).
- `cargo check`/build: 2.
- Active time: ~2 hr.

### Mechanism addressed

The reimplementation's `compile_tail_self_call` in `crates/cranelisp-backend/src/compiler/apply.rs:492` had no scope cleanup. A self-TCO jump directly reassigned the loop-header block params to the new argument values without dec'ing any of the heap-typed bindings that were about to be overwritten. This matches the sketch's documented need for `emit_scope_cleanup_for_tco` (see `sketch/src/codegen.rs:660` and `sketch/src/codegen/apply.rs:363`). Every iteration leaked the outgoing binding refs, and for match-projected arguments the backing allocation was never inc'd to survive the scrutinee's eventual dec — exactly the failure modes Phase 2 hypothesised.

The applied fix:

1. **Auto-upgrade borrowed match-projected args** before scope cleanup (`apply.rs:503–522`). When the TCO argument is a borrowed var (pattern-bound to a field of an outer value), emit an RC inc on the raw field pointer so the projected child survives the outer's cleanup.
2. **Emit scope cleanup for TCO** (`crates/cranelisp-backend/src/compiler/mod.rs:879–959`). Walk every active scope frame inner-most first; for each heap-typed binding (skipping consumed and borrowed vars, matching the discipline of `pop_scope_with_cleanup`), emit a runtime `icmp`-chain guard against the new-arg Values and dec only when no match. Pass-through aliasing (same SSA value in multiple arg slots, or the same runtime pointer from `(page g g)`-style calls where Cranelift SSA splits but the runtime pointer is equal) is handled because the guard uses runtime `IntCC::Equal`, not compile-time SSA identity.

### Files changed

- `crates/cranelisp-backend/src/compiler/apply.rs` — extended `compile_tail_self_call` with auto-upgrade and scope-cleanup calls.
- `crates/cranelisp-backend/src/compiler/mod.rs` — added `emit_scope_cleanup_for_tco` method on `FnCompiler`.
- `crates/cranelisp-backend/src/lib.rs` — added two unit tests (`emit_scope_cleanup_for_tco_preserves_passthrough_alias_rc`, `emit_scope_cleanup_for_tco_preserves_match_projected_arg_rc`).

### Test outcomes

| Verification step | Status |
|---|---|
| `cargo check -p cranelisp-backend` | PASS — compiles cleanly with no new warnings. |
| `cargo nextest run d45_html_min_v1_no_crash` | **FAIL — still crashes with SIGSEGV.** |
| `cargo nextest run d6_exemplar_propagate_only_does_not_segv` | **FAIL — still crashes.** |
| `cargo nextest run -p cranelisp-backend` | PASS (163/163 including the 2 new unit tests). |
| `cargo nextest run persist_import_survives_restart v4_cache_hit_dependency cache_repl_loads_on_startup` | PASS (3/3 regression spot-check). |

### Why the minimal repros still crash

The fix as written addresses the hypothesis described in Phase 2 (pass-through aliasing RC imbalance, match-projected arg dangling). Unit tests confirm the codegen emits valid CLIF for both shapes. Existing pre-fix PASSING reductions (the 22 prior-agent PASS cases + basic `test_mono_defn_self_recursive_tco`) remain green.

Yet `d45_html_min_v1_no_crash` and `d6_exemplar_propagate_only_does_not_segv` still SIGSEGV. That means one of:

1. **Additional root cause beyond the documented hypothesis.** The Phase 2 RC trace observation (same pointer reallocated after free, then dec'd against a still-live allocation) described a *symptom*; the underlying RC ledger corruption may originate earlier than the TCO edge — possibly in how `compile_consuming_arg_list` handles Var args to user fns whose return value aliases a param (`cell-at g idx` returns a projected field of `g` while `g` itself is about to be dec'd by the callee's scope cleanup).
2. **An interaction my guard chain doesn't cover.** The runtime `icmp` against `arg_vals[i]` succeeds only when the binding's Value at the TCO edge is *identical* to a new-arg Value. If the binding's Value has been modified mid-body (e.g., `vec-push-cow` rewrites a Var's binding), the icmp comparison against a now-stale pointer would miss the pass-through. I did not inspect every `def_var`-on-existing-Variable site for this.
3. **ADT drop glue emitting a field dec against a cell whose backing is shared.** `emit_rc_dec_with_inline_drop_glue` for `Grid (Vec Cell)` at rc=0 would iterate the Vec and dec each Cell. If those Cells are also referenced by `orig-cell`/`solved-cell` let bindings in `solution-cell` (via `vec-get`'s inc), the drop order matters — a TCO dec of the Grid might free it and its inner Cells before the let's scope cleanup dec's its own Cell refs.

None of (1)–(3) is disproved by the existing evidence. Each needs CLIF inspection + targeted smaller repro.

### Recommendation

- Carry forward to S60 as a dedicated defect-fix workstream with a firm budget for CLIF dump infrastructure first (the `FIXME(/backend)` at the top of §Phase 2). Without human-readable IR, further reduction is guess-and-check.
- The applied fix is safe to keep — it matches the sketch's proven pattern, passes all existing tests and both new unit tests, and is a necessary (if insufficient) part of correct TCO RC handling. Rolling it back would restore the iteration-wise leak for any TCO loop over heap params.
- Do NOT remove the CLIF-dump FIXME at the top of §Phase 2 — it remains the S60 infrastructure dependency.

### Budget used

| Resource | Usage |
|---|---|
| `cargo nextest run` | 12/12 (at cap) |
| Active time | ~2.5 hours |
| Unit tests added | 2 (both passing) |
| Regressions introduced | 0 |

---

## Sprint 60 A.2 audit findings (Wave 2 — /backend, CLIF evidence)

**Status**: H3 **PARTIALLY CONFIRMED** — the `func_addr`-bake-into-data pattern is pervasive and matches the /arch Phase-3a answer exactly, but the specific cross-module retention race is **not uniquely responsible** for the d6 repro; a second structural breach compounds it. Audit was diagnostic (Step A.2); no fix applied.

### Repro chosen and observed behaviour

`tests/sprint59_defects456_repro::d6_exemplar_propagate_only_does_not_segv` — one call to `(propagate g)` on the real grid/solver, no backtracking. Runs via the `--run` path, not the REPL.

- **Observed**: `cargo nextest run -E 'test(d6_exemplar_propagate_only_does_not_segv)'` → EXIT 100 (test failure, process killed by signal). Consistent with prior observations of raw SIGSEGV/SIGTRAP; no Rust panic backtrace reaches stderr.
- **CLIF captured**: `CRANELISP_CODEGEN_DUMP=*` produced 95,027 lines of CLIF spanning 320 function emissions (every builtin trait impl, every stdlib fn, plus `grid::*`, `solver::*`, and the generated `d6_propagate_only::main`). Written to `/tmp/s60_a2_clif.log`.

### CLIF evidence — drop-glue-value pattern (two distinct sites)

**Site 1 — Vec element-dec function address baked into a parameter**, `grid::set-cell` (lines 73213-73252 of dump):

```
        fn0 = colocated u0:103 sig0   ; (i64) -> i64  — runtime/vec_elem_dec_Cell (synthetic, Linkage::Local)
        fn2 = u0:25 sig2              ; (i64,i64,i64,i64) -> i64  — Vec COW helper
        ...
        v11 = func_addr.i64 fn0       ; BAKE address of local drop-dispatch fn as i64
        ...
        v29 = call fn2(v10, v4, v5, v11)   ; pass baked address as 4th arg
```

The `runtime/vec_elem_dec_{suffix}{type_suffix}` (`vec_codegen.rs:691`) and the ADT drop-glue `runtime/drop_glue_{fqtn}` (`vec_codegen.rs:817`) are **both declared `Linkage::Local`** (lines 711, 831). The `func_addr` instruction resolves at finalize to a **raw i64 pointer into the emitting batch's JIT pages**. That i64 flows into the Vec COW helper where it is dispatched via `call_indirect`. This is H3's exact signature for *non-closure* call sites: a `func_addr`-valued pointer into JIT pages, stored in a data word, later dispatched indirectly.

**Site 2 — inline ADT drop-glue called as Cranelift direct `call` against `Linkage::Local`**, `heap.rs:285-288`:

```rust
if let Some(glue_id) = drop_glue_id {
    let glue_ref = module.declare_func_in_func(glue_id, builder.func);
    builder.ins().call(glue_ref, &[ptr]);   // NOT call_indirect; NOT GOT-routed
}
```

CLIF from `solver::propagate` (lines 82871-82971) confirms user-defn cross-module calls DO route through the GOT explicitly:
```
        v6 = global_value.i64 gv0      ; gv0 = symbol userextname0 — imported module GOT
        v7 = iadd_imm v6, 24           ; slot 3
        v8 = load.i64 notrap aligned v7
        v9 = call_indirect sig0, v8(v1, v5)    ; GOT-indirect call to grid::propagate-pass-helper
```

But **the drop-glue call path at blocks 17-20 uses direct `call fn2(v57)` / `call fn5(v82)`** — Cranelift-resolved against a `UserExternalName`, which at JIT finalize is baked as either (a) an absolute address (external `Linkage::Local`) or (b) a relative branch if the target is co-emitted in the same batch. Either way, it is **not** indirected through the `__cranelisp_got_{M}` GOT mechanism.

### Multi-batch replication observation

Counting `func_addr` instances per batch in the single compile run: grid=18, solver=8, collections.vec=6, text.string=4, collections.list=3. `colocated u0:*` refs for `runtime/vec_elem_dec_Cell` and `runtime/drop_glue_Cell` appear in **both** `grid::*` functions (u0:101, u0:103) and `solver::*` functions (u0:95, u0:88) — **confirming each importing batch emits its own local copies** of per-type drop infrastructure when needed. The `get_name` dedup at `vec_codegen.rs:694-698` only dedupes within one `Module` (one batch); across batches each re-emits.

### H3 verdict — PARTIALLY CONFIRMED

- The **mechanism** named in H3 — `func_addr`-valued pointers into JIT pages, dispatched later via `call_indirect` or via baked direct `call` against `Linkage::Local` — is **present and pervasive**: closure `drop_glue_ptr` (`control_flow.rs:579`), Vec element-dec parameter baking (`grid::set-cell` et al.), inline ADT drop-glue dispatch (`heap.rs:287`).
- The **specific cross-module race** named in H3's prediction (module A's code holds a baked address into module B's reclaimed pages) is **architecturally possible** for the `func_addr`-valued Vec-COW helper parameter — if a closure constructed in module A captures a COW helper argument that embeds module B's `runtime/vec_elem_dec_Cell`, and module B's `Arc<Jit>` reclaims, the captured value dangles.
- But the d6 repro hits the crash on the **first** call to `(propagate g)` within a single `--run` invocation — *before* any REPL-redefinition or batch-reclaim has had the opportunity to fire. Decision 31 Scenario 2 (per-eval reclaim) does not apply on a single-shot `--run`. This refutes H3 as the **sole** explanation for this specific repro.
- The drop-glue dispatch from `heap.rs:287` uses direct `call glue_ref` NOT routed through the GOT. This **violates Decision 36's "Why all-GOT calling"** discipline, which §1.1 of the convergence invariant extends to "Drop-glue code pointers… must route through the GOT or through an Arc-rooted allocation that outlives every caller." The convergence invariant is **breached** regardless of whether the d6 crash traces to this specific line.

### What IS the root cause of the d6 single-run crash? (hypothesis from the evidence)

Not H3 directly. Most likely a correctness bug in the **inlined ADT drop-glue emission** for `Grid`'s `(Vec Cell)` field, interacting with the tail-recursive `propagate` loop. Evidence:

1. `d6_propagate_only::main` only does `(make-grid "..." → Some g → (propagate g) → ...)` ONE time. Crash reproduces. No redefinition, no reclaim.
2. `grid::cell-at` (line 73080 of dump) and `grid::set-cell` (73174) — the two functions called repeatedly inside propagate's fixpoint loop — both emit drop-glue via `runtime/drop_glue_Cell` (declared as `Linkage::Local`, called as direct CLIF `call`). The per-iteration RC dec on the old Grid chains into the Vec<Cell> drop, which chains into per-Cell drop-glue (`Given`/`Solved`/`Candidates`). An off-by-one or double-dec in that chain crashes on first fully-populated grid.
3. The S59 Pass-2 RC trace "alloc 0xb91c6d340 rc=1 / free 0xb91c6d320 / dec 0xb91c6d340 rc=1 / free 0xb91c6d340 / alloc 0xb91c6d340 rc=1 / dec 0xb91c6d140 / dec 0xb91c6d300 rc=2" is allocator-slot reuse colliding with a stale pointer **held somewhere between the drop-glue dispatch and the per-field dec**. Consistent with: the drop-glue fn reads the Grid's field pointer BEFORE the scope that holds the Grid has released, but the per-field dec closure over that pointer runs AFTER the Grid has been freed and reallocated.

### A.3 fix direction

Two distinct fixes are now clearly scoped:

**(a) H3 structural fix — route drop-glue through GOT** (per §5.3 option (a), /arch Phase-3a answer):
- Emit `runtime/drop_glue_{fqtn}` and `runtime/vec_elem_dec_*` as `Linkage::Export` in their *originating* batch; emit `Linkage::Import` declarations in every batch that needs them; allocate a GOT slot for each; dispatch via `call_indirect` on the GOT-loaded pointer.
- Change closure `drop_glue_ptr` layout from raw `*const u8` to a `(owning_got_base: i64, slot_index: i32)` pair; the tear-down at `compiler/mod.rs:1256` computes the address at call time.
- Estimated LOC: **180-280** (slightly above the §9 estimate because it extends to Vec COW helpers, not just closures). Primary files: `crates/cranelisp-backend/src/heap.rs` (~30 LOC), `control_flow.rs` (~40 LOC), `vec_codegen.rs` (~80 LOC), `compiler/mod.rs` (~60 LOC), plus boundary updates for slot registration.
- **Fits within existing decisions**: Decision 23 (two-GOT model) + Decision 31 (safety invariant extended to function-pointer data) + Decision 36 (all-GOT calling generalised). No new Decision needed pre-implementation; a Decision 38 will capture the final closure-layout shape post-validation, as /arch noted at `jit-object-convergence.md:518`.

**(b) Drop-glue correctness fix — independent of H3, narrower**:
- Audit `emit_standalone_field_decs` and `build_adt_drop_glue_fn` (`vec_codegen.rs:756+`) for the Grid/(Vec Cell) path. Specifically: when a data constructor has a `(Vec T)` field where T is another ADT (Cell), the generated drop-glue must (i) dec the Vec, which triggers its own element-dec; (ii) the element-dec for a Cell-typed element must recursively dec-and-drop the Cell *including* handling the Mixed category (Cells can be nullary `Given`/`Solved`/`Candidates` data variants).
- Estimated LOC: **40-100** in vec_codegen.rs; exact shape depends on whether the bug is in the guard for Mixed-heap elements, in the inc/dec pairing for the Vec's length header, or in the per-variant dispatch in multi-ctor drop glue.
- **Risk area**: this fix may be load-bearing for the d6 repro even after the H3 fix lands. The H3 fix prevents *stale pointers to freed pages*; it does NOT prevent *double-dec on a valid allocation*. The Pass-2 RC trace pattern is the latter.

**A.3 recommendation**: Land (a) first (it is the invariant-restoring structural fix; the convergence invariant is non-negotiable). Then re-run the five A-cluster tests. If `d6_exemplar_propagate_only_does_not_segv` still crashes, apply (b). If H3 fix alone flips all five, (b) becomes S61's concern.

### Decision 31 carry-forward invariant cross-reference

Per `jit-object-convergence.md §4.3`, the carry-forward at `program.rs:2184-2232` protects the `code` field through typecheck-layer upsert, but does NOT protect against the wholesale replacement of `symbol_tables[M].got`'s `Arc<GotTable>` when `restore_cached_module` runs. The d6 repro hits **before** any such reclaim, so §4.3's fix is not load-bearing for THIS defect. But the §4.3 breach remains open and is its own carry-forward risk.

### FIXME(/arch) filed — NONE

The audit surfaced no questions only /arch can answer. The two /arch Phase-3a answers embedded in `jit-object-convergence.md` (SymbolTable.got is already `Arc<GotTable>`; closure layout change to GOT-base+slot-index pair is authorised) cover the structural design space. A.3 implementation can proceed on the authority of those answers. If implementation uncovers a boundary-type change not already covered, FIXME(/arch) will be filed at that point.

### Budget used (A.2)

| Resource | Usage |
|---|---|
| `cargo nextest run` | 1 (`d6_exemplar_propagate_only_does_not_segv` with `CRANELISP_CODEGEN_DUMP=*`) |
| CLIF capture size | 95,027 lines / 320 functions / ~2.3 MB |
| Active time | ~40 minutes |
| Design docs updated | 2 (`defects-456-reduction.md` — this section; `jit-object-convergence.md §5` — "Wave 2 A.2 audit result" subsection) |

---

## Sprint 60 Reduction Pass — cache-reuse crash isolated to 5 LOC (`/backend`, committed as `tests/sprint60_reduction.rs`)

**Status**: A.3b's uncommitted "cache-reuse crashes deterministically" finding is now
committed as a test file with **8 failing reductions + 3 passing negative controls**.
The minimal crashing shape is **5 lines of Cranelisp across two files** — no heap,
no ADT, no recursion, no `let`. The bug is an invariant-layer breach in the
cache-hit load path, NOT an RC or drop-glue mechanism.

### Test file added

`tests/sprint60_reduction.rs` — 11 tests total:

| Test | Outcome | LOC source | What it pins |
|---|---|---|---|
| `s60_cache_reuse_exemplar_shaped_no_crash` | FAIL (SIGSEGV) | ~14 | A.3b baseline: Cell ADT + Grid + tail-recursive `build-helper` |
| `s60_cache_reuse_no_cell_adt_no_crash` | FAIL | ~10 | Cell ADT NOT load-bearing |
| `s60_cache_reuse_no_wrapper_adt_no_crash` | FAIL | ~8 | Grid wrapper ADT NOT load-bearing |
| `s60_cache_reuse_non_recursive_helper_no_crash` | FAIL | ~6 | Self-recursion NOT load-bearing |
| `s60_cache_reuse_nullary_helper_no_crash` | FAIL | ~5 | Helper arity NOT load-bearing |
| `s60_cache_reuse_empty_vec_helper_no_crash` | FAIL | ~5 | `vec-push` NOT load-bearing |
| `s60_cache_reuse_int_helper_no_heap_no_crash` | FAIL | ~5 | **HEAP NOT load-bearing** (kills RC/drop-glue hypotheses) |
| `s60_cache_reuse_minimal_5_loc_no_crash` | FAIL | **5** | MINIMAL — no `let`, literal Int return |
| `s60_control_single_file_no_crash` | PASS | n/a | Cross-module IS load-bearing |
| `s60_control_no_intra_module_call_no_crash` | PASS | n/a | Intra-module call IS load-bearing |
| `s60_control_direct_helper_call_no_crash` | PASS | n/a | Import of a WRAPPER that calls a same-module helper IS the specific shape |

### Minimal crashing source (5 LOC)

```lisp
;; grid.cl
(import [primitives [*]])
(defn build-helper [] 42)
(defn make-grid [] (build-helper))

;; program.cl
(import [grid [make-grid]])
(defn main [] (make-grid))
```

- First `cranelisp --run program.cl` exits 42 (correct — main returns 42).
- Second `cranelisp --run program.cl` in the same tempdir — cache-hit — SIGSEGV (exit 139) **deterministically** (10/10 trials).

### CLIF evidence

Dumped with `CRANELISP_CODEGEN_DUMP='*'` on both runs:

**First run** (fresh build, exit 42): emits ~81,100 lines of CLIF including:
```
; grid::build-helper
block1:
    v0 = iconst.i64 42
    return v0

; grid::make-grid
    gv0 = symbol userextname0
    ...
    v0 = global_value.i64 gv0       ; __cranelisp_got_grid base
    v1 = iadd_imm v0, 0              ; slot 0 = build-helper
    v2 = load.i64 notrap aligned v1
    v3 = call_indirect sig0, v2()
    return v3

; program::main
    gv0 = symbol userextname0
    ...
    v0 = global_value.i64 gv0       ; __cranelisp_got_grid base
    v1 = iadd_imm v0, 8              ; slot 1 = make-grid
    v2 = load.i64 notrap aligned v1
    v3 = call_indirect sig0, v2()
    return v3
```

**Second run** (cache-hit, SIGSEGV): emits only **32 lines** — just `program::main`
(repeated twice, already a red flag — duplicate emission). All other modules
(grid, control, defs, prelude deps) are loaded from cache without CLIF.

### `nm` / `otool` evidence

```
grid.o symbols:
  000000000000002c S ___cranelisp_got_grid   ; Linkage::Export, 16 bytes (2 slots)
  0000000000000024 t _build-helper
  0000000000000000 t _make-grid

program.o symbols:
                   U ___cranelisp_got_grid   ; Linkage::Import (undefined)
  0000000000000024 S ___cranelisp_got_program
  0000000000000000 t _main
```

`grid.o`'s `__DATA,__const` section has 2 relocation entries patching the two
GOT slots to point at `_make-grid` and `_build-helper` respectively, consistent
with the fresh-build CLIF.

### Root cause hypothesis (post-reduction)

Neither H3 (drop-glue × reclaim) nor A.3b's closure-env leak — **there are no
closures, no drop glue, no heap values at all** in the minimal repro.

**New hypothesis**: the JIT/object convergence invariant is breached in a more
fundamental way. On cache-hit:

- `grid.o` is loaded by `cache::Linker::load_object`, which mmap's its `.text`
  and `.__DATA,__const` sections, resolves the data-section relocations so the
  embedded `__cranelisp_got_grid` data contains real addresses for `make-grid`
  and `build-helper`.
- `program.cl` is freshly JIT-compiled: `inline_jit_codegen_for_names` runs
  against `symbol_tables[grid].got.base_ptr()` (NOT the linker's mmap'd GOT),
  registering that pointer with `JITBuilder::symbol("__cranelisp_got_grid", ...)`.
- `load_cached_module_via_linker` populates `symbol_tables[grid].got.slot[0]`
  and `slot[1]` with the linker-loaded function addresses (line 3180 of
  `src/worker.rs`).
- BUT `grid::make-grid`'s loaded code — compiled as an object — resolves its
  own `__cranelisp_got_grid` reference through `ARM64_RELOC_GOT_LOAD_*` against
  the LINKER's `got_slots` indirection (`cache/linker.rs:312-319`) — **a
  different `__cranelisp_got_grid` instance from the one program sees**.
- Both GOT instances *should* have the same contents. If a single slot in
  EITHER instance is unpopulated or stale, a call through it lands on garbage.

**Candidate narrow hypothesis**: the `ensure_got_slot(&target_name, raw_target_addr)`
path (linker.rs:317) is keyed on `target_name` — one slot per unique symbol
name across all `.o` loads. When grid.o's own code references `__cranelisp_got_grid`,
the `raw_target_addr` is the address of grid.o's own 16-byte data section
(offset 0x2c). BUT the linker's `ensure_got_slot` returns an *indirection slot*
whose contents are `raw_target_addr`. If that indirection slot was allocated
before grid.o's data relocations were applied, the slot may point to grid.o's
still-unrelocated (zero-filled) data. First-call miss, crash.

Alternatively the issue could be inside grid.o's own `.text` for `make-grid`:
the `call_indirect` loads slot 0 from `__cranelisp_got_grid` (grid.o's own
data section). If the relocation to populate grid.o's data section WITH
`build-helper`'s address was not applied (or applied with the wrong target),
that slot remains zero and calling it segfaults at address 0.

The 5-LOC repro means this is now inspectable at the instruction level. The
next /backend wave should:

1. Add a probe in `load_cached_object` that dumps each `.o`'s data-section
   contents AFTER relocations are applied, verifying each GOT slot is non-zero.
2. Compare against `symbol_tables[M].got.slot[i]` for each `i`, asserting byte-
   equality.
3. If the linker-loaded GOT has non-zero slots but the `symbol_tables` GOT has
   zero (or vice-versa), THAT is the breach.

### "Is the fix obvious" — NOT YET

The minimal repro is small enough to step through with a debugger, but the
exact codegen-vs-linker divergence needs one of: (a) the dual-GOT assertion
test above, (b) lldb on the minimal repro (a single instruction trace through
`program::main`'s `call_indirect` would show whether the crash is at the
first load (reading slot 1 of program's GOT, returns `make-grid`'s address),
the call (reaching `make-grid`'s entry), or the nested load inside `make-grid`
(reading slot 0 via grid.o's data section). My best guess at the fix direction:
the `load_cached_module_via_linker` path populates `symbol_tables[M].got` but
NOT the linker's in-process GOT slab for the same `__cranelisp_got_{M}`
symbol, OR vice-versa. A two-line fix if found; a larger restructure if the
two GOTs need to be unified to a single `Arc<GotTable>` shared between
linker and `symbol_tables`.

### Files added/modified (S60 reduction pass)

- `tests/sprint60_reduction.rs` — NEW FILE, 11 tests per table above.
- `design/backend/defects-456-reduction.md` — this section.

### Budget used (S60 reduction pass)

| Resource | Usage |
|---|---|
| `cargo nextest run --test sprint60_reduction` | 2 runs (parallel discovery + serial confirm) |
| Subprocess trials outside nextest | ~50 short `--run` invocations for bisection |
| Active time | ~90 minutes |
| New tests committed | 11 (8 failing regression guards + 3 negative controls) |
| Design docs updated | 1 (this section) |
