//! Sprint 94 — FIXME 0424 dependent-binding spark substrate (par-map / par-reduce
//! floor). QA-first (Phase 5 Stage 1) e2e guards. Plan: `tests/plan/sprint-94.md`
//! §2; arch R5 (`design/arch/effect-concurrency.md` App-B step 3 + §14 trailing
//! note "pure-value spark widening").
//!
//! The stdlib `par-map`/`par-reduce`/`par-map-reduce` are ordinary `.cl` defs
//! (`/stdlib`, a separate wave) and are NOT testable in `tests/` (free-standing
//! rule — zero stdlib dependency, root `CLAUDE.md`). So these exercise the
//! SUBSTRATE via inline par-map / par-reduce-SHAPED programs defined with
//! primitives + special forms only. The floor the substrate must hold:
//!   - correctness: parallel-eligible results are IDENTICAL to sequential
//!     (never wrong);
//!   - timing: the parallel-eligible workload is NOT slower than the
//!     forced-sequential workload of equal total work (never slower).
//!
//! Lane: default `nt` (these are backend-side sparks, no concurrency feature).
//!
//! Posture: the correctness rows are floors that must HOLD as sparking matures
//! (apply-arg sparking already ships; the let-path dependent-binding spark is the
//! new substrate — `tests/plan/sprint-94.md` §2). The timing row is the floor
//! sentinel (generous margin; timing flakiness is banned as a disposition).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;
use std::path::{Path, PathBuf};
use std::process::Command;

/// A bounded-depth tree-recursive `fib` (CPU-bound, no deep tail recursion → no
/// stack-overflow risk) plus a `main` body. Primitives + special forms only; no
/// prelude, no stdlib (free-standing).
fn fib_program(main_body: &str) -> String {
    format!(
        "(import [primitives [Pure add-i64 sub-i64 lt-i64]])\n\
         (defn fib [n]\n\
           (if (lt-i64 n 2) n (add-i64 (fib (sub-i64 n 1)) (fib (sub-i64 n 2)))))\n\
         (defn main [] {main_body})\n"
    )
}

/// Wall-clock (ms) one `--run` of `fib_program(main_body)`, asserting it exits
/// with `expect_exit` first so a silent mis-run cannot masquerade as a timing
/// pass.
fn run_exit_ms(main_body: &str, expect_exit: i32) -> u128 {
    let out = Cranelisp::new()
        .run("user.cl")
        .user(&fib_program(main_body))
        .output();
    let code = out.status.code();
    assert_eq!(
        code,
        Some(expect_exit),
        "expected exit {expect_exit}\nstdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    out.elapsed.as_millis()
}

/// Best-of-N minimum elapsed-ms (filters CPU-contention noise under a saturated
/// `cargo nextest run`; the S86 best-of-N precedent for positive timing
/// witnesses — contention only ever makes a measurement SLOWER).
fn best_of_n_ms(n: usize, mut attempt: impl FnMut() -> u128) -> u128 {
    (0..n).map(|_| attempt()).min().expect("n >= 1")
}

// =============================================================================
// §2 (f) — par-map-shaped: results IDENTICAL to sequential (correctness floor).
// =============================================================================

// spec: design/arch/effect-concurrency.md §14 (pure-value spark widening) /
// App-B step 3 — an inline par-map-shaped program (a pure fn applied to each of
// several independent inputs, summed) produces results identical to a sequential
// map over the same input. The four `(fib 26)` applications are data-independent
// → apply-arg-spark eligible; correctness must not depend on whether they spark.
// 4 * fib(26) = 4 * 121393 = 485572; 485572 mod 256 = 196 (Unix exit byte).
#[test]
fn par_map_shaped_inline_results_identical_to_sequential() {
    let out = Cranelisp::new()
        .run("user.cl")
        .user(&fib_program(
            "(Pure (add-i64 (add-i64 (fib 26) (fib 26)) (add-i64 (fib 26) (fib 26))))",
        ))
        .output();
    // Parallel-eligible sum == the known sequential sum (never wrong).
    out.assert_exit(196);
}

// =============================================================================
// §2 (f) — par-reduce-shaped: dependent accumulator over the `let` path.
// =============================================================================

// spec: design/arch/effect-concurrency.md App-B step 3 + arch R5 — an inline
// par-reduce-shaped program: a dependent accumulator built on the `let` path
// (each binding depends on the previous, while its fresh `(fib 26)` sub-expr is
// independent → the dependent-binding IVar spark forced on demand). Pins the
// dependent-binding spark's correctness: the fold result equals the sequential
// fold. a = fib(26) = 121393; b = a + fib(26) = 242786; c = b + fib(26) =
// 364179; 364179 mod 256 = 147.
#[test]
fn par_reduce_shaped_inline_results_identical_to_sequential() {
    let out = Cranelisp::new()
        .run("user.cl")
        .user(&fib_program(
            "(let [a (fib 26)\n\
                   b (add-i64 a (fib 26))\n\
                   c (add-i64 b (fib 26))]\n\
               (Pure c))",
        ))
        .output();
    // Dependent-accumulator fold == the known sequential fold (never wrong).
    out.assert_exit(147);
}

// =============================================================================
// §2 (f) — par-map-shaped: NOT slower than sequential (the floor sentinel).
// =============================================================================

// spec: design/arch/effect-concurrency.md App-B step 3 + arch R5 — the floor:
// "never slower than sequential." Compares two `let` shapes of EQUAL total work
// (4 * fib(30)):
//   - PARALLEL: four data-INDEPENDENT `(fib 30)` bindings → spark-eligible.
//   - SEQUENTIAL: four bindings each textually DEPENDENT on the previous (via
//     `(add-i64 30 (sub-i64 x x))` == 30) → the dataflow forbids sparking, so
//     they run strictly in order.
// Both exit 4 * fib(30) = 4 * 832040 = 3328160; 3328160 mod 256 = 160. The
// parallel wall-clock must be ≤ the sequential wall-clock (generous ×2 margin,
// best-of-N min — the load-bearing guards are the correctness rows above; this
// is the floor sentinel only).
#[test]
fn par_map_shaped_inline_not_slower_than_sequential() {
    let parallel_body = "(let [a (fib 30) b (fib 30) c (fib 30) d (fib 30)]\n\
                          (Pure (add-i64 (add-i64 a b) (add-i64 c d))))";
    let sequential_body =
        "(let [a (fib 30)\n\
               b (fib (add-i64 30 (sub-i64 a a)))\n\
               c (fib (add-i64 30 (sub-i64 b b)))\n\
               d (fib (add-i64 30 (sub-i64 c c)))]\n\
           (Pure (add-i64 (add-i64 a b) (add-i64 c d))))";

    let parallel_ms = best_of_n_ms(5, || run_exit_ms(parallel_body, 160));
    let sequential_ms = best_of_n_ms(3, || run_exit_ms(sequential_body, 160));

    assert!(
        parallel_ms <= sequential_ms * 2,
        "parallel-eligible workload must NOT be slower than sequential (floor): \
         parallel(best-of-5)={parallel_ms}ms, sequential(best-of-3)={sequential_ms}ms"
    );
}

// =============================================================================
// Sprint 94 Wave 3 — design-§9-mandated DEPENDENT-binding spark guards (the
// FIXME 0424 limit #2 substrate). `/review` findings I1/I2/I3 + the limit-#2 WIN.
//
// limit #2 (`design/backend/lenient-eval.md` §2.6/§2.6.2/§4.5): a `let` binding
// whose RHS references an EARLIER *sparked* binding is itself sparked as an IVar,
// its dependency forced on demand (§2.6.3 capture-the-IVar-pointer, §4.5 prologue
// force). The stdlib `par-*` were rewritten to combine-in-body and no longer
// exercise limit #2 — it is now a GENERAL capability that ONLY these tests pin,
// so these are LOAD-BEARING regression guards. All GREEN on HEAD (the feature
// shipped Wave 1); they are guards, not RED repros.
//
// Free-standing per `tests/CLAUDE.md`: inline shapes, primitives + special forms
// only, ZERO stdlib dependency.
// =============================================================================

/// `--run` `fib_program(main_body)` with extra env vars; return the exit code.
/// (`run_exit_ms` above asserts a fixed exit + returns ms; this returns the code
/// so the three-regime arms can be compared for byte-identical results.)
fn run_exit_env(main_body: &str, envs: &[(&str, &str)]) -> Option<i32> {
    let mut b = Cranelisp::new().run("user.cl").user(&fib_program(main_body));
    for (k, v) in envs {
        b = b.env(k, v);
    }
    b.output().status.code()
}

/// Count `[RC] alloc` / `[RC]  free` events in a `CRANELISP_RC_TRACE=1` stderr.
/// IVar cells go through the same `alloc_with_rc` / `dealloc` path as every other
/// heap object (`cranelisp-intrinsics/src/{alloc.rs,ivar.rs}`), so a leaked IVar
/// cell — or a leaked ferried error String — shows as an alloc with no matching
/// free. The eprintln trace is process-global, so spark-WORKER-thread allocs and
/// frees are captured too. Mirrors `spec_12_runtime.rs::rc_alloc_free_counts`.
fn rc_alloc_free_counts(stderr: &str) -> (usize, usize) {
    let allocs = stderr
        .lines()
        .filter(|l| l.contains("[RC]") && l.contains(" alloc "))
        .count();
    let frees = stderr
        .lines()
        .filter(|l| l.contains("[RC]") && l.contains(" free "))
        .count();
    (allocs, frees)
}

// ----- shared dependent-spark programs (primitives + special forms only) ------

/// A tail-recursive `work` leaf (single self-call, TCO'd, never sparks — apply-arg
/// sparking is gated off the TCO self-call fast path, §2.5.3). Used where `fib`'s
/// internal apply-arg sparking would flood the RC trace; `work(n,0) = n`.
const DEP_WORK_DEF: &str = "(defn work [:Int n :Int acc]\n\
       (if (le-i64 n 0) acc (work (sub-i64 n 1) (add-i64 acc 1))))\n";

/// Clean dependent-spark `let`: `a`/`b` independent sparks; `c (add-i64 a (work …))`
/// references the SPARKED `a` AND has independent sub-work → a dependent spark
/// (limit #2). `a=b=5000`, `c=10000`, sum `20000`, `/5000 = 4`.
fn dep_clean_program() -> String {
    format!(
        "(import [primitives [div-i64 add-i64 sub-i64 le-i64 Int Pure]])\n\
         {DEP_WORK_DEF}\
         (defn compute []\n\
           (let [a (work 5000 0)\n\
                 b (work 5000 0)\n\
                 c (add-i64 a (work 5000 0))]\n\
             (add-i64 (add-i64 a b) c)))\n\
         (defn main [] (Pure (div-i64 (compute) 5000)))\n"
    )
}

/// A dependent-spark `let` whose sparked DEPENDENCY `a (div-i64 10 0)` panics; the
/// dependent binding `c (add-i64 a b)` references it. Wrapped in
/// `catch-runtime-error` → the `Err` arm fires (exit 0 = caught, not swallowed).
const DEP_PANIC_CAUGHT_PROGRAM: &str =
    "(import [primitives [catch-runtime-error div-i64 add-i64 sub-i64 le-i64 Int Result Ok Err Pure]])\n\
     (defn work [:Int n :Int acc] (if (le-i64 n 0) acc (work (sub-i64 n 1) (add-i64 acc 1))))\n\
     (defn compute []\n\
       (let [a (div-i64 10 0)\n\
             b (work 5000 0)\n\
             c (add-i64 a b)]\n\
         c))\n\
     (defn main []\n\
       (Pure (match (catch-runtime-error (fn [] (compute)))\n\
               [(Ok v)  1\n\
                (Err m) 0])))\n";

/// Same dependent shape, UNCAUGHT — the sparked dependency's div-by-zero must
/// surface (not be silently dropped) on the joining thread.
const DEP_PANIC_UNCAUGHT_PROGRAM: &str =
    "(import [primitives [div-i64 add-i64 sub-i64 le-i64 Int Pure]])\n\
     (defn work [:Int n :Int acc] (if (le-i64 n 0) acc (work (sub-i64 n 1) (add-i64 acc 1))))\n\
     (defn compute []\n\
       (let [a (div-i64 10 0)\n\
             b (work 5000 0)\n\
             c (add-i64 a b)]\n\
         c))\n\
     (defn main [] (Pure (compute)))\n";

// =============================================================================
// I1 — three-regime equivalence for the DEPENDENT shape (`/review` finding I1).
// =============================================================================

// spec: design/backend/lenient-eval.md §2.6 — a `let` with two INDEPENDENT
// expensive sparks (`a`, `b`) PLUS a binding `c (add-i64 a (fib 26))` that depends
// on the SPARKED `a` (and has independent sub-work) → a dependent spark (limit #2).
// The result MUST be byte-identical across all three scheduling regimes:
//   - default lenient (dependent spark fires),
//   - CRANELISP_NO_LENIENT=1 (codegen-serial, no spark emitted),
//   - CRANELISP_SPARK_BUDGET=0 (create-gate forces every site onto the DIRECT arm
//     — the dependent-let's serial path, previously unexercised by any test).
// 4·fib(26) = 4·121393 = 485572; 485572 mod 256 = 196. Granted-vs-direct-vs-serial
// is a scheduling choice ONLY (§3.6 three-regime equivalence, dependent shape).
#[test]
fn dependent_spark_three_regime_result_equivalence() {
    let body = "(let [a (fib 26)\n\
                      b (fib 26)\n\
                      c (add-i64 a (fib 26))]\n\
                  (Pure (add-i64 (add-i64 a b) c)))";
    let lenient = run_exit_env(body, &[]);
    let no_lenient = run_exit_env(body, &[("CRANELISP_NO_LENIENT", "1")]);
    let budget_zero = run_exit_env(body, &[("CRANELISP_SPARK_BUDGET", "0")]);
    assert_eq!(
        lenient,
        Some(196),
        "default lenient: expected 4·fib(26)=485572 (exit 196); got {lenient:?}"
    );
    assert_eq!(
        no_lenient, lenient,
        "CRANELISP_NO_LENIENT=1 (codegen-serial) differs from default lenient on the \
         dependent shape — §2.6 observational equivalence violated ({no_lenient:?} vs {lenient:?})"
    );
    assert_eq!(
        budget_zero, lenient,
        "CRANELISP_SPARK_BUDGET=0 (create-gate direct/serial arm for the dependent let) \
         differs from default lenient — §3.6 degenerate-to-serial violated ({budget_zero:?} vs {lenient:?})"
    );
}

// =============================================================================
// I2 — dependent-panic ferry, first-error-wins (`/review` finding I2).
// =============================================================================

// spec: design/backend/lenient-eval.md §4.5.1 — a sparked DEPENDENCY (`a (div-i64
// 10 0)`) panics; the dependent binding `c (add-i64 a b)` references it. The panic
// is ferried (NOT swallowed) and surfaces at the source-order barrier — both
// Phase-2's force of `a` and the dependent thunk's force of `ivar_a` observe the
// ferried error. A `catch-runtime-error` enclosing the `let` catches it → the
// `Err` arm fires (exit 0 = caught). The existing apply/`let` ferry tests do NOT
// cover the dependent case. `--run`.
#[test]
fn dependent_spark_dependency_panic_ferried_caught_run() {
    Cranelisp::new()
        .file("user.cl", DEP_PANIC_CAUGHT_PROGRAM)
        .run("user.cl")
        .output()
        .assert_exit(0);
}

// spec: design/backend/lenient-eval.md §4.5.1 — same dependent-panic ferry under
// `--link` (ferry sound across modes); the `Err` arm fires → exit 0.
#[test]
fn dependent_spark_dependency_panic_ferried_caught_link() {
    Cranelisp::new()
        .file("user.cl", DEP_PANIC_CAUGHT_PROGRAM)
        .link_then_run("user.cl")
        .output()
        .assert_exit(0);
}

// spec: design/backend/lenient-eval.md §4.5.1 — NEGATIVE / first-error-wins: an
// UNCAUGHT panic in a sparked dependency MUST surface the DEPENDENCY's own error
// ("division by zero") — the source-order-first error — and MUST NOT be silently
// dropped (a swallowed spark panic would let the program complete with a sentinel
// value, the exact failure the ferry exists to prevent).
#[test]
fn dependent_spark_dependency_panic_not_swallowed_neg() {
    let out = Cranelisp::new()
        .file("user.cl", DEP_PANIC_UNCAUGHT_PROGRAM)
        .run("user.cl")
        .output();
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("division by zero"),
        "uncaught sparked-DEPENDENCY div-by-zero MUST surface 'division by zero' at the \
         source-order barrier (§4.5.1, not swallowed).\nstdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    assert_ne!(
        out.status.code(),
        Some(0),
        "an uncaught dependent-spark panic must NOT exit 0 (would mean the error was dropped)"
    );
}

// =============================================================================
// I3 — captured-IVar no-leak (`/review` finding I3): the gap a green suite hides.
// =============================================================================

// spec: design/backend/lenient-eval.md §4.5 — RC discipline for the captured IVar
// pointer. After a CLEAN dependent-spark workload, every heap allocation
// (IVar cells + thunk closures) is freed exactly once: `[RC] alloc` count ==
// `[RC] free` count. A leaked IVar cell (capture inc not balanced by drop-glue
// dec) would show alloc > free.
//
// MECHANISM + LIMIT: a pure cell LEAK has NO value/exit witness (the program
// computes the right answer and exits 0), so the ONLY observable is the
// alloc/free balance from CRANELISP_RC_TRACE=1 (the precedent the DEF-3 RC-balance
// tests set for allocation-imbalance cases). LIMIT: this is a WHOLE-PROGRAM
// balance — it proves no net leak anywhere, but cannot by itself attribute an
// imbalance to the IVar cell vs the thunk vs the error String. A double-free would
// instead ABORT the process (caught by the sustained-load test below).
#[test]
fn dependent_spark_rc_alloc_free_balanced() {
    let out = Cranelisp::new()
        .env("CRANELISP_RC_TRACE", "1")
        .file("user.cl", &dep_clean_program())
        .run("user.cl")
        .output();
    assert_eq!(
        out.status.code(),
        Some(4),
        "clean dependent-spark must exit 4 (20000/5000)\nstdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    let (allocs, frees) = rc_alloc_free_counts(&out.stderr);
    assert!(allocs > 0, "expected the RC trace to record allocations (IVar cells); got 0");
    assert_eq!(
        allocs, frees,
        "clean dependent-spark workload must be alloc/free balanced (no captured-IVar \
         leak, §4.5); got {allocs} allocs / {frees} frees.\nstderr:\n{}",
        out.stderr
    );
}

/// `--run` `prog` under `CRANELISP_RC_TRACE=1`, asserting `expect_exit`, and
/// return the heap-allocation imbalance (`allocs - frees`) — 0 means no net leak.
fn rc_leak(prog: &str, expect_exit: i32) -> i64 {
    let out = Cranelisp::new()
        .env("CRANELISP_RC_TRACE", "1")
        .file("user.cl", prog)
        .run("user.cl")
        .output();
    assert_eq!(
        out.status.code(),
        Some(expect_exit),
        "rc_leak: expected exit {expect_exit}\nstdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    let (allocs, frees) = rc_alloc_free_counts(&out.stderr);
    assert!(allocs > 0, "expected the RC trace to record allocations; got 0");
    allocs as i64 - frees as i64
}

/// A `let` that catches a panicking sparked DEPENDENCY `N` times in one process:
/// each iteration sparks `a (div-i64 10 0)` (panics) + `b (work …)` and a dependent
/// `c (add-i64 a b)` referencing the sparked `a`; the panic is caught (`Err` arm).
/// `acc` reaches `N`. Used to amplify any per-iteration captured-IVar leak.
fn dep_panic_loop_program(n: i64) -> String {
    format!(
        "(import [primitives [catch-runtime-error div-i64 add-i64 sub-i64 le-i64 Int Result Ok Err Pure]])\n\
         {DEP_WORK_DEF}\
         (defn step [:Int acc]\n\
           (match (catch-runtime-error (fn []\n\
                     (let [a (div-i64 10 0)\n\
                           b (work 2000 0)\n\
                           c (add-i64 a b)]\n\
                       c)))\n\
             [(Ok v)  acc\n\
              (Err m) (add-i64 acc 1)]))\n\
         (defn drive [:Int n :Int acc]\n\
           (if (le-i64 n 0) acc (drive (sub-i64 n 1) (step acc))))\n\
         (defn main [] (Pure (drive {n} 0)))\n"
    )
}

/// The NO-SPARK baseline: the SAME catch-in-a-loop shape, but the caught thunk is a
/// bare `(div-i64 10 0)` — no `let`, no sparkable bindings, no IVars. Its leak count
/// is the floor contributed by `catch-runtime-error` itself (a SEPARATE, pre-existing
/// per-caught-error heap-cell leak; see the dedicated repro in `spec_12_runtime.rs`).
fn catch_loop_baseline_program(n: i64) -> String {
    format!(
        "(import [primitives [catch-runtime-error div-i64 add-i64 sub-i64 le-i64 Int Result Ok Err Pure]])\n\
         (defn step [:Int acc]\n\
           (match (catch-runtime-error (fn [] (div-i64 10 0)))\n\
             [(Ok v)  acc\n\
              (Err m) (add-i64 acc 1)]))\n\
         (defn drive [:Int n :Int acc]\n\
           (if (le-i64 n 0) acc (drive (sub-i64 n 1) (step acc))))\n\
         (defn main [] (Pure (drive {n} 0)))\n"
    )
}

// spec: design/backend/lenient-eval.md §4.5 — the harder no-leak case: a dependent
// spark whose DEPENDENCY thunk PANICS (and is caught), driven N times. The captured
// IVar pointer's capture-inc MUST be balanced by the thunk's drop-glue dec, and the
// dependency cell + ferried error String freed exactly once, EVEN on the unwind
// path — so limit #2 must add ZERO net leak beyond what `catch-runtime-error`
// itself leaks.
//
// RELATIVE assertion (not absolute alloc==free): the panic path is contaminated by
// a SEPARATE, pre-existing per-caught-error heap-cell leak in `catch-runtime-error`
// (reproduced independently — see `spec_12_runtime.rs::
// catch_runtime_error_caught_leaks_one_heap_cell_per_catch_neg`; it fires even with
// NO sparking). To isolate limit #2's contribution we compare the dependent-spark
// loop's leak against the NO-SPARK catch-loop baseline at the same N: equal ⇒ the
// dependent spark (incl. its panicking dependency) adds no captured-IVar leak. A
// captured-IVar leak would push the dependent count strictly above the baseline.
//
// LIMIT: this is a whole-program balance differenced against a baseline; it proves
// limit #2 adds no NET extra leak but cannot localise to a specific cell. The
// absolute non-panic discipline is pinned by `dependent_spark_rc_alloc_free_balanced`
// (clean path balances exactly); double-free by `dependent_spark_panic_sustained_no_abort`.
#[test]
fn dependent_spark_panic_adds_no_leak_over_catch_baseline() {
    const N: i64 = 20;
    let dependent = rc_leak(&dep_panic_loop_program(N), N as i32);
    let baseline = rc_leak(&catch_loop_baseline_program(N), N as i32);
    assert!(
        dependent <= baseline,
        "limit-#2 dependent spark with a caught panicking dependency must add NO leak \
         beyond the catch-runtime-error baseline (§4.5 captured-IVar RC discipline): \
         dependent-spark leak={dependent}, no-spark catch baseline={baseline} (both over \
         N={N} catches). dependent > baseline ⇒ a leaked captured IVar cell on the panic path."
    );
}

// spec: design/backend/lenient-eval.md §4.5 — sustained-load guard: drive the
// caught-panicking dependent-spark path 200× IN ONE PROCESS (the sustained-load
// convention floor, tests/CLAUDE.md). A DOUBLE-FREE of an IVar cell or ferried String would abort
// the process (nonzero exit / crash); a permit/cell accumulation that grows
// without bound would eventually OOM. The accumulator (`acc` reaches 200) confirms
// EVERY iteration caught the dependency panic correctly under repetition.
//
// LIMIT: this catches double-free (abort) and gross/unbounded leaks (OOM) and
// per-iteration correctness, but NOT a small bounded per-iteration cell leak —
// 200 leaked small cells neither abort nor OOM, and IN_FLIGHT_SPARKS is a runtime
// static not observable from an e2e subprocess. The bounded-cell-leak gap is
// covered by `dependent_spark_panic_adds_no_leak_over_catch_baseline` above (the
// relative RC balance) and by the `cranelisp-intrinsics` `IN_FLIGHT_SPARKS`-
// returns-to-0 unit tests.
#[test]
fn dependent_spark_panic_sustained_no_abort() {
    let src = "(import [primitives [catch-runtime-error div-i64 add-i64 sub-i64 le-i64 Int Result Ok Err Pure]])\n\
               (defn work [:Int n :Int acc] (if (le-i64 n 0) acc (work (sub-i64 n 1) (add-i64 acc 1))))\n\
               (defn step [:Int acc]\n\
                 (match (catch-runtime-error (fn []\n\
                           (let [a (div-i64 10 0)\n\
                                 b (work 2000 0)\n\
                                 c (add-i64 a b)]\n\
                             c)))\n\
                   [(Ok v)  acc\n\
                    (Err m) (add-i64 acc 1)]))\n\
               (defn drive [:Int n :Int acc]\n\
                 (if (le-i64 n 0) acc (drive (sub-i64 n 1) (step acc))))\n\
               (defn main [] (Pure (drive 200 0)))\n";
    Cranelisp::new()
        .file("user.cl", src)
        .run("user.cl")
        .output()
        .assert_exit(200);
}

// =============================================================================
// limit-#2 WIN — the §2.6.2/§9 partial-dependency value+timing witness.
// =============================================================================

/// `--run` a full PrimitivesOnly program with extra env vars; assert `expect_exit`
/// and return elapsed ms. Used by the WIN timing witness with a `work` leaf (NOT
/// `fib_program`), so the ONLY sparking is the top-level dependent `let` — `fib`'s
/// internal apply-arg over-spark would swamp the top-level overlap signal and make
/// the timing row flaky (the documented naive-fib over-spark hazard).
fn run_prog_ms(prog: &str, expect_exit: i32, envs: &[(&str, &str)]) -> u128 {
    let mut b = Cranelisp::new().run("user.cl").user(prog);
    for (k, v) in envs {
        b = b.env(k, v);
    }
    let out = b.output();
    assert_eq!(
        out.status.code(),
        Some(expect_exit),
        "expected exit {expect_exit}\nenvs={envs:?}\nstdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    out.elapsed.as_millis()
}

/// The WIN program: three INDEPENDENT expensive `work` sparks (`a`, `b`, `d`) plus a
/// dependent spark `c (add-i64 (work N) (sub-i64 a a))` whose independent sub-work
/// `(work N)` is real and whose dependency reference `(sub-i64 a a)` forces the
/// SPARKED `a`. `work` is tail-recursive and NEVER sparks internally, so the only
/// parallelism is the top-level `let`. `compute = a+b+d+c = 4·N`; `/N = 4`.
fn win_program(n: i64) -> String {
    format!(
        "(import [primitives [div-i64 add-i64 sub-i64 le-i64 Int Pure]])\n\
         {DEP_WORK_DEF}\
         (defn compute []\n\
           (let [a (work {n} 0)\n\
                 b (work {n} 0)\n\
                 d (work {n} 0)\n\
                 c (add-i64 (work {n} 0) (sub-i64 a a))]\n\
             (add-i64 (add-i64 a b) (add-i64 d c))))\n\
         (defn main [] (Pure (div-i64 (compute) {n})))\n"
    )
}

// spec: design/backend/lenient-eval.md §2.6.2 — the partial-dependency shape that
// genuinely OVERLAPS. Under limit #2 the four bindings run concurrently — critical
// path ≈ 2·work(N) (force `a`, then `c`'s own `work`) vs 4·work(N) sequential —
// demonstrating limit #2 extracts real concurrency, which the (now combine-in-body)
// stdlib shape did not. `work` leaf (no internal over-spark) so the signal is the
// top-level overlap, not naive-fib spark noise.
//
// Asserts BOTH:
//   (a) result identical to the forced-sequential oracle (CRANELISP_NO_LENIENT=1)
//       AND the known value — 4·N / N = 4 (exit 4);
//   (b) a generous not-slower-than-sequential timing witness (best-of-N, ×2 margin
//       — never flaky), plus a logged speedup observation.
#[test]
fn dependent_spark_partial_dependency_win() {
    // N tuned so 4·work(N) compute (~150 ms serial) clears the ~40 ms process+JIT
    // floor — at smaller N the fixed overhead swamps the compute and the speedup is
    // invisible (parallel ≈ sequential). At 150M the overlap shows ~1.4–1.5× in the
    // logged witness; the assertion stays the generous not-slower-than floor.
    const N: i64 = 150_000_000;
    let prog = win_program(N);

    // (a) value floor — identical to the forced-sequential oracle and the known
    // value (contention-immune; a single ON/OFF pair suffices).
    let on = Cranelisp::new().run("user.cl").user(&prog).output().status.code();
    let off = Cranelisp::new()
        .run("user.cl")
        .user(&prog)
        .env("CRANELISP_NO_LENIENT", "1")
        .output()
        .status
        .code();
    assert_eq!(
        on,
        Some(4),
        "partial-dependency WIN value: expected 4·N/N=4 (exit 4); got {on:?}"
    );
    assert_eq!(
        on, off,
        "partial-dependency WIN: lenient ON vs forced-sequential OFF differ ({on:?} vs {off:?}) \
         — §2.6.2 observational equivalence violated"
    );

    // (b) timing witness — best-of-N min (contention only ever makes a run SLOWER).
    let parallel_ms = best_of_n_ms(5, || run_prog_ms(&prog, 4, &[]));
    let sequential_ms =
        best_of_n_ms(3, || run_prog_ms(&prog, 4, &[("CRANELISP_NO_LENIENT", "1")]));
    // Generous floor (×2): the dependent-spark substrate must NOT regress to
    // slower-than-serial. On a genuinely-parallel impl `parallel_ms` is ~half
    // `sequential_ms` (≈4·work serial vs ≈2·work critical path), so this clears by
    // a wide margin — the margin is what keeps the timing row non-flaky.
    assert!(
        parallel_ms <= sequential_ms * 2,
        "partial-dependency limit-#2 spark must NOT be slower than sequential (floor): \
         parallel(best-of-5)={parallel_ms}ms, sequential(best-of-3)={sequential_ms}ms"
    );
    // Observation (logged, not asserted, to stay non-flaky): the speedup that
    // demonstrates real concurrency. Run with `--nocapture` to see it.
    println!(
        "[dependent_spark_partial_dependency_win] parallel(best-of-5)={parallel_ms}ms \
         sequential(best-of-3)={sequential_ms}ms (limit-#2 overlap witness)"
    );
}

// =============================================================================
// Sprint 94 Phase 6 — /port floor-violation finding (alloc/RC-heavy parallel).
//
// Finding (/port, Phase 6): the "never slower than sequential" floor (the effect-
// concurrency thesis; `design/backend/lenient-eval.md` §3.6.3,
// `design/arch/effect-concurrency.md` §3.1) is VIOLATED for alloc/RC-heavy parallel
// workloads. Each independently-sparked recursive branch (`dac`'s two same-block
// `let` bindings `left`/`right`, both free of earlier bindings → both spark and run
// in parallel) churns `iters` `vec-set` copies of a SHARED `(Vec Box)` at each leaf.
// Because the Vec is shared across all frames and worker threads (rc > 1), every
// `vec-set` deep-copies the backing store AND atomically inc/dec's the RC of every
// retained `Box` element — so all workers hammer the SAME allocator lock and the
// SAME `Box` RC cache lines. The parallel run burns multiples of the forced-
// sequential CPU for byte-identical work. The spark-budget create-gate (§3.6) bounds
// spark COUNT but NOT per-branch shared-resource contention, so the floor is not
// restored for this shape.
//
// WHY THE TIMING SIGNAL CANNOT BE A DEFAULT-SUITE GUARD (the disposition decision):
//   - WALL CLOCK is unusable: on a multicore box the contention hides behind
//     parallelism — wall ratio is only ~1.0-1.2x (within noise) however hard the
//     workload is pushed (probed N=81..400, leaves=16..64, iters=2000..8000).
//   - CPU TIME (user+sys) is the real signal — but it is SCHEDULING-DEPENDENT, not
//     load-independent as first assumed. The contention CPU cost only materialises
//     when the spark workers get REAL concurrent cores. Measured on this 10-core box:
//     idle ⇒ ~6.5x (RED); under saturating background load ⇒ ~3.1x (right at K=3);
//     inside the full 1700-test concurrent `cargo nt` ⇒ dips below 3x ⇒ GREEN. A
//     hard CPU-ratio assert in the default lane therefore flips RED↔GREEN with
//     machine load — exactly the banned `flaky`/`timing-sensitive` disposition
//     (`tests/plan/ledger.md` §Discipline), and it would surface a spurious
//     "regression" on a loaded CI box.
//   - Deterministic-RED-in-the-concurrent-suite is INFEASIBLE from `tests/` alone:
//     it would need exclusive core scheduling (a nextest test-group in
//     `.config/nextest.toml`, outside `/qa`'s `tests/`-only edit scope), and a
//     bigger workload does not help (both arms scale together; the RATIO is set by
//     the contention factor, which is what load erodes).
//
// DISPOSITION (option 2 — demote): the default-suite member is the DETERMINISTIC
// correctness floor (`alloc_rc_heavy_parallel_result_equals_sequential` below:
// parallel result == serial == known value — load-immune, always GREEN). The
// CPU-contention demonstration is preserved as an `#[ignore]`'d on-demand benchmark
// (`alloc_rc_heavy_parallel_cpu_floor_benchmark_ignored`) that reproduces the floor
// violation on an IDLE box. The durable record of the finding lives in
// `tests/plan/ledger.md` (S94 Phase 6) + `design/arch/effect-concurrency.md` §3.1 —
// NOT a flaky default-suite RED. Owner of the floor fix: /backend + /arch.
// =============================================================================

fn cranelisp_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("debug")
        .join("cranelisp")
}

/// The alloc/RC-heavy divide-and-conquer program /port reduced to a minimal repro:
/// a binary D&C tree (`dac`) whose two recursive halves are INDEPENDENT same-block
/// `let` bindings (`left`/`right` reference only params → both sparkable → run in
/// parallel), each leaf (`churn`) doing `iters` `vec-set` copies of the SHARED
/// `(Vec Box)` `v`. `Box` is a single-field heap ADT, so each copy-on-write copy
/// inc/dec's the RC of every retained element atomically — the contention source.
/// Free-standing per `tests/CLAUDE.md`: primitives + special forms only, ZERO
/// stdlib. Result == `leaves * iters*(iters+1)/2` (each leaf sums the read-back
/// `(Box k)` values `iters..1`).
fn churn_dac_program(vec_len: usize, leaves: i64, iters: i64) -> String {
    let boxes: String = (0..vec_len)
        .map(|k| format!("(Box {k})"))
        .collect::<Vec<_>>()
        .join(" ");
    format!(
        "(import [primitives [Int add-i64 sub-i64 div-i64 le-i64 vec-get vec-set Pure]])\n\
         (deftype Box [:Int v])\n\
         (defn unbox [b] (match b [(Box x) x]))\n\
         (defn churn [v :Int iters :Int acc]\n\
           (if (le-i64 iters 0)\n\
               acc\n\
               (let [v2 (vec-set v 0 (Box iters))]\n\
                 (churn v (sub-i64 iters 1) (add-i64 acc (unbox (vec-get v2 0)))))))\n\
         (defn dac [v :Int lo :Int hi :Int iters]\n\
           (if (le-i64 (sub-i64 hi lo) 1)\n\
               (churn v iters 0)\n\
               (let [left  (dac v lo (add-i64 lo (div-i64 (sub-i64 hi lo) 2)) iters)\n\
                     right (dac v (add-i64 lo (div-i64 (sub-i64 hi lo) 2)) hi iters)]\n\
                 (add-i64 left right))))\n\
         (defn main []\n\
           (let [v [{boxes}]]\n\
             (Pure (dac v 0 {leaves} {iters}))))\n"
    )
}

/// One `--run` of the written `cl` file under `/usr/bin/time -v`; returns
/// `(cpu_seconds, exit_code)` where `cpu = user + sys` CPU of the child. Used ONLY
/// by the `#[ignore]`'d on-demand contention benchmark (the CPU-ratio signal is
/// scheduling-dependent — see banner — so it is not a default-suite guard).
/// `/usr/bin/time -o <file>` keeps its report out of the child's stderr.
fn run_cpu_seconds(td: &Path, cl: &Path, no_lenient: bool) -> (f64, Option<i32>) {
    let report = td.join(if no_lenient { "ser.time" } else { "par.time" });
    let mut cmd = Command::new("/usr/bin/time");
    cmd.arg("-v")
        .arg("-o")
        .arg(&report)
        .arg(cranelisp_bin())
        .arg("--run")
        .arg(cl);
    if no_lenient {
        cmd.env("CRANELISP_NO_LENIENT", "1");
    }
    let out = cmd
        .output()
        .expect("spawn `/usr/bin/time -v cranelisp --run` (GNU time required)");
    let rpt = std::fs::read_to_string(&report).expect("read `/usr/bin/time -v` report");
    let mut cpu = 0.0_f64;
    for line in rpt.lines() {
        let l = line.trim();
        if let Some(v) = l
            .strip_prefix("User time (seconds):")
            .or_else(|| l.strip_prefix("System time (seconds):"))
        {
            cpu += v.trim().parse::<f64>().unwrap_or(0.0);
        }
    }
    // GNU time propagates the child's exit code.
    (cpu, out.status.code())
}

// spec: design/backend/lenient-eval.md §3.6.3 — DEFAULT-SUITE GUARD (deterministic,
// load-immune): the alloc/RC-heavy parallel shape must compute the byte-identical
// result to the forced-sequential oracle (`CRANELISP_NO_LENIENT=1`) and the known
// value — the never-WRONG floor, which always holds regardless of scheduling. (The
// never-SLOWER floor is timing/scheduling-dependent and is demonstrated only by the
// `#[ignore]`'d benchmark below; see the section banner for why it cannot be a
// deterministic default-suite assertion.)
#[test]
fn alloc_rc_heavy_parallel_result_equals_sequential() {
    // Modest churn — correctness needs the shape (independent sparking branches +
    // shared (Vec Box) COW), not heavy contention — so it stays fast in the default
    // suite. Each leaf sums read-back (Box k) for k in iters..1 = iters*(iters+1)/2;
    // LEAVES identical leaves. Unix exit byte = result mod 256.
    const VEC_LEN: usize = 81;
    const LEAVES: i64 = 8;
    const ITERS: i64 = 500;
    let expected =
        (((LEAVES as i128) * (ITERS as i128) * (ITERS as i128 + 1) / 2) % 256) as i32;
    let prog = churn_dac_program(VEC_LEN, LEAVES, ITERS);

    // Lenient ON (sparks fire) vs forced-sequential OFF — must agree, and equal the
    // known value. Contention-immune: a single ON/OFF pair suffices.
    let on = Cranelisp::new().run("user.cl").user(&prog).output();
    let off = Cranelisp::new()
        .run("user.cl")
        .user(&prog)
        .env("CRANELISP_NO_LENIENT", "1")
        .output();
    assert_eq!(
        on.status.code(),
        Some(expected),
        "alloc/RC-heavy parallel result must equal the known sequential value \
         (exit {expected})\nstdout:\n{}\nstderr:\n{}",
        on.stdout,
        on.stderr
    );
    assert_eq!(
        off.status.code(),
        on.status.code(),
        "lenient ON vs forced-sequential OFF differ ({:?} vs {:?}) — §12.4.3 \
         observational equivalence violated for the alloc/RC-heavy shape",
        off.status.code(),
        on.status.code()
    );
}

// spec: design/backend/lenient-eval.md §3.6.3 — ON-DEMAND CONTENTION BENCHMARK (NOT
// a default-suite guard). Demonstrates /port's Phase-6 floor violation: the alloc/
// RC-heavy parallel workload burns multiples of the forced-sequential CPU
// (allocator-lock + atomic-RC cache-line contention across workers; the create-gate
// bounds spark COUNT, not per-branch contention).
//
// IGNORED by design: the CPU-ratio signal is SCHEDULING-DEPENDENT (idle ~6.5x RED;
// saturated ~3.1x; inside the concurrent default suite it dips below 3x ⇒ GREEN), so
// a hard assert here would be flaky in the default lane — the banned `flaky`/
// `timing-sensitive` disposition. Run it deliberately ON AN IDLE BOX to reproduce
// the violation:
//
//   cargo nextest run --test concurrency_spark --run-ignored ignored-only
//   # or:  cargo test  --test concurrency_spark -- --ignored
//
// Expected on an idle box: RED with `FLOOR VIOLATED … ~6x (> 3x margin)`. It flips
// GREEN when the floor is restored for the alloc/RC-heavy shape (a contention-aware
// create-gate, a non-copying / single-owner Vec path, or Phase-H memory work).
// Durable record: `tests/plan/ledger.md` (S94 Phase 6) + `design/arch/
// effect-concurrency.md` §3.1. Owner: /backend + /arch.
#[test]
#[ignore = "perf/contention benchmark: CPU-ratio signal is scheduling-dependent \
            (idle ~6.5x RED, saturated ~3x, concurrent-suite GREEN) so it cannot be a \
            deterministic default-suite assert — run on an IDLE box via --run-ignored; \
            durable record in tests/plan/ledger.md + effect-concurrency.md §3.1"]
fn alloc_rc_heavy_parallel_cpu_floor_benchmark_ignored() {
    const VEC_LEN: usize = 81; // /port's "~81-element Vec of (Box Int)".
    const LEAVES: i64 = 16; // 16 D&C leaves → a wide parallel frontier.
    const ITERS: i64 = 3000; // heavy per-leaf vec-set churn over the shared Vec.
    let expected =
        (((LEAVES as i128) * (ITERS as i128) * (ITERS as i128 + 1) / 2) % 256) as i32;

    let td = tempfile::tempdir().expect("tempdir");
    let cl = td.path().join("churn.cl");
    std::fs::write(&cl, churn_dac_program(VEC_LEN, LEAVES, ITERS)).expect("write churn.cl");

    // Correctness floor (always holds) — a mis-run cannot masquerade as a fast
    // (hence "in-floor") timing pass.
    let (par_cpu0, par_exit) = run_cpu_seconds(td.path(), &cl, false);
    let (ser_cpu0, ser_exit) = run_cpu_seconds(td.path(), &cl, true);
    assert_eq!(par_exit, Some(expected), "parallel result must equal the known value");
    assert_eq!(ser_exit, par_exit, "lenient ON vs OFF differ — equivalence violated");

    // CPU floor demonstration. Conservative arms: parallel = MIN over 5 (best case),
    // serial = MAX over 3 (worst/highest baseline). On an idle box this reproduces
    // the ~6x violation; under load the ratio erodes (the reason it is ignored).
    let mut par = par_cpu0;
    for _ in 0..4 {
        par = par.min(run_cpu_seconds(td.path(), &cl, false).0);
    }
    let mut ser = ser_cpu0;
    for _ in 0..2 {
        ser = ser.max(run_cpu_seconds(td.path(), &cl, true).0);
    }

    const K: f64 = 3.0;
    println!(
        "[alloc_rc_heavy_parallel_cpu_floor_benchmark_ignored] parallel(best-of-5)={par:.2}s \
         CPU vs serial(worst-of-3)={ser:.2}s CPU = {:.1}x (floor K={K}x)",
        par / ser
    );
    assert!(
        par <= ser * K,
        "FLOOR VIOLATED (design/backend/lenient-eval.md §3.6.3 'never slower than \
         sequential'): alloc/RC-heavy parallel workload burns {par:.2}s CPU (best-of-5) \
         vs {ser:.2}s serial (worst-of-3) = {ratio:.1}x (> {K}x margin). Root: per-branch \
         copy-on-write copies of a SHARED (Vec Box) → allocator-lock + atomic-RC \
         cache-line contention across workers; the spark-budget create-gate bounds spark \
         COUNT, not per-branch shared-resource contention. Owner: /backend + /arch.",
        ratio = par / ser
    );
}
