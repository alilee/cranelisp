//! FIXME 0474 repro — the vec-set/vec-push COW **copy branch** leaks the
//! consumed source Vec's extra owned reference (S101 Wave-3 review finding;
//! `design/arch/fixmes/0474-*.md`; resolver **FIXME(/backend)** on
//! `crates/cranelisp-backend/src/compiler/vec_codegen.rs` —
//! `emit_vec_query_into` / `emit_vec_set_cow_core` / `emit_vec_push_cow_core`).
//!
//! ## Mechanism (verified by RC-stats probes, 2026-07-03, post-Wave-3 binary)
//!
//! The COW cores release the source Vec only on the **mutate/grow** branches
//! (rc==1 — ownership transfers into the returned pointer). On the **rc>1
//! copy branch** the `vec-set-copy`/`vec-push-copy` externs do NOT dec the
//! source (the FIXME-0417 division of labour) — so any call site that hands
//! the core an EXTRA owned reference on the source leaks it: one Vec
//! (header + data buffer = 2 allocations) per copy-branch invocation.
//!
//! Shapes pinned RED below (200 iterations each; mutate-branch control is
//! exactly balanced, imbalance 0):
//!
//!   1. curried `(vec-set v)` partial — the capture holds a reference, so
//!      EVERY call takes the copy branch: leak 2 allocs/call
//!      (probe: allocs=600 deallocs=200).
//!   2. `vec-set` as a VALUE through a user HOF with the source still live —
//!      the wrapper's owned param protocol: leak 2 allocs/call
//!      (probe: allocs=1400 deallocs=1000).
//!   3. **WIDENING beyond FIXME 0474's claim**: a plain STATIC `(vec-set v 0
//!      9)` with `v` still live after the call ALSO leaks 2 allocs/call
//!      (probe: allocs=1200 deallocs=800). 0474 asserts static sites are
//!      balanced by scope machinery; empirically the copy branch leaks the
//!      protect-inc'd source reference at static shared-source sites too —
//!      same root class (the copy branch releases nothing), and since the
//!      Wave-3 cores are line-identical to the pre-S101 static bodies this
//!      leg is almost certainly PRE-EXISTING, newly pinned. Recorded in the
//!      ledger; the /backend cure for the class covers all three.
//!
//! Leak-only (polarity errs on the retain side — no UAF/double-free). COW
//! value semantics hold throughout (asserted via the computed results).
//!
//! Failing-not-ignored per `memory/feedback_failing_not_ignored.md`; these
//! are the durable record + regression guard and flip GREEN with the /backend
//! fix (a consumed-source polarity on the COW cores / call sites so the copy
//! branch releases exactly when an owned reference was handed in — see the
//! FIXME's proposed resolution; sequencing: before/with increment I's
//! R2-wrapper + `str-len$borrowed` work on the same seam). Ledger entry:
//! `tests/plan/ledger.md` §"Sprint 101 Wave-5 — FIXME 0474 repro".

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

const ITERS: i64 = 200;
/// Generous ambient tolerance between two sessions' alloc/dealloc imbalance
/// (session bootstrap noise; the balanced control probes at exactly 0). The
/// leak signature is ~2×ITERS = 400 — well above this.
const TOLERANCE: i64 = 16;

fn rc_stats_session(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .env("CRANELISP_RC_STATS", "1")
        .stdin(lines)
        .output()
}

/// `allocs - deallocs` from the `[RC_STATS]` exit line on stderr.
fn alloc_imbalance(stderr: &str) -> i64 {
    let line = stderr
        .lines()
        .find(|l| l.contains("[RC_STATS]"))
        .unwrap_or_else(|| panic!("no [RC_STATS] line on stderr: {stderr}"));
    let field = |k: &str| -> i64 {
        line.split_whitespace()
            .find_map(|tok| tok.strip_prefix(&format!("{k}=")))
            .and_then(|v| v.parse().ok())
            .unwrap_or_else(|| panic!("no {k}= field in RC_STATS line: {line}"))
    };
    field("allocs") - field("deallocs")
}

/// Balanced control: the same per-iteration work on the MUTATE branch — the
/// source is not live after the call, so rc==1 at the COW check and ownership
/// transfers into the result. Pins ambient session noise (probes at exactly
/// 0) so the leak tests' deltas isolate the copy branch.
fn mutate_branch_control_imbalance() -> i64 {
    let control = rc_stats_session(&format!(
        "(defn spinc [:Int n :Int acc] \
           (if (eq-i64 n 0) acc \
             (let [v [1 2 3]] \
               (spinc (sub-i64 n 1) (add-i64 acc (vec-get (vec-set v 0 9) 0))))))\n\
         (spinc {ITERS} 0)\n"
    ))
    .assert_ok()
    .assert_stdout_contains(&format!(":primitives/Int {}", 9 * ITERS));
    alloc_imbalance(&control.stderr)
}

// spec: spec/12-runtime.md §12.3.1 — heap values MUST be freed when
// unreachable; §12.3.3 — COW is semantically invisible, including its RC
// accounting. A CURRIED partial of vec-set holds one capture reference, so
// every call arrives at the COW check with rc>=2 and takes the copy branch —
// which leaks the consumed source Vec every call.
// RED on HEAD (post-Wave-3): imbalance delta ~= 2 x ITERS. FIXME(/backend).
#[test]
fn vec_set_curried_call_loop_neg_does_not_leak_source_vec() {
    let curried = rc_stats_session(&format!(
        "(defn spin [:Int n :Int acc] \
           (if (eq-i64 n 0) acc \
             (let [v [1 2 3] s (vec-set v)] \
               (spin (sub-i64 n 1) (add-i64 acc (vec-get (s 0 9) 0))))))\n\
         (spin {ITERS} 0)\n"
    ))
    .assert_ok()
    // COW value semantics hold: every iteration reads back the written 9.
    .assert_stdout_contains(&format!(":primitives/Int {}", 9 * ITERS));

    let (leak_imb, ctl_imb) = (
        alloc_imbalance(&curried.stderr),
        mutate_branch_control_imbalance(),
    );
    assert!(
        leak_imb - ctl_imb <= TOLERANCE,
        "curried vec-set loop leaks the consumed source Vec on the COW copy \
         branch (FIXME 0474, /backend): curried imbalance {leak_imb} vs \
         balanced control {ctl_imb} (allowed delta {TOLERANCE}; leak \
         signature ~{})",
        2 * ITERS
    );
}

// spec: spec/12-runtime.md §12.3.1 — heap values MUST be freed when
// unreachable; §12.3.3 — COW. vec-set passed as a VALUE to a user HOF while
// the source Vec stays live in the caller (read after the call): the wrapper
// receives an owned reference with rc>=2, the COW check takes the copy
// branch, and the wrapper's owned reference is never released. The original
// Vec is observably unchanged (COW correctness asserted: r[0]=9 and v[0]=1),
// but 2 allocations leak per call. RED on HEAD (post-Wave-3). FIXME(/backend).
#[test]
fn vec_set_as_value_shared_source_neg_does_not_leak() {
    let hof = rc_stats_session(&format!(
        "(defn upd [f v] (f v 0 9))\n\
         (defn use1 [:Int n :Int acc] \
           (if (eq-i64 n 0) acc \
             (let [v [1 2 3] r (upd vec-set v)] \
               (use1 (sub-i64 n 1) \
                     (add-i64 acc (add-i64 (vec-get r 0) (vec-get v 0)))))))\n\
         (use1 {ITERS} 0)\n"
    ))
    .assert_ok()
    // COW correctness: r[0]=9 (updated copy) and v[0]=1 (original untouched).
    .assert_stdout_contains(&format!(":primitives/Int {}", 10 * ITERS));

    let (leak_imb, ctl_imb) = (
        alloc_imbalance(&hof.stderr),
        mutate_branch_control_imbalance(),
    );
    assert!(
        leak_imb - ctl_imb <= TOLERANCE,
        "vec-set as a value over a still-live source Vec leaks on the COW copy \
         branch (FIXME 0474, /backend): HOF imbalance {leak_imb} vs balanced \
         control {ctl_imb} (allowed delta {TOLERANCE}; leak signature ~{})",
        2 * ITERS
    );
}

// spec: spec/12-runtime.md §12.3.1 — heap values MUST be freed when
// unreachable; §12.3.3 — COW. WIDENING (module header note 3): a plain
// STATIC-site `(vec-set v 0 9)` whose source is still live after the call
// takes the copy branch and leaks the protect-inc'd source reference — the
// scope machinery releases only the binding's own reference. Same root class
// as the wrapper/curry legs (the copy branch releases nothing); pre-existing
// on the line-identical pre-S101 static bodies, newly pinned here.
// RED on HEAD. FIXME(/backend).
#[test]
fn vec_set_static_site_shared_source_neg_does_not_leak() {
    let static_shared = rc_stats_session(&format!(
        "(defn use1c [:Int n :Int acc] \
           (if (eq-i64 n 0) acc \
             (let [v [1 2 3] r (vec-set v 0 9)] \
               (use1c (sub-i64 n 1) \
                      (add-i64 acc (add-i64 (vec-get r 0) (vec-get v 0)))))))\n\
         (use1c {ITERS} 0)\n"
    ))
    .assert_ok()
    // COW correctness: r[0]=9 (updated copy) and v[0]=1 (original untouched).
    .assert_stdout_contains(&format!(":primitives/Int {}", 10 * ITERS));

    let (leak_imb, ctl_imb) = (
        alloc_imbalance(&static_shared.stderr),
        mutate_branch_control_imbalance(),
    );
    assert!(
        leak_imb - ctl_imb <= TOLERANCE,
        "STATIC-site vec-set with a still-live source leaks on the COW copy \
         branch (widens FIXME 0474, /backend): imbalance {leak_imb} vs \
         balanced control {ctl_imb} (allowed delta {TOLERANCE}; leak \
         signature ~{})",
        2 * ITERS
    );
}
