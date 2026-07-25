//! S102 Phase-5 Stage-1 — increment-I QA-first set: starved-inc fences
//! (S1–S6), projection-escape negatives (L-D3a–f), the declared-fact-table
//! row tests, stack-slot behavioural lanes (L-C2), and the owed-observability
//! hook smokes (H1/H2/H3/H5).
//!
//! Plan: `tests/plan/s100-ownership-verification.md` §3.2 (fence design),
//! §3.3 (L-D3), §3.4 (L-C2), §3.7 (hooks), §6 (drafting list);
//! `tests/plan/s102-test-plan.md` §1.5. Spine:
//! `design/arch/ownership-inference.md` §3–§4 (borrow-elision + projection);
//! typecheck half `design/typecheck/ownership-inference.md` §4/§9; backend
//! half `design/backend/ownership-codegen.md` §3/§13.
//!
//! **Fence design** (every S-fence): (i) BEHAVIORAL leg — the guarded value
//! is *used after the elided-inc window*, sustained (1000 crossings, the
//! §"Sustained-load convention" of tests/CLAUDE.md), asserting VALUES, not
//! crash-absence; (ii) BALANCE leg — `CRANELISP_RC_STATS` alloc/dealloc
//! imbalance must be ITERATION-INDEPENDENT (measured at N=50 vs N=1000 —
//! self-calibrating, no absolute-baseline fragility); (iii) two-condition
//! rule — each fence also runs under the scripted checking-allocator lane
//! (`tests/scripts/asan/`), executed at B3 wave gates, not per-commit.
//!
//! ALL S-fences and L-D3a–e rows are **GREEN at draft** — today's
//! conservative Decision-24 codegen satisfies them by construction. They
//! become load-bearing the moment each B3 mechanism lands (borrow-elision
//! B3.2, non-atomic RC B3.3, stack slots B3.4, str-len sibling B3.5): a
//! mechanism that skips an inc it must not skip fails the behavioral leg; a
//! mechanism that leaks fails the balance leg.
//!
//! Draft-time polarity (probed 2026-07-03 on the CS-A binary):
//!   RED ×7 — the owed hooks + the golden smoke (loud signals, flip in the
//!   named waves) + TWO defects DISCOVERED at drafting (guards are the
//!   record; both live in the fn_as_value B3.1 seam):
//!     clif_golden_single_module_smoke      (L-B1 in-suite smoke — flips at
//!                                           Wave 3 B0-be golden capture)
//!     h2_rc_stats_reports_per_mechanism_counters  (H2 — /backend, B3)
//!     h3_rc_stats_reports_per_extern_adaptation_pairs (H3 — /backend, B3 or
//!                                           deferred with the L-D5 decision)
//!     h5_ownership_trace_emits_verdicts    (H5 — /typecheck, B2 CS-4)
//!     l_d3f_stored_param_not_summarised_borrowed (needs H5)
//!     curried_partial_and_static_call_of_same_fn_in_one_body_compiles
//!                                          (NEW defect: span-keyed curry
//!                                           drop-glue collision — /backend B3.1)
//!     vec_returned_from_generic_fn_consumed_by_vec_op_releases_temp
//!                                          (NEW defect: 1-alloc-per-call leak
//!                                           — /backend B3.1, 0474-adjacent)
//!   GREEN ×24.
//! Ledger: tests/plan/ledger.md §"Sprint 102 Phase-5 Stage-1 QA-first RED set".

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

/// Run a free-standing program in `--run` mode (no prelude file; the program
/// self-imports) and return the capture.
fn run_program(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new().run("user.cl").user(src).output()
}

/// Run with `CRANELISP_RC_STATS=1` and return (capture, allocs − deallocs).
fn run_with_rc_stats(src: &str) -> (helpers::e2e::CrOutput, i64) {
    let out = Cranelisp::new()
        .run("user.cl")
        .user(src)
        .env("CRANELISP_RC_STATS", "1")
        .output();
    let imb = rc_imbalance(&out.stderr);
    (out, imb)
}

/// Parse `[RC_STATS] rc_inc=N rc_dec=N allocs=N deallocs=N` (stderr, at exit).
fn rc_imbalance(stderr: &str) -> i64 {
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

/// Assert exit code equals `value % 256` (batch `main` returns `Pure Int`;
/// the process exit code carries it, mod 256).
fn assert_exit_value(out: helpers::e2e::CrOutput, value: i64) -> helpers::e2e::CrOutput {
    let expected = (value % 256) as i32;
    match out.status.code() {
        Some(c) if c == expected => out,
        other => panic!(
            "expected exit {expected} (= {value} mod 256), got {other:?}\nstdout:\n{}\nstderr:\n{}",
            out.stdout, out.stderr
        ),
    }
}

/// The balance leg: run `template` (which must contain `{N}`) at N=50 and
/// N=1000 and assert the alloc/dealloc imbalance is ITERATION-INDEPENDENT —
/// a leak scales with N (a 1-alloc-per-iteration leak shows a delta of 950
/// here); a fixed baseline does not.
///
/// Tolerance (the fence spec's "± documented baseline",
/// s100-ownership-verification.md §3.2): |delta| ≤ 2.
///
/// **Race isolation, not a loose bar (S102, `fact_row_char_at_…` intermittent,
/// `feedback_frame_recurring_failure_by_symptom`).** The at-exit `[RC_STATS]`
/// accounting exhibits a small TRANSIENT jitter under full-parallel suite load
/// — one dealloc racing the stats-print at process exit. It is N-independent
/// ("0 vs 1 across repeats") and BOUNDED: a 288-run high-concurrency probe
/// (load ≈10, 48-way) capped the raw imbalance at ±1, never negative, never a
/// missing line. That alone cannot trip |delta| ≤ 2 (each measurement ∈ {0,1}
/// ⇒ delta ≤ 1); the rare full-suite FAIL is the pathological at-exit collision
/// pushing one measurement to 2–3. We do NOT absorb that by widening the bar
/// (which would blunt small-leak sensitivity). Instead we distinguish the race
/// from a real leak by REPETITION — the property the ledger §Discipline
/// mandates over "flaky": a genuine per-iteration leak is DETERMINISTIC and
/// huge (≥ 950 at this N-spread, every pair), while the at-exit race is
/// transient and collapses to ≤1 on a clean re-measure. Take the tightest
/// delta across up to 3 measurement pairs, re-measuring ONLY when a pair is
/// ambiguous (delta > 2). The deterministic clean case (delta 0–1) passes on
/// the first pair with zero extra subprocess cost; the retry budget targets the
/// rare race pair. A real leak fails all 3 pairs and stays RED (the #26
/// `vec_returned_from_generic_fn…` guard reads delta 950 — 59× the bar —
/// unaffected). Bug-not-flake per `tests/plan/ledger.md` §Discipline.
fn assert_iteration_independent_imbalance(template: &str, context: &str) {
    let measure = || {
        let (_o1, small) = run_with_rc_stats(&template.replace("{N}", "50"));
        let (_o2, large) = run_with_rc_stats(&template.replace("{N}", "1000"));
        (small, large, (large - small).abs())
    };
    let mut best = measure();
    // Only re-measure the ambiguous case (delta > 2). A real ≥950 leak never
    // enters this loop's benefit — it stays far above the bar on every pair.
    for _ in 0..2 {
        if best.2 <= 2 {
            break;
        }
        let next = measure();
        if next.2 < best.2 {
            best = next;
        }
    }
    let (small, large, delta) = best;
    assert!(
        delta <= 2,
        "[{context}] alloc/dealloc imbalance scales with iteration count \
         (N=50 → {small}, N=1000 → {large}, best-of-3 delta {delta}) — a \
         per-iteration leak (fence balance leg, \
         s100-ownership-verification.md §3.2)"
    );
}

// =============================================================================
// S1 — caller-side skip-inc: Var arg → Borrowed param; caller uses the var
// AFTER the call, sustained (spine §3.1)
// =============================================================================

/// S1 fence template: heap String var passed to a callee that only reads it;
/// the caller uses `s` again after every call. Result: N × (len + first-len).
const S1_TEMPLATE: &str = "(import [primitives [*]])\n\
    (defn use-len [:String s] (str-len s))\n\
    (defn spin [:Int n :Int acc :String s]\n\
    \x20 (if (eq-i64 n 0) acc\n\
    \x20   (spin (sub-i64 n 1) (add-i64 acc (add-i64 (use-len s) (str-len s))) s)))\n\
    (defn main [] (Pure (spin {N} 0 \"hello\")))\n";

// spec: design/arch/ownership-inference.md §3.1 — S1 behavioral leg: the
// borrowed-param elision site; the var survives every crossing and reads
// correctly after. 1000 sustained crossings. GREEN at draft (conservative
// codegen); load-bearing when borrow-elision (B3.2) lands.
#[test]
fn s1_borrowed_param_var_used_after_call_sustained() {
    let out = run_program(&S1_TEMPLATE.replace("{N}", "1000"));
    assert_exit_value(out, 1000 * (5 + 5));
}

// spec: design/arch/ownership-inference.md §3.1 — S1 balance leg: no
// per-crossing leak and no double-free (imbalance iteration-independent).
#[test]
fn s1_borrowed_param_heap_balance_iteration_independent() {
    assert_iteration_independent_imbalance(S1_TEMPLATE, "S1");
}

// =============================================================================
// S2 — projection reads: vec-get on a borrowed root; root AND projection
// used again, interleaved, sustained (spine §3.3)
// =============================================================================

const S2_TEMPLATE: &str = "(import [primitives [*]])\n\
    (defn walk [v :Int n :Int acc]\n\
    \x20 (if (eq-i64 n 0) acc\n\
    \x20   (walk v (sub-i64 n 1)\n\
    \x20     (add-i64 acc (add-i64 (str-len (vec-get v 0)) (vec-len v))))))\n\
    (defn main [] (Pure (walk [\"aa\" \"bbb\"] {N} 0)))\n";

// spec: design/arch/ownership-inference.md §3.3 — S2 behavioral leg:
// projection skip-inc on a borrowed root; the ROOT is used again (vec-len)
// and the projection re-read every iteration. GREEN at draft.
#[test]
fn s2_projection_read_root_and_projection_interleaved_sustained() {
    let out = run_program(&S2_TEMPLATE.replace("{N}", "1000"));
    assert_exit_value(out, 1000 * (2 + 2));
}

// spec: design/arch/ownership-inference.md §3.3 — S2 balance leg.
#[test]
fn s2_projection_read_heap_balance_iteration_independent() {
    assert_iteration_independent_imbalance(S2_TEMPLATE, "S2");
}

// =============================================================================
// S3 — temporary arg → Borrowed param post-call dec (spine §3.1): the leak
// side of the adaptation algebra
// =============================================================================

const S3_TEMPLATE: &str = "(import [primitives [*]])\n\
    (defn use-len [:String s] (str-len s))\n\
    (defn spin [:Int n :Int acc]\n\
    \x20 (if (eq-i64 n 0) acc\n\
    \x20   (spin (sub-i64 n 1) (add-i64 acc (use-len (str-concat \"ab\" \"cd\"))))))\n\
    (defn main [] (Pure (spin {N} 0)))\n";

// spec: design/arch/ownership-inference.md §3.1 — S3 behavioral leg: a fresh
// temporary passed where a borrowed param lands must still be released
// exactly once (no leak — balance leg; no double-free — the process exits
// cleanly with the right value). GREEN at draft.
#[test]
fn s3_temporary_to_borrowed_param_sustained() {
    let out = run_program(&S3_TEMPLATE.replace("{N}", "1000"));
    assert_exit_value(out, 1000 * 4);
}

// spec: design/arch/ownership-inference.md §3.1 — S3 balance leg: the
// per-iteration temporary MUST NOT accumulate.
#[test]
fn s3_temporary_heap_balance_iteration_independent() {
    assert_iteration_independent_imbalance(S3_TEMPLATE, "S3");
}

// =============================================================================
// S4 — wrapper adaptation: the same fn called (a) statically, (b) through a
// closure value, (c) curried — same inputs, same outputs, heap balance
// (spine §3.4/§3.5, the R2 wrapper + curry adapter)
// =============================================================================

// S4 DRAFTING NOTE (defect found at draft, 2026-07-03): the spec'd S4 shape
// is THREE routes — static, fn-as-value, curried — in one body. The curried
// route CANNOT join the fence yet: combining a static call and a curried
// partial of the same fn in one body fails codegen (the duplicate
// curry-drop-glue guard below). S4 fences the two compilable routes; when
// the guard flips (B3.1 wrapper-identity rework), ADD the curried route
// (`((measure s) 1)`, per-iter +5) back into this template.
const S4_TEMPLATE: &str = "(import [primitives [*]])\n\
    (defn measure [:String s :Int extra] (add-i64 (str-len s) extra))\n\
    (defn call2 [f :String s :Int extra] (f s extra))\n\
    (defn spin [:Int n :Int acc :String s]\n\
    \x20 (if (eq-i64 n 0) acc\n\
    \x20   (spin (sub-i64 n 1)\n\
    \x20     (add-i64 acc (add-i64 (measure s 1) (call2 measure s 1))) s)))\n\
    (defn main [] (Pure (spin {N} 0 \"abcd\")))\n";

// spec: design/arch/ownership-inference.md §3.4 — S4 behavioral leg: static
// call and fn-as-value through a HOF give identical results over the same
// borrowed input, sustained (curried route pending the guard below). GREEN
// at draft.
#[test]
fn s4_static_and_value_routes_agree_sustained() {
    let out = run_program(&S4_TEMPLATE.replace("{N}", "1000"));
    assert_exit_value(out, 1000 * (5 + 5));
}

// spec: design/arch/ownership-inference.md §3.5 — S4 balance leg: the
// wrapper/adapter routes must not diverge in RC balance from the static one.
#[test]
fn s4_wrapper_adaptation_heap_balance_iteration_independent() {
    assert_iteration_independent_imbalance(S4_TEMPLATE, "S4");
}

// spec: spec/04-expressions.md §4.6.3 — auto-curry: a partial application of
// a defined fn is an ordinary expression; combining it with a STATIC call of
// the SAME fn in one body MUST compile. DEFECT DISCOVERED AT S102 DRAFTING
// (failing-not-ignored; this guard is the record — no FIXME per
// memory/feedback_no_fixme_with_failing_test.md): codegen dies
// `failed to define auto-curry drop glue: Duplicate definition of
// identifier: runtime/curry_drop_glue_{span}` — the drop-glue identifier is
// SPAN-keyed (fn_as_value.rs::build_auto_curry_drop_glue), the exact
// (span × discriminator) wrapper-identity anti-pattern
// design/backend/ownership-codegen.md §13's ruling forbids ((dispatch
// identity × concrete signature) is the pinned key). Owner /backend — rides
// the B3.1 fn_as_value seam rework. Reduced 2026-07-03: 3 defns, both modes
// (probed --run; REPL asserted here).
#[test]
fn curried_partial_and_static_call_of_same_fn_in_one_body_compiles() {
    let out = run_program(
        "(import [primitives [*]])\n\
         (defn measure [:String s :Int extra] (add-i64 (str-len s) extra))\n\
         (defn both [:String s] (add-i64 (measure s 1) ((measure s) 1)))\n\
         (defn main [] (Pure (both \"ab\")))\n",
    );
    // (2+1) + (2+1) = 6.
    let out = assert_exit_value(out, 6);
    assert!(
        !out.stderr.contains("Duplicate definition"),
        "duplicate curry-drop-glue identifier (span-keyed); stderr:\n{}",
        out.stderr
    );
}

// =============================================================================
// S5 — the str-len$borrowed sibling fence (spine §9.3): borrowed string
// through a `(str-len s)` hot loop, `s` used after; discriminating when the
// B3.5 sibling lands (no adaptation inc at the sibling call)
// =============================================================================

const S5_TEMPLATE: &str = "(import [primitives [*]])\n\
    (defn hot [:Int n :Int acc :String s]\n\
    \x20 (if (eq-i64 n 0) (add-i64 acc (str-len s))\n\
    \x20   (hot (sub-i64 n 1) (add-i64 acc (str-len s)) s)))\n\
    (defn main [] (Pure (hot {N} 0 \"xyz\")))\n";

// spec: design/backend/ownership-codegen.md §9.2 — S5 behavioral + balance
// legs in one: the sibling-targeted call must preserve `s` across 1000
// crossings AND the final use. GREEN at draft; the discriminating leg (no
// adaptation inc) is I-G-side (H2/H3 counters) when B3.5 lands.
#[test]
fn s5_str_len_borrowed_sibling_hot_loop_value_and_balance() {
    let out = run_program(&S5_TEMPLATE.replace("{N}", "1000"));
    assert_exit_value(out, 1001 * 3);
    assert_iteration_independent_imbalance(S5_TEMPLATE, "S5");
}

// =============================================================================
// S6 / L-D3a — borrowed projection RETURNED: rule-5 materialization at the
// escape edge (the inc must EXIST); UAF side + exactly-once release side
// =============================================================================

const D3A_TEMPLATE: &str = "(import [primitives [*]])\n\
    (defn first-of [v] (vec-get v 0))\n\
    (defn spin [:Int n :Int acc v]\n\
    \x20 (if (eq-i64 n 0) acc\n\
    \x20   (spin (sub-i64 n 1)\n\
    \x20     (add-i64 acc (add-i64 (str-len (first-of v)) (vec-len v))) v)))\n\
    (defn main [] (Pure (spin {N} 0 [\"hello\" \"bb\"])))\n";

// spec: design/typecheck/ownership-inference.md §4.4 — L-D3a behavioral leg:
// a projection returned OUT of the projecting fn escapes — the returned
// value survives (UAF side: str-len reads it correctly every crossing) and
// the ROOT stays intact (vec-len after). GREEN at draft.
#[test]
fn l_d3a_projection_returned_escapes_and_survives_sustained() {
    let out = run_program(&D3A_TEMPLATE.replace("{N}", "1000"));
    assert_exit_value(out, 1000 * (5 + 2));
}

// spec: design/typecheck/ownership-inference.md §4.4 — L-D3a double-free
// twin (balance leg): the escaping projection is released exactly once.
#[test]
fn l_d3a_projection_returned_heap_balance_iteration_independent() {
    assert_iteration_independent_imbalance(D3A_TEMPLATE, "L-D3a");
}

// spec: design/typecheck/ownership-inference.md §4.4 — L-D3b: a borrowed
// projection STORED into an escaping Vec (inline construction — the
// helper-fn variant is the RED leak guard below): the store materializes
// (values read back correctly), root intact, balance iteration-independent.
// GREEN at draft.
#[test]
fn l_d3b_projection_stored_into_escaping_vec_sustained() {
    let template = "(import [primitives [*]])\n\
        (defn spin [:Int n :Int acc v]\n\
        \x20 (if (eq-i64 n 0) acc\n\
        \x20   (spin (sub-i64 n 1)\n\
        \x20     (add-i64 acc (add-i64 (str-len (vec-get (vec-push [] (vec-get v 0)) 0)) (vec-len v))) v)))\n\
        (defn main [] (Pure (spin {N} 0 [\"hello\" \"bb\"])))\n";
    let out = run_program(&template.replace("{N}", "500"));
    assert_exit_value(out, 500 * (5 + 2));
    assert_iteration_independent_imbalance(template, "L-D3b");
}

// spec: spec/12-runtime.md §12.2 — reference counting frees a value when its
// last reference is released: a fresh Vec RETURNED from a (generic) user fn
// and consumed by an inline vec op at the call site must be released after
// the read. DEFECT DISCOVERED AT S102 DRAFTING (failing-not-ignored; this
// guard is the record): the returned Vec leaks — exactly ONE alloc per call
// (RC_STATS imbalance 5 at N=5, 20 at N=20; the inline-constructed sibling
// above is balanced, and a NON-generic helper returning a fresh Vec of
// Strings is balanced too — the leak keys on the generic-helper-returned
// temp consumed by the inline op). 0474-adjacent class (vec-op caller
// handling / emit_vec_drop_if_temporary never sees a call-result temp).
// Owner /backend — rides the B3.1 fn_as_value/COW seam rework. Reduced
// 2026-07-03: Int elements, 5 lines, no strings needed.
#[test]
fn vec_returned_from_generic_fn_consumed_by_vec_op_releases_temp() {
    let template = "(import [primitives [*]])\n\
        (defn stash [v] (vec-push [] (vec-get v 0)))\n\
        (defn spin [:Int n :Int acc v]\n\
        \x20 (if (eq-i64 n 0) acc\n\
        \x20   (spin (sub-i64 n 1) (add-i64 acc (vec-get (stash v) 0)) v)))\n\
        (defn main [] (Pure (spin {N} 0 [7 8])))\n";
    // Behavioral leg is green (values correct); the leak is the defect.
    let out = run_program(&template.replace("{N}", "20"));
    assert_exit_value(out, 20 * 7);
    assert_iteration_independent_imbalance(template, "generic-fn-returned vec temp");
}

// spec: tests/plan/s100-ownership-verification.md §3.3 — L-D3c: a borrowed
// capture crossing a SUSPENSION (auto-sparked divide-and-conquer args under
// lenient eval — the ParBind/LaunchContinue class; the R6/S98-0486 UAF
// site). The shared Vec is read inside every sparked leaf; 256 leaves,
// values asserted. GREEN at draft; the standing launched-strand fences
// (tests/launch_grid_corrupt.rs, tests/launch_vec_send_corrupt.rs) remain
// this lane's floor per §3.4 L-C1.
#[test]
fn l_d3c_borrowed_capture_crosses_suspension_sustained() {
    let src = "(import [primitives [*]])\n\
        (defn leaf [v :Int i] (str-len (vec-get v 0)))\n\
        (defn mid-of [:Int lo :Int hi] (add-i64 lo (div-i64 (sub-i64 hi lo) 2)))\n\
        (defn reduce-range [v :Int lo :Int hi]\n\
        \x20 (if (eq-i64 (sub-i64 hi lo) 1) (leaf v lo)\n\
        \x20   (let [m (mid-of lo hi)]\n\
        \x20     (add-i64 (reduce-range v lo m) (reduce-range v m hi)))))\n\
        (defn main [] (Pure (reduce-range [\"hello\" \"bb\"] 0 256)))\n";
    let out = run_program(src);
    // 256 leaves × str-len "hello" = 1280; mod 256 = 0.
    assert_exit_value(out, 256 * 5);
}

// spec: design/typecheck/ownership-inference.md §4.2 — L-D3d: the
// root-release-ordering shape (rule 4; the Sprint-61 aliased-COW class one
// level up): the root vec reaches its syntactic last use (`vec-set`) WHILE a
// projected borrow of an element is still live; the projected value must
// read correctly after the write. Small, CLIF-inspectable. GREEN at draft.
#[test]
fn l_d3d_root_last_use_write_with_live_projected_borrow() {
    let src = "(import [primitives [*]])\n\
        (defn probe []\n\
        \x20 (let [v [\"aa\" \"bbb\"]\n\
        \x20       e (vec-get v 0)\n\
        \x20       w (vec-set v 0 \"cccc\")]\n\
        \x20   (add-i64 (str-len e) (str-len (vec-get w 0)))))\n\
        (defn main [] (Pure (probe)))\n";
    let out = run_program(src);
    // e must still read "aa" (2) after the COW write; w[0] is "cccc" (4).
    assert_exit_value(out, 2 + 4);
}

// spec: tests/plan/s100-ownership-verification.md §3.3 — L-D3f: NO FALSE
// ELISION, asserted on the summary itself via Hook H5's classification dump:
// a param the callee RETURNS must not be summarised Borrowed. RED on HEAD —
// H5 (`CRANELISP_OWNERSHIP_TRACE`) does not exist until B2 CS-4
// (/typecheck); this failing smoke is the loud signal the hook is owed.
// When H5 lands, tighten the needle to its ratified verdict grammar.
#[test]
fn l_d3f_stored_param_not_summarised_borrowed() {
    let out = Cranelisp::new()
        .run("user.cl")
        .user(
            "(import [primitives [*]])\n\
             (defn keepit [s] s)\n\
             (defn main [] (Pure (str-len (keepit \"abc\"))))\n",
        )
        .env("CRANELISP_OWNERSHIP_TRACE", "1")
        .output();
    assert!(
        out.stderr.contains("keepit"),
        "CRANELISP_OWNERSHIP_TRACE must dump a per-fn ownership verdict for \
         `keepit` (Hook H5, typecheck §11 — owed at B2 CS-4; L-D3f then \
         asserts its param is NOT Borrowed: it flows out through the \
         return). stderr:\n{}",
        out.stderr
    );
}

// =============================================================================
// L-D3e — the declared-fact-table row tests, generated per row from the
// ring2-rc.md §3.3 extern-consumption audit (the CS-B seed table,
// design/typecheck/ownership-inference.md §9.1). For every row a behavioral
// guard: the Var arg SURVIVES the call, is USABLE AFTER, and balances — so a
// mis-declared row (says only-read, actually retains/frees) fails a test
// rather than corrupting silently. All rows GREEN at draft (Decision-24
// caller-inc/callee-dec nets zero for Var args).
// =============================================================================

/// Row driver: `expr` uses the String var `s` once; `reuse` reads `s` after.
/// Result = expr-value + str-len(s) per iteration.
fn fact_row_string(row: &str, expr: &str, per_iter: i64) {
    let template = format!(
        "(import [primitives [*]])\n\
         (defn spin [:Int n :Int acc :String s]\n\
         \x20 (if (eq-i64 n 0) acc\n\
         \x20   (spin (sub-i64 n 1) (add-i64 acc (add-i64 {expr} (str-len s))) s)))\n\
         (defn main [] (Pure (spin {{N}} 0 \"Hello\")))\n"
    );
    let out = run_program(&template.replace("{N}", "200"));
    assert_exit_value(out, 200 * (per_iter + 5));
    assert_iteration_independent_imbalance(&template, row);
}

// spec: design/typecheck/ownership-inference.md §9.1 — fact-table row
// `str-len: [Borrowed(analysis)/Consumed] → Fresh(Int)`.
#[test]
fn fact_row_str_len_arg_survives_and_balances() {
    fact_row_string("str-len", "(str-len s)", 5);
}

// spec: design/typecheck/ownership-inference.md §9.1 — row `str-eq` (both
// params only-read; audit row "dec both").
#[test]
fn fact_row_str_eq_arg_survives_and_balances() {
    fact_row_string("str-eq", "(if (str-eq s \"Hello\") 1 0)", 1);
}

// spec: design/typecheck/ownership-inference.md §9.1 — row `substring`
// (only-read s, Fresh result).
#[test]
fn fact_row_substring_arg_survives_and_balances() {
    fact_row_string("substring", "(str-len (substring s 0 2))", 2);
}

// spec: design/typecheck/ownership-inference.md §9.1 — row `char-at`.
#[test]
fn fact_row_char_at_arg_survives_and_balances() {
    fact_row_string("char-at", "(str-len (char-at s 1))", 1);
}

// spec: design/typecheck/ownership-inference.md §9.1 — row `contains?`.
#[test]
fn fact_row_contains_arg_survives_and_balances() {
    fact_row_string("contains?", "(if (contains? s \"ell\") 1 0)", 1);
}

// spec: design/typecheck/ownership-inference.md §9.1 — rows `starts-with?` /
// `ends-with?`.
#[test]
fn fact_row_starts_ends_with_arg_survives_and_balances() {
    fact_row_string(
        "starts-with?/ends-with?",
        "(add-i64 (if (starts-with? s \"He\") 1 0) (if (ends-with? s \"lo\") 1 0))",
        2,
    );
}

// spec: design/typecheck/ownership-inference.md §9.1 — rows `to-upper` /
// `to-lower` / `trim` (only-read, Fresh results).
#[test]
fn fact_row_case_and_trim_arg_survives_and_balances() {
    fact_row_string(
        "to-upper/to-lower/trim",
        "(add-i64 (str-len (to-upper s)) (add-i64 (str-len (to-lower s)) (str-len (trim s))))",
        15,
    );
}

// spec: design/typecheck/ownership-inference.md §9.1 — row `str-concat`
// (Owned/Consumed ×2 → Fresh; the CONSUMED-row control: consuming rows must
// ALSO leave Var args usable — the caller inc covers the callee dec).
#[test]
fn fact_row_str_concat_consumed_row_var_still_usable() {
    fact_row_string("str-concat", "(str-len (str-concat s \"!\"))", 6);
}

// spec: design/typecheck/ownership-inference.md §9.1 — row
// `string-identity: [Owned] → AliasOf(0)` (the audit's one alias case).
#[test]
fn fact_row_string_identity_alias_row_var_still_usable() {
    fact_row_string("string-identity", "(str-len (string-identity s))", 5);
}

// spec: design/typecheck/ownership-inference.md §9.1 — S103 0510 write-path row
// `neq-string` (the `!=` counterpart of `str-eq`; both params only-read, Fresh
// Bool result). Extends the L-D3e per-declared-fact-row behavioral guards with
// the row FIXME 0510 registers as a ring1 primitive so it can carry declared
// facts (SPRINT.md §0510 ruled option (a)). RED-until-the-row-exists (probed
// 2026-07-05): `neq-string` is shim-only today (`neq-string` export exists in
// cranelisp-primitives but is NOT a resolvable `PrimitiveDef` entry) — the call
// fails typecheck with `undefined variable: neq-string`. When 0510 registers it
// as a ring1 primitive, the symbol resolves AND this behavioral guard asserts
// the declared facts are sound: the Var arg SURVIVES the call, is USABLE after
// (str-len), and the heap balances. A row that then mis-declares (says
// only-read, actually retains/frees a comparand) fails this test rather than
// corrupting silently. `s` = "Hello"; `(neq-string s "world")` is true ⇒ 1 per
// iteration (per_iter 1 + str-len 5 = 6).
#[test]
fn fact_row_neq_string_arg_survives_and_balances() {
    fact_row_string("neq-string", "(if (neq-string s \"world\") 1 0)", 1);
}

// spec: design/typecheck/ownership-inference.md §9.1 — 0510 symmetry control:
// `neq-string` must leave BOTH string comparands usable, mirroring the
// `fact_row_str_eq` row (uniqueness is about the result, not the comparands —
// design §14.1 watch-item). Here the SECOND comparand is also a live var `t`
// re-read after the call. RED-until-0510 (undefined variable today); when the
// row lands, fails if a declared fact wrongly consumes either comparand.
#[test]
fn fact_row_neq_string_both_comparands_survive() {
    let out = run_program(
        "(import [primitives [*]])\n\
         (defn spin [:Int n :Int acc :String s :String t]\n\
         \x20 (if (eq-i64 n 0) acc\n\
         \x20   (spin (sub-i64 n 1)\n\
         \x20     (add-i64 acc (add-i64 (if (neq-string s t) 1 0)\n\
         \x20                           (add-i64 (str-len s) (str-len t)))) s t)))\n\
         (defn main [] (Pure (spin 200 0 \"Hello\" \"world\")))\n",
    );
    // per iter: neq ⇒ 1; str-len "Hello" 5 + str-len "world" 5 = 10; total 11.
    assert_exit_value(out, 200 * 11);
    assert_iteration_independent_imbalance(
        "(import [primitives [*]])\n\
         (defn spin [:Int n :Int acc :String s :String t]\n\
         \x20 (if (eq-i64 n 0) acc\n\
         \x20   (spin (sub-i64 n 1)\n\
         \x20     (add-i64 acc (add-i64 (if (neq-string s t) 1 0)\n\
         \x20                           (add-i64 (str-len s) (str-len t)))) s t)))\n\
         (defn main [] (Pure (spin {N} 0 \"Hello\" \"world\")))\n",
        "neq-string both-comparands",
    );
}

// spec: design/typecheck/ownership-inference.md §9.3 — rows `vec-len` (extern
// leaf, Borrowed-analysis) and `vec-get` (inline projection vocabulary:
// params [Borrowed], result ProjectionOf(0)).
#[test]
fn fact_row_vec_len_and_vec_get_root_survives_and_balances() {
    let template = "(import [primitives [*]])\n\
        (defn spin [:Int n :Int acc v]\n\
        \x20 (if (eq-i64 n 0) acc\n\
        \x20   (spin (sub-i64 n 1)\n\
        \x20     (add-i64 acc (add-i64 (vec-len v) (str-len (vec-get v 1)))) v)))\n\
        (defn main [] (Pure (spin {N} 0 [\"aa\" \"bbb\"])))\n";
    let out = run_program(&template.replace("{N}", "200"));
    assert_exit_value(out, 200 * (2 + 3));
    assert_iteration_independent_imbalance(template, "vec-len/vec-get");
}

// =============================================================================
// L-C2 — stack-slot behavioural lanes (backend §12.3). At draft these are
// the behavioral halves only (GREEN); the counter-attribution halves key on
// Hook H2 and activate at B3.4. ASan legs: tests/scripts/asan/ (wave gates).
// =============================================================================

// spec: design/backend/ownership-codegen.md §13.2 — L-C2(a) behavioral half:
// an allocation in a TCO loop body flowing into the recur args survives 10k
// iterations with correct values (the back-edge shape that must NOT
// stack-allocate once B3.4 lands; the negative is then asserted via the H2
// stack-slot-hit counter). GREEN at draft.
#[test]
fn l_c2a_tco_backedge_allocation_flows_into_recur_args_10k() {
    let src = "(import [primitives [*]])\n\
        (defn spin [:Int n :String s]\n\
        \x20 (if (eq-i64 n 0) (str-len s)\n\
        \x20   (spin (sub-i64 n 1) (substring (str-concat s \"ab\") 0 3))))\n\
        (defn main [] (Pure (spin 10000 \"xy\")))\n";
    let out = run_program(src);
    assert_exit_value(out, 3);
}

// spec: design/backend/ownership-codegen.md §13.2 — L-C2(b) behavioral half:
// sparked branches read a parent-frame value, sustained (the
// spark-reads-parent-stack-slot shape once B3.4 lands). GREEN at draft.
#[test]
fn l_c2b_sparked_branches_read_parent_value_sustained() {
    let src = "(import [primitives [*]])\n\
        (defn leaf [v :Int i] (add-i64 (vec-get v 0) i))\n\
        (defn mid-of [:Int lo :Int hi] (add-i64 lo (div-i64 (sub-i64 hi lo) 2)))\n\
        (defn rr [v :Int lo :Int hi]\n\
        \x20 (if (eq-i64 (sub-i64 hi lo) 1) (leaf v lo)\n\
        \x20   (let [m (mid-of lo hi)] (add-i64 (rr v lo m) (rr v m hi)))))\n\
        (defn main [] (Pure (rr [7] 0 128)))\n";
    let out = run_program(src);
    // sum(i=0..127) (7 + i) = 128*7 + 127*128/2 = 896 + 8128 = 9024; mod 256 = 64.
    assert_exit_value(out, 9024);
}

// =============================================================================
// Owed-observability hook smokes (qa plan §6 gaps G-2/G-3/G-4; s100 plan
// §3.7). RED at draft — the loud signal each hook is owed in its named wave.
// =============================================================================

// spec: design/backend/ownership-codegen.md §13.2 — Hook H2: per-mechanism
// stat counters (stack-slot hits, reuse hit/miss, non-atomic op share) in
// the RC-stats surface. RED on HEAD (/backend, B3 change-sets; gate-blocking
// for I-G3/I-G7). Needle is the counter FAMILY name; tighten to the ratified
// grammar when H2 lands.
#[test]
fn h2_rc_stats_reports_per_mechanism_counters() {
    let (out, _) = run_with_rc_stats(
        "(import [primitives [*]])\n\
         (defn main [] (Pure (str-len \"abc\")))\n",
    );
    let stats_line = out
        .stderr
        .lines()
        .find(|l| l.contains("[RC_STATS]"))
        .unwrap_or("")
        .to_string();
    assert!(
        stats_line.contains("stack_slot"),
        "Hook H2 (per-mechanism counters — stack-slot hits, reuse hit/miss, \
         non-atomic share) is owed in the B3 change-sets (/backend); the \
         RC_STATS line carries no per-mechanism counters yet: {stats_line}"
    );
}

// spec: design/backend/ownership-codegen.md §13.2 — Hook H3: per-extern
// adaptation-pair attribution in CRANELISP_RC_STATS (needed by the L-D5
// sibling-funding decision rule — report-grade, not gate-blocking).
// RE-DISPOSITIONED → increment II (S102, /dev for /backend): per-extern
// attribution needs a runtime name-keyed tally + per-extern emitted hooks that
// ride the L-D5 sibling-expansion (str-len$borrowed, §9.2) — increment-II work,
// not a cheap fall-out of H2's codegen-time counters. Stays RED as the owed
// signal; see ledger.md #22 for the deferral rationale + target increment.
#[test]
fn h3_rc_stats_reports_per_extern_adaptation_pairs() {
    let (out, _) = run_with_rc_stats(
        "(import [primitives [*]])\n\
         (defn main [] (Pure (str-len \"abc\")))\n",
    );
    assert!(
        out.stderr.contains("str-len"),
        "Hook H3 (per-extern adaptation-pair attribution) is owed with the B3 \
         intrinsics-seam work (/backend); RC_STATS carries no per-extern \
         attribution yet. stderr:\n{}",
        out.stderr
    );
}

// spec: tests/plan/s100-ownership-verification.md §3.7 — Hook H5:
// `CRANELISP_OWNERSHIP_TRACE` per-cluster summary + per-site verdict dump.
// RED on HEAD (/typecheck, B2 CS-4; gate-blocking for I-G3 and L-D3f).
#[test]
fn h5_ownership_trace_emits_verdicts() {
    let out = Cranelisp::new()
        .run("user.cl")
        .user(
            "(import [primitives [*]])\n\
             (defn reader [:String s] (str-len s))\n\
             (defn main [] (Pure (reader \"abc\")))\n",
        )
        .env("CRANELISP_OWNERSHIP_TRACE", "1")
        .output();
    assert!(
        !out.stderr.is_empty() && out.stderr.contains("reader"),
        "Hook H5 (CRANELISP_OWNERSHIP_TRACE) is owed at B2 CS-4 (/typecheck): \
         the trace must dump a per-fn ownership verdict naming `reader`. \
         stderr:\n{}",
        out.stderr
    );
}

// =============================================================================
// L-B1 in-suite smoke — single-module golden compared in nextest, so the
// canonical suite catches gross emission breakage between wave-gate script
// runs (tests/scripts/clif_golden.sh is the full-corpus lane).
// =============================================================================

// spec: design/backend/ownership-codegen.md §13.1 — the L-B1 smoke: the
// smallest corpus entry (06_tco_loop) dumps CLIF byte-identical to its
// committed golden (frames sorted module::symbol, byte-verbatim, no
// canonicalization). RED on HEAD: the golden does not exist until the Wave-3
// B0-be capture change-set commits it (tests/fixtures/clif_baseline/
// MANIFEST.md §Capture contract) — this smoke is that wave's in-suite
// acceptance and flips green with the capture.
#[test]
fn clif_golden_single_module_smoke() {
    let golden_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/clif_baseline/golden/06_tco_loop.clif");
    let golden = std::fs::read_to_string(&golden_path).unwrap_or_else(|e| {
        panic!(
            "L-B1 golden missing at {path} ({e}) — the B0-be capture change-set \
             (Wave 3, /dev backend) commits it via `tests/scripts/clif_golden.sh \
             capture` per tests/fixtures/clif_baseline/MANIFEST.md",
            path = golden_path.display()
        )
    });

    let corpus = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/clif_baseline/corpus/06_tco_loop.cl"),
    )
    .expect("corpus fixture 06_tco_loop.cl");
    // `--no-cache` (Wave 3R, review F4): structurally eliminates the
    // nice-worker `.o` cache-write pass, so each symbol dumps exactly ONCE
    // (the JIT pass — the pass the goldens pinned). The env_remove set is
    // the MANIFEST §Capture contract pin list — every emission-affecting
    // toggle must be absent regardless of the ambient runner env (review
    // F2: CAPTURE_BORROW was a live emission hole; RC_DEC_CHECK/RC_STATS
    // gate extra RC emission; NO_IO_SCHEDULE reshapes bind chains
    // pre-typecheck) — plus the compile-time trace vars, which write to
    // stderr, the dump channel.
    let out = Cranelisp::new()
        .run("user.cl")
        .user(&corpus)
        .cli_flag("--no-cache")
        .env("CRANELISP_CODEGEN_DUMP", "*")
        .env_remove("CRANELISP_NO_OWNERSHIP")
        .env_remove("CRANELISP_NO_LENIENT")
        .env_remove("CRANELISP_CAPTURE_BORROW")
        .env_remove("CRANELISP_NONATOMIC_RC")
        .env_remove("CRANELISP_RC_STATS")
        .env_remove("CRANELISP_RC_DEC_CHECK")
        .env_remove("CRANELISP_NO_IO_SCHEDULE")
        .env_remove("CRANELISP_RC_TRACE")
        .env_remove("CRANELISP_CODEGEN_TRACE")
        .env_remove("CRANELISP_GOT_TRACE")
        .env_remove("CRANELISP_MODULE_TRACE")
        .env_remove("CRANELISP_SCHEDULER_TRACE")
        .env_remove("CRANELISP_IO_TRACE")
        .output();

    // Extract + sort frames exactly as the script does (module::symbol,
    // byte-verbatim bodies). CRANELISP_CODEGEN_DUMP frames arrive on
    // STDERR (backend lib.rs) — stdout is the program's own output.
    // NOTE (review F6): this extraction mirrors the Python one in
    // tests/scripts/clif_golden.sh dump() — keep the two in lockstep; a
    // THIRD consumer is the bar for unifying them into one tool.
    let re = regex::Regex::new(r"(?s); === CLIF (\S+) ===\n.*?; === end CLIF (\S+) ===\n").unwrap();
    let mut frames: std::collections::BTreeMap<String, String> = Default::default();
    for cap in re.captures_iter(&out.stderr) {
        assert_eq!(
            &cap[1], &cap[2],
            "malformed CLIF frame: start/end symbol names disagree \
             (interleaved or truncated dump); stderr:\n{}",
            out.stderr
        );
        let prev = frames.insert(cap[1].to_string(), cap[0].to_string());
        assert!(
            prev.is_none(),
            "DUPLICATE FRAME: {} — under --no-cache each symbol dumps \
             exactly once (JIT pass); a second frame means the nice-worker \
             .o cache-write pass leaked into the capture (config drift). \
             Hard error — do NOT dedup (review F4).",
            &cap[1]
        );
    }
    let dumped: String = frames.into_values().collect();
    assert!(
        !dumped.is_empty(),
        "no CLIF frames captured from CRANELISP_CODEGEN_DUMP — the \
         empty-vs-empty false-green class (S102 Wave 1, review F3); stderr:\n{}",
        out.stderr
    );
    assert_eq!(
        dumped, golden,
        "toggle-off CLIF of corpus entry 06_tco_loop diverged from the \
         golden (L-B1 zero-diff gate; scoped re-baseline required if this \
         change-set is emission-affecting — MANIFEST.md §Capture contract)"
    );
}

// =============================================================================
// S111 §A.4 — Fence 3: declared-fact reachability TWINS (the a3 leg).
//
// The gap `ownership-inference.md` §3.7 names: `ClusterEnv` resolves callees
// via the fallback-LESS `resolve_terminal_entry_and_home`, so a declared leaf
// fact (`vec-len` param → `Borrowed`) is reachable through an EXPLICIT-import
// chain but SILENTLY DEAD for prelude-fallback modules. The twin fixture (one
// invariant — "the vec's rc_inc is iteration-INDEPENDENT because the param is
// borrowed" — two provenances, SAME assertion): the explicit-import leg is the
// GREEN control that VERIFIES facts are reachable at all (the escalation gate:
// if it were RED the gap would be wider than §3.7 states); the prelude-fallback
// leg is RED until the a3 fix (prelude-fallback-aware ownership envs), landing
// with the schema-20 change-set (CS-5).
//
// Measured at HEAD (2026-07-17): explicit rc_inc = 1 at N∈{50,1000} (O(1));
// prelude-fallback rc_inc = 51 → 1001 (O(K)). The signal is the per-call inc,
// NOT alloc/dealloc balance — a borrowed param skips the inc; an Owned (the
// conservative default when the fact is unreachable) incs the vec every call.
// =============================================================================

/// Parse `rc_inc=N` from the `[RC_STATS]` exit line (stderr).
fn rc_inc_count(stderr: &str) -> i64 {
    let line = stderr
        .lines()
        .find(|l| l.contains("[RC_STATS]"))
        .unwrap_or_else(|| panic!("no [RC_STATS] line on stderr: {stderr}"));
    line.split_whitespace()
        .find_map(|tok| tok.strip_prefix("rc_inc="))
        .and_then(|v| v.parse().ok())
        .unwrap_or_else(|| panic!("no rc_inc= field in RC_STATS line: {line}"))
}

/// Run a `{N}`-templated program under `--run` with the PrimitivesOnly prelude
/// (so non-`vec-len` primitives + `Pure` resolve) and RC_STATS on, returning
/// the vec's rc_inc count.
fn vlen_loop_rc_inc(user: &str, n: i64) -> i64 {
    let out = Cranelisp::new()
        .run("user.cl")
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .env("CRANELISP_RC_STATS", "1")
        .user(&user.replace("{N}", &n.to_string()))
        .output();
    rc_inc_count(&out.stderr)
}

// The vec `[1 2 3]` is bound once and passed as a borrowed param to a fn that
// only READS it (`vec-len`) across a K-iteration loop. A borrowed `vec-len`
// param ⇒ no per-call inc on the vec ⇒ rc_inc iteration-independent.
const F3_EXPLICIT: &str = "(import [primitives [vec-len]])\n\
    (defn use-vlen [v] (vec-len v))\n\
    (defn spin [:Int n :Int acc v]\n\
    \x20 (if (eq-i64 n 0) acc\n\
    \x20   (spin (sub-i64 n 1) (add-i64 acc (use-vlen v)) v)))\n\
    (defn main [] (Pure (spin {N} 0 [1 2 3])))\n";

// IDENTICAL program with NO explicit `vec-len` import: `vec-len` is reached
// through the implicit prelude fallback (spec/08-modules.md §8.6.4).
const F3_PRELUDE_FALLBACK: &str = "(defn use-vlen [v] (vec-len v))\n\
    (defn spin [:Int n :Int acc v]\n\
    \x20 (if (eq-i64 n 0) acc\n\
    \x20   (spin (sub-i64 n 1) (add-i64 acc (use-vlen v)) v)))\n\
    (defn main [] (Pure (spin {N} 0 [1 2 3])))\n";

// CW-F3a — explicit-import control (the declared-fact-reachability PROBE). The
// borrowed `vec-len` fact IS reachable through the explicit-import chain today,
// so the vec's rc_inc is iteration-independent. GREEN at HEAD; if this ever
// goes RED the reachability gap is wider than §3.7 states — escalate to /arch
// BEFORE the ownership wave.
// spec: design/arch/ownership-inference.md §3.7 — declared-fact reachability
// (a3 leg); the explicit-chain provenance (spec/08-modules.md §8.6.4).
#[test]
fn borrowed_declared_primitive_explicit_import_no_percall_rc() {
    let small = vlen_loop_rc_inc(F3_EXPLICIT, 50);
    let large = vlen_loop_rc_inc(F3_EXPLICIT, 1000);
    assert!(
        (large - small).abs() <= 2,
        "explicit-import `vec-len` borrowed fact MUST be reachable — the vec's \
         rc_inc must be iteration-INDEPENDENT (O(1)); got N=50 → {small}, \
         N=1000 → {large}. If this is RED the declared-fact reachability gap is \
         WIDER than ownership-inference.md §3.7 states (explicit chain does not \
         reach facts either) — ESCALATE to /arch before the ownership wave."
    );
}

// CW-F3b — prelude-fallback sibling. The IDENTICAL borrowed-`vec-len` program,
// vec-len reached via the implicit prelude fallback, does NOT reach the
// declared fact (`ClusterEnv` resolves via the fallback-less terminal lookup),
// so `vec-len` defaults to the conservative Owned and incs the vec every call.
// RED at HEAD (rc_inc 51 → 1001); flips GREEN at the a3 prelude-fallback-aware
// ownership envs (schema-20 change-set, CS-5). This is the fence that would
// have caught "declared facts silently dead in production".
// spec: design/arch/ownership-inference.md §3.7 — declared-fact reachability
// (a3 leg); the prelude-fallback provenance (spec/08-modules.md §8.6.4).
// defect: class=prelude-scope-miss locus=crates/cranelisp-typecheck/src/ownership/fixpoint.rs (ClusterEnv resolve_terminal_entry_and_home has no prelude fallback) found=S110 owner=/dev
#[test]
fn borrowed_declared_primitive_prelude_fallback_no_percall_rc() {
    let small = vlen_loop_rc_inc(F3_PRELUDE_FALLBACK, 50);
    let large = vlen_loop_rc_inc(F3_PRELUDE_FALLBACK, 1000);
    assert!(
        (large - small).abs() <= 2,
        "prelude-fallback `vec-len` borrowed fact MUST be reachable — the vec's \
         rc_inc must be iteration-INDEPENDENT (O(1)); got N=50 → {small}, \
         N=1000 → {large} (scales with N ⇒ the declared fact is unreachable via \
         the prelude fallback, the exact §3.7 a3 gap). Flips GREEN when the \
         ownership envs become prelude-fallback-aware (schema-20 change-set)."
    );
}
