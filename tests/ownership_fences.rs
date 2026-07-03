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

use helpers::e2e::Cranelisp;

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
/// Documented tolerance (the fence spec's "± documented baseline",
/// s100-ownership-verification.md §3.2): |delta| ≤ 2. The at-exit
/// `[RC_STATS]` accounting exhibits a ±1 jitter under parallel suite load
/// (one dealloc racing the stats print at process exit — observed at S102
/// drafting, N-independent: 0 vs 1 across repeats, standalone runs 20/20
/// stable; recorded in the S102 stage-1 ledger entry). Any genuine
/// per-iteration leak exceeds the tolerance by orders of magnitude.
fn assert_iteration_independent_imbalance(template: &str, context: &str) {
    let (_o1, small) = run_with_rc_stats(&template.replace("{N}", "50"));
    let (_o2, large) = run_with_rc_stats(&template.replace("{N}", "1000"));
    let delta = (large - small).abs();
    assert!(
        delta <= 2,
        "[{context}] alloc/dealloc imbalance scales with iteration count \
         (N=50 → {small}, N=1000 → {large}) — a per-iteration leak \
         (fence balance leg, s100-ownership-verification.md §3.2)"
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

// spec: design/arch/ownership-inference.md §9.3 — S5 behavioral + balance
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

// spec: design/typecheck/ownership-inference.md §12.7 — L-D3c: a borrowed
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

// spec: design/typecheck/ownership-inference.md §12.7 — L-D3f: NO FALSE
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
// sibling-funding decision rule — report-grade, not gate-blocking). RED on
// HEAD (/backend, B3 — or re-dispositioned if the sibling-expansion decision
// defers it to increment II; annotate the ledger entry either way).
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

// spec: design/typecheck/ownership-inference.md §11 — Hook H5:
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
    let out = Cranelisp::new()
        .run("user.cl")
        .user(&corpus)
        .env("CRANELISP_CODEGEN_DUMP", "*")
        .env_remove("CRANELISP_NO_OWNERSHIP")
        .output();

    // Extract + sort frames exactly as the script does (module::symbol,
    // byte-verbatim bodies, duplicate frames dedup to last occurrence).
    let re = regex::Regex::new(
        r"(?s); === CLIF (\S+) ===\n.*?; === end CLIF (\S+) ===\n",
    )
    .unwrap();
    let mut frames: std::collections::BTreeMap<String, String> = Default::default();
    for cap in re.captures_iter(&out.stdout) {
        if cap[1] == cap[2] {
            frames.insert(cap[1].to_string(), cap[0].to_string());
        }
    }
    let dumped: String = frames.into_values().collect();
    assert!(
        !dumped.is_empty(),
        "no CLIF frames captured from CRANELISP_CODEGEN_DUMP; stdout:\n{}",
        out.stdout
    );
    assert_eq!(
        dumped, golden,
        "toggle-off CLIF of corpus entry 06_tco_loop diverged from the \
         golden (L-B1 zero-diff gate; scoped re-baseline required if this \
         change-set is emission-affecting — MANIFEST.md §Capture contract)"
    );
}
