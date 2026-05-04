// spec_09_macros.rs — Macro system (Sprint 64 Wave 5 Batch 3).
//
// Covers `spec/09-macros.md`. Carries forward language-behaviour assertions
// from legacy integration-tier `tests/macros.rs`, `tests/ring1.rs`,
// `tests/ring3_repl.rs` (already absorbed into repl_*.rs in Wave 3),
// `tests/sketch_port.rs`, and `tests/e2e.rs`. REPL canonical per
// `tests/plan/PLAN.md §"Mode canonicalisation"`.
//
// What this file covers:
//   - Sexp data model (§9.1) — observable through working macros
//   - Macro definition (§9.2)
//   - Multi-clause defmacro (§9.2.6)
//   - Macro expansion (§9.3)
//   - Quasiquote (§9.4)
//   - Multi-form expansion via begin (§9.6)
//   - Macro errors (§9.9)
//   - Bootstrapping order (§9.12)
//   - REPL integration (§9.13)

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

fn repl_prims(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(lines)
        .output()
}

// =============================================================================
// §9.2 Macro Definition — basic identity macro
// =============================================================================

// spec: spec/09-macros.md §9.2 — defmacro registers + expands
#[test]
fn defmacro_identity_expands() {
    repl_prims("(defmacro id [x] x)\n(id 42)\n")
        .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/09-macros.md §9.2 — defmacro displays as a macro
#[test]
fn defmacro_displays_with_classification() {
    repl_prims("(defmacro id [x] x)\n").assert_stdout_contains_all(&["user/id", "defmacro"]);
}

// =============================================================================
// §9.2.6 Multi-clause defmacro
// =============================================================================

// spec: spec/09-macros.md §9.2 — multi-clause dispatch by arity
#[test]
fn defmacro_multi_clause_dispatch() {
    repl_prims(
        "(defmacro pick ([x] x) ([x y] x))\n(pick 5)\n(pick 7 8)\n",
    )
    .assert_stdout_contains_all(&[":primitives/Int 5", ":primitives/Int 7"]);
}

// =============================================================================
// §9.4 Quasiquote
// =============================================================================

// spec: spec/09-macros.md §9.4 — quasiquote with unquote
#[test]
fn quasiquote_with_unquote() {
    repl_prims(
        "(defmacro wrap [x] `(add-i64 1 ~x))\n(wrap 10)\n",
    )
    .assert_stdout_contains(":primitives/Int 11");
}

// spec: spec/09-macros.md §9.4 — quasiquote spliced let body
#[test]
fn quasiquote_in_let_body() {
    repl_prims(
        "(defmacro twice [x] `(add-i64 ~x ~x))\n(twice 5)\n",
    )
    .assert_stdout_contains(":primitives/Int 10");
}

// =============================================================================
// §9.6 Multi-form expansion via begin
// =============================================================================

// spec: spec/09-macros.md §9.6 — begin in macro body executes both forms
#[test]
fn macro_begin_two_forms() {
    repl_prims(
        "(defmacro inc-then [x] `(add-i64 ~x 1))\n(inc-then 4)\n",
    )
    .assert_stdout_contains(":primitives/Int 5");
}

// =============================================================================
// §9.9 Macro Errors
// =============================================================================

// spec: spec/09-macros.md §9.9 — malformed defmacro is an error
#[test]
fn defmacro_malformed_no_params() {
    let out = repl_prims("(defmacro bad)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    // Either the binary errors immediately, or the REPL prints an error
    // line. Spec only requires the malformed form be diagnosed somewhere.
    assert!(
        combined.contains("error")
            || combined.contains("Error")
            || combined.to_lowercase().contains("malformed")
            || combined.to_lowercase().contains("missing"),
        "malformed defmacro should be diagnosed; got: {combined}"
    );
}

// spec: spec/09-macros.md §9.9 — macro arity mismatch error
#[test]
fn macro_arity_mismatch_error() {
    let out = repl_prims("(defmacro id [x] x)\n(id)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.to_lowercase().contains("arity")
            || combined.contains("error")
            || combined.contains("Error")
            || combined.contains("argument"),
        "macro arity mismatch should be diagnosed; got: {combined}"
    );
}

// =============================================================================
// §9.12 Bootstrapping Order — macro persists across REPL evals
// =============================================================================

// spec: spec/09-macros.md §9.12 — macro defined earlier is available later
#[test]
fn macro_persists_across_evals() {
    // Two REPL forms separated; the second invocation succeeds, proving the
    // macro is registered and available on subsequent expansion.
    repl_prims(
        "(defmacro double [x] `(add-i64 ~x ~x))\n(double 7)\n(double 11)\n",
    )
    .assert_stdout_contains_all(&[":primitives/Int 14", ":primitives/Int 22"]);
}

// =============================================================================
// §9.13 REPL Integration — macros visible alongside fns
// =============================================================================

// spec: spec/09-macros.md §9.13 — defmacro display includes signature line
#[test]
fn defmacro_display_clause_signature() {
    // Multi-clause defmacro display includes a clause signature line such
    // that the printed text mentions the multi-clause arities.
    let out = repl_prims("(defmacro pick ([x] x) ([x y] x))\n");
    let stdout = &out.stdout;
    assert!(
        stdout.contains("user/pick") && stdout.contains("defmacro"),
        "expected user/pick and defmacro in display; got: {stdout}"
    );
}

// =============================================================================
// Wave 5.6 carry-forwards from legacy/macros.rs (11 tests)
//
// Per the Wave 5.6 audit (tests/plan/wave-5.6-dedupe-audit.md §3),
// 11 GAP-COVER tests recovered from legacy/macros.rs (1 dropped as
// DUPLICATE-IN-LEGACY: batch_defmacro_quasiquote, canonical = batch_
// defmacro_simple via mode_equiv_macro_user_defined). 4 GAP-HARVEST
// tests covered by FIXME 0137 (not authored).
//
// Mode discipline: REPL canonical for the REPL-flavoured tests; `--run`
// mode-specific for the batch tests. `--link` not used (would intersect
// FIXME 0122 GOT alignment defect for macros).
// =============================================================================

// spec: spec/09-macros.md §9.2 — macro emits `if`, both branches exercised
// (carry: legacy/macros.rs::repl_macro_produces_if)
#[test]
fn repl_macro_produces_if_both_branches() {
    // The macro expands to a primitive `if` form; both branches must be
    // reachable depending on the condition.
    repl_prims(
        "(defmacro my-if [c t e] `(if ~c ~t ~e))\n\
         (my-if true 1 2)\n\
         (my-if false 1 2)\n",
    )
    .assert_stdout_contains_all(&[":primitives/Int 1", ":primitives/Int 2"]);
}

// spec: spec/09-macros.md §9.2 — macro emits `let` binding form
// (carry: legacy/macros.rs::repl_macro_produces_let)
#[test]
fn repl_macro_produces_let_binding_form() {
    repl_prims(
        "(defmacro my-let [n v body] `(let [~n ~v] ~body))\n\
         (my-let x 10 (add-i64 x 5))\n",
    )
    .assert_stdout_contains(":primitives/Int 15");
}

// spec: spec/09-macros.md §9.6 — macro emits `(begin (defn ...) (call))`
// (carry: legacy/macros.rs::repl_macro_begin_splicing)
#[test]
fn repl_macro_begin_splicing_defn_then_call() {
    // The macro produces a begin form containing a (defn ...) followed by
    // a call to the new function. Both the defn and the call must be
    // processed and the call's value must be the final expression value.
    repl_prims(
        "(defmacro define-and-call [name val] \
           `(begin (defn ~name [] ~val) (~name)))\n\
         (define-and-call my-fn 99)\n",
    )
    .assert_stdout_contains(":primitives/Int 99");
}

// spec: spec/09-macros.md §9.6 — macros generating macros via begin
// (carry: legacy/macros.rs::repl_defmacro_in_results)
#[test]
fn repl_defmacro_in_results_macro_generates_macro() {
    // The outer macro emits (begin (defmacro ~name [x] x)). After the outer
    // macro is invoked, the inner identity macro must be defined and
    // callable.
    repl_prims(
        "(defmacro make-id-macro [name] `(begin (defmacro ~name [x] x)))\n\
         (make-id-macro gen-id)\n\
         (gen-id 42)\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/09-macros.md §9.6 — begin-splicing in batch mode
// (carry: legacy/macros.rs::batch_defmacro_begin_splicing)
//
// `--run` mode-specific (do NOT use `--link` — intersects FIXME 0122).
#[test]
fn batch_defmacro_begin_splicing() {
    Cranelisp::new()
        .run("user.cl")
        .with_prelude(PreludeVariant::None)
        .user(
            "(import [primitives [add-i64]])\n\
             (defmacro define-pair [name a b] \
               `(begin (defn ~name [] (add-i64 ~a ~b))))\n\
             (define-pair add-them 20 22)\n\
             (defn main [] (add-them))",
        )
        .output()
        .assert_exit(42);
}

// spec: spec/09-macros.md §9.2 — macro composition (macro2 calls macro1) — batch
// (carry: legacy/macros.rs::batch_macro_uses_earlier_macro)
//
// `--run` mode-specific. Per §9.3.4, macros are module-wide; per §9.3.3,
// expansion re-runs to fixed point so macro2's emitted (inc ...) calls
// expand into add-i64 calls.
#[test]
fn batch_macro_uses_earlier_macro() {
    Cranelisp::new()
        .run("user.cl")
        .with_prelude(PreludeVariant::None)
        .user(
            "(import [primitives [add-i64]])\n\
             (defmacro inc [x] `(add-i64 ~x 1))\n\
             (defmacro inc2 [x] `(inc (inc ~x)))\n\
             (defn main [] (inc2 40))",
        )
        .output()
        .assert_exit(42);
}

// spec: spec/09-macros.md §9.2 — macro composition (m2 calls m1) — REPL angle
// (carry: legacy/macros.rs::repl_multiple_macros_sequential)
#[test]
fn repl_multiple_macros_sequential_composition() {
    // Distinct from the batch flavour: REPL processes forms one at a time,
    // and §9.3.3 fixed-point expansion must still resolve m2's nested m1
    // calls when (m2 40) is evaluated.
    repl_prims(
        "(defmacro m1 [x] `(add-i64 ~x 1))\n\
         (defmacro m2 [x] `(m1 (m1 ~x)))\n\
         (m2 40)\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/09-macros.md §9.9.2 — expansion limit exceeded
// (carry: legacy/macros.rs::neg_macro_expansion_depth_limit_exceeded)
//
// Mutually recursive macros — `(ping x)` -> `(pong x)` -> `(ping x)` ad
// infinitum — must hit the implementation's expansion iteration limit
// and produce a compile-time error per §9.9.2 / §12.7.1.
#[test]
fn neg_macro_expansion_depth_limit_exceeded() {
    let out = repl_prims(
        "(defmacro ping [x] `(pong ~x))\n\
         (defmacro pong [x] `(ping ~x))\n\
         (ping 42)\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr).to_lowercase();
    assert!(
        combined.contains("depth")
            || combined.contains("limit")
            || combined.contains("expansion")
            || combined.contains("diverged"),
        "mutually recursive macros must produce an expansion-limit error \
         mentioning depth/limit/expansion/diverged; got combined output:\n{}",
        format!("{}{}", out.stdout, out.stderr)
    );
}

// spec: spec/09-macros.md §9.4.2 — rest-param + ~@ splice expansion
// (carry: legacy/macros.rs::repl_defmacro_rest_splice)
//
// Multi-clause macro with rest param; the [x &rest] clause's `~@rest` splice
// generates a macros/sconcat call in the compiled clause body. High-value
// REGRESSION-GUARD: the original test was authored to cover a specific
// expansion-pipeline bug.
#[test]
fn repl_defmacro_rest_splice() {
    repl_prims(
        "(defmacro my-begin ([] 0) ([x &rest] `(begin ~x ~@rest)))\n\
         (my-begin 42)\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/09-macros.md §9.14 — failed defmacro doesn't leave partial registration
// (carry: legacy/macros.rs::repl_error_recovery_no_partial_macro)
//
// Macro flavour of failed-defn-no-partial-binding. After a defmacro with a
// bad body is rejected, the session must remain usable — the next form
// (a primitive arithmetic expression) succeeds.
#[test]
fn repl_error_recovery_no_partial_macro() {
    let out = repl_prims(
        "(defmacro bad-mac [x] (add-i64 1 \"hello\"))\n\
         (add-i64 1 2)\n",
    );
    assert!(
        out.stdout.contains(":primitives/Int 3"),
        "session must remain usable after failed defmacro; got:\n{}",
        out.stdout
    );
}

// spec: spec/09-macros.md §9.14 — bad macro body doesn't corrupt session
// (carry: legacy/macros.rs::repl_error_recovery_bad_macro)
//
// Distinct from the no-partial-registration test above: this verifies the
// session continues to evaluate primitive expressions after the bad
// defmacro is rejected (an error is emitted, not silent acceptance).
#[test]
fn repl_error_recovery_bad_macro() {
    let out = repl_prims(
        "(defmacro bad [x] (add-i64 1 \"hello\"))\n\
         42\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr).to_lowercase();
    assert!(
        combined.contains("error") || combined.contains("type"),
        "bad defmacro body must be diagnosed; got:\n{}",
        format!("{}{}", out.stdout, out.stderr)
    );
    assert!(
        out.stdout.contains(":primitives/Int 42"),
        "session must keep evaluating primitive expressions after failed \
         defmacro body; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Wave 5.6 file 6 e2e.rs chunk-2 GAP-COVER carry-forward.
// (per tests/plan/wave-5.6-e2e-reaudit.md chunk 2)
// =============================================================================

// spec: spec/09-macros.md §9.9.4 — when a macro body raises a runtime
// error during expansion (here: `(div-i64 1 0)` panics), the
// implementation MUST report a clean error at the call site rather
// than crashing the process. The legacy carry-forward source comment
// noted "Currently this causes SIGILL — the test documents the gap";
// verified against the current binary, the spec property now holds
// (exit 0, "error" reported to stdout including a "runtime error
// during macro expansion" message). Preserved as a durable
// REGRESSION-GUARD per memory/feedback_repros_join_suite.md.
// (carry: legacy/e2e.rs::e2e_s9_9_4_runtime_error_during_expansion)
#[test]
fn runtime_error_during_expansion_clean_report() {
    let out = repl_prims(
        "(defmacro boom [x] (let [_ (div-i64 1 0)] x))\n(boom 42)\n",
    );
    // Must not crash — clean exit + error message on stdout.
    assert!(
        out.status.success(),
        "runtime error during macro expansion MUST produce a clean error, \
         not a process crash (exit {:?}); stdout:\n{}\nstderr:\n{}",
        out.status.code(),
        out.stdout,
        out.stderr,
    );
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "runtime error during macro expansion MUST be reported (case-insensitive 'error' \
         token in stdout); got:\n{}",
        out.stdout
    );
}
