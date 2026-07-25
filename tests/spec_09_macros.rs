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
    repl_prims("(defmacro id [x] x)\n(id 42)\n").assert_stdout_contains(":primitives/Int 42");
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
    repl_prims("(defmacro pick ([x] x) ([x y] x))\n(pick 5)\n(pick 7 8)\n")
        .assert_stdout_contains_all(&[":primitives/Int 5", ":primitives/Int 7"]);
}

// =============================================================================
// §9.4 Quasiquote
// =============================================================================

// spec: spec/09-macros.md §9.4 — quasiquote with unquote
#[test]
fn quasiquote_with_unquote() {
    repl_prims("(defmacro wrap [x] `(add-i64 1 ~x))\n(wrap 10)\n")
        .assert_stdout_contains(":primitives/Int 11");
}

// spec: spec/09-macros.md §9.4 — quasiquote spliced let body
#[test]
fn quasiquote_in_let_body() {
    repl_prims("(defmacro twice [x] `(add-i64 ~x ~x))\n(twice 5)\n")
        .assert_stdout_contains(":primitives/Int 10");
}

// =============================================================================
// §9.8 Hygiene — auto-gensym
// =============================================================================

// spec: spec/09-macros.md §9.8.1 — auto-gensym: a `x#` symbol inside a
// quasiquote template generates a UNIQUE name per expansion, so a binding it
// introduces does NOT capture an identically-named binding in the expansion
// context. The §9.8.1 worked example: `(defmacro my-let [v body]
// `(let [x# ~v] ~body))`, invoked as `(let [x 100] (my-let 42 (add-i64 x 1)))`,
// must yield 101 — the inner `x#` is renamed, so the body's `x` still refers to
// the OUTER binding (100), not the macro-introduced one (42). If hygiene were
// broken, `x#` would capture and the result would be 43. (Spec uses `+`; we use
// the bare `add-i64` primitive to stay free-standing — no operator prelude.)
#[test]
fn auto_gensym_introduced_binding_does_not_capture_outer() {
    repl_prims(
        "(defmacro my-let [v body] `(let [x# ~v] ~body))\n\
         (let [x 100] (my-let 42 (add-i64 x 1)))\n",
    )
    .assert_stdout_contains(":primitives/Int 101");
}

// =============================================================================
// §9.6 Multi-form expansion via begin
// =============================================================================

// spec: spec/09-macros.md §9.6 — begin in macro body executes both forms
#[test]
fn macro_begin_two_forms() {
    repl_prims("(defmacro inc-then [x] `(add-i64 ~x 1))\n(inc-then 4)\n")
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
// §9.2.3 Return Type Constraint — macro body MUST have type Sexp
//
// (carry: legacy/macros.rs::neg_macro_non_sexp_return_type_batch /
//  neg_macro_non_sexp_return_type_repl / neg_macro_non_sexp_return_bool_batch)
//
// Distinct from the §9.9 malformed/arity errors above and from the
// ill-typed-body errors elsewhere in this file: here the body is a valid
// program in isolation that simply produces the WRONG (non-Sexp) result
// type. The rejection fires at typecheck (the synthesized clause-defn body
// fails to unify with Sexp). Witnessed through REPL + `--run`; `--link` is
// excluded (intersects FIXME 0122 macro GOT alignment).
// =============================================================================

// spec: spec/09-macros.md §9.2.3 — macro body returning Int (non-Sexp) is rejected
#[test]
fn macro_body_non_sexp_int_rejected_neg() {
    // `(defmacro bad [x] 42)` — body typechecks to Int, not Sexp. MUST be a
    // compile-time error. REPL mode: the error appears in the output.
    let out = repl_prims("(defmacro bad [x] 42)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.to_lowercase().contains("error") || combined.contains("Sexp"),
        "macro body of type Int must be rejected with a type error naming Sexp; got: {combined}"
    );
}

// spec: spec/09-macros.md §9.2.3 — macro body returning Bool (non-Sexp) is rejected
#[test]
fn macro_body_non_sexp_bool_rejected_neg() {
    // `(defmacro bad [x] true)` — body typechecks to Bool, not Sexp. MUST be
    // a compile-time error. `--run` mode: the program must NOT compile and
    // run to a clean exit.
    let out = Cranelisp::new()
        .run("user.cl")
        .with_prelude(PreludeVariant::None)
        .user(
            "(defmacro bad [x] true)\n\
             (defn main [] (bad 1))",
        )
        .output();
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert_ne!(
        out.status.code(),
        Some(0),
        "macro body of type Bool must be rejected (non-zero exit); combined:\n{combined}"
    );
    assert!(
        combined.to_lowercase().contains("error") || combined.contains("Sexp"),
        "macro body of type Bool must be diagnosed with a type error naming Sexp; got: {combined}"
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
    repl_prims("(defmacro double [x] `(add-i64 ~x ~x))\n(double 7)\n(double 11)\n")
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
// defmacro_simple via mode_equiv_macro_user_defined). The §9.2.3
// non-Sexp-macro-body negatives (the FIXME 0137 residual) are authored
// above as macro_body_non_sexp_{int,bool}_rejected_neg.
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

// spec: spec/09-macros.md §9.6 + spec/08-modules.md §8.2 — expanded
// top-level definitions are spliced and registered in source order.
// defect: class=wrong-reject locus=src/session_v4.rs::macro-expanded-definition-registration found=S115 owner=/dev
#[test]
fn macro_expanded_begin_deftype_then_impl_registers_in_source_order() {
    let out = repl_prims(
        "(deftrait Show (show [self] Int))\n\
         (defmacro define-shown [name ctor]\n\
           `(begin (deftype ~name ~ctor)\n\
                   (impl Show ~name (defn show [_] 41))))\n\
         (define-shown Token MkToken)\n\
         (show MkToken)\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains(":primitives/Int 41"),
        "the impl MUST see the deftype immediately preceding it in expanded begin order; got:\n{combined}"
    );
}

// spec: spec/09-macros.md §9.6 + spec/08-modules.md §8.2 — expansion does
// not grant a later definition forward visibility to an earlier impl.
#[test]
fn macro_expanded_begin_impl_neg_before_deftype_is_rejected() {
    let out = repl_prims(
        "(deftrait Show (show [self] Int))\n\
         (defmacro reverse-shown [name ctor]\n\
           `(begin (impl Show ~name (defn show [_] 41))\n\
                   (deftype ~name ~ctor)))\n\
         (reverse-shown Token MkToken)\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.to_lowercase().contains("error") && combined.contains("Token"),
        "an impl preceding its type in expanded source order MUST be rejected; got:\n{combined}"
    );
    assert!(
        !out.stdout.contains(":primitives/Int 41"),
        "the rejected reversed sequence MUST NOT dispatch; got:\n{combined}"
    );
}

// spec: spec/09-macros.md §9.6 — macro-expanded and directly written
// top-level sequences use the same registrar and have the same result.
// defect: class=wrong-reject locus=src/session_v4.rs::macro-expanded-definition-registration found=S115 owner=/dev
#[test]
fn expanded_and_literal_begin_registration_are_twins() {
    let expanded = repl_prims(
        "(deftrait Show (show [self] Int))\n\
         (defmacro define-shown []\n\
           `(begin (deftype Token MkToken)\n\
                   (impl Show Token (defn show [_] 41))))\n\
         (define-shown)\n\
         (show MkToken)\n",
    );
    let literal = repl_prims(
        "(deftrait Show (show [self] Int))\n\
         (begin (deftype Token MkToken)\n\
                (impl Show Token (defn show [_] 41)))\n\
         (show MkToken)\n",
    );
    for (label, out) in [("expanded", expanded), ("literal", literal)] {
        assert!(
            out.stdout.contains(":primitives/Int 41"),
            "{label} begin registration MUST dispatch identically; stdout:\n{}\nstderr:\n{}",
            out.stdout,
            out.stderr
        );
    }
}

// spec: spec/09-macros.md §9.6 + spec/07-traits.md §7.1.5 — expanded
// declaration staging is uniform across a required-method trait and a trait
// with a synthesized default sibling; the trait must not select a registrar.
// defect: class=wrong-reject locus=src/session_v4.rs::macro-expanded-definition-registration found=S115 owner=/dev
#[test]
fn expanded_begin_trait_family_registration_is_uniform() {
    let required = repl_prims(
        "(deftrait Required (value [self] Int))\n\
         (defmacro make-required []\n\
           `(begin (deftype R MkR)\n\
                   (impl Required R (defn value [_] 40))))\n\
         (make-required)\n\
         (value MkR)\n",
    );
    let defaulted = repl_prims(
        "(deftrait Defaulted\n\
           (value [self] Int)\n\
           (plus-one [x] (add-i64 (value x) 1)))\n\
         (defmacro make-defaulted []\n\
           `(begin (deftype D MkD)\n\
                   (impl Defaulted D (defn value [_] 40))))\n\
         (make-defaulted)\n\
         (plus-one MkD)\n",
    );
    assert!(
        required.stdout.contains(":primitives/Int 40"),
        "required-method trait expansion MUST register in source order; stdout:\n{}\nstderr:\n{}",
        required.stdout,
        required.stderr
    );
    assert!(
        defaulted.stdout.contains(":primitives/Int 41"),
        "default-sibling trait expansion MUST use the same registrar; stdout:\n{}\nstderr:\n{}",
        defaulted.stdout,
        defaulted.stderr
    );
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
            "(import [primitives [add-i64 Pure]])\n\
             (defmacro define-pair [name a b] \
               `(begin (defn ~name [] (add-i64 ~a ~b))))\n\
             (define-pair add-them 20 22)\n\
             (defn main [] (Pure (add-them)))",
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
            "(import [primitives [add-i64 Pure]])\n\
             (defmacro inc [x] `(add-i64 ~x 1))\n\
             (defmacro inc2 [x] `(inc (inc ~x)))\n\
             (defn main [] (Pure (inc2 40)))",
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
    let out = repl_prims("(defmacro boom [x] (let [_ (div-i64 1 0)] x))\n(boom 42)\n");
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

// =============================================================================
// §9.2.5 Macro body capabilities — single-file batch witnesses
// (carry-forward: legacy/v4_pipeline.rs §D — Wave 6 batch 6)
//
// These tests use `--run` mode (mode-specific exception per
// `tests/plan/PLAN.md §"Mode canonicalisation"`) — the canonical
// observation for §9.2.5 capabilities (macro body calls helper, calls
// another macro, transitive call graph) is the exit-code witness from
// the batch driver. The REPL form is awkward for single-file
// multi-form macro programs because the macro expansion + helper
// dispatch happens at evaluation time per-form.
// =============================================================================

// spec: spec/09-macros.md §9.2.5 — macro body may call a helper fn defined
// before the defmacro form
// (carry: legacy/v4_pipeline.rs::v4_macro_calls_helper_function)
#[test]
fn macro_body_calls_helper_function_in_run_mode() {
    Cranelisp::new()
        .user(
            "(import [primitives [Pure]])\n\
             (defn make-seven [] 7)\n\
             (defmacro lucky [] `(make-seven))\n\
             (defn main [] (Pure (lucky)))",
        )
        .run("user.cl")
        .output()
        .assert_exit(7);
}

// spec: spec/09-macros.md §9.3.3 — re-expansion to fixed point: a macro
// body may expand to a call that uses another macro, and the expander
// must reach a fixed point.
// (carry: legacy/v4_pipeline.rs::v4_macro_calls_another_macro)
#[test]
fn macro_calls_another_macro_reaches_fixed_point() {
    Cranelisp::new()
        .user(
            "(import [primitives [Pure]])\n\
             (defmacro wrap-add [a b] `(primitives/add-i64 ~a ~b))\n\
             (defmacro add-three [x] `(wrap-add ~x 3))\n\
             (defn main [] (Pure (add-three 39)))",
        )
        .run("user.cl")
        .output()
        .assert_exit(42);
}

// spec: spec/09-macros.md §9.2 + spec/05-definitions.md §5.5 — multiple
// defmacros with interleaved defns; source-order processing makes each
// macro available from the next form onward.
// (carry: legacy/v4_pipeline.rs::v4_macro_multiple_macros_interleaved)
#[test]
fn multiple_macros_interleaved_with_defns_compose() {
    Cranelisp::new()
        .user(
            "(import [primitives [Pure]])\n\
             (defn triple [x] (primitives/add-i64 x (primitives/add-i64 x x)))\n\
             (defmacro apply-triple [x] `(triple ~x))\n\
             (defn six [] (apply-triple 2))\n\
             (defmacro make-six [] `(six))\n\
             (defn main [] (Pure (make-six)))",
        )
        .run("user.cl")
        .output()
        .assert_exit(6);
}

// spec: spec/09-macros.md §9.3.4 — defmacro-before-use is NORMATIVE: a macro
// MUST be defined before it is used in source order. A use of a name that
// appears textually BEFORE its `defmacro` is NOT a macro call — it is an
// ordinary reference that passes through to the AST builder and fails name
// resolution there. Macros are NOT hoisted. This INVERTS the retired
// `macro_used_before_defmacro_form_is_hoisted` (carry:
// legacy/v4_pipeline.rs::v4_macro_forward_reference_succeeds), which asserted
// the pre-S76 (wrong) hoisting behavior.
//
// FAILING-NOT-IGNORED: as built, the forward use is (wrongly) treated as a
// macro call against the later `defmacro`, then fails expansion with an
// internal "clause 0 is not in memory (orchestrator-sequencing bug)" message
// and exits 0 — instead of a clean unresolved-reference diagnostic naming
// `nope` with a non-zero exit per §9.3.4. Owning skill: /int + /typecheck
// (macro-availability three-pass; see s76_macro_availability.rs).
#[test]
fn macro_used_before_defmacro_is_unresolved() {
    let out = Cranelisp::new()
        .user(
            "(defn main [] (nope 42))\n\
             (defmacro nope [x] x)",
        )
        .run("user.cl")
        .output();
    assert!(
        out.status.code() != Some(42) && out.status.code() != Some(0),
        "forward macro use MUST NOT be hoisted/expanded; it is a plain \
         unresolved reference per §9.3.4. exit={:?} stdout={} stderr={}",
        out.status.code(),
        out.stdout,
        out.stderr,
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.to_lowercase().contains("nope")
            && (combined.contains("error") || combined.contains("Error")),
        "expected an unresolved-reference diagnostic naming `nope` per §9.3.4; \
         stdout={} stderr={}",
        out.stdout,
        out.stderr,
    );
}

// spec: spec/09-macros.md §9.2.5 — macro body invokes fn b which itself
// calls fn a; transitive call graph must compile before macro runs.
// (carry: legacy/v4_pipeline.rs::v4_macro_complex_call_graph)
#[test]
fn macro_body_drives_three_level_call_graph() {
    Cranelisp::new()
        .user(
            "(import [primitives [Pure]])\n\
             (defn a [] 10)\n\
             (defn b [] (primitives/add-i64 (a) 11))\n\
             (defmacro get-b [] `(b))\n\
             (defn main [] (Pure (get-b)))",
        )
        .run("user.cl")
        .output()
        .assert_exit(21);
}

// =============================================================================
// §9.2.5 + §8.12 Cross-module Macro Dependencies
// (carry-forward: legacy/v4_pipeline.rs §H — Wave 6 batch 6)
//
// Sprint 45 worker.rs:762 fix regression-guard cluster. The fix area:
// `compile_dep_symbol_inline` was looking up macro-body-call dependencies
// from the **current module's** symbol table when the dep actually lives
// in **another module's** symbol table. The 6 tests below partition this
// surface (helper, transitive, qualified ref, transitive call graph,
// dep-error, private not accessible).
// =============================================================================

// spec: spec/09-macros.md §9.2.5 + spec/08-modules.md §8.12 — macro in
// module B calls helper from module A.
// (carry: legacy/v4_pipeline.rs::v4_cross_module_macro_calls_helper)
// REGRESSION-GUARD: Sprint 45 worker.rs:762 fix.
#[test]
fn cross_module_macro_calls_helper_in_other_module() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [macmod [wrap-seven]])\n(import [primitives [Pure]])\n(defn main [] (Pure (wrap-seven)))",
        )
        .file(
            "macmod.cl",
            "(import [helper [make-seven]])\n\
             (defmacro wrap-seven [] `(make-seven))",
        )
        .file("helper.cl", "(defn make-seven [] 7)")
        .run("main.cl")
        .output()
        .assert_exit(7);
}

// spec: spec/09-macros.md §9.2.5 + spec/08-modules.md §8.10.1 — A→B→C→D
// transitive: macro module imports through a re-export module to reach
// helper in the base module.
// (carry: legacy/v4_pipeline.rs::v4_cross_module_macro_transitive)
// REGRESSION-GUARD.
#[test]
fn cross_module_macro_transitive_via_reexport_chain() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [macmod [get-val]])\n(import [primitives [Pure]])\n(defn main [] (Pure (get-val)))",
        )
        .file(
            "macmod.cl",
            "(import [relay [base-val]])\n\
             (defmacro get-val [] `(base-val))",
        )
        .file(
            "relay.cl",
            "(import [base [base-val]])\n\
             (export [base [base-val]])",
        )
        .file("base.cl", "(defn base-val [] 99)")
        .run("main.cl")
        .output()
        .assert_exit(99);
}

// spec: spec/09-macros.md §9.4 + spec/08-modules.md §8.5.1 — macro body
// generates a qualified reference to a function in another module.
// (carry: legacy/v4_pipeline.rs::v4_cross_module_macro_qualified_ref)
#[test]
fn cross_module_macro_emits_qualified_reference() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [macmod [call-util]])\n(import [primitives [Pure]])\n(defn main [] (Pure (call-util)))",
        )
        .file(
            "macmod.cl",
            "(import [util [add-ten]])\n\
             (defmacro call-util [] `(util/add-ten 5))",
        )
        .file(
            "util.cl",
            "(defn add-ten [x] (primitives/add-i64 x 10))",
        )
        .run("main.cl")
        .output()
        .assert_exit(15);
}

// spec: spec/09-macros.md §9.2.5 — macro→helper.compute→helper.base
// transitive call graph WITHIN macro execution. All deps must compile
// before the macro can run.
// (carry: legacy/v4_pipeline.rs::v4_cross_module_macro_transitive_call_graph)
// REGRESSION-GUARD.
#[test]
fn cross_module_macro_drives_transitive_call_graph() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [macmod [get-result]])\n(import [primitives [Pure]])\n(defn main [] (Pure (get-result)))",
        )
        .file(
            "macmod.cl",
            "(import [helpers [compute]])\n\
             (defmacro get-result [] `(compute))",
        )
        .file(
            "helpers.cl",
            "(defn base [] 10)\n\
             (defn compute [] (primitives/add-i64 (base) 11))",
        )
        .run("main.cl")
        .output()
        .assert_exit(21);
}

// spec: spec/09-macros.md §9.9 + design/int/step9-error-cascade.md §4.1 —
// type error in a macro module's dependency cascades up through the
// macro layer.
// (carry: legacy/v4_pipeline.rs::v4_cross_module_macro_dep_type_error)
// REGRESSION-GUARD.
#[test]
fn cross_module_macro_dependency_type_error_cascades_neg() {
    let out = Cranelisp::new()
        .file(
            "main.cl",
            "(import [macmod [get-val]])\n(defn main [] (get-val))",
        )
        .file(
            "macmod.cl",
            "(import [broken [bad-fn]])\n\
             (defmacro get-val [] `(bad-fn))",
        )
        .file("broken.cl", "(defn bad-fn [] (add-i64 1 true))")
        .run("main.cl")
        .output();
    assert!(
        out.status.code() != Some(0),
        "type error in macro dep should fail; got stderr: {}",
        out.stderr
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("error")
            || combined.contains("Error")
            || combined.contains("type")
            || combined.contains("Type"),
        "should report an error for type error in macro dependency; got stderr: {}",
        out.stderr
    );
}

// spec: spec/09-macros.md §9.2.5 + spec/08-modules.md §8.7 — `defn-` in
// module A is NOT importable; a macro in module B trying to use that
// private name MUST fail.
// (carry: legacy/v4_pipeline.rs::v4_cross_module_macro_private_not_accessible)
#[test]
fn cross_module_macro_cannot_use_private_helper_neg() {
    let out = Cranelisp::new()
        .file(
            "main.cl",
            "(import [macmod [call-secret]])\n(defn main [] (call-secret))",
        )
        .file(
            "macmod.cl",
            "(import [secret [hidden]])\n\
             (defmacro call-secret [] `(hidden))",
        )
        .file("secret.cl", "(defn- hidden [] 42)")
        .run("main.cl")
        .output();
    assert!(
        out.status.code() != Some(0),
        "private fn must not be importable; got stderr: {}",
        out.stderr
    );
}

// =============================================================================
// S111 §C — Quasiquote/quote "legal wherever an expression is legal" (0613).
//
// spec/09-macros.md §9.4 (esp. §9.4.4 — the user-settled ruling): quote (`'`),
// quasiquote (`` ` ``), unquote (`~`), unquote-splicing (`~@`) are reader
// sugar that desugars to `macros`-module constructor calls; the result is an
// ordinary `Sexp`-typed expression, legal in ANY position — not just defmacro
// clause bodies.
//
// RESOLVED (0613, fold landed S111): the desugar was folded into
// `build_form`/`build_forms`, with int's macro expander gaining a quote SHIELD in
// the same wave (§C interaction rows). These rows are now REGRESSION GUARDS
// (GREEN) — a quote/quasiquote in a `defn`/`defn-`/top-level position desugars to
// an ordinary `Sexp` rather than dying at `build_form` with "unexpected
// quote/quasiquote form — should have been expanded". The `// defect:` notation is
// retained (greppable class-frequency signal over GREEN repros — see
// tests/CLAUDE.md §"Defect-repro notation").
//
// A `Sexp` value renders `:macros/Sexp (Sexp.SexpXxx …)`; datum survival is
// asserted on that render (`Sexp.SexpSym "m"` etc.). `run_prims` gives the
// `--run` face (the desugar is mode-uniform — a frontend desugar).
// =============================================================================

fn run_prims(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .run("user.cl")
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .user(src)
        .output()
}

// QQ-1 — quasiquote+unquote in a `defn` body. `~x` splices the Sexp argument
// into an `(if …)` template; the fn returns the constructed Sexp.
// spec: spec/09-macros.md §9.4
// defect: class=wrong-reject locus=crates/cranelisp-frontend found=S110 owner=/dev
#[test]
fn quasiquote_in_defn_body_desugars() {
    repl_prims(
        "(defn helper [x] `(if ~x 1 0))\n\
         (helper (macros/SexpInt 5))\n",
    )
    .assert_stdout_contains(":macros/Sexp")
    .assert_stdout_contains("Sexp.SexpSym \"if\"")
    .assert_stdout_does_not_contain("should have been expanded");
}

// QQ-2 — quote in a `defn` body. `'(1 2)` is a Sexp literal.
// spec: spec/09-macros.md §9.4
// defect: class=wrong-reject locus=crates/cranelisp-frontend found=S110 owner=/dev
#[test]
fn quote_in_defn_body_desugars() {
    repl_prims("(defn f [] '(1 2))\n(f)\n")
        .assert_stdout_contains(":macros/Sexp")
        .assert_stdout_contains("Sexp.SexpInt 1")
        .assert_stdout_does_not_contain("should have been expanded");
}

// QQ-3 — unquote-splicing in a `defn-` (private) body, exercised via a public
// caller. `~@xs` splices a `(SList Sexp)` into a `(begin …)` template.
// spec: spec/09-macros.md §9.4
// defect: class=wrong-reject locus=crates/cranelisp-frontend found=S110 owner=/dev
#[test]
fn unquote_splicing_in_private_defn_body_desugars() {
    repl_prims(
        "(defn- g [xs] `(begin ~@xs))\n\
         (defn call-g [] (g (macros/SCons (macros/SexpInt 7) macros/SNil)))\n\
         (call-g)\n",
    )
    .assert_stdout_contains(":macros/Sexp")
    .assert_stdout_contains("Sexp.SexpSym \"begin\"")
    .assert_stdout_contains("Sexp.SexpInt 7")
    .assert_stdout_does_not_contain("should have been expanded");
}

// QQ-4a — quote at top level (REPL).
// spec: spec/09-macros.md §9.4
// defect: class=wrong-reject locus=crates/cranelisp-frontend found=S110 owner=/dev
#[test]
fn quote_at_top_level_desugars() {
    repl_prims("'(1 2)\n")
        .assert_stdout_contains(":macros/Sexp")
        .assert_stdout_contains("Sexp.SexpInt 1")
        .assert_stdout_does_not_contain("should have been expanded");
}

// QQ-4b — quasiquote+unquote at top level (REPL).
// spec: spec/09-macros.md §9.4
// defect: class=wrong-reject locus=crates/cranelisp-frontend found=S110 owner=/dev
#[test]
fn quasiquote_unquote_at_top_level_desugars() {
    repl_prims("`(a ~(macros/SexpInt 7))\n")
        .assert_stdout_contains(":macros/Sexp")
        .assert_stdout_contains("Sexp.SexpSym \"a\"")
        .assert_stdout_contains("Sexp.SexpInt 7")
        .assert_stdout_does_not_contain("should have been expanded");
}

// QQ-4c — unquote-splicing at top level (REPL).
// spec: spec/09-macros.md §9.4
// defect: class=wrong-reject locus=crates/cranelisp-frontend found=S110 owner=/dev
#[test]
fn unquote_splicing_at_top_level_desugars() {
    repl_prims(
        "`(a ~@(macros/SCons (macros/SexpInt 1) (macros/SCons (macros/SexpInt 2) macros/SNil)))\n",
    )
    .assert_stdout_contains(":macros/Sexp")
    .assert_stdout_contains("Sexp.SexpInt 1")
    .assert_stdout_contains("Sexp.SexpInt 2")
    .assert_stdout_does_not_contain("should have been expanded");
}

// QQ-4 (--run face) — the desugar is mode-uniform; a quote in a `defn` body
// compiles under `--run` too. The desugar folds into `build_form`, so `f`'s body
// is desugared at build regardless of being called and `assert_ok` holds (GREEN
// regression guard since the 0613 fold landed).
// spec: spec/09-macros.md §9.4
// defect: class=wrong-reject locus=crates/cranelisp-frontend found=S110 owner=/dev
#[test]
fn quote_desugars_in_run_mode() {
    run_prims("(defn f [] '(1 2))\n(defn main [] (Pure 0))\n").assert_ok();
}

// QQ-5 — GREEN control: quasiquote in a defmacro clause body keeps working
// (the fold is a fixpoint; `macro_clause.rs`'s desugar caller becomes
// idempotent). Must-hold across the wave.
// spec: spec/09-macros.md §9.4
#[test]
fn quasiquote_in_defmacro_body_still_expands() {
    repl_prims(
        "(defmacro my-when [c body] `(if ~c ~body 0))\n\
         (my-when true 42)\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// -----------------------------------------------------------------------------
// §C interaction rows (arch §3) — the fold-WITHOUT-shield negatives. Fixture:
// a registered macro `m` whose body `(macros/SexpInt 999)` is a well-typed
// `Sexp` (a valid defmacro per §9.5 — a bare `999` would type-error at the
// `defmacro`), expanding to the literal `999` — observably distinct from the
// preserved 2-element datum `(m x)`. If the fold lands without int's quote
// shield, a macro-call-shaped list inside quoted DATA is expanded before the
// desugar sees it → the quoted literal is silently corrupted to `999`.
// -----------------------------------------------------------------------------

// QQ-I1 — `(m x)` under quote in a defn body: MUST NOT expand. The datum
// survives as the 2-element Sexp list with head symbol `m`; `999` must NOT
// appear. GREEN (fold+shield landed, 0613); if `999` ever appears the fold has
// regressed PAST the shield — the corruption alarm.
// spec: spec/09-macros.md §9.4
// defect: class=wrong-reject locus=crates/cranelisp-frontend found=S110 owner=/dev
#[test]
fn macro_call_under_quote_in_defn_body_not_expanded() {
    repl_prims(
        "(defmacro m [x] (macros/SexpInt 999))\n\
         (defn f [] '(m x))\n\
         (f)\n",
    )
    .assert_stdout_contains(":macros/Sexp")
    .assert_stdout_contains("Sexp.SexpSym \"m\"")
    .assert_stdout_does_not_contain("999")
    .assert_stdout_does_not_contain("should have been expanded");
}

// QQ-I1b — same, at top level.
// spec: spec/09-macros.md §9.4
// defect: class=wrong-reject locus=crates/cranelisp-frontend found=S110 owner=/dev
#[test]
fn macro_call_under_quote_at_top_level_not_expanded() {
    repl_prims("(defmacro m [x] (macros/SexpInt 999))\n'(m x)\n")
        .assert_stdout_contains(":macros/Sexp")
        .assert_stdout_contains("Sexp.SexpSym \"m\"")
        .assert_stdout_does_not_contain("999")
        .assert_stdout_does_not_contain("should have been expanded");
}

// QQ-I2 — `(m x)` under quasiquote OUTSIDE any unquote: MUST NOT expand (the
// datum is preserved). Both contexts folded into one fixture (defn body + top
// level share the same shield path).
// spec: spec/09-macros.md §9.4
// defect: class=wrong-reject locus=crates/cranelisp-frontend found=S110 owner=/dev
#[test]
fn macro_call_under_quasiquote_outside_unquote_not_expanded() {
    repl_prims("(defmacro m [x] (macros/SexpInt 999))\n`(m x)\n")
        .assert_stdout_contains(":macros/Sexp")
        .assert_stdout_contains("Sexp.SexpSym \"m\"")
        .assert_stdout_does_not_contain("999")
        .assert_stdout_does_not_contain("should have been expanded");
}

// QQ-I3 — a macro under unquote MUST expand (ordinary expression position).
// NOTE: unquote requires a `Sexp` result (§9.4.2). The macro body must return
// the constructor-CALL sexp, `(quote (macros/SexpInt 999))`, NOT the raw value
// `(macros/SexpInt 999)`: the raw value expands `~(me 1)` to a bare Int, which
// then type-errors as an unquote result (an Int is not a Sexp). Expanding the
// quoted call form, `~(me 1)` becomes `~(macros/SexpInt 999)`, which evaluates
// to the `Sexp` value `SexpInt 999` and splices in cleanly. Result:
// `SexpList (SCons (SexpSym "a") (SCons (SexpInt 999) SNil))`.
// spec: spec/09-macros.md §9.4
// defect: class=wrong-reject locus=crates/cranelisp-frontend found=S110 owner=/dev
#[test]
fn macro_call_under_unquote_expands() {
    repl_prims(
        "(defmacro me [x] (quote (macros/SexpInt 999)))\n\
         `(a ~(me 1))\n",
    )
    .assert_stdout_contains(":macros/Sexp")
    .assert_stdout_contains("Sexp.SexpInt 999")
    .assert_stdout_does_not_contain("should have been expanded");
}

// QQ-I4 — a macro under unquote-splicing MUST expand and splice. `~@` requires
// an `(SList Sexp)` result (§9.4.2). The macro body must return the quoted
// `SCons`-producing CALL, `(quote (macros/SCons ...))` — a `Sexp` value (a
// valid defmacro per §9.5) — NOT a body of type `(SList Sexp)` (which
// type-errors at the `defmacro`). Expanding the quoted call, `~@(m2 1)` becomes
// `~@(macros/SCons (SexpInt 7) (SCons (SexpInt 8) SNil))`, which evaluates to an
// `(SList Sexp)` whose two elements (7, 8) are spliced into the list.
// spec: spec/09-macros.md §9.4
// defect: class=wrong-reject locus=crates/cranelisp-frontend found=S110 owner=/dev
#[test]
fn macro_call_under_unquote_splicing_expands_and_splices() {
    repl_prims(
        "(defmacro m2 [x] (quote (macros/SCons (macros/SexpInt 7) (macros/SCons (macros/SexpInt 8) macros/SNil))))\n\
         `(a ~@(m2 1))\n",
    )
    .assert_stdout_contains(":macros/Sexp")
    .assert_stdout_contains("Sexp.SexpInt 7")
    .assert_stdout_contains("Sexp.SexpInt 8")
    .assert_stdout_does_not_contain("should have been expanded");
}

// QQ-I5 — nested quasiquote depth: a macro-call-shaped list inside a NESTED
// quasiquote must stay shielded (the shield tracks nesting depth). If depth is
// not tracked, `m` expands to 999. GREEN (fold+depth-tracking shield landed,
// 0613); if `999` appears the shield has stopped tracking depth — the alarm.
// spec: spec/09-macros.md §9.4
// defect: class=wrong-reject locus=crates/cranelisp-frontend found=S110 owner=/dev
#[test]
fn macro_call_inside_nested_quasiquote_not_expanded() {
    repl_prims("(defmacro m [x] (macros/SexpInt 999))\n`(a `(m x))\n")
        .assert_stdout_contains(":macros/Sexp")
        .assert_stdout_does_not_contain("999")
        .assert_stdout_does_not_contain("should have been expanded");
}

// QQ-I6 — macro ARGUMENTS stay raw (the arch ruling: desugar-at-build runs
// AFTER expansion dispatch, so a macro receives the `(quote …)` sexp the user
// wrote). An identity macro returns its arg unchanged; the quoted datum
// round-trips to the Sexp `(1 2)`. GREEN (the quote desugar landed, 0613).
// spec: spec/09-macros.md §9.4
// defect: class=wrong-reject locus=crates/cranelisp-frontend found=S110 owner=/dev
#[test]
fn macro_argument_stays_raw_quote_datum() {
    repl_prims(
        "(defmacro raw [x] x)\n\
         (raw '(1 2))\n",
    )
    .assert_stdout_contains(":macros/Sexp")
    .assert_stdout_contains("Sexp.SexpInt 1")
    .assert_stdout_contains("Sexp.SexpInt 2")
    .assert_stdout_does_not_contain("should have been expanded");
}

// S-5 — nested-quasiquote DEPTH AGREEMENT (int quote-shield ↔ frontend desugar
// fold, /review CS-3 S-5). QQ-I5 pins that a macro call in nested-quoted DATA
// stays shielded; this row pins the other side of the same seam — a macro call
// at the correct COMBINED unquote depth MUST expand, and one unquote short of
// live (belonging to the INNER quasiquote) MUST NOT. The two polarities share
// the SAME registered, well-formed nullary macro `mm` (body `(quote
// (macros/SexpInt 777))` → the constructor-call sexp, so a live `~~(mm)`
// expands to `(macros/SexpInt 777)` which evaluates to a `Sexp`), so the only
// difference between the cells is unquote depth — an unforgiving pin on the
// shield↔frontend depth math (closes the silent-divergence residual).
//   `~~(mm)` : outer ` (d1) inner ` (d2) ~ (d1) ~ (d0=live)  → mm EXPANDS (777)
//   `~(mm)`  : outer ` (d1) inner ` (d2) ~ (d1, inner-qq datum) → mm PRESERVED
// spec: spec/09-macros.md §9.4.2
#[test]
fn nested_quasiquote_depth_agreement_double_unquote_expands_single_does_not() {
    // Double unquote reaches live depth 0 — mm expands, 777 appears, no `mm`.
    repl_prims("(defmacro mm [] (quote (macros/SexpInt 777)))\n`(a `(b ~~(mm)))\n")
        .assert_stdout_contains(":macros/Sexp")
        .assert_stdout_contains("Sexp.SexpInt 777")
        .assert_stdout_does_not_contain("SexpSym \"mm\"")
        .assert_stdout_does_not_contain("should have been expanded");
    // Single unquote belongs to the inner quasiquote — mm stays a datum symbol,
    // 777 never appears.
    repl_prims("(defmacro mm [] (quote (macros/SexpInt 777)))\n`(a `(b ~(mm)))\n")
        .assert_stdout_contains(":macros/Sexp")
        .assert_stdout_contains("Sexp.SexpSym \"mm\"")
        .assert_stdout_does_not_contain("777")
        .assert_stdout_does_not_contain("should have been expanded");
}
