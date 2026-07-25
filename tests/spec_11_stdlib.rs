// spec_11_stdlib.rs — Stdlib conformance, REPL canonical
// (Sprint 64 Wave 2 Batch 5; re-ported under REPL canonical in Wave 2.5).
//
// This file is the named exception to the no-stdlib rule (root CLAUDE.md
// §"Design Principles" — Stdlib separation): it loads the workspace stdlib
// via the `use_workspace_stdlib_for_stdlib_conformance_only()` gate. No
// other test file may use that gate.
//
// Wave 2.5 architecture pivot (per `tests/plan/PLAN.md §"Mode
// canonicalisation"`): bulk language-conformance tests run in REPL mode,
// not `--run`. The REPL prints `:Type value` per top-level expression
// (`repl/spec.md §1.2`); each test pipes one expression and asserts the
// stdout contains the expected `:Type value` substring. This validates
// BOTH the value AND the type in one assertion — closer to the legacy
// integration-tier `(value, ty)` shape than the Wave 2 `--run` exit-code
// witness was.
//
// The legacy `tests/stdlib.rs` integration-tier suite (54 tests) used
// `ReplSession::eval(src) -> (i64, Type)`. The Wave 2 port packed each
// assertion as `(defn main [] expr-or-Bool-witness)` returning Int via
// the process exit code. Wave 2.5 retains every assertion's spec
// coverage but routes through REPL canonical instead.
//
// ADT match-witness rationale (per Wave 3.5 audit, Part C §"Maintainability"):
// Several Option/Result tests below use a `match` expression as the witness
// (e.g., `(match (Some 7) [(Some x) (= x 7) None false])`) rather than
// constructing the bare ADT and asserting on its display. This is deliberate
// for two reasons:
//   1. At top-level REPL, an unconstrained type variable in `(Some 7)` would
//      need explicit annotation to fix the `b` in `Result a b` (or the unused
//      None arm in Option). The match-arm body uses `=` / a pinned type to
//      anchor the type variable, so no annotation is required at the surface.
//   2. The test asserts `:primitives/Bool true` — a single deterministic
//      output line — which keeps each test small and the assertion tight.
// The shape looks more complex than it is; per-test comments explain the
// witness arm where it is non-obvious. See also `tests/plan/PLAN.md
// §"Mode canonicalisation"` for the broader Wave 2.5 decision.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;

// =============================================================================
// Helpers — keep the per-test boilerplate small.
// =============================================================================

/// Pipe `expr` to a fresh REPL session under the workspace stdlib and assert
/// stdout contains `expected` (typically `:Type value`).
fn assert_repl_eval_contains(expr: &str, expected: &str) {
    Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .repl()
        .stdin(&format!("{expr}\n"))
        .output()
        .assert_ok()
        .assert_stdout_contains(expected);
}

/// Pipe `expr` to a fresh REPL session under the workspace stdlib and assert
/// stdout contains EVERY substring in `expected`. Useful for multi-form
/// scripts where each form's display matters.
fn assert_repl_lines_contain(forms: &[&str], expected: &[&str]) {
    let stdin = forms.join("\n") + "\n";
    let out = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .repl()
        .stdin(&stdin)
        .output()
        .assert_ok();
    for needle in expected {
        if !out.stdout.contains(needle) {
            panic!("stdout missing '{}'\nstdout:\n{}", needle, out.stdout);
        }
    }
}

// =============================================================================
// a. Prelude loads without errors
// =============================================================================

// spec: spec/09-macros.md §9.5 — prelude loads successfully (a trivial
// arithmetic form succeeds at the REPL → prelude loaded).
#[test]
fn prelude_loads_without_errors() {
    assert_repl_eval_contains("(+ 0 0)", ":primitives/Int 0");
}

// spec: repl/spec.md §1.3 — a stdlib `def` definition confirmation presents
// the user binding and bound value, not the macro's synthesized thunk.
// defect: class=display-envelope-mirror locus=src/repl.rs::definition-result found=S115 owner=/dev
#[test]
fn def_definition_echo_names_user_binding_not_internal_thunk() {
    let out = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .repl()
        .stdin("(def n 42)\n")
        .output();
    assert!(
        out.stdout.contains("user/n") && out.stdout.contains("primitives/Int"),
        "`def` echo MUST describe the user binding `n` with value type Int; got:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("n-def"),
        "`def` echo MUST NOT leak the synthesized `n-def` thunk; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §1.3 + §4.1 — `/info`, `/sig`, and bare lookup of a
// stdlib `def` binding describe the same bound value, not its macro carrier.
// defect: class=display-envelope-mirror locus=src/repl.rs::symbol_introspection found=S115 owner=/dev
#[test]
fn def_info_and_sig_describe_bound_value_not_macro() {
    let out = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .repl()
        .stdin("(def n 42)\n/info n\n/sig n\nn\n")
        .output();
    assert!(
        out.stdout.matches(":primitives/Int").count() >= 3,
        "definition/introspection/bare lookup MUST agree that `n` is an Int value; got:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("n-def")
            && !out.stdout.contains("; defmacro")
            && !out.stdout.contains("Sexp"),
        "`def` introspection MUST NOT expose its zero-arg macro implementation; got:\n{}",
        out.stdout
    );
}

// spec: repl/spec.md §18.4 — a failed codegen turn is discarded; the next
// independent literal starts from the last committed session state.
// defect: class=routing-misclassify locus=src/session_v4.rs::process_cluster_with_staging found=S115 owner=/dev
#[test]
fn failed_codegen_turn_does_not_poison_following_literal() {
    let out = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .repl()
        .stdin(
            "(import [collections.vec [vec-flatten]])\n\
             (vec-flatten [[1 2] [3 4]])\n\
             42\n",
        )
        .output();
    assert!(
        out.stdout.contains(":primitives/Int 42"),
        "a literal after a genuine codegen failure MUST evaluate normally; stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    assert!(
        format!("{}{}", out.stdout, out.stderr)
            .matches("generic value reference 'vec-concat'")
            .count()
            <= 1,
        "the failed batch MUST NOT be retried on the following literal; stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
}

// spec: repl/spec.md §18.4 — recovery after failed codegen includes later
// definition registration, compilation, publication, and evaluation.
// defect: class=routing-misclassify locus=src/session_v4.rs::process_cluster_with_staging found=S115 owner=/dev
#[test]
fn failed_codegen_turn_does_not_poison_following_definition_and_call() {
    let out = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .repl()
        .stdin(
            "(import [collections.vec [vec-flatten]])\n\
             (vec-flatten [[1 2] [3 4]])\n\
             (defn alive [] 42)\n\
             (alive)\n",
        )
        .output();
    assert!(
        out.stdout.contains(":primitives/Int 42") && out.stdout.contains("user/alive"),
        "definition and call after failed codegen MUST publish and evaluate; stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
}

// spec: repl/spec.md §18.4 — a failed codegen turn publishes no partial
// definition/specialization; a clean redefinition of the same public symbol
// can subsequently compile, replace it, and run.
// defect: class=routing-misclassify locus=src/session_v4.rs::process_cluster_with_staging found=S115 owner=/dev
#[test]
fn failed_codegen_turn_does_not_publish_partial_definition() {
    let out = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .repl()
        .stdin(
            "(import [collections.vec [vec-flatten]])\n\
             (defn failed-unit [v] (vec-flatten v))\n\
             (failed-unit [[1 2] [3 4]])\n\
             (defn failed-unit [_] 42)\n\
             (failed-unit 0)\n\
             /info failed-unit\n",
        )
        .output();
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains(":primitives/Int 42"),
        "a clean same-name redefinition after failed codegen MUST compile and run; got:\n{combined}"
    );
    let info = out.stdout.rsplit("user/failed-unit").next().unwrap_or("");
    assert!(
        !info.contains("broken") && !info.contains("vec-flatten"),
        "failed turn metadata/code MUST not survive into the clean redefinition's /info; got:\n{combined}"
    );
}

// spec: repl/spec.md §18.4 — a codegen diagnostic names the actual failing
// compilation unit, never an incidental operator spelling.
// defect: class=display-envelope-mirror locus=src/session_v4.rs::inline_jit_codegen_for_names found=S115 owner=/dev
#[test]
fn failed_codegen_diagnostic_names_actual_failing_unit_not_operator_slash() {
    let out = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .repl()
        .stdin(
            "(import [collections.vec [vec-flatten]])\n\
             (vec-flatten [[1 2] [3 4]])\n",
        )
        .output();
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("codegen failed for /"),
        "diagnostic MUST NOT attribute vec-flatten/vec-concat failure to `/`; got:\n{combined}"
    );
    assert!(
        combined.contains("vec-flatten") || combined.contains("vec-concat"),
        "diagnostic MUST identify the actual failing unit or located backend subject; got:\n{combined}"
    );
}

// =============================================================================
// b. Arithmetic operators (Num trait)
// =============================================================================

// spec: spec/07-traits.md §7.1 — Num trait: Int addition
#[test]
fn arithmetic_add_int() {
    assert_repl_eval_contains("(+ 1 2)", ":primitives/Int 3");
}

// spec: spec/07-traits.md §7.1 — Num trait: Int subtraction
#[test]
fn arithmetic_sub_int() {
    assert_repl_eval_contains("(- 5 3)", ":primitives/Int 2");
}

// spec: spec/07-traits.md §7.1 — Num trait: Int multiplication
#[test]
fn arithmetic_mul_int() {
    assert_repl_eval_contains("(* 2 3)", ":primitives/Int 6");
}

// spec: spec/07-traits.md §7.1 — Num trait: Int division
#[test]
fn arithmetic_div_int() {
    assert_repl_eval_contains("(/ 10 2)", ":primitives/Int 5");
}

// =============================================================================
// c. Float arithmetic (canonical form: print `:primitives/Float 3`)
// =============================================================================

// spec: spec/07-traits.md §7.1 — Num trait: Float addition
#[test]
fn arithmetic_add_float() {
    assert_repl_eval_contains("(+ 1.0 2.0)", ":primitives/Float 3");
}

// =============================================================================
// d. Comparison operators (Eq / Ord)
// =============================================================================

// spec: spec/07-traits.md §7.1 — Eq trait: Int equality
#[test]
fn comparison_eq_int() {
    assert_repl_eval_contains("(= 1 1)", ":primitives/Bool true");
}

// spec: spec/07-traits.md §7.1 — Ord trait: Int less-than
#[test]
fn comparison_lt_int() {
    assert_repl_eval_contains("(< 1 2)", ":primitives/Bool true");
}

// spec: spec/07-traits.md §7.1 — Ord trait: Int greater-than
#[test]
fn comparison_gt_int() {
    assert_repl_eval_contains("(> 2 1)", ":primitives/Bool true");
}

// =============================================================================
// e. Boolean equality
// =============================================================================

// spec: spec/07-traits.md §7.1 — Eq trait: Bool equality
#[test]
fn comparison_eq_bool() {
    assert_repl_eval_contains("(= true true)", ":primitives/Bool true");
}

// =============================================================================
// f. String equality
// =============================================================================

// spec: spec/07-traits.md §7.1 — Eq trait: String equality
#[test]
fn comparison_eq_string() {
    assert_repl_eval_contains(r#"(= "hi" "hi")"#, ":primitives/Bool true");
}

// =============================================================================
// g. Display trait: show
// =============================================================================

// spec: spec/07-traits.md §7.1 — Display trait: show Int
#[test]
fn display_show_int() {
    assert_repl_eval_contains("(show 42)", ":primitives/String \"42\"");
}

// =============================================================================
// h. Option type
// =============================================================================

// spec: spec/05-definitions.md §5.2 (deftype) + spec/06-pattern-matching.md §6.1 — Option Some constructor (witness via match)
#[test]
fn option_some_constructs() {
    assert_repl_eval_contains(
        "(match (Some 7) [(Some x) (= x 7) None false])",
        ":primitives/Bool true",
    );
}

// spec: spec/05-definitions.md §5.2 (deftype) + spec/06-pattern-matching.md §6.1 — Option None constructor (witness: a fn body
// pins Option's type variable via the Some arm; calling with None hits
// the None arm).
#[test]
fn option_none_exists() {
    assert_repl_lines_contain(
        &[
            "(defn unwrap-or-zero [opt] (match opt [(Some x) x None 0]))",
            "(unwrap-or-zero None)",
        ],
        &[":primitives/Int 0"],
    );
}

// =============================================================================
// i. Macros: do, bind!
// (the `when` cases live in section s — "Prelude macros: when")
// =============================================================================

// spec: spec/10-io.md §10.4 — do macro sequences IO actions, returns last
#[test]
fn macro_do_returns_last() {
    assert_repl_eval_contains(
        "(import [primitives [Pure]]) (do (Pure 1) (Pure 2) (Pure 3))",
        ":primitives/Int 3",
    );
}

// spec: spec/10-io.md §10.5 — bind! macro: single binding desugars to
// `(bind (Pure 42) (fn [x] (Pure x)))`, body returns the bound value.
// (harvest: legacy/io.rs::io_bind_bang_single_binding_desugared)
#[test]
fn macro_bind_bang_single_binding() {
    assert_repl_eval_contains(
        "(import [primitives [Pure]]) (bind! [x (Pure 42)] (Pure x))",
        ":primitives/Int 42",
    );
}

// spec: spec/10-io.md §10.5 — bind! macro: multiple bindings desugar to nested
// binds; later bindings see earlier ones.
// (harvest: legacy/io.rs::io_bind_bang_multiple_bindings_desugared
//  + io_bind_bang_sequential_reference_desugared)
#[test]
fn macro_bind_bang_multiple_bindings() {
    assert_repl_eval_contains(
        "(import [primitives [Pure add-i64]]) \
         (bind! [x (Pure 10) y (Pure 20)] (Pure (add-i64 x y)))",
        ":primitives/Int 30",
    );
}

// spec: spec/10-io.md §10.5.2 — bind! later bindings reference earlier bindings.
#[test]
fn macro_bind_bang_sequential_reference() {
    assert_repl_eval_contains(
        "(import [primitives [Pure add-i64]]) \
         (bind! [x (Pure 5) y (Pure (add-i64 x x))] (Pure y))",
        ":primitives/Int 10",
    );
}

// =============================================================================
// j. cond macro
// =============================================================================

// spec: spec/09-macros.md §9.5 — cond macro multi-way conditional fallthrough
#[test]
fn macro_cond_fallthrough() {
    assert_repl_eval_contains("(cond (= 1 2) 0 1)", ":primitives/Int 1");
}

// =============================================================================
// k. Result type
// =============================================================================

// spec: spec/05-definitions.md §5.2 (deftype) + spec/06-pattern-matching.md §6.1 — Result Ok constructor.
// spec: spec/03-types.md §3.11.1 — `(Ok 42)` has type `(Result Int b)`: the
// `Int` is determined by the payload, but the `Err`-arm payload var `b` is a
// PHANTOM (unused-ctor-position) free var. Under the tightened
// full-concreteness verdict any residual free var — occurring OR phantom — at a
// codegen-reaching value position is ambiguous (USER RULED strict, phantom not
// exempt), so the construction MUST be pinned `:(Result Int String) (Ok 42)`.
// The annotation is pinned in value position (a `let` binding) rather than the
// `match` scrutinee, which has a separate frontend parse bug (FIXME 0389);
// matching on the bound var keeps the test's pattern-dispatch semantics.
#[test]
fn result_ok_constructs() {
    assert_repl_eval_contains(
        r#"(let [r :(Result Int String) (Ok 42)] (match r [(Ok x) (= x 42) (Err _) false]))"#,
        ":primitives/Bool true",
    );
}

// spec: spec/05-definitions.md §5.2 (deftype) + spec/06-pattern-matching.md §6.1 — Result Err constructor.
// spec: spec/03-types.md §3.11.1 — `(Err "oops")` has type `(Result a String)`:
// the `String` is determined by the payload, but the `Ok`-arm payload var `a`
// is a PHANTOM free var. The strict verdict rejects it unpinned, so the
// construction is pinned `:(Result Int String) (Err "oops")` (value position,
// then matched on the bound var — sidestepping the FIXME-0389 scrutinee parse
// bug).
#[test]
fn result_err_constructs() {
    assert_repl_eval_contains(
        r#"(let [r :(Result Int String) (Err "oops")] (match r [(Ok _) false (Err _) true]))"#,
        ":primitives/Bool true",
    );
}

// =============================================================================
// l. Inequality operator
// =============================================================================

// spec: spec/07-traits.md §7.1 — Eq trait: != true case
#[test]
fn comparison_neq_int() {
    assert_repl_eval_contains("(!= 1 2)", ":primitives/Bool true");
}

// spec: spec/07-traits.md §7.1 — Eq trait: != false case
#[test]
fn comparison_neq_int_false() {
    assert_repl_eval_contains("(!= 1 1)", ":primitives/Bool false");
}

// =============================================================================
// m. Ord operator coverage
// =============================================================================

// spec: spec/07-traits.md §7.1 — Ord trait: <= operator
#[test]
fn comparison_le_int() {
    assert_repl_eval_contains("(<= 1 1)", ":primitives/Bool true");
}

// spec: spec/07-traits.md §7.1 — Ord trait: >= operator
#[test]
fn comparison_ge_int() {
    assert_repl_eval_contains("(>= 2 1)", ":primitives/Bool true");
}

// spec: spec/07-traits.md §7.1 — Ord trait: Float less-than
#[test]
fn comparison_lt_float() {
    assert_repl_eval_contains("(< 1.0 2.0)", ":primitives/Bool true");
}

// =============================================================================
// n. Display trait coverage
// =============================================================================

// spec: spec/07-traits.md §7.1 — Display trait: show Bool
#[test]
fn display_show_bool() {
    assert_repl_eval_contains("(show true)", ":primitives/String \"true\"");
}

// spec: spec/07-traits.md §7.1 — Display trait: show String
#[test]
fn display_show_string() {
    assert_repl_eval_contains(r#"(show "hello")"#, ":primitives/String \"hello\"");
}

// =============================================================================
// o. Multi-module loading (transitive prelude re-exports)
// =============================================================================

// spec: spec/08-modules.md §8.2 — prelude loads domain submodules
#[test]
fn domain_modules_traits_available() {
    assert_repl_eval_contains("(+ (- 10 3) (* 2 3))", ":primitives/Int 13");
}

// =============================================================================
// p. Prelude macros: cond
// =============================================================================

// spec: spec/09-macros.md §9.5 — cond first branch match
#[test]
fn macro_cond_first_match() {
    assert_repl_eval_contains("(cond (= 1 1) 10 20)", ":primitives/Int 10");
}

// spec: spec/09-macros.md §9.5 — cond second branch match
#[test]
fn macro_cond_second_match() {
    assert_repl_eval_contains("(cond (= 1 2) 10 (= 2 2) 20 30)", ":primitives/Int 20");
}

// spec: spec/09-macros.md §9.5 — cond default (all conditions false)
#[test]
fn macro_cond_default() {
    assert_repl_eval_contains("(cond (= 1 2) 10 (= 3 4) 20 99)", ":primitives/Int 99");
}

// spec: spec/09-macros.md §9.5 — cond with comparison expression
#[test]
fn macro_cond_with_comparison() {
    assert_repl_eval_contains("(cond (> 5 10) 1 (< 5 10) 2 3)", ":primitives/Int 2");
}

// =============================================================================
// q. Prelude macros: case
// =============================================================================

// spec: spec/09-macros.md §9.5 — case first match
#[test]
fn macro_case_first_match() {
    assert_repl_eval_contains("(case 1 1 10 2 20 99)", ":primitives/Int 10");
}

// spec: spec/09-macros.md §9.5 — case second match
#[test]
fn macro_case_second_match() {
    assert_repl_eval_contains("(case 2 1 10 2 20 99)", ":primitives/Int 20");
}

// spec: spec/09-macros.md §9.5 — case default fallthrough
#[test]
fn macro_case_default() {
    assert_repl_eval_contains("(case 3 1 10 2 20 99)", ":primitives/Int 99");
}

// =============================================================================
// r. Prelude macros: do (IO semantics)
// =============================================================================

// spec: spec/10-io.md §10.4 — do single expression passes through
#[test]
fn macro_do_single() {
    assert_repl_eval_contains("(do 42)", ":primitives/Int 42");
}

// spec: spec/10-io.md §10.4 — do multi-expression sequences IO actions
#[test]
fn macro_do_multi() {
    assert_repl_eval_contains(
        "(import [primitives [Pure]]) (do (Pure 1) (Pure 2) (Pure 3) (Pure 42))",
        ":primitives/Int 42",
    );
}

// =============================================================================
// s. Prelude macros: when
// =============================================================================

// `when`/`unless` are prelude macros supplied by `stdlib/control.cl`; their
// contract is the docstring "Conditional returning (Some body) when test
// holds, else None" — the body is wrapped UNCONDITIONALLY, so the two `if`
// branches unify at `(Option a)` for ANY body type `a`. Prior to S115 the
// expansion was `(if ~test ~body None)` (no wrap), which only typechecked when
// the body was ALREADY an Option; `(when true 5)` failed outright. The three
// tests below pin the post-fix contract: a non-Option body (the regression
// shape), the None branch, and an Option body (the wrap is not special-cased —
// an already-`Some` body nests).
//
// Spec note: `when`/`unless` have no §9.10 entry of their own (§9.4.3's `when`
// is a pedagogical `(if ~cond ~body 0)` example, NOT this macro), so these
// tests cite §9.10 "Example Prelude Macros" as the nearest normative home.
// FIXME 0841 (/qa) tracks the resulting traceability gap.

// spec: spec/09-macros.md §9.10 — `when` with a true test wraps a non-Option
// body in `Some` (the S115 regression shape).
#[test]
fn macro_when_true() {
    assert_repl_eval_contains(
        "(match (when true 42) [(Some x) (= x 42) None false])",
        ":primitives/Bool true",
    );
}

// spec: spec/09-macros.md §9.10 — `when` with a false test yields `None`.
#[test]
fn macro_when_false_none() {
    assert_repl_eval_contains(
        "(match (when false 42) [(Some _) false None true])",
        ":primitives/Bool true",
    );
}

// spec: spec/09-macros.md §9.10 — the `Some` wrap is unconditional: a body that
// is already an `Option` nests, giving `(Some (Some 42))`. (This is precisely
// what the pre-S115 duplicate pair asserted the WRONG way round — it read the
// outer `Some` as the body's own and expected `x : Int`.)
#[test]
fn macro_when_option_body_nests_the_wrap() {
    assert_repl_eval_contains(
        "(match (when true (Some 42)) \
           [(Some inner) (match inner [(Some x) (= x 42) None false]) None false])",
        ":primitives/Bool true",
    );
}

// =============================================================================
// t. Prelude macros: vec
// =============================================================================

// spec: spec/09-macros.md §9.5 — vec macro creates vector (length witness)
#[test]
fn macro_vec_elements() {
    assert_repl_eval_contains(
        "(import [primitives [vec-len]]) (vec-len (vec 10 20 30))",
        ":primitives/Int 3",
    );
}

// spec: spec/03-types.md §3.11.1 — a fully-empty vector `(vec)` / `[]` has
// type `(Vec a)`; with the element type `a` unpinned and the `vec-len`
// application reaching codegen (the §3.11.1 `(id [])` worked example), it is
// ambiguous and MUST error. User ruling 2026-07-12: `(vec-len (vec))` on a
// fully-empty vector with no element-type witness is ambiguous, not length 0.
// (Re-baselined from a former false-green that asserted `:primitives/Int 0`;
// the Wave-C error-swallow fix unmasked it.) Message wording per §3.11.4.
#[test]
fn macro_vec_empty_neg_ambiguous_element_type() {
    assert_repl_eval_contains(
        "(import [primitives [vec-len]]) (vec-len (vec))",
        "ambiguous type",
    );
}

// spec: spec/03-types.md §3.11.1 — pinning the element type concrete resolves
// the ambiguity: an annotated empty vector has a determined `(Vec Int)` type,
// so `vec-len` computes length 0. This is the §3.11.1 fix form
// (`(id :(Vec Int) [])`) and the positive witness that empty-vec length stays
// computable once the element type is witnessed.
#[test]
fn macro_vec_empty_pinned_ok() {
    assert_repl_eval_contains(
        "(import [primitives [Vec vec-len]]) (vec-len :(Vec Int) (vec))",
        ":primitives/Int 0",
    );
}

// spec: spec/09-macros.md §9.5 — vec macro element access
#[test]
fn macro_vec_access() {
    assert_repl_eval_contains(
        "(import [primitives [vec-get]]) (vec-get (vec 10 20 30) 1)",
        ":primitives/Int 20",
    );
}

// =============================================================================
// u. Prelude macros: str
// =============================================================================

// spec: spec/09-macros.md §9.5 — str macro empty
#[test]
fn macro_str_empty() {
    assert_repl_eval_contains(r#"(str)"#, ":primitives/String \"\"");
}

// spec: spec/09-macros.md §9.5 — str macro single argument
#[test]
fn macro_str_single() {
    assert_repl_eval_contains(r#"(str "hello")"#, ":primitives/String \"hello\"");
}

// spec: spec/09-macros.md §9.5 — str macro concatenation
#[test]
fn macro_str_multi() {
    assert_repl_eval_contains(
        r#"(str "hello" " " "world")"#,
        ":primitives/String \"hello world\"",
    );
}

// =============================================================================
// v. Prelude macros: const
// =============================================================================

// spec: spec/09-macros.md §9.5 — const defines bare-symbol macro
#[test]
fn macro_const_int() {
    assert_repl_lines_contain(
        &["(const MY-CONST 42)", "MY-CONST"],
        &[":primitives/Int 42"],
    );
}

// spec: spec/09-macros.md §9.5 — const with string value
#[test]
fn macro_const_string() {
    assert_repl_lines_contain(
        &[r#"(const GREETING "hi")"#, "GREETING"],
        &[":primitives/String \"hi\""],
    );
}

// =============================================================================
// w. Prelude macros: def
// =============================================================================

// spec: spec/09-macros.md §9.5 — def creates named value
#[test]
fn macro_def_basic() {
    assert_repl_lines_contain(&["(def MY-VAL 42)", "MY-VAL"], &[":primitives/Int 42"]);
}

// spec: spec/09-macros.md §9.5 — def with expression
#[test]
fn macro_def_expression() {
    assert_repl_lines_contain(
        &[
            "(import [primitives [add-i64]])",
            "(def MY-SUM (add-i64 1 2))",
            "MY-SUM",
        ],
        &[":primitives/Int 3"],
    );
}

// =============================================================================
// x. Prelude macros: -> (thread-first)
// =============================================================================

// spec: spec/09-macros.md §9.5 — thread-first single form: (-> 5 (+ 3)) => 8
#[test]
fn macro_thread_first_single() {
    assert_repl_eval_contains("(-> 5 (+ 3))", ":primitives/Int 8");
}

// spec: spec/09-macros.md §9.5 — thread-first bare symbol: (-> 5 show) => "5"
#[test]
fn macro_thread_first_bare() {
    assert_repl_eval_contains("(-> 5 show)", ":primitives/String \"5\"");
}

// spec: spec/09-macros.md §9.5 — thread-first multi-form: (-> 1 (+ 2) (* 3)) => 9
#[test]
fn macro_thread_first_multi() {
    assert_repl_eval_contains("(-> 1 (+ 2) (* 3))", ":primitives/Int 9");
}

// =============================================================================
// y. Prelude macros: ->> (thread-last)
// =============================================================================

// spec: spec/09-macros.md §9.5 — thread-last single form: (->> 5 (+ 3)) => 8
#[test]
fn macro_thread_last_single() {
    assert_repl_eval_contains("(->> 5 (+ 3))", ":primitives/Int 8");
}

// spec: spec/09-macros.md §9.5 — thread-last bare symbol: (->> 5 show) => "5"
#[test]
fn macro_thread_last_bare() {
    assert_repl_eval_contains("(->> 5 show)", ":primitives/String \"5\"");
}

// spec: spec/09-macros.md §9.5 — thread-last multi-form: (->> 1 (+ 2) (* 3)) => 9
#[test]
fn macro_thread_last_multi() {
    assert_repl_eval_contains("(->> 1 (+ 2) (* 3))", ":primitives/Int 9");
}

// =============================================================================
// Sprint 109 W1-prep — AN-1(b) prelude-cascade availability smoke.
// Plan: tests/plan/PLAN.md §S109 §D.1 AN-1.
// =============================================================================

// spec: spec/08-modules.md §8.6.2 + root CLAUDE.md stdlib-separation exception —
// AN-1(b): each core prelude name `do`/`pure`/`cond`/`when`/`case`/`vec`/`list`/
// `def` is available (the cascade that took them ALL down via one submodule's
// one-hop miss must not recur). GREEN today; invariance pin + commit-2 acceptance.
// Gated stdlib-conformance entry (the sole sanctioned workspace-stdlib use).
#[test]
fn workspace_prelude_core_names_all_available() {
    let out = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .repl()
        .stdin(
            "(do (pure 1) (pure 42))\n\
             (cond (= 1 1) 10 20)\n\
             (when true (Some 7))\n\
             (case 2 1 100 2 200 999)\n\
             (vec 1 2 3)\n\
             (list 1 2 3)\n\
             (def answer 55)\n\
             answer\n",
        )
        .output()
        .assert_ok();
    // Cascade guard: NONE of the core names may be undefined.
    for name in ["do", "pure", "cond", "when", "case", "vec", "list", "def"] {
        assert!(
            !out.stdout.contains(&format!("undefined variable: {name}")),
            "core prelude name `{name}` MUST be available (AN-1 cascade guard); \
             got:\n{}",
            out.stdout
        );
    }
    // Positive witnesses that a representative macro + `def` actually evaluate.
    assert!(
        out.stdout.contains(":primitives/Int 42") // (do (pure 1) (pure 42))
            && out.stdout.contains(":primitives/Int 10") // (cond (= 1 1) 10 20)
            && out.stdout.contains(":primitives/Int 200") // (case 2 … 2 200 …)
            && out.stdout.contains(":primitives/Int 55"), // (def answer 55) ; answer
        "the core prelude names MUST evaluate to their expected values \
         (AN-1 availability); got:\n{}",
        out.stdout
    );
}
