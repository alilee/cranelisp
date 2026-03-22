// Ring 4 integration tests: trace special form (spec §4.12).
//
// Tests the `(trace expr)` special form which instruments function calls
// and returns a Trace ADT value recording the call tree.
//
// Trace is compiler-seeded in the `primitives` module. Per spec §3.2.4,
// `trace` requires explicit import from `primitives`. The Trace ADT has a
// single constructor TraceCall with fields: name, params, result, children, nanos.
//
// Tests MUST NOT depend on stdlib. Uses compiler primitives directly.
// Inline trait definitions are used where operators (+, -, *, =, <) are needed.
//
// IMPORTANT: Tests that invoke `(trace ...)` or `(run-tests ...)` must be
// serialized because the runtime trace infrastructure uses process-global
// state (`TRACE_THREAD_ID`, `TRACE_STACK`) that races when tests run in
// parallel on different threads.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::*;
use cranelisp_types::{Type, TypeName};
use serial_test::serial;

/// Helper: build REPL session with inline traits and a factorial function,
/// with trace imported from primitives.
///
fn setup_repl_with_fact() -> cranelisp::repl::ReplSession {
    let mut s = repl_session_with_test_prelude();
    repl_eval(&mut s, "(import [primitives [trace Trace TraceCall]])");
    repl_eval(&mut s, "(defn fact [n] (if (= n 0) 1 (* n (fact (- n 1)))))");
    s
}

// =============================================================================
// §4.12.1 — Trace type: (trace expr) always returns Trace
// =============================================================================

// spec: 04-expressions §4.12.1 — trace returns Trace type for Int body
#[test]
#[serial(trace)]
fn trace_returns_trace_type_int_body() {
    let mut s = setup_repl_with_fact();
    let (_val, ty) = repl_eval_typed(&mut s, "(trace (fact 5))");
    assert_eq!(
        ty,
        Type::ADT("Trace".into(), vec![]),
        "trace should return Trace type, got: {:?}",
        ty
    );
}

// spec: 04-expressions §4.12.1 — trace returns Trace regardless of body type
#[test]
#[serial(trace)]
fn trace_returns_trace_type_regardless_of_body() {
    let mut s = repl_session();
    repl_eval(&mut s, "(import [primitives [trace Trace TraceCall]])");
    // A function returning Bool
    repl_eval(&mut s, "(defn always-true [] true)");
    let (_val, ty) = repl_eval_typed(&mut s, "(trace (always-true))");
    assert_eq!(
        ty,
        Type::ADT("Trace".into(), vec![]),
        "trace should return Trace type even for Bool body, got: {:?}",
        ty
    );
}

// =============================================================================
// §4.12.2 — Basic trace semantics
// =============================================================================

// spec: 04-expressions §4.12.2 — tracing a recursive function returns a Trace value
#[test]
#[serial(trace)]
fn trace_basic_fact() {
    let mut s = setup_repl_with_fact();
    // trace (fact 5) should succeed and return a non-zero Trace value
    let (val, ty) = repl_eval_typed(&mut s, "(trace (fact 5))");
    assert_eq!(ty, Type::ADT("Trace".into(), vec![]));
    // The value should be a heap pointer (non-zero)
    assert_ne!(val, 0, "trace should return a heap-allocated Trace value");
}

// spec: 04-expressions §4.12.2 — tracing an expression with no user-defined calls
#[test]
#[serial(trace)]
fn trace_inline_primitive_no_calls() {
    let mut s = repl_session();
    repl_eval(&mut s, "(import [primitives [trace Trace TraceCall]])");
    // (+ 1 2) uses inline primitives — no user-defined calls to trace.
    // Should still return a Trace value (with an empty/root-only call tree).
    let (_val, ty) = repl_eval_typed(&mut s, "(trace (add-i64 1 2))");
    assert_eq!(
        ty,
        Type::ADT("Trace".into(), vec![]),
        "trace of inline primitive should still return Trace type"
    );
}

// spec: 04-expressions §4.12.2 — trace of user function has non-empty children (direct subexpr)
#[test]
#[serial(trace)]
fn trace_has_children_subexpr() {
    let mut s = setup_repl_with_fact();
    repl_eval(&mut s, "(import [primitives [children]])");
    repl_eval(&mut s, "(import [macros [SCons SNil]])");
    let display = repl_eval_display(&mut s, "(match (children (trace (fact 3))) [(SCons _ _) true SNil false])");
    assert!(
        display.contains("true"),
        "trace of user function should have non-empty children, got: {display}"
    );
}

// spec: 04-expressions §4.12.2 — trace children accessible via let binding
#[test]
#[serial(trace)]
fn trace_has_children_via_let() {
    let mut s = setup_repl_with_fact();
    repl_eval(&mut s, "(import [primitives [children]])");
    repl_eval(&mut s, "(import [macros [SCons SNil]])");
    let display = repl_eval_display(&mut s, "(let [t (trace (fact 3))] (match (children t) [(SCons _ _) true SNil false]))");
    assert!(
        display.contains("true"),
        "trace via let should have non-empty children, got: {display}"
    );
}

// =============================================================================
// §4.12.3 — What is traced (user-defined functions only)
// =============================================================================

// spec: 04-expressions §4.12.3 — user-defined functions are traced
// The root trace node is always "::trace::" — actual function calls are in children.
#[test]
#[serial(trace)]
fn trace_user_defined_function() {
    let mut s = setup_repl_with_fact();
    repl_eval(&mut s, "(import [primitives [name]])");
    // Root trace name is always "::trace::" per spec §4.12.2
    let display = repl_eval_display(&mut s, "(let [t (trace (fact 3))] (name t))");
    assert!(
        display.contains("::trace::"),
        "root trace name should be '::trace::', got: {display}"
    );
}

// spec: 04-expressions §4.12.3 — name accessor on trace subexpression
#[test]
#[serial(trace)]
fn trace_user_defined_function_subexpr() {
    let mut s = setup_repl_with_fact();
    repl_eval(&mut s, "(import [primitives [name]])");
    let display = repl_eval_display(&mut s, "(name (trace (fact 3)))");
    assert!(
        display.contains("::trace::"),
        "root trace name should be '::trace::', got: {display}"
    );
}

// =============================================================================
// §4.12.4 — Trace ADT field access
// =============================================================================

// spec: 04-expressions §4.12.4 — name field returns String
#[test]
#[serial(trace)]
fn trace_field_name_returns_string() {
    let mut s = setup_repl_with_fact();
    repl_eval(&mut s, "(import [primitives [name]])");
    let (_val, ty) = repl_eval_typed(&mut s, "(name (trace (fact 3)))");
    assert_eq!(
        ty,
        Type::String,
        "name field of Trace should be String, got: {:?}",
        ty
    );
}

// spec: 04-expressions §4.12.4 — params field returns (SList String)
#[test]
#[serial(trace)]
fn trace_field_params_returns_slist_string() {
    let mut s = setup_repl_with_fact();
    repl_eval(&mut s, "(import [primitives [params]])");
    let (_val, ty) = repl_eval_typed(&mut s, "(params (trace (fact 3)))");
    let expected = Type::ADT(TypeName::from("SList"), vec![Type::String]);
    assert_eq!(
        ty,
        expected,
        "params field of Trace should be (SList String), got: {:?}",
        ty
    );
}

// spec: 04-expressions §4.12.4 — result field returns String
#[test]
#[serial(trace)]
fn trace_field_result_returns_string() {
    let mut s = setup_repl_with_fact();
    repl_eval(&mut s, "(import [primitives [result]])");
    let (_val, ty) = repl_eval_typed(&mut s, "(result (trace (fact 3)))");
    assert_eq!(
        ty,
        Type::String,
        "result field of Trace should be String, got: {:?}",
        ty
    );
}

// spec: 04-expressions §4.12.4 — nanos field returns Int
#[test]
#[serial(trace)]
fn trace_field_nanos_returns_int() {
    let mut s = setup_repl_with_fact();
    repl_eval(&mut s, "(import [primitives [nanos]])");
    let (_val, ty) = repl_eval_typed(&mut s, "(nanos (trace (fact 3)))");
    assert_eq!(
        ty,
        Type::Int,
        "nanos field of Trace should be Int, got: {:?}",
        ty
    );
}

// spec: 04-expressions §4.12.4 — children field returns (SList Trace)
#[test]
#[serial(trace)]
fn trace_field_children_returns_slist_trace() {
    let mut s = setup_repl_with_fact();
    repl_eval(&mut s, "(import [primitives [children]])");
    let (_val, ty) = repl_eval_typed(&mut s, "(children (trace (fact 3)))");
    let expected = Type::ADT(
        TypeName::from("SList"),
        vec![Type::ADT(TypeName::from("Trace"), vec![])],
    );
    assert_eq!(
        ty,
        expected,
        "children field of Trace should be (SList Trace), got: {:?}",
        ty
    );
}

// =============================================================================
// §4.12.5 — Nested trace
// =============================================================================

// spec: 04-expressions §4.12.5 — nested trace produces single Trace, not nested
#[test]
#[serial(trace)]
fn trace_nested_single_trace() {
    let mut s = setup_repl_with_fact();
    // (trace (trace (fact 3))) should produce a single Trace value
    let (_val, ty) = repl_eval_typed(&mut s, "(trace (trace (fact 3)))");
    assert_eq!(
        ty,
        Type::ADT("Trace".into(), vec![]),
        "nested trace should still return Trace type, got: {:?}",
        ty
    );
}

// =============================================================================
// §4.12.7 — Composability: Trace is an ordinary ADT value
// =============================================================================

// spec: 04-expressions §4.12.7 — trace value can be bound with let
#[test]
#[serial(trace)]
fn trace_composability_let_binding() {
    let mut s = setup_repl_with_fact();
    let (_val, ty) = repl_eval_typed(&mut s, "(let [t (trace (fact 3))] t)");
    assert_eq!(
        ty,
        Type::ADT("Trace".into(), vec![]),
        "let-bound trace should be Trace type, got: {:?}",
        ty
    );
}

// spec: 04-expressions §4.12.7 — trace value can be passed to a function
#[test]
#[serial(trace)]
fn trace_composability_pass_to_function() {
    let mut s = setup_repl_with_fact();
    repl_eval(&mut s, "(import [primitives [name]])");
    // Define a function that takes a Trace and returns its name
    repl_eval(&mut s, "(defn trace-name [t] (name t))");
    let (_val, ty) = repl_eval_typed(&mut s, "(trace-name (trace (fact 3)))");
    assert_eq!(
        ty,
        Type::String,
        "function taking Trace should work, got: {:?}",
        ty
    );
}

// spec: 04-expressions §4.12.7 — pattern matching on Trace ADT
#[test]
#[serial(trace)]
fn trace_composability_pattern_match() {
    let mut s = setup_repl_with_fact();
    // Pattern match on TraceCall constructor
    let (_val, ty) = repl_eval_typed(
        &mut s,
        "(let [t (trace (fact 3))] (match t [(TraceCall n p r c ns) n]))",
    );
    assert_eq!(
        ty,
        Type::String,
        "pattern matching on TraceCall should extract name as String, got: {:?}",
        ty
    );
}

// =============================================================================
// Import requirement: trace must be imported from primitives
// =============================================================================

// spec: 04-expressions §4.12 + 03-types §3.2.4 — trace without import fails
#[test]
fn trace_without_import_fails() {
    let mut s = repl_session();
    // trace is NOT auto-imported; using it without import should error
    let result = s.eval("(trace (add-i64 1 2))");
    assert!(
        result.is_err(),
        "trace without import should produce an error"
    );
    let err_msg = match result {
        Err(e) => e.to_string(),
        Ok(_) => panic!("expected error but eval succeeded"),
    };
    assert!(
        err_msg.contains("trace") || err_msg.contains("undefined") || err_msg.contains("Undefined"),
        "error should mention trace or undefined, got: {err_msg}"
    );
}

// =============================================================================
// Trace ADT type registration (can verify without using trace special form)
// =============================================================================

// spec: 03-types §3.2.4 — Trace type is importable from primitives
#[test]
fn trace_type_importable_from_primitives() {
    let mut s = repl_session();
    // Trace, TraceCall, and field accessors should be in primitives
    let result = s.eval("(import [primitives [Trace TraceCall]])");
    assert!(
        result.is_ok(),
        "importing Trace and TraceCall from primitives should succeed, got: {:?}",
        result.err()
    );
}

// spec: 03-types §3.2.4 — Trace field accessors importable from primitives
#[test]
fn trace_field_accessors_importable() {
    let mut s = repl_session();
    let result = s.eval("(import [primitives [Trace TraceCall name params result children nanos]])");
    assert!(
        result.is_ok(),
        "importing Trace field accessors from primitives should succeed, got: {:?}",
        result.err()
    );
}

// spec: 03-types §3.2.4 — Trace is NOT auto-imported
#[test]
fn trace_type_not_auto_imported() {
    let mut s = repl_session();
    // Using TraceCall without import should fail
    let result = s.eval("(TraceCall)");
    assert!(
        result.is_err(),
        "TraceCall without import should produce an error"
    );
}

// =============================================================================
// §4.12.8 — Examples from spec
// =============================================================================

// spec: 04-expressions §4.12.8 — composed expression tracing
// Root trace is always "::trace::" — actual function calls are in children.
#[test]
#[serial(trace)]
fn trace_composed_expression() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(&mut s, "(import [primitives [trace Trace TraceCall name]])");
    repl_eval(&mut s, "(defn double [x] (* x 2))");
    repl_eval(&mut s, "(defn inc-then-double [x] (double (+ x 1)))");
    let (_val, ty) = repl_eval_typed(&mut s, "(trace (inc-then-double 3))");
    assert_eq!(ty, Type::ADT("Trace".into(), vec![]));
    // Root trace name is always "::trace::" — use let binding
    let display = repl_eval_display(&mut s, "(let [t (trace (inc-then-double 3))] (name t))");
    assert!(
        display.contains("::trace::"),
        "root trace name should be '::trace::', got: {display}"
    );
}

// spec: 04-expressions §4.12.8 — trace is a value, not an effect
#[test]
#[serial(trace)]
fn trace_is_value_not_effect() {
    let mut s = setup_repl_with_fact();
    // (let [t (trace (fact 3))] t) — should just return the Trace, no side effects
    let (val, ty) = repl_eval_typed(&mut s, "(let [t (trace (fact 3))] t)");
    assert_eq!(ty, Type::ADT("Trace".into(), vec![]));
    assert_ne!(val, 0, "trace value should be a heap pointer");
}

// =============================================================================
// (run-tests init pass-fn fail-fn) special form — Ring 4
//
// The `(run-tests ...)` special form is parsed by the AST builder into
// Expr::RunTests, typechecked with accumulator/pass-fn/fail-fn inference,
// and compiled by the backend. In REPL mode it discovers and runs test-*
// functions; in batch mode it returns init unchanged.
//
// The `/run-tests` slash command (separate from the expression form) is
// tested in tests/e2e.rs.
// =============================================================================

// spec: run-tests special form — basic pass: single passing test, counter increments
#[test]
#[serial(trace)]
fn run_tests_basic_pass() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(&mut s, "(import [primitives [trace Trace TraceCall]])");
    // Define a test function returning None (pass)
    repl_eval(&mut s, "(defn test-one [] None)");
    // Run tests with a counter: pass-fn increments, fail-fn increments
    let result = repl_eval(
        &mut s,
        "(run-tests 0 (fn [acc name nanos] (add-i64 acc 1)) (fn [acc name nanos reason trace] (add-i64 acc 100)))",
    );
    assert_eq!(result, 1, "one passing test should increment counter by 1");
}

// spec: run-tests special form — basic fail: single failing test
#[test]
#[serial(trace)]
fn run_tests_basic_fail() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(&mut s, "(import [primitives [trace Trace TraceCall]])");
    // Define a test function returning Some (fail)
    repl_eval(&mut s, "(defn test-fail [] (Some \"expected failure\"))");
    // pass-fn adds 1, fail-fn adds 100 — result should be 100
    let result = repl_eval(
        &mut s,
        "(run-tests 0 (fn [acc name nanos] (add-i64 acc 1)) (fn [acc name nanos reason trace] (add-i64 acc 100)))",
    );
    assert_eq!(result, 100, "one failing test should invoke fail-fn");
}

// spec: run-tests special form — multiple tests accumulate correctly
#[test]
#[serial(trace)]
fn run_tests_multiple_tests() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(&mut s, "(import [primitives [trace Trace TraceCall]])");
    // Define 3 passing test functions
    repl_eval(&mut s, "(defn test-a [] None)");
    repl_eval(&mut s, "(defn test-b [] None)");
    repl_eval(&mut s, "(defn test-c [] None)");
    // Counter should reach 3
    let result = repl_eval(
        &mut s,
        "(run-tests 0 (fn [acc name nanos] (add-i64 acc 1)) (fn [acc name nanos reason trace] (add-i64 acc 1)))",
    );
    assert_eq!(result, 3, "three passing tests should increment counter to 3");
}

// spec: run-tests special form — batch mode returns init unchanged
#[test]
fn run_tests_batch_returns_init() {
    // In batch mode, run-tests returns init unchanged (no test discovery)
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn test-a [] None)
        (defn main [] (run-tests 42 (fn [acc name nanos] acc) (fn [acc name nanos reason trace] acc)))
    "#;
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: run-tests special form — no test functions returns init
#[test]
#[serial(trace)]
fn run_tests_empty_no_tests() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(&mut s, "(import [primitives [trace Trace TraceCall]])");
    // No test-* functions defined — should return init (99) unchanged
    let result = repl_eval(
        &mut s,
        "(run-tests 99 (fn [acc name nanos] (add-i64 acc 1)) (fn [acc name nanos reason trace] (add-i64 acc 1)))",
    );
    assert_eq!(result, 99, "with no test functions, init should be returned unchanged");
}

// spec: run-tests special form — mixed pass and fail
#[test]
#[serial(trace)]
fn run_tests_mixed_pass_fail() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(&mut s, "(import [primitives [trace Trace TraceCall]])");
    // 2 passing, 1 failing
    repl_eval(&mut s, "(defn test-pass-1 [] None)");
    repl_eval(&mut s, "(defn test-pass-2 [] None)");
    repl_eval(&mut s, "(defn test-fail-1 [] (Some \"broken\"))");
    // pass-fn adds 1, fail-fn adds 100
    let result = repl_eval(
        &mut s,
        "(run-tests 0 (fn [acc name nanos] (add-i64 acc 1)) (fn [acc name nanos reason trace] (add-i64 acc 100)))",
    );
    assert_eq!(result, 102, "2 passes (2) + 1 fail (100) = 102");
}
