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
use cranelisp_types::{FQTypeName, ModuleFullPath, Type, TypeName};
use serial_test::serial;

/// Helper: build REPL session with inline traits and a factorial function,
/// with trace imported from primitives.
///
fn setup_repl_with_fact() -> helpers::ReplSession {
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
        Type::ADT(FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Trace")), vec![]),
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
        Type::ADT(FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Trace")), vec![]),
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
    assert_eq!(ty, Type::ADT(FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Trace")), vec![]));
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
        Type::ADT(FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Trace")), vec![]),
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
    let expected = Type::ADT(FQTypeName::new(ModuleFullPath::from("macros"), TypeName::from("SList")), vec![Type::String]);
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
        FQTypeName::new(ModuleFullPath::from("macros"), TypeName::from("SList")),
        vec![Type::ADT(FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Trace")), vec![])],
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
        Type::ADT(FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Trace")), vec![]),
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
        Type::ADT(FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Trace")), vec![]),
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

// spec: 02-grammar §2.2 + 04-expressions §4.12 — trace keyword always in scope
#[test]
#[serial]
fn trace_form_available_without_import() {
    let mut s = repl_session_with(None, None);
    // trace is a parser keyword — always available without import
    let result = s.eval("(defn id [x] x)");
    assert!(result.is_ok());
    let result = s.eval("(trace (id 42))");
    assert!(result.is_ok(), "trace form should work without import");
}

// spec: 04-expressions §4.12.4 — TraceCall requires import for pattern matching
#[test]
#[serial]
fn trace_type_requires_import_for_match() {
    let mut s = repl_session_with(None, None);
    let result = s.eval("(defn id [x] x)");
    assert!(result.is_ok());
    // Pattern matching on TraceCall without import should fail
    let result = s.eval("(match (trace (id 42)) [(TraceCall n p r c ns) n])");
    assert!(result.is_err(), "TraceCall pattern match should fail without import");
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
    assert_eq!(ty, Type::ADT(FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Trace")), vec![]));
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
    assert_eq!(ty, Type::ADT(FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Trace")), vec![]));
    assert_ne!(val, 0, "trace value should be a heap pointer");
}

// =============================================================================
// /run-tests slash command + discover-tests/run-test special forms — Ring 4
//
// The old `(run-tests init pass-fn fail-fn)` sexp-level API has been replaced:
//
// 1. `/run-tests` REPL slash command — discovers test-* functions in the
//    current module and runs them, producing formatted output (ok/FAILED).
//    Tested via `session.process_commands("/run-tests", ...)`.
//
// 2. `discover-tests` and `run-test` special forms — programmatic primitives
//    in the `primitives` module. `(discover-tests)` returns `IO(SList Sexp)`
//    with SexpSym values for test-* functions. `(run-test name)` takes a
//    Sexp and returns `IO(TestResult)` — TestPass or TestFail.
//    Tested via `session.eval(...)`.
//
// See spec: appendix-a-builtins.md (discover-tests, run-test),
//      spec: 03-types.md §3.2.5 (TestResult type).
// =============================================================================

/// Helper: invoke a slash command on a session and return the output string.
fn run_slash_command(s: &mut helpers::ReplSession, cmd: &str) -> String {
    use cranelisp::session_v4::CommandResult;
    let mut stdout = Vec::new();
    let result = s.session.process_commands(cmd, &mut stdout);
    match result {
        CommandResult::Final(output) => output,
        _ => {
            let stdout_str = String::from_utf8_lossy(&stdout).to_string();
            panic!("expected CommandResult::Final from '{cmd}', got stdout: {stdout_str}");
        }
    }
}

// spec: repl/spec.md §3 + appendix-a-builtins — /run-tests discovers and runs passing test
#[test]
#[serial(trace)]
fn run_tests_basic_pass() {
    let mut s = repl_session_with_test_prelude();
    // Define a test function returning None (pass)
    repl_eval(&mut s, "(defn test-one [] None)");
    let output = run_slash_command(&mut s, "/run-tests");
    assert!(
        output.contains("ok"),
        "passing test should show 'ok' in output, got: {output}"
    );
    assert!(
        output.contains("1 passed"),
        "should report 1 passed, got: {output}"
    );
}

// spec: repl/spec.md §3 + appendix-a-builtins — /run-tests reports failing test
#[test]
#[serial(trace)]
fn run_tests_basic_fail() {
    let mut s = repl_session_with_test_prelude();
    // Define a test function returning Some (fail)
    repl_eval(&mut s, "(defn test-fail [] (Some \"expected failure\"))");
    let output = run_slash_command(&mut s, "/run-tests");
    assert!(
        output.contains("FAIL"),
        "failing test should show 'FAIL' in output, got: {output}"
    );
    assert!(
        output.contains("expected failure"),
        "failure reason should appear in output, got: {output}"
    );
}

// spec: repl/spec.md §3 + appendix-a-builtins — /run-tests with multiple tests
#[test]
#[serial(trace)]
fn run_tests_multiple_tests() {
    let mut s = repl_session_with_test_prelude();
    // Define 3 passing test functions
    repl_eval(&mut s, "(defn test-a [] None)");
    repl_eval(&mut s, "(defn test-b [] None)");
    repl_eval(&mut s, "(defn test-c [] None)");
    let output = run_slash_command(&mut s, "/run-tests");
    assert!(
        output.contains("3 passed"),
        "three passing tests should report '3 passed', got: {output}"
    );
}

// spec: repl/spec.md §3 + appendix-a-builtins — /run-tests with no test functions
#[test]
#[serial(trace)]
fn run_tests_empty_no_tests() {
    let mut s = repl_session_with_test_prelude();
    // No test-* functions defined
    let output = run_slash_command(&mut s, "/run-tests");
    assert!(
        output.contains("No test-* functions found"),
        "with no test functions, should report 'No test-* functions found', got: {output}"
    );
}

// spec: repl/spec.md §3 + appendix-a-builtins — /run-tests with mixed pass and fail
#[test]
#[serial(trace)]
fn run_tests_mixed_pass_fail() {
    let mut s = repl_session_with_test_prelude();
    // 2 passing, 1 failing
    repl_eval(&mut s, "(defn test-pass-1 [] None)");
    repl_eval(&mut s, "(defn test-pass-2 [] None)");
    repl_eval(&mut s, "(defn test-fail-1 [] (Some \"broken\"))");
    let output = run_slash_command(&mut s, "/run-tests");
    assert!(
        output.contains("2 passed"),
        "should report 2 passed, got: {output}"
    );
    assert!(
        output.contains("1 failed"),
        "should report 1 failed, got: {output}"
    );
}

// spec: appendix-a-builtins — discover-tests special form returns IO(SList(Sexp))
//
// Sprint 57 Wave 6: eval unwraps IO inline, so the caller sees the unwrapped
// inner type (SList(Sexp)). The IO-wrapped shape at the type-inference level
// is covered by typecheck unit tests; at the eval boundary we assert the
// unwrapped inner type.
#[test]
#[serial(trace)]
fn run_tests_discover_tests_form_type() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(&mut s, "(import [primitives [discover-tests]])");
    // Define a test so there's something to discover
    repl_eval(&mut s, "(defn test-ok [] None)");
    // (discover-tests) : IO(SList Sexp); eval unwraps to (SList Sexp).
    let (_val, ty) = repl_eval_typed(&mut s, "(discover-tests)");
    let ty_str = format!("{:?}", ty);
    assert!(
        ty_str.contains("SList") && !ty_str.contains("IO"),
        "discover-tests IO(SList Sexp) must unwrap to SList Sexp; got: {ty_str}"
    );
}

// spec: appendix-a-builtins — run-test special form returns IO(TestResult)
//
// Sprint 57 Wave 6: eval unwraps IO inline; caller sees TestResult.
#[test]
#[serial(trace)]
fn run_tests_run_test_form_type() {
    let mut s = repl_session_with_test_prelude();
    repl_eval(&mut s, "(import [primitives [run-test]])");
    // Define a test function
    repl_eval(&mut s, "(defn test-ok [] None)");
    // (run-test user/test-ok) : IO(TestResult); eval unwraps to TestResult.
    let (_val, ty) = repl_eval_typed(&mut s, "(run-test user/test-ok)");
    let ty_str = format!("{:?}", ty);
    assert!(
        ty_str.contains("TestResult") && !ty_str.contains("IO"),
        "run-test IO(TestResult) must unwrap to TestResult; got: {ty_str}"
    );
}
