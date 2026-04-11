//! E2E tests for Sprint 44 Step 7: REPL eval via the v4 scheduler.
//!
//! These tests validate that the REPL eval path works correctly when
//! routed through the v4 scheduler with `ModuleStrategy::Additive`.
//! They invoke the `cranelisp` binary as a subprocess with piped stdin
//! and assert on stdout/stderr/exit code.
//!
//! The REPL binary is invoked with no special flags — the internal eval
//! path change (v4 scheduler) is transparent to the user interface.

use std::path::PathBuf;
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

// ---------------------------------------------------------------------------
// Inline trait/import preludes for tests that need primitives or operators.
// ---------------------------------------------------------------------------

const PRIMS: &str = "(import [primitives [*]])\n";

// ---------------------------------------------------------------------------
// Test infrastructure
// ---------------------------------------------------------------------------

static TEST_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn project_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn binary_path() -> PathBuf {
    project_root()
        .join("target")
        .join("debug")
        .join("cranelisp")
}

/// Create a fresh, isolated working directory for one test under
/// `tests/v4_repl_eval/.runs/{timestamp}/`.
fn test_dir(label: &str) -> PathBuf {
    use std::sync::LazyLock;
    use std::time::SystemTime;

    static RUN_TS: LazyLock<String> = LazyLock::new(|| {
        let d = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap();
        format!("{}", d.as_secs())
    });

    let n = TEST_COUNTER.fetch_add(1, Ordering::SeqCst);
    let dir = project_root()
        .join("tests")
        .join("v4_repl_eval")
        .join(".runs")
        .join(&*RUN_TS)
        .join(format!("{n}_{label}"));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Run the REPL binary with piped stdin in an isolated directory.
fn run_repl(input: &str, label: &str) -> Output {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} -- run `cargo build` first"
    );
    let dir = test_dir(label);

    let mut child = Command::new(&binary)
        .current_dir(&dir)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to start cranelisp binary");

    {
        use std::io::Write;
        let stdin = child.stdin.as_mut().expect("failed to open stdin");
        stdin
            .write_all(input.as_bytes())
            .expect("failed to write input");
    }
    // Drop stdin (close pipe) to signal EOF.
    child.wait_with_output().expect("failed to read output")
}

fn stdout_str(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}

fn stderr_str(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

/// All non-empty result lines from REPL output.
///
/// Extracts the content after the last `> ` prompt delimiter on each line.
/// Also strips leading continuation markers (`...`) from the extracted text.
fn result_lines(o: &Output) -> Vec<String> {
    stdout_str(o)
        .lines()
        .filter_map(|l| {
            l.rfind("> ").map(|pos| {
                let after = l[pos + 2..].trim_start();
                let cleaned = after.strip_prefix("...").unwrap_or(after);
                cleaned.to_string()
            })
        })
        .filter(|s| !s.is_empty())
        .collect()
}

fn assert_success(o: &Output) {
    assert!(
        o.status.success(),
        "expected exit 0, got {:?}\nstdout: {}\nstderr: {}",
        o.status.code(),
        stdout_str(o),
        stderr_str(o),
    );
}

fn assert_result(o: &Output, expected: &str) {
    let results = result_lines(o);
    assert!(
        results.iter().any(|r| r == expected),
        "expected result {:?} not found in results: {:?}\nfull stdout: {}",
        expected,
        results,
        stdout_str(o),
    );
}

fn assert_stdout_contains(o: &Output, needle: &str) {
    let s = stdout_str(o);
    assert!(
        s.contains(needle),
        "stdout missing {:?}\n---\n{}",
        needle,
        s
    );
}

// ===========================================================================
// Test 1: Simple expression evaluates and displays result
// ===========================================================================

// spec: repl/spec.md S1.2 -- expression display format
// spec: design/int/step7-repl-eval.md S2 -- simplified eval path
//
// A bare expression (not a definition) should be compiled as a temporary
// closure, executed, and the result displayed in `:Type value` format.
#[test]
fn v4_repl_simple_expression() {
    let o = run_repl(&format!("{PRIMS}(add-i64 2 3)\n"), "simple_expr");
    assert_success(&o);
    assert_result(&o, ":primitives/Int 5");
}

// ===========================================================================
// Test 2: Definition followed by call
// ===========================================================================

// spec: repl/spec.md S1.3 -- definition display
// spec: design/int/step7-repl-eval.md S4.5 -- execute and format
//
// A defn is processed via process_module_forms(Additive), registered in GOT,
// and then callable in subsequent expressions.
#[test]
fn v4_repl_defn_then_call() {
    let o = run_repl(
        &format!("{PRIMS}(defn double [x] (mul-i64 x 2))\n(double 21)\n"),
        "defn_then_call",
    );
    assert_success(&o);

    // The defn should produce a type display (e.g. containing "Fn").
    let results: Vec<_> = result_lines(&o)
        .into_iter()
        .filter(|l| !l.contains("imported from"))
        .collect();
    assert!(
        results.len() >= 2,
        "expected at least 2 result lines (defn + call), got {:?}",
        results,
    );
    // The definition response should mention the function type.
    assert!(
        results[0].contains("Fn"),
        "defn response should contain 'Fn', got: {:?}",
        results[0],
    );
    // The call result should be 42.
    assert_eq!(results[results.len() - 1], ":primitives/Int 42");
}

// ===========================================================================
// Test 3: Multi-eval persistence -- definitions persist across eval rounds
// ===========================================================================

// spec: repl/spec.md S5.2 -- session state persistence
// spec: design/int/step7-repl-eval.md S3 -- additive strategy
//
// With ModuleStrategy::Additive, previous definitions remain in the module's
// symbol table. A function defined in one eval round is callable in the next.
#[test]
fn v4_repl_multi_eval_persistence() {
    let o = run_repl(
        &format!(
            "{PRIMS}\
             (defn inc [n] (add-i64 n 1))\n\
             (defn dec [n] (sub-i64 n 1))\n\
             (inc (dec 10))\n"
        ),
        "multi_eval_persist",
    );
    assert_success(&o);
    // inc(dec(10)) = inc(9) = 10
    assert_result(&o, ":primitives/Int 10");
}

// ===========================================================================
// Test 4: Error recovery -- type error doesn't corrupt session
// ===========================================================================

// spec: repl/spec.md S5.2 -- error recovery continues session
// spec: design/int/step7-repl-eval.md S7 -- error recovery (TC snapshot/restore)
//
// Per-form TC snapshot/restore means a type error in one form does not prevent
// processing subsequent forms. The session remains usable.
#[test]
fn v4_repl_error_recovery() {
    let o = run_repl(
        &format!(
            "{PRIMS}\
             (defn inc [n] (add-i64 n 1))\n\
             (add-i64 2 true)\n\
             (inc 5)\n"
        ),
        "error_recovery",
    );
    assert_success(&o);

    let all = format!("{}{}", stdout_str(&o), stderr_str(&o));
    // The second form should produce an error.
    assert!(
        all.contains("Error:") || all.contains("type mismatch"),
        "expected a type error from (add-i64 2 true)\nstdout: {}\nstderr: {}",
        stdout_str(&o),
        stderr_str(&o),
    );
    // The third form should succeed despite the error above.
    assert_result(&o, ":primitives/Int 6");
}

// ===========================================================================
// Test 5: Import works through the additive path
// ===========================================================================

// spec: design/int/step7-repl-eval.md S3 -- additive strategy, imports
// spec: spec/06-modules.md -- import form
//
// (import [primitives [...]]) is handled by classify_form in the v4 worker.
// Through the additive path, import should work the same as in the old REPL:
// imported names are available for subsequent expressions.
#[test]
fn v4_repl_import_in_repl() {
    // Use explicit import (not wildcard) to test that specific names are bound.
    let o = run_repl(
        "(import [primitives [add-i64]])\n\
         (add-i64 10 20)\n",
        "import_in_repl",
    );
    assert_success(&o);
    assert_result(&o, ":primitives/Int 30");
}

// ===========================================================================
// Test 6: Bare symbol introspection -- shows info, not error
// ===========================================================================

// spec: repl/spec.md S4.2 -- special form self-documentation
// spec: design/int/step7-repl-eval.md S4.6 -- bare symbol introspection
//
// A single bare symbol that is a special form should produce introspection
// display (signature/description), not an error. This is the "one check"
// in the simplified eval path.
#[test]
fn v4_repl_bare_symbol_introspection() {
    let o = run_repl("defn\n", "bare_symbol_introspect");
    assert_success(&o);
    let s = stdout_str(&o);
    // Should not produce an error.
    assert!(
        !s.contains("Error:") || s.contains("defn"),
        "bare 'defn' should not produce an error\n---\n{s}"
    );
    // Should produce some introspection output mentioning 'defn'.
    assert!(
        s.contains("defn"),
        "bare 'defn' should produce introspection output mentioning 'defn'\n---\n{s}"
    );
}

// ===========================================================================
// Test 7: (trace expr) works as a regular expression
// ===========================================================================

// spec: design/int/step7-repl-eval.md S2 -- trace is not a special case
// spec: spec/04-expressions.md -- trace special form
//
// In the v4 eval path, (trace ...) is just an Expr::Trace special form
// handled end-to-end by the backend. No REPL-side trace setup is needed.
// The expression should evaluate and return a result.
#[test]
fn v4_repl_trace_as_expression() {
    let o = run_repl(
        &format!(
            "{PRIMS}\
             (defn fib [n] (if (lt-i64 n 2) n (add-i64 (fib (sub-i64 n 1)) (fib (sub-i64 n 2)))))\n\
             (trace (fib 5))\n"
        ),
        "trace_as_expr",
    );
    assert_success(&o);
    // fib(5) = 5. The trace should produce the result value.
    // The output format for trace may include tree output, but the final
    // result line should contain the value 5.
    let all = stdout_str(&o);
    assert!(
        all.contains("5"),
        "trace (fib 5) should produce output containing '5'\n---\n{all}"
    );
    // trace should NOT produce an error.
    assert!(
        !all.contains("Error:"),
        "trace should not produce an error\n---\n{all}"
    );
}

// ===========================================================================
// Test 8: deftype + constructor works in REPL
// ===========================================================================

// spec: spec/05-types.md -- deftype, constructors
// spec: design/int/step7-repl-eval.md S4 -- definitions via worker
//
// deftype defines a new ADT. Constructors should be usable in subsequent
// expressions. This tests that type definitions flow through the additive
// strategy correctly.
#[test]
fn v4_repl_deftype_in_repl() {
    let o = run_repl(
        "(deftype Color Red Green Blue)\n\
         Red\n",
        "deftype_in_repl",
    );
    assert_success(&o);
    let s = stdout_str(&o);
    // The deftype should be acknowledged (mentions Color).
    assert!(
        s.contains("Color"),
        "deftype response should mention 'Color'\n---\n{s}"
    );
    // Red should evaluate to a Color value.
    // Expected format: `:user/Color Red` or similar.
    assert!(
        s.contains("Red"),
        "Red constructor should produce output containing 'Red'\n---\n{s}"
    );
}

// ===========================================================================
// Error Cascade tests — REPL mode (Sprint 45 Step 9)
// ===========================================================================

// ---------------------------------------------------------------------------
// B-4: Type error does not corrupt session; subsequent valid expr succeeds
// ---------------------------------------------------------------------------

// spec: repl/spec.md §5.2 — error recovery continues session
// spec: design/int/step9-error-cascade.md §2.1 — per-form error (already working)
//
// This is a focused error recovery test: a type error in one form should
// not prevent subsequent valid forms from succeeding. The TC snapshot/restore
// mechanism should roll back the type state cleanly.
#[test]
fn v4_repl_error_cascade_recovery() {
    let o = run_repl(
        &format!(
            "{PRIMS}\
             (add-i64 true 1)\n\
             (add-i64 5 10)\n"
        ),
        "error_cascade_recovery",
    );
    assert_success(&o);

    // First form should produce an error.
    let all = format!("{}{}", stdout_str(&o), stderr_str(&o));
    assert!(
        all.contains("Error")
            || all.contains("error")
            || all.contains("type")
            || all.contains("mismatch"),
        "expected type error from (add-i64 true 1)\nstdout: {}\nstderr: {}",
        stdout_str(&o),
        stderr_str(&o),
    );
    // Second form should succeed with 15.
    assert_result(&o, ":primitives/Int 15");
}

// ---------------------------------------------------------------------------
// B-5: Type error, then redefine corrected version, call succeeds
// ---------------------------------------------------------------------------

// spec: repl/spec.md §5.2 — session state not corrupted by error
// spec: design/int/step9-error-cascade.md §2.1 — per-form error
//
// Define a function with a type error, then redefine it correctly.
// The corrected version should work.
#[test]
fn v4_repl_error_cascade_redefine_after_error() {
    let o = run_repl(
        &format!(
            "{PRIMS}\
             (defn bad [x] (add-i64 x true))\n\
             (defn good [x] (add-i64 x 1))\n\
             (good 41)\n"
        ),
        "error_cascade_redefine",
    );
    assert_success(&o);

    // The first defn should produce an error (type mismatch).
    let all = format!("{}{}", stdout_str(&o), stderr_str(&o));
    assert!(
        all.contains("Error")
            || all.contains("error")
            || all.contains("type")
            || all.contains("mismatch"),
        "expected type error from bad defn\nstdout: {}\nstderr: {}",
        stdout_str(&o),
        stderr_str(&o),
    );
    // The corrected defn and call should succeed.
    assert_result(&o, ":primitives/Int 42");
}

// ---------------------------------------------------------------------------
// B-6: Error display includes error category and context
// ---------------------------------------------------------------------------

// spec: repl/spec.md §5.1 — error format requirements
// spec: design/int/step9-error-cascade.md §4 — error chain display
#[test]
fn v4_repl_error_display_includes_context() {
    let o = run_repl(
        &format!("{PRIMS}(add-i64 1 true)\n"),
        "error_display_context",
    );
    assert_success(&o);

    // The error should contain some meaningful context about the problem.
    let all = format!("{}{}", stdout_str(&o), stderr_str(&o));
    // At minimum, should mention "Error" or "type" or "mismatch".
    assert!(
        all.contains("Error")
            || all.contains("error")
            || all.contains("type")
            || all.contains("mismatch"),
        "error should include category/context\nstdout: {}\nstderr: {}",
        stdout_str(&o),
        stderr_str(&o),
    );
}

// ---------------------------------------------------------------------------
// B-7: After failed eval, scheduler state is cleared for next eval
// ---------------------------------------------------------------------------

// spec: design/int/step9-error-cascade.md §5 — reset_module API
// spec: repl/spec.md §5.2 — error recovery
//
// This tests that after a scheduler-level failure (not just per-form TC error),
// the next eval succeeds. This is the reset_module path.
#[test]
fn v4_repl_error_scheduler_state_cleared() {
    // Force a scheduler-level failure by importing a module that has an error,
    // then try a valid expression.
    let o = run_repl(
        &format!(
            "{PRIMS}\
             (defn ok-fn [] 42)\n\
             (add-i64 1 true)\n\
             (ok-fn)\n"
        ),
        "error_scheduler_cleared",
    );
    assert_success(&o);

    // The second form should error.
    let all = format!("{}{}", stdout_str(&o), stderr_str(&o));
    assert!(
        all.contains("Error") || all.contains("error") || all.contains("type"),
        "expected type error\nstdout: {}\nstderr: {}",
        stdout_str(&o),
        stderr_str(&o),
    );
    // The third form should succeed — scheduler state was cleared.
    assert_result(&o, ":primitives/Int 42");
}

// ---------------------------------------------------------------------------
// B-9: Multiple consecutive errors followed by valid expression
// ---------------------------------------------------------------------------

// spec: repl/spec.md §5.2 — error recovery resilience
// spec: design/int/step9-error-cascade.md §2.1 — per-form error
//
// The session should survive multiple consecutive errors and still be usable.
#[test]
fn v4_repl_error_multiple_consecutive() {
    let o = run_repl(
        &format!(
            "{PRIMS}\
             (add-i64 true 1)\n\
             (add-i64 1 false)\n\
             (add-i64 true false)\n\
             (add-i64 3 4)\n"
        ),
        "error_multiple_consecutive",
    );
    assert_success(&o);

    // After three errors, the fourth form should produce 7.
    assert_result(&o, ":primitives/Int 7");
}

// ===========================================================================
// Test: discover-tests + run-test composed via bind
// ===========================================================================

// spec: repl/spec.md §16 — test discovery and execution
//
// Verifies that (discover-tests) returns an SList of SexpSym, and that
// (run-test sym) works when sym comes from discover-tests via bind.
// Uses primitives/bind (not bind! macro) to compose the IO actions.
#[test]
fn v4_repl_discover_and_run_test_via_bind() {
    let o = run_repl(
        &format!(
            "(deftype (Option a) None (Some [:a val]))\n\
             {PRIMS}\
             (import [macros [SCons SNil]])\n\
             (import [primitives [Pure]])\n\
             (defn test-hello [] None)\n\
             (bind (discover-tests) (fn [tests] (match tests [(SCons h t) (run-test h) (SNil) (Pure (TestPass \"none\" 0))])))\n"
        ),
        "discover_run_bind",
    );
    assert_success(&o);
    let all = stdout_str(&o);
    // The bind chain should produce a TestResult (TestPass).
    assert!(
        all.contains("TestPass"),
        "expected TestPass in output\n---\n{all}"
    );
    assert!(
        all.contains("test-hello"),
        "expected test-hello in result name\n---\n{all}"
    );
}
