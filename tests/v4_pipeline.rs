//! Integration tests for the v4 scheduler-driven pipeline (`--v4 --run`).
//!
//! Sprint 41 Wave 3: verifies that simple programs (primitives + special forms
//! only, no imports, no macros, no operators) compile correctly through the
//! scheduler path. Also verifies that non-qualifying programs fall back to the
//! old delegation path and still produce correct output.
//!
//! These are Layer 4 (E2E) tests: they invoke the binary as a subprocess and
//! assert on stdout content and exit code. No Rust APIs.

use std::path::PathBuf;
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

// ---------------------------------------------------------------------------
// Test infrastructure
// ---------------------------------------------------------------------------

static TEST_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn project_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn binary_path() -> PathBuf {
    project_root().join("target").join("debug").join("cranelisp")
}

/// Create a fresh, isolated working directory for one test.
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
        .join("v4_pipeline")
        .join(".runs")
        .join(&*RUN_TS)
        .join(format!("{n}_{label}"));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Run a Cranelisp source file through `--v4 --run` and return the output.
fn run_v4(source: &str, label: &str) -> Output {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} — run `cargo build` first"
    );
    let dir = test_dir(label);
    let source_path = dir.join("test.cl");
    std::fs::write(&source_path, source).unwrap();

    Command::new(&binary)
        .args(["--v4", "--run", source_path.to_str().unwrap()])
        .current_dir(&dir)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("failed to run cranelisp")
}

/// Run a Cranelisp source file through `--run` (old path) and return the output.
fn run_old(source: &str, label: &str) -> Output {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} — run `cargo build` first"
    );
    let dir = test_dir(label);
    let source_path = dir.join("test.cl");
    std::fs::write(&source_path, source).unwrap();

    Command::new(&binary)
        .args(["--run", source_path.to_str().unwrap()])
        .current_dir(&dir)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("failed to run cranelisp")
}

fn stdout_of(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).trim().to_string()
}

fn stderr_of(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).trim().to_string()
}

// ===========================================================================
// Basic expressions (scheduler path)
// ===========================================================================

// spec: spec/01-syntax.md §2.1 — integer literals
#[test]
fn test_v4_integer_literal() {
    let out = run_v4("(defn main [] 42)", "int_literal");
    assert_eq!(stdout_of(&out), ":primitives/Int 42");
}

// spec: spec/01-syntax.md §2.2 — boolean literals
#[test]
fn test_v4_boolean_literal() {
    let out = run_v4("(defn main [] true)", "bool_literal");
    assert_eq!(stdout_of(&out), ":primitives/Bool true");
    assert_eq!(out.status.code(), Some(0));
}

// spec: spec/appendix-a-builtins.md — add-i64 primitive
#[test]
fn test_v4_add_i64() {
    let out = run_v4("(defn main [] (add-i64 1 2))", "add_i64");
    assert_eq!(stdout_of(&out), ":primitives/Int 3");
}

// spec: spec/appendix-a-builtins.md — sub-i64 primitive
#[test]
fn test_v4_sub_i64() {
    let out = run_v4("(defn main [] (sub-i64 10 3))", "sub_i64");
    assert_eq!(stdout_of(&out), ":primitives/Int 7");
}

// spec: spec/04-expressions.md §2.1 — if expression
#[test]
fn test_v4_if_expression() {
    let out = run_v4("(defn main [] (if true (add-i64 1 2) 0))", "if_expr");
    assert_eq!(stdout_of(&out), ":primitives/Int 3");
}

// spec: spec/04-expressions.md §3 — let binding
#[test]
fn test_v4_let_binding() {
    let out = run_v4("(defn main [] (let [x (add-i64 3 4)] x))", "let_binding");
    assert_eq!(stdout_of(&out), ":primitives/Int 7");
}

// ===========================================================================
// Functions (scheduler path)
// ===========================================================================

// spec: spec/05-functions.md §1 — defn and function call
#[test]
fn test_v4_defn_and_call() {
    let src = "(defn double [x] (add-i64 x x)) (defn main [] (double 5))";
    let out = run_v4(src, "defn_and_call");
    assert_eq!(stdout_of(&out), ":primitives/Int 10");
}

// spec: spec/05-functions.md §3 — recursive function (factorial)
#[test]
fn test_v4_recursive_function() {
    let src = "\
(defn fact [n]
  (if (eq-i64 n 0)
    1
    (mul-i64 n (fact (sub-i64 n 1)))))
(defn main [] (fact 5))";
    let out = run_v4(src, "recursive_fn");
    assert_eq!(stdout_of(&out), ":primitives/Int 120");
}

// ===========================================================================
// Fallback detection (old delegation path)
// ===========================================================================

// spec: design/arch/pipeline-v4-roadmap.md §Step 3 — import triggers fallback
#[test]
fn test_v4_falls_back_for_imports() {
    // A program with (import ...) should fall back to the old delegation path
    // and still produce correct output.
    let src = "(import [primitives [add-i64]]) (defn main [] (add-i64 1 2))";
    let v4_out = run_v4(src, "fallback_import");
    assert_eq!(stdout_of(&v4_out), ":primitives/Int 3");

    // Verify same output as old path.
    let old_out = run_old(src, "fallback_import_old");
    assert_eq!(stdout_of(&v4_out), stdout_of(&old_out));
}

// spec: design/arch/pipeline-v4-roadmap.md §Step 3 — operators trigger fallback
#[test]
fn test_v4_falls_back_for_operators() {
    // A program with operator syntax (+) should fall back to the old delegation
    // path. Without prelude, `+` is undefined — both paths produce the same
    // error. The key assertion is that --v4 does not crash or diverge.
    let src = "(defn main [] (+ 1 2))";
    let v4_out = run_v4(src, "fallback_operators");
    let old_out = run_old(src, "fallback_operators_old");

    // Both should fail with exit code 1.
    assert_eq!(v4_out.status.code(), Some(1));
    assert_eq!(old_out.status.code(), Some(1));

    // Both should produce the same error on stderr (undefined variable: +).
    assert_eq!(stderr_of(&v4_out), stderr_of(&old_out));
}
