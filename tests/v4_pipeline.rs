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

// ===========================================================================
// Macro expansion (Step 4 — v4 scheduler path)
// ===========================================================================

/// Helper: run source through both --v4 --run and --run, assert stdout matches
/// and both exit with code 0.
fn assert_v4_parity(source: &str, label: &str) {
    let v4_out = run_v4(source, &format!("{label}_v4"));
    let old_out = run_old(source, &format!("{label}_old"));

    let v4_stdout = stdout_of(&v4_out);
    let old_stdout = stdout_of(&old_out);

    assert_eq!(
        v4_out.status.code(),
        old_out.status.code(),
        "exit code mismatch for {label}: v4={:?}, old={:?}\nv4 stderr: {}\nold stderr: {}",
        v4_out.status.code(),
        old_out.status.code(),
        stderr_of(&v4_out),
        stderr_of(&old_out)
    );
    assert_eq!(
        v4_stdout, old_stdout,
        "stdout mismatch for {label}: v4={v4_stdout:?}, old={old_stdout:?}"
    );
}

/// Helper: run source through both paths, assert both produce nonzero exit code.
fn assert_v4_error_parity(source: &str, label: &str) {
    let v4_out = run_v4(source, &format!("{label}_v4"));
    let old_out = run_old(source, &format!("{label}_old"));

    assert_ne!(
        old_out.status.code(),
        Some(0),
        "old path should fail for {label} but succeeded: stdout={}",
        stdout_of(&old_out)
    );
    assert_ne!(
        v4_out.status.code(),
        Some(0),
        "v4 path should fail for {label} but succeeded: stdout={}",
        stdout_of(&v4_out)
    );
}

// spec: spec/09-macros.md §9.2 — defmacro definition and expansion
// spec: spec/05-definitions.md §5.13.2 — macros must be defined before use
#[test]

fn v4_macro_simple_defmacro_and_call() {
    // Simplest possible macro: identity transform. defmacro + call in same file.
    let src = "\
(defmacro id [x] x)
(defn main [] (id 42))";
    assert_v4_parity(src, "macro_simple");
}

// spec: spec/09-macros.md §9.4 — quasiquote template-based construction
#[test]

fn v4_macro_quasiquote() {
    // Macro using quasiquote + unquote to build an expression.
    // Uses add-i64 primitive (no prelude needed).
    let src = "\
(defmacro double [x] `(add-i64 ~x ~x))
(defn main [] (double 21))";
    assert_v4_parity(src, "macro_quasiquote");
}

// spec: spec/09-macros.md §9.2.5 — macro body may call functions defined before it
#[test]

fn v4_macro_calls_helper_function() {
    // A defn helper is defined before the defmacro. The macro body calls the
    // helper at expansion time (the helper must be compiled before the macro
    // can execute).
    let src = "\
(defn make-seven [] 7)
(defmacro lucky [] `(make-seven))
(defn main [] (lucky))";
    assert_v4_parity(src, "macro_calls_helper");
}

// spec: spec/09-macros.md §9.3.3 — re-expansion to fixed point (macro calls another macro)
#[test]

fn v4_macro_calls_another_macro() {
    // Two sequential macros. The second macro expands to a call that uses the
    // first macro. Re-expansion should reach a fixed point.
    let src = "\
(defmacro wrap-add [a b] `(add-i64 ~a ~b))
(defmacro add-three [x] `(wrap-add ~x 3))
(defn main [] (add-three 39))";
    assert_v4_parity(src, "macro_calls_macro");
}

// spec: spec/09-macros.md §9.2 — multiple defmacro forms in one file
// spec: spec/05-definitions.md §5.13.2 — macros available from next form onward
#[test]

fn v4_macro_multiple_macros_interleaved() {
    // Multiple defmacros with interleaved defns. Verifies that the v4 pipeline
    // processes forms in source order and macros become available sequentially.
    let src = "\
(defn triple [x] (add-i64 x (add-i64 x x)))
(defmacro apply-triple [x] `(triple ~x))
(defn six [] (apply-triple 2))
(defmacro make-six [] `(six))
(defn main [] (make-six))";
    assert_v4_parity(src, "macro_interleaved");
}

// spec: spec/09-macros.md §9.2.6 — multi-clause macros with arity dispatch
#[test]

fn v4_macro_multi_clause_dispatch() {
    // Multi-clause macro: different arities select different clauses.
    // Clause 1: (my-op x) => x (identity)
    // Clause 2: (my-op x y) => (add-i64 x y)
    let src = "\
(defmacro my-op
  ([x] x)
  ([x y] `(add-i64 ~x ~y)))
(defn main [] (add-i64 (my-op 10) (my-op 20 12)))";
    assert_v4_parity(src, "macro_multi_clause");
}

// spec: spec/05-definitions.md §5.13.2 — macro used before definition is an error
// spec: spec/09-macros.md §9.3.4 — define-before-use
#[test]

fn v4_macro_define_before_use_violation() {
    // Macro used before its defmacro form. Both paths should produce an error.
    // (The old path treats it as an undefined function call; v4 should also error.)
    let src = "\
(defn main [] (nope 42))
(defmacro nope [x] x)";
    assert_v4_error_parity(src, "macro_forward_ref");
}

// spec: spec/09-macros.md §9.2.5 — macro body calls fn that calls another fn
#[test]

fn v4_macro_complex_call_graph() {
    // Macro body generates a call to fn `b`, which itself calls fn `a`.
    // The v4 pipeline must compile both `a` and `b` (transitive deps) before
    // the macro can expand.
    let src = "\
(defn a [] 10)
(defn b [] (add-i64 (a) 11))
(defmacro get-b [] `(b))
(defn main [] (get-b))";
    assert_v4_parity(src, "macro_complex_call_graph");
}

// spec: spec/09-macros.md §9.2.3 — macro body must return Sexp
#[test]

fn v4_macro_type_error_in_body() {
    // Macro body returns Int instead of Sexp. Both paths should report a type error.
    let src = "\
(defmacro bad-macro [] 42)
(defn main [] (bad-macro))";
    assert_v4_error_parity(src, "macro_type_error");
}

// spec: spec/09-macros.md §9.6 — begin splicing produces multiple top-level forms
#[test]

fn v4_macro_begin_splicing() {
    // Macro expands to (begin ...) which splices two defn forms into the
    // top-level. Both are then available for use.
    let src = "\
(defmacro def-pair [name1 val1 name2 val2]
  `(begin
    (defn ~name1 [] ~val1)
    (defn ~name2 [] ~val2)))
(def-pair get-ten 10 get-twenty 20)
(defn main [] (add-i64 (get-ten) (get-twenty)))";
    assert_v4_parity(src, "macro_begin_splicing");
}
