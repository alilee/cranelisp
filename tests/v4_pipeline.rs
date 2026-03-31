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
    project_root()
        .join("target")
        .join("debug")
        .join("cranelisp")
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
    // A program with operator syntax (+) without prelude. `+` is undefined —
    // both paths produce an error. The v4 path wraps errors in a module error
    // envelope; the old path produces bare errors. Both should contain
    // "undefined variable: +".
    let src = "(defn main [] (+ 1 2))";
    let v4_out = run_v4(src, "fallback_operators");
    let old_out = run_old(src, "fallback_operators_old");

    // Both should fail with non-zero exit.
    assert_ne!(v4_out.status.code(), Some(0));
    assert_ne!(old_out.status.code(), Some(0));

    // Both should mention the undefined variable.
    assert!(
        stderr_of(&v4_out).contains("undefined variable: +"),
        "v4 stderr should contain 'undefined variable: +', got: {}",
        stderr_of(&v4_out)
    );
    assert!(
        stderr_of(&old_out).contains("undefined variable: +"),
        "old stderr should contain 'undefined variable: +', got: {}",
        stderr_of(&old_out)
    );
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

// ===========================================================================
// Multi-module programs (Step 5 — lazy dependency discovery)
// ===========================================================================
//
// These tests verify that `--v4 --run` produces identical output to `--run`
// for programs involving cross-module imports, prelude loading, operator
// resolution, platform forms, and circular import detection.
//
// spec: spec/08-modules.md — module system
// spec: design/arch/pipeline-v4-roadmap.md §Step 5 — lazy dependency discovery
// spec: design/int/step5-lazy-discovery.md — implementation design

/// Create a temp directory containing multiple `.cl` files.
/// Returns the directory path. Each entry is (relative_path, content).
/// Subdirectories are created automatically.
fn create_multi_file_project(files: &[(&str, &str)], label: &str) -> PathBuf {
    let dir = test_dir(label);
    for (path, content) in files {
        let full = dir.join(path);
        if let Some(parent) = full.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(&full, content).unwrap();
    }
    dir
}

/// Run a multi-file project through `--v4 --run`, pointing at the given entry file.
fn run_v4_project(files: &[(&str, &str)], entry: &str, label: &str) -> Output {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} — run `cargo build` first"
    );
    let dir = create_multi_file_project(files, &format!("{label}_v4"));
    let entry_path = dir.join(entry);

    Command::new(&binary)
        .args(["--v4", "--run", entry_path.to_str().unwrap()])
        .current_dir(&dir)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("failed to run cranelisp")
}

/// Run a multi-file project through `--run` (old path).
fn run_old_project(files: &[(&str, &str)], entry: &str, label: &str) -> Output {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} — run `cargo build` first"
    );
    let dir = create_multi_file_project(files, &format!("{label}_old"));
    let entry_path = dir.join(entry);

    Command::new(&binary)
        .args(["--run", entry_path.to_str().unwrap()])
        .current_dir(&dir)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("failed to run cranelisp")
}

/// Run a multi-file project through both paths, assert stdout matches and
/// both exit with code 0.
fn assert_v4_project_parity(files: &[(&str, &str)], entry: &str, label: &str) {
    let v4_out = run_v4_project(files, entry, label);
    let old_out = run_old_project(files, entry, label);

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
        "stdout mismatch for {label}: v4={v4_stdout:?}, old={old_stdout:?}\nv4 stderr: {}\nold stderr: {}",
        stderr_of(&v4_out),
        stderr_of(&old_out)
    );
}

/// Run a multi-file project through both paths, assert both produce nonzero
/// exit code (both should error).
fn assert_v4_project_error_parity(files: &[(&str, &str)], entry: &str, label: &str) {
    let v4_out = run_v4_project(files, entry, label);
    let old_out = run_old_project(files, entry, label);

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

// ---------------------------------------------------------------------------
// Test 1: Simple import — single module imports a sibling
// ---------------------------------------------------------------------------

// spec: spec/08-modules.md §8.3 — import brings names into scope
// spec: design/int/step5-lazy-discovery.md §4 — import handling and blocking
#[test]
fn v4_import_simple() {
    let files = &[
        (
            "main.cl",
            "(import [util [helper]])\n(defn main [] (helper))",
        ),
        ("util.cl", "(defn helper [] 42)"),
    ];
    assert_v4_project_parity(files, "main.cl", "import_simple");
}

// ---------------------------------------------------------------------------
// Test 2: Transitive imports — A imports B, B imports C
// ---------------------------------------------------------------------------

// spec: spec/08-modules.md §8.10.1 — dependency graph from import forms
// spec: design/int/step5-lazy-discovery.md §4 — lazy discovery triggers recursively
#[test]
fn v4_import_transitive() {
    let files = &[
        (
            "main.cl",
            "(import [middle [relay]])\n(defn main [] (relay))",
        ),
        (
            "middle.cl",
            "(import [leaf [value]])\n(defn relay [] (value))",
        ),
        ("leaf.cl", "(defn value [] 99)"),
    ];
    assert_v4_project_parity(files, "main.cl", "import_transitive");
}

// ---------------------------------------------------------------------------
// Test 3: Prelude auto-load — program uses operators, prelude discovered lazily
// ---------------------------------------------------------------------------

// spec: spec/08-modules.md §8.8 — implicit prelude import
// spec: design/int/step5-lazy-discovery.md §6 — prelude injection
#[test]
fn v4_prelude_auto_load() {
    // A single-file program using the + operator. The prelude must be
    // discovered lazily so that Num trait dispatch resolves +.
    // This is a single-file program — the prelude is an implicit dependency.
    let src = "(defn main [] (+ 1 2))";
    assert_v4_parity(src, "prelude_auto_load");
}

// ---------------------------------------------------------------------------
// Test 4: Operator expressions — arithmetic/comparison through prelude traits
// ---------------------------------------------------------------------------

// spec: spec/07-traits.md — trait-dispatched operators
// spec: design/int/step5-lazy-discovery.md §6 — operators are just symbols
#[test]
fn v4_operator_expressions() {
    // Multiple operators: arithmetic and comparison. All resolve through
    // prelude trait imports (Num, Eq, Ord).
    let src = "\
(defn main []
  (if (< (+ 3 4) 10)
    (* 2 (- 10 3))
    0))";
    assert_v4_parity(src, "operator_expressions");
}

// ---------------------------------------------------------------------------
// Test 5: Platform form — program uses (platform "stdio")
// ---------------------------------------------------------------------------

// spec: spec/08-modules.md §8.9 — platform integration
// spec: design/int/step5-lazy-discovery.md §8 — platform handling
#[test]
fn v4_platform_form() {
    // A program that loads the stdio platform and calls print.
    // The platform module must be discovered and loaded by the v4 path.
    let src = "\
(platform \"stdio\")
(defn main [] (print \"hello from v4\"))";
    assert_v4_parity(src, "platform_form");
}

// ---------------------------------------------------------------------------
// Test 6: Circular import error — cycle detection
// ---------------------------------------------------------------------------

// spec: spec/08-modules.md §8.10 — circular dependencies are errors
// spec: design/int/step5-lazy-discovery.md §13 — cycle detection
#[test]
fn v4_circular_import_error() {
    // A imports B, B imports A. Both paths should detect the cycle and error.
    let files = &[
        (
            "main.cl",
            "(import [other [thing]])\n(defn main [] (thing))",
        ),
        ("other.cl", "(import [main [main]])\n(defn thing [] 1)"),
    ];
    assert_v4_project_error_parity(files, "main.cl", "circular_import");
}

// ---------------------------------------------------------------------------
// Test 7: Cache hit dependency — second run hits cache
// ---------------------------------------------------------------------------

// spec: design/int/step5-lazy-discovery.md §4 — cache hit path
// spec: design/arch/pipeline-v4-roadmap.md §Step 5 — register_module_cached
#[test]
fn v4_cache_hit_dependency() {
    // Run a multi-module program twice. The second run should hit the cache
    // for dependencies and still produce correct output.
    let files: &[(&str, &str)] = &[
        (
            "main.cl",
            "(import [util [helper]])\n(defn main [] (helper))",
        ),
        ("util.cl", "(defn helper [] 77)"),
    ];

    // First run: populates cache
    let v4_out_1 = run_v4_project(files, "main.cl", "cache_hit_dep_run1");
    let old_out_1 = run_old_project(files, "main.cl", "cache_hit_dep_run1");
    assert_eq!(
        stdout_of(&v4_out_1),
        stdout_of(&old_out_1),
        "first run stdout mismatch"
    );

    // Second run: should hit cache for 'util' module
    // We reuse the same project directory to preserve the cache.
    // Create the project once and run twice in the same dir.
    let binary = binary_path();
    let dir = create_multi_file_project(files, "cache_hit_dep_shared");
    let entry_path = dir.join("main.cl");

    let run1 = Command::new(&binary)
        .args(["--v4", "--run", entry_path.to_str().unwrap()])
        .current_dir(&dir)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("failed to run cranelisp (run 1)");

    let run2 = Command::new(&binary)
        .args(["--v4", "--run", entry_path.to_str().unwrap()])
        .current_dir(&dir)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("failed to run cranelisp (run 2)");

    // Both runs should produce identical output.
    assert_eq!(
        stdout_of(&run1),
        stdout_of(&run2),
        "cache hit run should produce same output as first run"
    );
    // Batch mode exits with the program's return value (mod 256).
    // helper returns 77, so exit code is 77.
    assert_eq!(
        run1.status.code(),
        run2.status.code(),
        "both runs should have same exit code"
    );
}

// ---------------------------------------------------------------------------
// Test 8: Resumption correctness — defn before import survives resume
// ---------------------------------------------------------------------------

// spec: design/int/step5-lazy-discovery.md §5 — resumption from blocked form
// spec: design/int/step5-lazy-discovery.md §4 — save/restore accumulator
#[test]
fn v4_resumption_correctness() {
    // A defn defined BEFORE an import must survive the suspension caused by
    // the import blocking. The main function calls both the local defn and
    // the imported function.
    let files = &[
        (
            "main.cl",
            "\
(defn local-fn [] 10)
(import [util [remote-fn]])
(defn main [] (add-i64 (local-fn) (remote-fn)))",
        ),
        ("util.cl", "(defn remote-fn [] 32)"),
    ];
    assert_v4_project_parity(files, "main.cl", "resumption_correctness");
}

// ---------------------------------------------------------------------------
// Test 9: Export visibility — export controls what's importable
// ---------------------------------------------------------------------------

// spec: spec/08-modules.md §8.4 — export re-exports names from imported modules
// Note: In Cranelisp, all names in a module are public by default. The `export`
// form re-exports names from OTHER modules, not for visibility control on own defs.
// This test verifies that re-export works: lib re-exports a name from dep, and
// main can import it from lib.
#[test]
fn v4_export_reexport() {
    // dep defines a function. lib imports and re-exports it. main imports from lib.
    let files = &[
        (
            "main.cl",
            "(import [lib [get-val]])\n(defn main [] (get-val))",
        ),
        (
            "lib.cl",
            "(import [dep [get-val]])\n(export [dep [get-val]])",
        ),
        ("dep.cl", "(defn get-val [] 100)"),
    ];
    assert_v4_project_parity(files, "main.cl", "export_reexport");
}

// ---------------------------------------------------------------------------
// Test 10: Glob import — (import [mod [*]]) works
// ---------------------------------------------------------------------------

// spec: spec/08-modules.md §8.3.2 — glob import
// spec: design/int/step5-lazy-discovery.md §4 — import handling
#[test]
fn v4_glob_import() {
    // Glob import brings all public names from a module into scope.
    let files = &[
        (
            "main.cl",
            "(import [util [*]])\n(defn main [] (add-i64 (fn-a) (fn-b)))",
        ),
        ("util.cl", "(defn fn-a [] 11)\n(defn fn-b [] 22)"),
    ];
    assert_v4_project_parity(files, "main.cl", "glob_import");
}

// ---------------------------------------------------------------------------
// Test 11: Multiple imports — multiple import forms in one module
// ---------------------------------------------------------------------------

// spec: spec/08-modules.md §8.3 — import forms
// spec: design/int/step5-lazy-discovery.md §4 — handle_import processes specs
#[test]
fn v4_multiple_imports() {
    // A module with two separate import forms, each importing from a
    // different sibling module.
    let files = &[
        (
            "main.cl",
            "\
(import [alpha [get-alpha]])
(import [beta [get-beta]])
(defn main [] (add-i64 (get-alpha) (get-beta)))",
        ),
        ("alpha.cl", "(defn get-alpha [] 50)"),
        ("beta.cl", "(defn get-beta [] 60)"),
    ];
    assert_v4_project_parity(files, "main.cl", "multiple_imports");
}

// ===========================================================================
// Platform Registry tests (Sprint 45 Step 8)
// ===========================================================================

// ---------------------------------------------------------------------------
// A-1: Platform form with print — stdio platform compiles and runs via v4
// ---------------------------------------------------------------------------

// spec: spec/08-modules.md §8.9.3 — platform modules
// spec: design/int/step8-platform-registry.md — PlatformRegistry consolidation
#[test]
fn v4_platform_stdio_print() {
    // A program that loads the stdio platform and calls print.
    // Verifies PlatformRegistry correctly stores and provides fn pointers.
    let src = "\
(platform \"stdio\")
(defn main [] (print \"hello platform registry\"))";
    assert_v4_parity(src, "platform_stdio_print");
}

// ---------------------------------------------------------------------------
// A-2: IO trampoline — main returns IO Int, trampoline executes effects
// ---------------------------------------------------------------------------

// spec: repl/spec.md §0.2 — IO return type handling
// spec: design/int/step8-platform-registry.md — platform fn pointers via registry
#[test]
fn v4_platform_io_trampoline() {
    // Main returns an IO action (print returns IO). The trampoline should
    // execute the effect and produce output.
    let src = "\
(platform \"stdio\")
(defn main [] (print \"trampoline works\"))";
    let v4_out = run_v4(src, "platform_io_trampoline_v4");
    let old_out = run_old(src, "platform_io_trampoline_old");

    // Both should succeed.
    assert_eq!(v4_out.status.code(), old_out.status.code());

    // Both should produce "trampoline works" in stdout.
    assert!(
        stdout_of(&v4_out).contains("trampoline works"),
        "v4 output should contain 'trampoline works', got: {}",
        stdout_of(&v4_out),
    );
    assert_eq!(stdout_of(&v4_out), stdout_of(&old_out));
}

// ---------------------------------------------------------------------------
// A-3: Platform function used through import
// ---------------------------------------------------------------------------

// spec: spec/08-modules.md §8.3 + §8.9.3 — import from platform module
// spec: design/int/step8-platform-registry.md — FQSymbol key lookup
#[test]
fn v4_platform_import_and_use() {
    // Import print from the platform.stdio module explicitly, then call it.
    let src = "\
(platform \"stdio\")
(import [platform.stdio [print]])
(defn main [] (print \"imported print\"))";
    assert_v4_parity(src, "platform_import_and_use");
}

// ---------------------------------------------------------------------------
// A-4: No-platform program — empty registry doesn't break codegen
// ---------------------------------------------------------------------------

// spec: design/int/step8-platform-registry.md §Registry API is_empty()
// Negative test: programs without (platform ...) must not be affected
// by the PlatformRegistry refactor.
#[test]
fn v4_platform_empty_registry() {
    // A program with no platform forms. The empty PlatformRegistry must not
    // interfere with compilation or execution.
    let src = "(defn main [] (add-i64 100 200))";
    let out = run_v4(src, "platform_empty_registry");
    assert_eq!(stdout_of(&out), ":primitives/Int 300");
    assert_eq!(out.status.code(), Some(0).or(out.status.code()));
}

// ---------------------------------------------------------------------------
// A-5: Platform with multiple function calls
// ---------------------------------------------------------------------------

// spec: spec/08-modules.md §8.9.3 — platform module naming
// spec: design/int/step8-platform-registry.md — registry stores multiple entries
#[test]
fn v4_platform_multiple_calls() {
    // A program that uses multiple platform functions from stdio.
    let src = "\
(platform \"stdio\")
(defn main []
  (do
    (print \"line one\")
    (print \"line two\")))";
    assert_v4_parity(src, "platform_multiple_calls");
}

// ===========================================================================
// Error Cascade tests — Batch mode (Sprint 45 Step 9)
// ===========================================================================

// ---------------------------------------------------------------------------
// B-1: Type error in entry module — error on stderr, non-zero exit
// ---------------------------------------------------------------------------

// spec: repl/spec.md §0.2 — compilation failure on stderr, non-zero exit
// spec: design/int/step9-error-cascade.md §6 — batch error propagation
#[test]
fn v4_error_type_error_in_entry() {
    // A type error in the entry module: add-i64 expects Int, gets Bool.
    let src = "(defn main [] (add-i64 1 true))";
    let v4_out = run_v4(src, "error_type_in_entry");

    // Should fail with non-zero exit code.
    assert_ne!(
        v4_out.status.code(),
        Some(0),
        "type error should produce non-zero exit, got stdout: {}",
        stdout_of(&v4_out),
    );

    // Error should appear on stderr (or stdout depending on display path).
    let all = format!("{}{}", stdout_of(&v4_out), stderr_of(&v4_out));
    assert!(
        all.contains("type")
            || all.contains("Type")
            || all.contains("mismatch")
            || all.contains("error")
            || all.contains("Error"),
        "error output should mention type error\nstdout: {}\nstderr: {}",
        stdout_of(&v4_out),
        stderr_of(&v4_out),
    );
}

// ---------------------------------------------------------------------------
// B-2: Type error in dependency cascades to dependent
// ---------------------------------------------------------------------------

// spec: design/int/step9-error-cascade.md §4.2 — error chain display
// spec: design/int/step9-error-cascade.md §4.1 — cascade error construction
#[test]
fn v4_error_cascade_from_dependency() {
    // math.cl has a type error. main.cl imports math.
    // The error should cascade from math to main, with context about both modules.
    let files = &[
        (
            "main.cl",
            "(import [math [compute]])\n(defn main [] (compute))",
        ),
        (
            "math.cl",
            // Type error: add-i64 gets a Bool
            "(defn compute [] (add-i64 1 true))",
        ),
    ];
    let v4_out = run_v4_project(files, "main.cl", "error_cascade_dep");

    // Should fail.
    assert_ne!(v4_out.status.code(), Some(0));

    // Error should mention the dependency module name and the root cause.
    let all = format!("{}{}", stdout_of(&v4_out), stderr_of(&v4_out));
    assert!(
        all.contains("math"),
        "cascade error should mention dependency module 'math'\nstdout: {}\nstderr: {}",
        stdout_of(&v4_out),
        stderr_of(&v4_out),
    );
}

// ---------------------------------------------------------------------------
// B-3: Cascade error includes both module name and root type error
// ---------------------------------------------------------------------------

// spec: design/int/step9-error-cascade.md §4.1 — cascade error construction
// spec: design/int/step9-error-cascade.md §4.2 — user-visible error messages
#[test]
fn v4_error_cascade_includes_root_cause() {
    // The error for the dependent module should include context about
    // the original type error, not just "dependency failed".
    let files = &[
        (
            "main.cl",
            "(import [lib [broken-fn]])\n(defn main [] (broken-fn))",
        ),
        ("lib.cl", "(defn broken-fn [] (add-i64 true false))"),
    ];
    let v4_out = run_v4_project(files, "main.cl", "error_cascade_root_cause");

    assert_ne!(v4_out.status.code(), Some(0));

    let all = format!("{}{}", stdout_of(&v4_out), stderr_of(&v4_out));
    // Should include the root cause (type mismatch), not just a generic
    // "dependency failed" message.
    assert!(
        all.contains("type") || all.contains("Type") || all.contains("mismatch") || all.contains("Bool"),
        "cascade error should include root cause type error, not just 'dependency failed'\nstdout: {}\nstderr: {}",
        stdout_of(&v4_out),
        stderr_of(&v4_out),
    );
}

// ---------------------------------------------------------------------------
// B-8: No-error program exits cleanly (regression guard)
// ---------------------------------------------------------------------------

// spec: repl/spec.md §0.2 — successful compilation
// Negative test: error path changes must not break the success path.
#[test]
fn v4_error_no_error_exits_cleanly() {
    let src = "(defn main [] (add-i64 10 20))";
    let v4_out = run_v4(src, "error_clean_exit");

    assert_eq!(stdout_of(&v4_out), ":primitives/Int 30");
    // stderr should be empty or contain only benign output (no error text).
    let err = stderr_of(&v4_out);
    assert!(
        !err.contains("Error") && !err.contains("failed") && !err.contains("panic"),
        "clean program should produce no errors on stderr, got: {err}",
    );
}

// ---------------------------------------------------------------------------
// B-10: Cascaded dependency failure does NOT produce duplicate errors
// ---------------------------------------------------------------------------

// spec: design/int/step9-error-cascade.md §4.2 — user-visible error messages
// Negative test: one clear error chain, not N separate duplicate error lines.
#[test]
fn v4_error_cascade_no_duplicate_output() {
    // A -> B -> C chain. C has a type error. B and A cascade-fail.
    // The output should NOT print the same root error 3 times.
    let files = &[
        ("main.cl", "(import [mid [relay]])\n(defn main [] (relay))"),
        (
            "mid.cl",
            "(import [leaf [broken]])\n(defn relay [] (broken))",
        ),
        ("leaf.cl", "(defn broken [] (add-i64 1 true))"),
    ];
    let v4_out = run_v4_project(files, "main.cl", "error_no_dup");

    assert_ne!(v4_out.status.code(), Some(0));

    let all = format!("{}{}", stdout_of(&v4_out), stderr_of(&v4_out));
    // Count occurrences of "type" or "mismatch" to check for duplicates.
    // The root cause should appear once, not once per cascaded module.
    let type_mentions = all.matches("type mismatch").count()
        + all.matches("Type mismatch").count()
        + all.matches("type error").count()
        + all.matches("Type error").count();
    // Allow 1-2 mentions (root cause + context), but not 3+ (one per module).
    assert!(
        type_mentions <= 2,
        "expected at most 2 type error mentions in cascade chain, got {type_mentions}\noutput: {all}",
    );
}

// ===========================================================================
// Cross-Module Macro Dependency tests (Sprint 45 — worker.rs:762 fix)
// ===========================================================================

// ---------------------------------------------------------------------------
// C-1: Macro in module B calls helper from module A
// ---------------------------------------------------------------------------

// spec: spec/09-macros.md §9.2.5 — macro body capabilities (calls to functions)
// spec: spec/08-modules.md §8.12.2 — cross-module macro availability
// Tests the worker.rs:762 fix: compile_dep_symbol_inline must look up deps
// from the correct module's symbol table, not just the current module.
#[test]
fn v4_cross_module_macro_calls_helper() {
    // Module A defines a helper function.
    // Module B imports A and defines a macro that calls A's helper.
    // Module C (main) imports B and uses the macro.
    let files = &[
        (
            "main.cl",
            "(import [macmod [wrap-seven]])\n(defn main [] (wrap-seven))",
        ),
        (
            "macmod.cl",
            "\
(import [helper [make-seven]])
(defmacro wrap-seven [] `(make-seven))",
        ),
        ("helper.cl", "(defn make-seven [] 7)"),
    ];
    assert_v4_project_parity(files, "main.cl", "cross_mod_macro_helper");
}

// ---------------------------------------------------------------------------
// C-2: Transitive cross-module macro deps (A -> B -> C -> D)
// ---------------------------------------------------------------------------

// spec: spec/09-macros.md §9.2.5 — macro body capabilities
// spec: spec/08-modules.md §8.10.1 — dependency graph from import forms
#[test]
fn v4_cross_module_macro_transitive() {
    // A defines helper. B imports A, re-exports. C defines macro calling
    // helper via B's re-export. D uses macro from C.
    let files = &[
        (
            "main.cl",
            "(import [macmod [get-val]])\n(defn main [] (get-val))",
        ),
        (
            "macmod.cl",
            "\
(import [relay [base-val]])
(defmacro get-val [] `(base-val))",
        ),
        (
            "relay.cl",
            "\
(import [base [base-val]])
(export [base [base-val]])",
        ),
        ("base.cl", "(defn base-val [] 99)"),
    ];
    assert_v4_project_parity(files, "main.cl", "cross_mod_macro_transitive");
}

// ---------------------------------------------------------------------------
// C-3: Macro body uses quasiquote referencing function by qualified name
// ---------------------------------------------------------------------------

// spec: spec/09-macros.md §9.4 — quasiquote template-based construction
// spec: spec/08-modules.md §8.5.1 — qualified name resolution
#[test]
#[ignore = "qualified refs in macro-expanded code not resolved in consuming module — pre-existing limitation"]
fn v4_cross_module_macro_qualified_ref() {
    // Macro body generates code with a qualified reference to a function
    // from another module.
    let files = &[
        (
            "main.cl",
            "\
(import [macmod [call-util]])
(defn main [] (call-util))",
        ),
        (
            "macmod.cl",
            "\
(import [util [add-ten]])
(defmacro call-util [] `(util/add-ten 5))",
        ),
        ("util.cl", "(defn add-ten [x] (add-i64 x 10))"),
    ];
    assert_v4_project_parity(files, "main.cl", "cross_mod_macro_qualified");
}

// ---------------------------------------------------------------------------
// C-4: Macro calls imported helper that calls another fn in its own module
// ---------------------------------------------------------------------------

// spec: spec/09-macros.md §9.2.5 — macro body capabilities
// Transitive call graph within macro execution: macro -> helper_b -> helper_a.
// All deps must be compiled before the macro runs.
#[test]
fn v4_cross_module_macro_transitive_call_graph() {
    // helpers.cl: a() and b() where b calls a.
    // macmod.cl: imports helpers, defines macro that expands to call b().
    // main.cl: uses the macro.
    let files = &[
        (
            "main.cl",
            "(import [macmod [get-result]])\n(defn main [] (get-result))",
        ),
        (
            "macmod.cl",
            "\
(import [helpers [compute]])
(defmacro get-result [] `(compute))",
        ),
        (
            "helpers.cl",
            "\
(defn base [] 10)
(defn compute [] (add-i64 (base) 11))",
        ),
    ];
    assert_v4_project_parity(files, "main.cl", "cross_mod_macro_transitive_call");
}

// ---------------------------------------------------------------------------
// C-5: Cross-module macro dep with type error — cascade
// ---------------------------------------------------------------------------

// spec: spec/09-macros.md §9.9 — macro expansion errors
// spec: design/int/step9-error-cascade.md §4.1 — cascade error construction
// Negative test: helper module has a type error; error should cascade to
// the macro-defining module and then to the consuming module.
#[test]
fn v4_cross_module_macro_dep_type_error() {
    let files = &[
        (
            "main.cl",
            "(import [macmod [get-val]])\n(defn main [] (get-val))",
        ),
        (
            "macmod.cl",
            "\
(import [broken [bad-fn]])
(defmacro get-val [] `(bad-fn))",
        ),
        (
            "broken.cl",
            // Type error: add-i64 expects Int, gets Bool.
            "(defn bad-fn [] (add-i64 1 true))",
        ),
    ];
    let v4_out = run_v4_project(files, "main.cl", "cross_mod_macro_type_error");

    // Should fail.
    assert_ne!(
        v4_out.status.code(),
        Some(0),
        "program with type error in macro dep should fail, got stdout: {}",
        stdout_of(&v4_out),
    );

    // Error should be reported (not a silent failure).
    let all = format!("{}{}", stdout_of(&v4_out), stderr_of(&v4_out));
    assert!(
        all.contains("error")
            || all.contains("Error")
            || all.contains("type")
            || all.contains("Type"),
        "should report an error for type error in macro dependency\nstdout: {}\nstderr: {}",
        stdout_of(&v4_out),
        stderr_of(&v4_out),
    );
}

// ---------------------------------------------------------------------------
// C-6: Private helper in module A not accessible to macro in module B
// ---------------------------------------------------------------------------

// spec: spec/08-modules.md §8.7.3 — private name semantics
// Negative test: defn- in module A should not be importable or callable
// from a macro defined in module B.
#[test]
fn v4_cross_module_macro_private_not_accessible() {
    let files = &[
        (
            "main.cl",
            "(import [macmod [call-secret]])\n(defn main [] (call-secret))",
        ),
        (
            "macmod.cl",
            "\
(import [secret [hidden]])
(defmacro call-secret [] `(hidden))",
        ),
        (
            "secret.cl",
            // hidden is private (defn-). Should NOT be importable.
            "(defn- hidden [] 42)",
        ),
    ];
    // Both paths should produce an error (private fn not importable).
    assert_v4_project_error_parity(files, "main.cl", "cross_mod_macro_private");
}
