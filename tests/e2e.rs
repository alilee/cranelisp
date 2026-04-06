//! Layer 4: E2E black-box tests.
//!
//! These tests invoke the `cranelisp` binary as a subprocess, pipe input to
//! stdin, and assert on stdout/stderr content and exit code.  No Rust APIs.
//! This is the release gate — tests survive any internal restructuring.
//!
//! Tests are organized by `repl/spec.md` section number.  Tests for spec
//! requirements the implementation hasn't reached yet are `#[ignore]` with a
//! comment citing the spec section.
//!
//! Each test runs in an isolated temp directory so `.cache` artifacts from one
//! test never leak into another.

use std::path::PathBuf;
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

// ---------------------------------------------------------------------------
// Trait prelude for tests that use operators (+, -, *, /, =, <)
// ---------------------------------------------------------------------------

/// Import all primitives as bare names — needed by any E2E test that uses
/// bare primitive calls (add-i64, str-concat, etc.) via `run_repl`.
const PRIMS: &str = "(import [primitives [*]])\n";

const NUM_TRAIT_PRELUDE: &str = "(deftrait Num (+ [self self] self) (- [self self] self) (* [self self] self) (/ [self self] self))\n\
(impl Num Int (defn + [a b] (add-i64 a b)) (defn - [a b] (sub-i64 a b)) (defn * [a b] (mul-i64 a b)) (defn / [a b] (div-i64 a b)))\n\
(impl Num Float (defn + [a b] (add-f64 a b)) (defn - [a b] (sub-f64 a b)) (defn * [a b] (mul-f64 a b)) (defn / [a b] (div-f64 a b)))\n";

const EQ_TRAIT_PRELUDE: &str = "(deftrait Eq (= [self self] Bool))\n\
(impl Eq Int (defn = [a b] (eq-i64 a b)))\n\
(impl Eq Float (defn = [a b] (eq-f64 a b)))\n\
(impl Eq String (defn = [a b] (str-eq a b)))\n\
(impl Eq Bool (defn = [a b] (eq-bool a b)))\n";

const ORD_TRAIT_PRELUDE: &str = "(deftrait Ord (< [self self] Bool))\n\
(impl Ord Int (defn < [a b] (lt-i64 a b)))\n\
(impl Ord Float (defn < [a b] (lt-f64 a b)))\n";

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

/// Create a fresh, isolated working directory for one test under
/// `tests/e2e/.runs/{timestamp}/`.  The `.runs/` directory is git-ignored.
fn test_dir(label: &str) -> PathBuf {
    use std::sync::LazyLock;
    use std::time::SystemTime;

    // One timestamp per test-run invocation (all tests in the same run share
    // a parent directory so they're easy to inspect or clean up).
    static RUN_TS: LazyLock<String> = LazyLock::new(|| {
        let d = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap();
        format!("{}", d.as_secs())
    });

    let n = TEST_COUNTER.fetch_add(1, Ordering::SeqCst);
    let dir = project_root()
        .join("tests")
        .join("e2e")
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
        "cranelisp binary not found at {binary:?} — run `cargo build` first"
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

/// Run the REPL binary with the test prelude loaded.
///
/// Sets CRANELISP_LIB to `tests/fixtures/` which contains a QA-owned
/// `prelude.cl` fixture. NOT the real stdlib — see strategy.md
/// §"Prelude & Stdlib Test Isolation".
fn run_repl_with_test_prelude(input: &str, label: &str) -> Output {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} — run `cargo build` first"
    );
    let dir = test_dir(label);
    let fixtures = project_root().join("tests").join("fixtures");

    let mut child = Command::new(&binary)
        .current_dir(&dir)
        .env("CRANELISP_LIB", fixtures.as_os_str())
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
/// Also strips leading continuation markers (`...`) from the extracted text
/// to handle multi-line input where the result follows `...` on the same line.
fn result_lines(o: &Output) -> Vec<String> {
    stdout_str(o)
        .lines()
        .filter_map(|l| {
            // Find the last prompt delimiter "> " and extract the result after it.
            l.rfind("> ").map(|pos| {
                let after = l[pos + 2..].trim_start();
                // Strip continuation marker if present.
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

fn assert_stdout_contains(o: &Output, needle: &str) {
    let s = stdout_str(o);
    assert!(s.contains(needle), "stdout missing {needle:?}\n---\n{s}");
}

fn assert_result(o: &Output, expected: &str) {
    let results = result_lines(o);
    assert!(
        results.iter().any(|r| r == expected),
        "expected result {expected:?} not found in results: {results:?}\nstdout: {}",
        stdout_str(o)
    );
}

// ===========================================================================
// Smoke: binary starts, accepts input, exits cleanly
// ===========================================================================

// spec: repl/spec.md §2.1 — REPL starts and exits cleanly
#[test]
fn e2e_binary_starts_and_exits() {
    let o = run_repl("", "smoke_start");
    assert_success(&o);
}

// spec: repl/spec.md §1.2 — expression display format
#[test]
fn e2e_single_expression() {
    let o = run_repl(&format!("{PRIMS}(add-i64 2 3)\n"), "smoke_expr");
    assert_success(&o);
    assert_result(&o, ":primitives/Int 5");
}

// ===========================================================================
// §1.2  Expression display format
// ===========================================================================

// Current: `:Int 5`.  Spec: `:primitives/Int 5` (fully qualified).
// spec: repl/spec.md §1.2 — fully qualified type names in display
#[test]
fn e2e_s1_2_int_display_qualified() {
    let o = run_repl(&format!("{PRIMS}(add-i64 2 3)\n"), "s1_2_int");
    assert_result(&o, ":primitives/Int 5");
}

// spec: repl/spec.md §1.2 — fully qualified Bool type display
#[test]
fn e2e_s1_2_bool_display_qualified() {
    let o = run_repl(&format!("{PRIMS}(eq-i64 3 3)\n"), "s1_2_bool");
    assert_result(&o, ":primitives/Bool true");
}

// spec: repl/spec.md §1.2 — fully qualified String type display
#[test]
fn e2e_s1_2_string_display_qualified() {
    let o = run_repl("\"hello\"\n", "s1_2_str");
    assert_result(&o, ":primitives/String \"hello\"");
}

// spec: repl/spec.md §1.5 — nullary constructor dot notation
#[test]
fn e2e_s1_5_nullary_ctor_dot_notation() {
    let o = run_repl(
        "(deftype Color Red Green Blue)\nRed\n",
        "s1_5_nullary",
    );
    assert_stdout_contains(&o, "Color.Red");
}

// spec: repl/spec.md §1.5 — data constructor dot notation
#[test]
fn e2e_s1_5_data_ctor_dot_notation() {
    let o = run_repl(
        "(deftype (Option a) None (Some [:a val]))\n(Some 42)\n",
        "s1_5_data",
    );
    assert_stdout_contains(&o, "(Option.Some 42)");
}

// spec: repl/spec.md §1.5 — prelude Option data ctor displays formatted value, not raw pointer
#[test]
// BUG: prelude Option (Some 42) shows raw pointer instead of (Option.Some 42)
fn e2e_s1_5_prelude_option_some_display() {
    let o = run_repl_with_test_prelude("(Some 42)\n", "s1_5_prelude_some");
    let s = stdout_str(&o);
    assert!(
        s.contains("(Option.Some 42)"),
        "expected '(Option.Some 42)' in output, got:\n{s}"
    );
    // Negative: must NOT contain a raw heap pointer in the value position
    assert!(
        !s.lines().any(|l| {
            l.contains("Option") && l.chars().filter(|c| c.is_ascii_digit()).count() > 5
                && !l.contains("(Option.Some 42)")
        }),
        "result should not contain raw heap pointer:\n{s}"
    );
}

// spec: repl/spec.md §1.5 — prelude Option None displays as value, not definition
#[test]
// BUG: prelude None shows definition display instead of value display
fn e2e_s1_5_prelude_option_none_display() {
    let o = run_repl_with_test_prelude("None\n", "s1_5_prelude_none");
    let s = stdout_str(&o);
    // Should display as a value: :(Option a) Option.None
    // Must NOT show definition metadata ("; deftype") or module-qualified ctor name
    assert!(
        s.contains("Option.None"),
        "expected 'Option.None' in output, got:\n{s}"
    );
    assert!(
        !s.contains("; deftype"),
        "None evaluation should show value display, not definition display:\n{s}"
    );
    assert!(
        !s.contains("fn.option/"),
        "None value should not show module-qualified constructor path:\n{s}"
    );
}

// spec: repl/spec.md §1.5 — prelude Option (Some "hello") displays string contents, not pointer
#[test]
// BUG: prelude Option (Some string) shows raw pointer instead of formatted value
fn e2e_s1_5_prelude_option_some_string_display() {
    let o = run_repl_with_test_prelude("(Some \"hello\")\n", "s1_5_prelude_some_str");
    let s = stdout_str(&o);
    assert!(
        s.contains("\"hello\""),
        "expected string contents in Option display, got:\n{s}"
    );
    assert!(
        s.contains("Option.Some"),
        "expected 'Option.Some' constructor notation, got:\n{s}"
    );
}

// spec: spec/02-grammar.md §2.3.8 — type annotation as standalone expression
#[test]
fn e2e_s2_3_8_annotation_expr_simple() {
    let o = run_repl(":Int 42\n", "s2_3_8_annot_int");
    assert_result(&o, ":primitives/Int 42");
}

// spec: spec/02-grammar.md §2.3.8 — applied type annotation constrains polymorphic constructor
#[test]
fn e2e_s2_3_8_annotation_expr_applied_type() {
    let o = run_repl_with_test_prelude(":(Option Int) None\n", "s2_3_8_annot_option");
    assert_stdout_contains(&o, "Option.None");
}

// spec: spec/02-grammar.md §2.3.8 — neg: type annotation is not parsed as variable lookup
#[test]
fn e2e_s2_3_8_annotation_neg_not_variable_error() {
    // :Int 42 must NOT produce "undefined variable: :" or "undefined variable: :Int"
    let o = run_repl(":Int 42\n", "s2_3_8_neg_var");
    let s = stdout_str(&o);
    assert!(
        !s.contains("undefined variable"),
        "type annotation should not produce 'undefined variable' error:\n{s}"
    );
}

// ===========================================================================
// §1.3  Definition display format
// ===========================================================================

// spec: repl/spec.md §1.3 — definition display with qualified name
#[test]
fn e2e_s1_3_defn_shows_qualified_name() {
    let o = run_repl("(defn id [x] x)\n", "s1_3_defn");
    assert_stdout_contains(&o, "user/id");
}

// spec: repl/spec.md §1.3 — deftype display with qualified name
#[test]
fn e2e_s1_3_deftype_shows_qualified_name() {
    let o = run_repl("(deftype Color Red Green Blue)\n", "s1_3_deftype");
    assert_stdout_contains(&o, ":user/Color");
}

// ===========================================================================
// §2.1  Prompt format
// ===========================================================================

// spec: repl/spec.md §2.1 — prompt format with timing and module
#[test]
fn e2e_s2_1_prompt_format() {
    let o = run_repl("", "s2_1_prompt");
    // On startup, the prompt should contain timing and module.
    let s = stdout_str(&o);
    assert!(
        s.contains("ms;") && s.contains("user>"),
        "prompt should match '{{N}}+{{N}}ms; user>'\n---\n{s}"
    );
}

// ===========================================================================
// §2.2  Continuation prompt
// ===========================================================================

// spec: repl/spec.md §2.2 — continuation prompt for incomplete input
#[test]
fn e2e_s2_2_continuation_prompt() {
    // Open paren without close — should show continuation prompt.
    let o = run_repl(&format!("{PRIMS}(add-i64\n  2 3)\n"), "s2_2_cont");
    let s = stdout_str(&o);
    assert!(s.contains("..."), "expected '...' continuation\n---\n{s}");
    assert_result(&o, ":primitives/Int 5");
}

// ===========================================================================
// §3  Slash commands
// ===========================================================================

// spec: repl/spec.md §3.1 — /help slash command
#[test]
fn e2e_s3_1_help() {
    let o = run_repl("/help\n", "s3_help");
    let s = stdout_str(&o);
    assert!(s.contains("/help"), "expected /help in output\n---\n{s}");
    assert!(s.contains("/sig"), "expected /sig in output\n---\n{s}");
    assert!(s.contains("/list"), "expected /list in output\n---\n{s}");
}

// spec: repl/spec.md §3.1 — /quit slash command
#[test]
fn e2e_s3_1_quit() {
    let o = run_repl("/quit\n", "s3_quit");
    assert_success(&o);
}

// spec: repl/spec.md §3.3 — /list slash command
#[test]
fn e2e_s3_3_list() {
    let o = run_repl(
        "(defn foo [x] x)\n(deftype Color Red)\n/list\n",
        "s3_list",
    );
    let s = stdout_str(&o);
    assert!(s.contains("Fns"), "expected Fns category\n---\n{s}");
    assert!(s.contains("foo"), "expected foo in listing\n---\n{s}");
    assert!(s.contains("Types"), "expected Types category\n---\n{s}");
}

// spec: repl/spec.md §3.1 — /sig slash command
#[test]
fn e2e_s3_1_sig() {
    let o = run_repl(&format!("{PRIMS}(defn double [x] (mul-i64 x 2))\n/sig double\n"), "s3_sig");
    let s = stdout_str(&o);
    assert!(
        s.contains("Fn") && s.contains("Int"),
        "expected function signature\n---\n{s}"
    );
}

// spec: repl/spec.md §3.4 — /info slash command
#[test]
fn e2e_s3_4_info() {
    let o = run_repl(
        &format!("{PRIMS}(defn double [x] (mul-i64 x 2))\n/info double\n"),
        "s3_info",
    );
    let s = stdout_str(&o);
    assert!(s.contains("double"), "expected 'double' in info\n---\n{s}");
    assert!(s.contains("bytes"), "expected code size in info\n---\n{s}");
}

// spec: repl/spec.md §3.1 — /time slash command
#[test]
fn e2e_s3_1_time() {
    let o = run_repl(&format!("{PRIMS}/time (add-i64 1 2)\n"), "s3_time");
    let s = stdout_str(&o);
    assert!(s.contains("ms"), "expected timing in output\n---\n{s}");
}

// spec: repl/spec.md §3.1 — /type slash command
#[test]
fn e2e_s3_1_type() {
    let o = run_repl(&format!("{PRIMS}/type (add-i64 1 2)\n"), "s3_type");
    let s = stdout_str(&o);
    assert!(s.contains("Int"), "expected Int type\n---\n{s}");
}

// spec: repl/spec.md §3 — /run-tests discovers and runs test-* functions
#[test]
#[ignore] // /run-tests not yet ported to v4 REPL
fn e2e_run_tests_basic_pass() {
    let input = "(deftype (Option a) None (Some [:a val]))\n\
                 (defn test-one [] None)\n\
                 /run-tests\n";
    let o = run_repl(input, "rt_basic_pass");
    let s = stdout_str(&o);
    assert!(
        s.contains("ok"),
        "passing test should show 'ok'\n---\n{s}"
    );
    assert!(
        s.contains("1 passed"),
        "should report 1 passed\n---\n{s}"
    );
}

// spec: repl/spec.md §3 — /run-tests reports failing tests
#[test]
#[ignore] // /run-tests not yet ported to v4 REPL
fn e2e_run_tests_basic_fail() {
    let input = "(deftype (Option a) None (Some [:a val]))\n\
                 (defn test-fail [] (Some \"expected\"))\n\
                 /run-tests\n";
    let o = run_repl(input, "rt_basic_fail");
    let s = stdout_str(&o);
    assert!(
        s.contains("FAILED"),
        "failing test should show 'FAILED'\n---\n{s}"
    );
    assert!(
        s.contains("expected"),
        "failure reason should appear in output\n---\n{s}"
    );
}

// spec: repl/spec.md §3 — /run-tests with multiple tests
#[test]
#[ignore] // /run-tests not yet ported to v4 REPL
fn e2e_run_tests_multiple() {
    let input = "(deftype (Option a) None (Some [:a val]))\n\
                 (defn test-a [] None)\n\
                 (defn test-b [] None)\n\
                 (defn test-c [] None)\n\
                 /run-tests\n";
    let o = run_repl(input, "rt_multiple");
    let s = stdout_str(&o);
    assert!(
        s.contains("3 passed"),
        "should report 3 passed\n---\n{s}"
    );
}

// spec: repl/spec.md §3 — /run-tests with no test functions
#[test]
#[ignore] // /run-tests not yet ported to v4 REPL
fn e2e_run_tests_empty() {
    let input = "/run-tests\n";
    let o = run_repl(input, "rt_empty");
    let s = stdout_str(&o);
    assert!(
        s.contains("No test-* functions found"),
        "should report no tests found\n---\n{s}"
    );
}

// spec: repl/spec.md §3 — /run-tests mixed pass and fail
#[test]
#[ignore] // /run-tests not yet ported to v4 REPL
fn e2e_run_tests_mixed_pass_fail() {
    let input = "(deftype (Option a) None (Some [:a val]))\n\
                 (defn test-pass-1 [] None)\n\
                 (defn test-pass-2 [] None)\n\
                 (defn test-fail-1 [] (Some \"broken\"))\n\
                 /run-tests\n";
    let o = run_repl(input, "rt_mixed");
    let s = stdout_str(&o);
    assert!(
        s.contains("2 passed") && s.contains("1 failed"),
        "should report 2 passed, 1 failed\n---\n{s}"
    );
}

// spec: repl/spec.md §3 — /run-tests ignores non-test functions
#[test]
#[ignore] // /run-tests not yet ported to v4 REPL
fn e2e_run_tests_ignores_non_test() {
    let input = "(deftype (Option a) None (Some [:a val]))\n\
                 (defn helper [] None)\n\
                 (defn test-one [] None)\n\
                 /run-tests\n";
    let o = run_repl(input, "rt_ignores_non_test");
    let s = stdout_str(&o);
    assert!(
        s.contains("1 passed"),
        "should only discover test-* functions, not 'helper'\n---\n{s}"
    );
    // "helper" will appear in the defn display line (user/helper ; defn),
    // but it must NOT appear in the /run-tests results (no "helper ... ok/FAIL")
    assert!(
        !s.contains("helper ."),
        "non-test function 'helper' should not appear in run-tests results\n---\n{s}"
    );
}

// ===========================================================================
// §4  Self-documentation
// ===========================================================================

// spec: repl/spec.md §4.2 — special form self-documentation
#[test]
fn e2e_s4_2_special_form_feedback() {
    let o = run_repl("if\n", "s4_2_if");
    let s = stdout_str(&o);
    // Must NOT be an error; must show a signature.
    assert!(
        !s.contains("Error:"),
        "bare 'if' should produce a signature, not an error\n---\n{s}"
    );
    assert!(
        s.contains("Fn") || s.contains("Bool"),
        "expected signature-like output for 'if'\n---\n{s}"
    );
}

// spec: repl/spec.md §4.2 — special form self-documentation (let)
#[test]
fn e2e_s4_2_special_form_let() {
    let o = run_repl("let\n", "s4_2_let");
    let s = stdout_str(&o);
    assert!(
        !s.contains("Error:"),
        "bare 'let' should produce a signature, not an error\n---\n{s}"
    );
}

// ===========================================================================
// §1.1  Output Categories — bare type name lookup
// ===========================================================================

// spec: repl/spec.md §1.1 — bare primitive type name produces output
#[test]
fn e2e_s1_1_bare_type_int() {
    let o = run_repl("Int\n", "s1_1_int");
    assert_success(&o);
    let s = stdout_str(&o);
    assert!(
        !s.contains("Error:"),
        "bare 'Int' should show type info, not error\n---\n{s}"
    );
    assert!(
        s.contains("Int"),
        "bare 'Int' should display type info\n---\n{s}"
    );
}

// spec: repl/spec.md §1.1 — bare primitive type Bool produces output
#[test]
fn e2e_s1_1_bare_type_bool() {
    let o = run_repl("Bool\n", "s1_1_bool");
    assert_success(&o);
    let s = stdout_str(&o);
    assert!(
        !s.contains("Error:"),
        "bare 'Bool' should show type info, not error\n---\n{s}"
    );
}

// spec: repl/spec.md §1.1 — bare primitive type Float produces output
#[test]
fn e2e_s1_1_bare_type_float() {
    let o = run_repl("Float\n", "s1_1_float");
    assert_success(&o);
    let s = stdout_str(&o);
    assert!(
        !s.contains("Error:"),
        "bare 'Float' should show type info, not error\n---\n{s}"
    );
    assert!(
        s.contains("Float"),
        "bare 'Float' should display type info\n---\n{s}"
    );
}

// spec: repl/spec.md §1.1 — bare primitive type String produces output
#[test]
fn e2e_s1_1_bare_type_string() {
    let o = run_repl("String\n", "s1_1_string");
    assert_success(&o);
    let s = stdout_str(&o);
    assert!(
        !s.contains("Error:"),
        "bare 'String' should show type info, not error\n---\n{s}"
    );
    assert!(
        s.contains("String"),
        "bare 'String' should display type info\n---\n{s}"
    );
}

// spec: repl/spec.md §1.1 — bare user-defined type name produces output
#[test]
fn e2e_s1_1_bare_type_user_defined() {
    let o = run_repl("(deftype Color Red Green Blue)\nColor\n", "s1_1_color");
    assert_success(&o);
    let s = stdout_str(&o);
    assert!(
        !s.contains("Error:"),
        "bare 'Color' should show type info, not error\n---\n{s}"
    );
    assert!(
        s.contains("Color"),
        "bare 'Color' should display the type name\n---\n{s}"
    );
}

// spec: repl/spec.md §4.1 — bare symbol lookup shows type
#[test]
fn e2e_s4_1_bare_symbol_lookup() {
    // repl/spec.md §4.1: entering a function name shows its type.
    // Currently works (shows type + <closure>) though not fully qualified.
    let o = run_repl(&format!("{PRIMS}(defn inc [n] (add-i64 n 1))\ninc\n"), "s4_1_bare");
    assert_success(&o);
    let results = result_lines(&o);
    assert!(results.len() >= 2, "expected defn result + lookup result");
    // Second result should show the function type.
    assert!(
        results[1].contains("Fn"),
        "bare symbol should show type: {:?}",
        results[1]
    );
}

// ===========================================================================
// §5  Error presentation
// ===========================================================================

// spec: repl/spec.md §5.1 — errors visible in stdout (part of REPL conversation)
#[test]
fn e2e_s5_1_errors_on_stdout() {
    let o = run_repl(&format!("{PRIMS}(add-i64 2 true)\n"), "s5_1_stdout");
    let out = stdout_str(&o);
    assert!(
        out.contains("Error:") || out.contains("type mismatch"),
        "error should be on stdout\nstdout: {out}\nstderr: {}",
        stderr_str(&o)
    );
}

// spec: repl/spec.md §5.1 — error category and source location
#[test]
fn e2e_s5_1_error_contains_category_and_location() {
    // repl/spec.md §5.1: errors show category + source location + message.
    let o = run_repl(&format!("{PRIMS}(add-i64 2 true)\n"), "s5_1_format");
    assert_success(&o);
    // Currently errors go to stdout — check there.
    let all = format!("{}{}", stdout_str(&o), stderr_str(&o));
    assert!(all.contains("Error:"), "missing error category");
    assert!(all.contains("type mismatch"), "missing error message");
}

// spec: repl/spec.md §5.2 — error recovery continues session
#[test]
fn e2e_s5_2_error_recovery() {
    // repl/spec.md §5.2: after an error, REPL continues and accepts new input.
    let o = run_repl(&format!("{PRIMS}(add-i64 2 true)\n(add-i64 1 2)\n"), "s5_2_recovery");
    assert_success(&o);
    let all = format!("{}{}", stdout_str(&o), stderr_str(&o));
    assert!(all.contains("Error:"), "first expr should error");
    assert_result(&o, ":primitives/Int 3");
}

// spec: repl/spec.md §5.2 — session state survives error
#[test]
fn e2e_s5_2_session_state_survives_error() {
    // repl/spec.md §5.2: definitions before an error remain usable after.
    let o = run_repl(
        &format!("{PRIMS}(defn inc [n] (add-i64 n 1))\n\
         (add-i64 2 true)\n\
         (inc 5)\n"),
        "s5_2_state",
    );
    assert_success(&o);
    assert_result(&o, ":primitives/Int 6");
}

// spec: repl/spec.md §5.3 — type error shows expected and actual
#[test]
fn e2e_s5_3_type_error_shows_expected_actual() {
    // repl/spec.md §5.3: type errors include expected and actual types.
    let o = run_repl(&format!("{PRIMS}(add-i64 2 true)\n"), "s5_3_types");
    let all = format!("{}{}", stdout_str(&o), stderr_str(&o));
    assert!(
        all.contains("Int") && all.contains("Bool"),
        "type error should mention both expected (Int) and actual (Bool)\n---\n{all}"
    );
}

// ===========================================================================
// §6  Discoverability
// ===========================================================================

// spec: repl/spec.md §6.2 — startup banner
#[test]
fn e2e_s6_2_startup_banner() {
    let o = run_repl("", "s6_2_banner");
    let s = stdout_str(&o);
    assert!(
        s.contains("Cranelisp") || s.contains("cranelisp"),
        "banner should mention language name\n---\n{s}"
    );
    assert!(
        s.contains("/help") || s.contains("help"),
        "banner should hint at /help\n---\n{s}"
    );
}

// ===========================================================================
// §7  Performance
// ===========================================================================

// spec: repl/spec.md §7.1 — startup latency under 500ms
#[test]
fn e2e_s7_1_startup_under_500ms() {
    // repl/spec.md §7.1: startup to first prompt within 500ms.
    let start = std::time::Instant::now();
    let o = run_repl("", "s7_1_startup");
    let elapsed = start.elapsed();
    assert_success(&o);
    assert!(
        elapsed.as_millis() < 500,
        "startup took {}ms, spec requires < 500ms",
        elapsed.as_millis()
    );
}

// spec: repl/spec.md §7.2 — simple eval latency under 50ms
#[test]
fn e2e_s7_2_simple_eval_under_50ms() {
    // repl/spec.md §7.2: simple eval within 50ms of Enter.
    // We measure the full run (startup + eval + exit) and check it's fast.
    let start = std::time::Instant::now();
    let o = run_repl(&format!("{PRIMS}(add-i64 1 2)\n"), "s7_2_eval");
    let elapsed = start.elapsed();
    assert_success(&o);
    assert_result(&o, ":primitives/Int 3");
    // Allow generous headroom — subprocess overhead adds latency.
    // The spec target is 50ms for eval alone; we check total < 2000ms.
    assert!(
        elapsed.as_millis() < 2000,
        "expression eval took {}ms total (subprocess)",
        elapsed.as_millis()
    );
}

// ===========================================================================
// Ring 0: Core expression evaluation
// ===========================================================================

// spec: 04-expressions §4.1.1 — integer arithmetic in REPL
#[test]
fn e2e_ring0_arithmetic() {
    let o = run_repl(
        &format!("{PRIMS}(add-i64 2 3)\n(sub-i64 10 4)\n(mul-i64 6 7)\n"),
        "r0_arith",
    );
    assert_success(&o);
    let r: Vec<_> = result_lines(&o).into_iter().filter(|l| !l.contains("imported from")).collect();
    assert_eq!(r, vec![":primitives/Int 5", ":primitives/Int 6", ":primitives/Int 42"]);
}

// spec: 04-expressions §4.1.3 — boolean expressions in REPL
#[test]
fn e2e_ring0_booleans() {
    let o = run_repl(
        &format!("{PRIMS}(eq-i64 3 3)\n(lt-i64 2 5)\n(not true)\n"),
        "r0_bool",
    );
    assert_success(&o);
    let r: Vec<_> = result_lines(&o).into_iter().filter(|l| !l.contains("imported from")).collect();
    assert_eq!(r, vec![":primitives/Bool true", ":primitives/Bool true", ":primitives/Bool false"]);
}

// spec: 04-expressions §4.3 — let binding in REPL
#[test]
fn e2e_ring0_let_binding() {
    let o = run_repl(
        &format!("{PRIMS}(let [x 10] (let [y 20] (add-i64 x y)))\n"),
        "r0_let",
    );
    assert_success(&o);
    assert_result(&o, ":primitives/Int 30");
}

// spec: 05-definitions §5.1 — function definition and call in REPL
#[test]
fn e2e_ring0_defn_and_call() {
    let o = run_repl(
        &format!("{PRIMS}(defn double [x] (mul-i64 x 2))\n(double 21)\n"),
        "r0_defn",
    );
    assert_success(&o);
    let r: Vec<_> = result_lines(&o).into_iter().filter(|l| !l.contains("imported from")).collect();
    assert_eq!(r.len(), 2);
    assert!(r[0].contains("(Fn [primitives/Int] primitives/Int)"), "defn type: {:?}", r[0]);
    assert_eq!(r[1], ":primitives/Int 42");
}

// spec: 04-expressions §4.6 — recursive function application
#[test]
fn e2e_ring0_recursion_factorial() {
    let o = run_repl(
        &format!("{PRIMS}(defn factorial [n] (if (eq-i64 n 0) 1 (mul-i64 n (factorial (sub-i64 n 1)))))\n\
         (factorial 10)\n"),
        "r0_fact",
    );
    assert_success(&o);
    assert_result(&o, ":primitives/Int 3628800");
}

// spec: 04-expressions §4.4 — if expression
#[test]
fn e2e_ring0_conditional() {
    let o = run_repl(
        &format!("{PRIMS}(defn abs [n] (if (lt-i64 n 0) (sub-i64 0 n) n))\n\
         (abs -42)\n(abs 7)\n"),
        "r0_cond",
    );
    assert_success(&o);
    let r = result_lines(&o);
    assert!(r.contains(&":primitives/Int 42".to_string()));
    assert!(r.contains(&":primitives/Int 7".to_string()));
}

// spec: 12-runtime §12.7.1 — compile-time type error
#[test]
fn e2e_ring0_type_error() {
    let o = run_repl(&format!("{PRIMS}(add-i64 2 true)\n"), "r0_tyerr");
    assert_success(&o); // REPL continues
    let all = format!("{}{}", stdout_str(&o), stderr_str(&o));
    assert!(all.contains("Error:"));
    assert!(all.contains("type mismatch"));
}

// spec: 04-expressions §4.2 — unbound variable reference error
#[test]
fn e2e_ring0_unbound_name() {
    let o = run_repl("(nonexistent 1 2)\n", "r0_unbound");
    assert_success(&o);
    let all = format!("{}{}", stdout_str(&o), stderr_str(&o));
    assert!(all.contains("Error:"));
}

// ===========================================================================
// Ring 1: Heap types
// ===========================================================================

// spec: 04-expressions §4.1.4 — string literal
#[test]
fn e2e_ring1_string_literal() {
    let o = run_repl("\"hello, world\"\n", "r1_str");
    assert_success(&o);
    assert_result(&o, ":primitives/String \"hello, world\"");
}

// spec: appendix-a-builtins §A.3 — string primitive functions
#[test]
fn e2e_ring1_string_primitives() {
    let o = run_repl(
        &format!("{PRIMS}(str-len \"cranelisp\")\n\
         (str-concat \"hello\" \" world\")\n\
         (int-to-string 42)\n\
         (str-eq \"abc\" \"abc\")\n"),
        "r1_strops",
    );
    assert_success(&o);
    let r: Vec<_> = result_lines(&o).into_iter().filter(|l| !l.contains("imported from")).collect();
    assert_eq!(
        r,
        vec![":primitives/Int 9", ":primitives/String \"hello world\"", ":primitives/String \"42\"", ":primitives/Bool true"]
    );
}

// spec: 05-definitions §5.2.1 — product type construction
#[test]
fn e2e_ring1_adt_product() {
    let o = run_repl(
        "(deftype Point [:Int x :Int y])\n(Point 3 4)\n",
        "r1_product",
    );
    assert_success(&o);
    assert_result(&o, ":user/Point (Point 3 4)");
}

// spec: 05-definitions §5.2.2 — sum type construction
#[test]
fn e2e_ring1_adt_sum() {
    let o = run_repl(
        "(deftype (Option a) None (Some [:a val]))\n(Some 42)\nNone\n",
        "r1_sum",
    );
    assert_success(&o);
    assert_stdout_contains(&o, "(Option.Some 42)");
    assert_stdout_contains(&o, "Option.None");
}

// spec: 06-pattern-matching §6.1 — match expression with ADT
#[test]
fn e2e_ring1_pattern_matching() {
    let o = run_repl(
        "(deftype (Option a) None (Some [:a val]))\n\
         (defn get-or-zero [o] (match o [None 0 (Some x) x]))\n\
         (get-or-zero (Some 99))\n\
         (get-or-zero None)\n",
        "r1_match",
    );
    assert_success(&o);
    let r = result_lines(&o);
    assert!(r.contains(&":primitives/Int 99".to_string()));
    assert!(r.contains(&":primitives/Int 0".to_string()));
}

// spec: 04-expressions §4.5 — lambda expression
#[test]
fn e2e_ring1_closure() {
    let o = run_repl(
        &format!("{PRIMS}(let [add-five (fn [x] (add-i64 x 5))] (add-five 10))\n"),
        "r1_closure",
    );
    assert_success(&o);
    assert_result(&o, ":primitives/Int 15");
}

// spec: 04-expressions §4.5.1 — free variable capture
#[test]
fn e2e_ring1_closure_capture() {
    let o = run_repl(
        &format!("{PRIMS}(defn make-adder [n] (fn [x] (add-i64 n x)))\n\
         (let [add-ten (make-adder 10)] (add-ten 25))\n"),
        "r1_capture",
    );
    assert_success(&o);
    assert_result(&o, ":primitives/Int 35");
}

// spec: 04-expressions §4.6 — higher-order function application
#[test]
fn e2e_ring1_higher_order() {
    let o = run_repl(
        &format!("{PRIMS}(defn apply-twice [f x] (f (f x)))\n\
         (defn inc [n] (add-i64 n 1))\n\
         (apply-twice inc 5)\n"),
        "r1_hof",
    );
    assert_success(&o);
    assert_result(&o, ":primitives/Int 7");
}

// ===========================================================================
// Multi-feature sessions
// ===========================================================================

// spec: repl/spec.md §5.2 — multi-step REPL session
#[test]
fn e2e_session_ring0_full() {
    let o = run_repl(
        &format!("{PRIMS}(defn square [n] (mul-i64 n n))\n\
         (defn sum-to [n] (if (eq-i64 n 0) 0 (add-i64 n (sum-to (sub-i64 n 1)))))\n\
         (square 8)\n\
         (sum-to 100)\n\
         (square (sum-to 10))\n"),
        "session_r0",
    );
    assert_success(&o);
    let r = result_lines(&o);
    assert!(r.contains(&":primitives/Int 64".to_string()));
    assert!(r.contains(&":primitives/Int 5050".to_string()));
    assert!(r.contains(&":primitives/Int 3025".to_string()));
}

// spec: 06-pattern-matching §6.1 — ADT workflow session
#[test]
fn e2e_session_ring1_adt_workflow() {
    let o = run_repl(
        &format!("{PRIMS}(deftype (Option a) None (Some [:a val]))\n\
         (defn map-opt [f opt] (match opt [None None (Some x) (Some (f x))]))\n\
         (defn inc [n] (add-i64 n 1))\n\
         (map-opt inc (Some 41))\n\
         (map-opt inc None)\n"),
        "session_r1",
    );
    assert_success(&o);
    assert_stdout_contains(&o, "(Option.Some 42)");
    let r = result_lines(&o);
    let none_results: Vec<_> = r
        .iter()
        .filter(|l| l.contains("Option.None") && !l.contains("Some"))
        .collect();
    assert!(!none_results.is_empty(), "expected Option.None in: {r:?}");
}

// ===========================================================================
// §4.2  Special form feedback — fn, defn, deftype, match
// ===========================================================================

// spec: repl/spec.md §4.2 — special form self-documentation (fn)
#[test]
fn e2e_s4_2_special_form_fn() {
    let o = run_repl("fn\n", "s4_2_fn");
    let s = stdout_str(&o);
    assert!(
        !s.contains("Error:"),
        "bare 'fn' should produce a signature, not an error\n---\n{s}"
    );
    assert!(
        s.contains("Fn") && s.contains("fn"),
        "expected signature-like output for 'fn'\n---\n{s}"
    );
}

// spec: repl/spec.md §4.2 — special form self-documentation (defn)
#[test]
fn e2e_s4_2_special_form_defn() {
    let o = run_repl("defn\n", "s4_2_defn");
    let s = stdout_str(&o);
    assert!(
        !s.contains("Error:"),
        "bare 'defn' should produce a signature, not an error\n---\n{s}"
    );
    assert!(
        s.contains("Fn") && s.contains("defn"),
        "expected signature-like output for 'defn'\n---\n{s}"
    );
}

// spec: repl/spec.md §4.2 — special form self-documentation (deftype)
#[test]
fn e2e_s4_2_special_form_deftype() {
    let o = run_repl("deftype\n", "s4_2_deftype");
    let s = stdout_str(&o);
    assert!(
        !s.contains("Error:"),
        "bare 'deftype' should produce a signature, not an error\n---\n{s}"
    );
    assert!(
        s.contains("Fn") && s.contains("deftype"),
        "expected signature-like output for 'deftype'\n---\n{s}"
    );
}

// spec: repl/spec.md §4.2 — special form self-documentation (match)
#[test]
fn e2e_s4_2_special_form_match() {
    let o = run_repl("match\n", "s4_2_match");
    let s = stdout_str(&o);
    assert!(
        !s.contains("Error:"),
        "bare 'match' should produce a signature, not an error\n---\n{s}"
    );
    assert!(
        s.contains("Fn") && s.contains("match"),
        "expected signature-like output for 'match'\n---\n{s}"
    );
}

// ===========================================================================
// §4.3  Operator feedback
// ===========================================================================

// spec: repl/spec.md §4.3 — bare + operator shows type
#[test]
fn e2e_s4_3_operator_plus_feedback() {
    let input = format!("{PRIMS}{NUM_TRAIT_PRELUDE}+\n");
    let o = run_repl(&input, "s4_3_plus");
    let s = stdout_str(&o);
    assert!(
        !s.contains("Error:"),
        "bare '+' should produce type info, not an error\n---\n{s}"
    );
    assert!(
        s.contains("Fn") && s.contains("+"),
        "expected type signature for '+'\n---\n{s}"
    );
}

// spec: repl/spec.md §4.3 — bare = operator shows type
#[test]
fn e2e_s4_3_operator_eq_feedback() {
    let input = format!("{PRIMS}{EQ_TRAIT_PRELUDE}=\n");
    let o = run_repl(&input, "s4_3_eq");
    let s = stdout_str(&o);
    assert!(
        !s.contains("Error:"),
        "bare '=' should produce type info, not an error\n---\n{s}"
    );
    assert!(
        s.contains("Fn") && s.contains("Bool"),
        "expected type signature for '=' showing Bool return\n---\n{s}"
    );
}

// spec: repl/spec.md §4.3 — bare < operator shows type
#[test]
fn e2e_s4_3_operator_lt_feedback() {
    let input = format!("{PRIMS}{ORD_TRAIT_PRELUDE}<\n");
    let o = run_repl(&input, "s4_3_lt");
    let s = stdout_str(&o);
    assert!(
        !s.contains("Error:"),
        "bare '<' should produce type info, not an error\n---\n{s}"
    );
    assert!(
        s.contains("Fn") && s.contains("Bool"),
        "expected type signature for '<' showing Bool return\n---\n{s}"
    );
}

// ===========================================================================
// §1.1  Constructor lookup
// ===========================================================================

// spec: repl/spec.md §1.1 — bare constructor lookup shows type and dot notation
#[test]
fn e2e_s1_1_constructor_lookup() {
    let o = run_repl(
        "(deftype Color Red Green Blue)\nRed\n",
        "s1_1_ctor",
    );
    let s = stdout_str(&o);
    assert!(
        s.contains("Color.Red"),
        "bare constructor 'Red' should show Color.Red\n---\n{s}"
    );
    assert!(
        s.contains("user/Color"),
        "constructor lookup should show qualified type\n---\n{s}"
    );
}

// ===========================================================================
// §3.3  /list categories: Special forms, Traits
// ===========================================================================

// spec: repl/spec.md §3.4 — /imports shows Special forms category
#[test]
fn e2e_s3_4_imports_special_forms() {
    let o = run_repl("/imports\n", "s3_4_specials");
    let s = stdout_str(&o);
    assert!(
        s.contains("Special forms"),
        "expected 'Special forms' category in /imports\n---\n{s}"
    );
    assert!(
        s.contains("if") && s.contains("let") && s.contains("defn"),
        "expected special forms in /imports listing\n---\n{s}"
    );
}

// spec: repl/spec.md §3.3 — /list shows Traits category
#[test]
fn e2e_s3_3_list_traits() {
    let input = format!("{PRIMS}{NUM_TRAIT_PRELUDE}/list\n");
    let o = run_repl(&input, "s3_3_traits");
    let s = stdout_str(&o);
    assert!(
        s.contains("Traits"),
        "expected 'Traits' category in /list\n---\n{s}"
    );
}

// ===========================================================================
// §4.1  Bare trait lookup
// ===========================================================================

// spec: repl/spec.md §4.1 — bare trait name shows trait info
#[test]
fn e2e_s4_1_bare_trait_lookup() {
    let o = run_repl(
        "(deftrait (Sizeable a) (size [a] Int))\nSizeable\n",
        "s4_1_trait",
    );
    let s = stdout_str(&o);
    assert!(
        s.contains("Sizeable"),
        "bare trait name should show trait info\n---\n{s}"
    );
    assert!(
        !s.contains("Error:"),
        "bare trait name should not error\n---\n{s}"
    );
}

// ===========================================================================
// Directory isolation — cache artifacts don't leak
// ===========================================================================

// spec: none — session isolation regression test
#[test]
fn e2e_isolation_no_shared_state() {
    // Two independent sessions should not see each other's definitions.
    let o1 = run_repl(&format!("{PRIMS}(defn secret [x] (mul-i64 x 99))\n"), "iso_a");
    assert_success(&o1);

    let o2 = run_repl("(secret 1)\n", "iso_b");
    assert_success(&o2);
    let all = format!("{}{}", stdout_str(&o2), stderr_str(&o2));
    assert!(
        all.contains("Error:"),
        "second session should not see 'secret' from first\n---\n{all}"
    );
}

// ===========================================================================
// Ring 3: /expand command (repl/spec.md §11.1)
// ===========================================================================

// spec: repl/spec.md §11.1 — /expand with a single macro shows expanded form
#[test]
fn e2e_s11_1_expand_single_macro() {
    let input = "(defmacro double [x] `(add-i64 ~x ~x))\n/expand (double 21)\n";
    let o = run_repl(input, "expand_single");
    assert_success(&o);
    let out = stdout_str(&o);
    // The expanded form should contain add-i64 with the argument substituted.
    assert!(
        out.contains("add-i64") && out.contains("21"),
        "/expand should show expanded form with add-i64 and 21, got:\n{out}"
    );
}

// spec: repl/spec.md §11.1 — /expand with nested macros expands recursively
#[test]
fn e2e_s11_1_expand_nested_macros() {
    let input = "(defmacro inc [x] `(add-i64 ~x 1))\n\
                 (defmacro double-inc [x] `(inc (inc ~x)))\n\
                 /expand (double-inc 5)\n";
    let o = run_repl(input, "expand_nested");
    assert_success(&o);
    let results = result_lines(&o);
    // The /expand output line should contain add-i64 (fully expanded).
    let expand_line = results.iter().find(|r| r.contains("add-i64"));
    assert!(
        expand_line.is_some(),
        "/expand should recursively expand to add-i64, got results: {results:?}"
    );
    // The expansion result itself should not contain 'inc' — fully expanded.
    let line = expand_line.unwrap();
    assert!(
        !line.contains("inc"),
        "/expand should fully expand (no 'inc' in expansion), got: {line}"
    );
}

// spec: repl/spec.md §11.1 — /expand with no macro calls shows input unchanged
#[test]
fn e2e_s11_1_expand_no_macro() {
    let input = "/expand (add-i64 1 2)\n";
    let o = run_repl(input, "expand_no_macro");
    assert_success(&o);
    let out = stdout_str(&o);
    assert!(
        out.contains("add-i64") && out.contains("1") && out.contains("2"),
        "/expand should display form unchanged, got:\n{out}"
    );
}

// spec: repl/spec.md §11.1 — /expand on non-macro form displays input unchanged (negative)
#[test]
fn e2e_s11_1_neg_expand_non_macro_unchanged() {
    let input = "/expand (add-i64 1 2)\n";
    let o = run_repl(input, "expand_neg_nonmacro");
    assert_success(&o);
    let out = stdout_str(&o);
    // Should NOT contain "error" — just display the form.
    assert!(
        !out.contains("Error:"),
        "/expand on non-macro should not error, got:\n{out}"
    );
}

// ===========================================================================
// Ring 3: /doc on macro (repl/spec.md §11.2.4)
// ===========================================================================

// spec: repl/spec.md §11.2.4 — /doc on macro with no docstring
#[test]
fn e2e_s11_2_4_doc_macro_no_docstring() {
    let input = "(defmacro my-mac [x] x)\n/doc my-mac\n";
    let o = run_repl(input, "doc_macro_nodoc");
    assert_success(&o);
    let out = stdout_str(&o);
    // Should show something about the macro, even without docstring.
    assert!(
        out.contains("my-mac"),
        "/doc should mention the macro name, got:\n{out}"
    );
}

// spec: repl/spec.md §11.2.4 — /doc on macro with docstring
#[test]
fn e2e_s11_2_4_doc_macro_with_docstring() {
    let input = "(defmacro my-inc \"Increment by one\" [x] `(add-i64 ~x 1))\n/doc my-inc\n";
    let o = run_repl(input, "doc_macro_withdoc");
    assert_success(&o);
    let out = stdout_str(&o);
    assert!(
        out.contains("Increment by one"),
        "/doc should show docstring, got:\n{out}"
    );
}

// ===========================================================================
// Ring 3: /imports command (repl/spec.md §3.4)
// ===========================================================================

// spec: repl/spec.md §3.4 — /imports with no explicit imports
#[test]
fn e2e_s3_4_imports_empty() {
    let input = "/imports\n";
    let o = run_repl(input, "imports_empty");
    assert_success(&o);
    // Should not error — empty or shows prelude imports.
    let out = stdout_str(&o);
    assert!(
        !out.contains("Error:"),
        "/imports should not error on empty session, got:\n{out}"
    );
}

// spec: repl/spec.md §3.4 — /imports after explicit import
#[test]
fn e2e_s3_4_imports_after_import() {
    let input = "(import [primitives [add-i64 sub-i64]])\n/imports\n";
    let o = run_repl(input, "imports_after");
    assert_success(&o);
    let out = stdout_str(&o);
    assert!(
        out.contains("add-i64"),
        "/imports should show imported names, got:\n{out}"
    );
}

// spec: repl/spec.md §3.4 — /imports <module> filters to one module
#[test]
fn e2e_s3_4_imports_filter_by_module() {
    let input = "(import [primitives [add-i64]])\n/imports primitives\n";
    let o = run_repl(input, "imports_filter");
    assert_success(&o);
    let out = stdout_str(&o);
    assert!(
        out.contains("add-i64"),
        "/imports primitives should show primitives imports, got:\n{out}"
    );
}

// spec: repl/spec.md §3.4 — /imports <nonexistent> is empty, not error (negative)
#[test]
fn e2e_s3_4_neg_imports_nonexistent_not_error() {
    let input = "/imports nonexistent\n";
    let o = run_repl(input, "imports_neg_nonexist");
    assert_success(&o);
    let out = stdout_str(&o);
    assert!(
        !out.contains("Error:"),
        "/imports nonexistent should not error, got:\n{out}"
    );
}

// ===========================================================================
// Ring 3: defmacro special form (repl/spec.md §4.2)
// ===========================================================================

// spec: 09-macros.md §9.9.4 — runtime error during expansion reported as error, not crash
#[test]
fn e2e_s9_9_4_runtime_error_during_expansion() {
    // Define a macro whose body triggers division by zero during expansion.
    let input = "(defmacro boom [x] (let [_ (div-i64 1 0)] x))\n(boom 42)\n";
    let o = run_repl(input, "macro_runtime_error");
    // The process should not crash (exit 0 with error message on stdout).
    // Currently this causes SIGILL — the test documents the gap.
    assert!(
        o.status.success(),
        "runtime error during macro expansion should produce clean error, not crash (exit {:?})",
        o.status.code()
    );
    let out = stdout_str(&o);
    assert!(
        out.contains("error"),
        "runtime error during expansion should report error, got:\n{out}"
    );
}

// spec: repl/spec.md §4.2 — bare 'defmacro' shows special form signature
#[test]
fn e2e_s4_2_special_form_defmacro() {
    let input = "defmacro\n";
    let o = run_repl(input, "sf_defmacro");
    assert_success(&o);
    let out = stdout_str(&o);
    // Should show special form info, not "undefined variable" error.
    assert!(
        !out.contains("undefined variable"),
        "bare 'defmacro' should produce feedback, not 'undefined variable', got:\n{out}"
    );
}

// ===========================================================================
// Sprint 15 Wave 3: /list boundary tests (repl/spec.md §3.3)
// ===========================================================================

// spec: repl/spec.md §3.3 — /list on empty module shows `(no definitions)`
#[test]
fn e2e_s3_3_list_empty_module() {
    let o = run_repl("/list\n", "s3_3_empty");
    let s = stdout_str(&o);
    assert!(
        s.contains("(no definitions)"),
        "expected '(no definitions)' for empty module, got:\n{s}"
    );
}

// spec: repl/spec.md §3.3 — /list prefix filter matches names
#[test]
fn e2e_s3_3_list_prefix_filter() {
    let o = run_repl(
        "(defn foo [x] x)\n(defn bar [x] x)\n(defn fuzz [x] x)\n/list f\n",
        "s3_3_prefix",
    );
    let s = stdout_str(&o);
    assert!(
        s.contains("foo"),
        "expected 'foo' with prefix 'f'\n---\n{s}"
    );
    assert!(
        s.contains("fuzz"),
        "expected 'fuzz' with prefix 'f'\n---\n{s}"
    );
}

// spec: repl/spec.md §3.3 — /list MUST NOT show imports
#[test]
fn e2e_s3_3_list_neg_no_imports() {
    let o = run_repl(
        "(import [primitives [add-i64]])\n/list\n",
        "s3_3_neg_imports",
    );
    let s = stdout_str(&o);
    // The /list result lines (after the import line) should not contain add-i64.
    // /list should show "(no definitions)" since only an import was made.
    assert!(
        s.contains("(no definitions)"),
        "expected '(no definitions)' when only imports exist, got:\n{s}"
    );
}

// spec: repl/spec.md §3.3 — /list MUST NOT show special forms
#[test]
fn e2e_s3_3_list_neg_no_special_forms() {
    let o = run_repl("/list\n", "s3_3_neg_sf");
    let s = stdout_str(&o);
    assert!(
        !s.contains("Special forms"),
        "expected NO 'Special forms' in /list output\n---\n{s}"
    );
}

// spec: repl/spec.md §3.3 — /list shows constructors in Types category
#[test]
fn e2e_s3_3_list_constructors_in_types() {
    let o = run_repl(
        "(deftype Color Red Green Blue)\n/list\n",
        "s3_3_ctors_types",
    );
    let s = stdout_str(&o);
    assert!(
        s.contains("Types"),
        "expected 'Types' category\n---\n{s}"
    );
    // Constructors should appear in Types alongside their type name.
    assert!(
        s.contains("Red") && s.contains("Green") && s.contains("Blue"),
        "expected constructors in Types category\n---\n{s}"
    );
    assert!(
        s.contains("Color"),
        "expected type name in Types category\n---\n{s}"
    );
}

// spec: repl/spec.md §3.3 — /list shows Fns category (not Functions)
#[test]
fn e2e_s3_3_list_fns_category_name() {
    let o = run_repl("(defn foo [x] x)\n/list\n", "s3_3_fns_name");
    let s = stdout_str(&o);
    assert!(
        s.contains("Fns:"),
        "expected 'Fns:' category label\n---\n{s}"
    );
    assert!(
        !s.contains("Functions:"),
        "expected 'Fns:' not 'Functions:'\n---\n{s}"
    );
}

// ===========================================================================
// Sprint 15 Wave 3: /imports tests (repl/spec.md §3.4)
// ===========================================================================

// spec: repl/spec.md §3.4 — /imports always shows Special forms
#[test]
fn e2e_s3_4_imports_special_forms_always() {
    let o = run_repl("/imports\n", "s3_4_sf_always");
    let s = stdout_str(&o);
    assert!(
        s.contains("Special forms"),
        "expected 'Special forms' always present in /imports\n---\n{s}"
    );
    // Should contain at least some special forms
    assert!(
        s.contains("if") && s.contains("let"),
        "expected 'if' and 'let' in /imports Special forms\n---\n{s}"
    );
}

// spec: repl/spec.md §3.4 — /imports <module> filters by source module
// Note: E2E tests run in isolated dirs without stdlib, so (import [primitives ...])
// doesn't work. Instead, we define a module and import from it.
#[test]
fn e2e_s3_4_imports_filter_shows_from() {
    let input = "/mod mymod\n(defn bar [x] x)\n/mod user\n(import [mymod [bar]])\n/imports mymod\n";
    let o = run_repl(input, "s3_4_filter_from");
    let s = stdout_str(&o);
    assert!(
        s.contains("bar"),
        "expected 'bar' in /imports mymod\n---\n{s}"
    );
}

// spec: repl/spec.md §3.4 — /imports includes reexports
// Note: E2E tests run in isolated dirs without stdlib/prelude. Instead, we
// define a module, import from it, and verify the import appears.
#[test]
fn e2e_s3_4_imports_includes_imports() {
    let input = "/mod mymod\n(defn bar [x] x)\n/mod user\n(import [mymod [bar]])\n/imports\n";
    let o = run_repl(input, "s3_4_imports_incl");
    let s = stdout_str(&o);
    // Should show Fns category with imported bar
    assert!(
        s.contains("Fns") || s.contains("bar"),
        "expected imported function 'bar' in /imports\n---\n{s}"
    );
}

// spec: repl/spec.md §3.4 — /imports nonexistent: silent re-prompt, not error (negative)
#[test]
fn e2e_s3_4_neg_imports_nonexistent_silent() {
    let input = "/imports nonexistent\n42\n";
    let o = run_repl(input, "s3_4_neg_nomod");
    assert_success(&o);
    let s = stdout_str(&o);
    assert!(
        !s.contains("Error:"),
        "/imports nonexistent should not produce an error\n---\n{s}"
    );
    // The next expression should still work
    assert_result(&o, ":primitives/Int 42");
}

// ===========================================================================
// Sprint 15 Wave 3: /exports tests (repl/spec.md §3.5)
// ===========================================================================

// spec: repl/spec.md §3.5 — /exports with no argument prints usage hint
#[test]
fn e2e_s3_5_exports_no_arg_usage() {
    let o = run_repl("/exports\n", "s3_5_no_arg");
    let s = stdout_str(&o);
    assert!(
        s.contains("Usage:") || s.contains("usage:") || s.contains("/exports <module"),
        "expected usage hint for /exports with no argument\n---\n{s}"
    );
}

// spec: repl/spec.md §3.5 — /exports nonexistent prints module not found
#[test]
fn e2e_s3_5_exports_not_found() {
    let o = run_repl("/exports nonexistent\n", "s3_5_notfound");
    let s = stdout_str(&o);
    assert!(
        s.contains("not found") || s.contains("Module"),
        "expected 'not found' for /exports nonexistent\n---\n{s}"
    );
}

// spec: repl/spec.md §3.5 — /exports on module with public symbols
#[test]
fn e2e_s3_5_exports_lists_symbols() {
    // Define a module via /mod, add definitions, then check /exports from user.
    let input = "/mod mymod\n(defn bar [x] x)\n/mod user\n/exports mymod\n";
    let o = run_repl(input, "s3_5_exports");
    let s = stdout_str(&o);
    assert!(
        s.contains("bar"),
        "expected 'bar' in /exports mymod output\n---\n{s}"
    );
}

// ===========================================================================
// Sprint 15 Wave 3: Universal format — definition results (repl/spec.md §1.1, §1.3)
// ===========================================================================

// spec: repl/spec.md §1.3 — defn response includes `; defn` classification
#[test]
fn e2e_s1_3_defn_classification() {
    let o = run_repl(&format!("{PRIMS}(defn double [x] (mul-i64 x 2))\n"), "s1_3_defn_class");
    let s = stdout_str(&o);
    assert!(
        s.contains("; defn"),
        "defn response should include '; defn' classification\n---\n{s}"
    );
}

// spec: repl/spec.md §1.3 — deftype response includes `; deftype`
#[test]
fn e2e_s1_3_deftype_classification() {
    let o = run_repl("(deftype Color Red Green Blue)\n", "s1_3_deftype_class");
    let s = stdout_str(&o);
    assert!(
        s.contains("; deftype"),
        "deftype response should include '; deftype' classification\n---\n{s}"
    );
}

// spec: repl/spec.md §1.3 — deftype response includes `; match:` with constructors
#[test]
fn e2e_s1_3_deftype_match_section() {
    let o = run_repl("(deftype Color Red Green Blue)\n", "s1_3_deftype_match");
    let s = stdout_str(&o);
    assert!(
        s.contains("; match:"),
        "deftype response should include '; match:' section\n---\n{s}"
    );
    assert!(
        s.contains("Red") && s.contains("Green") && s.contains("Blue"),
        "deftype match section should list constructors\n---\n{s}"
    );
}

// spec: repl/spec.md §1.3 — deftrait response includes `; deftrait` and `; defn:` section
#[test]
fn e2e_s1_3_deftrait_defn_section() {
    let o = run_repl(
        "(deftrait (Sizeable a) (size [a] Int))\n",
        "s1_3_deftrait_defn",
    );
    let s = stdout_str(&o);
    assert!(
        s.contains("; deftrait"),
        "deftrait response should include '; deftrait'\n---\n{s}"
    );
    assert!(
        s.contains("; defn:"),
        "deftrait response should include '; defn:' section\n---\n{s}"
    );
    assert!(
        s.contains("size"),
        "deftrait '; defn:' section should list 'size'\n---\n{s}"
    );
}

// ===========================================================================
// Sprint 15 Wave 3: Universal format — bare symbol lookup (repl/spec.md §4.1)
// ===========================================================================

// spec: repl/spec.md §4.1.1 — bare function shows `; defn` classification
#[test]
fn e2e_s4_1_bare_fn_classification() {
    let o = run_repl(&format!("{PRIMS}(defn inc [n] (add-i64 n 1))\ninc\n"), "s4_1_fn_class");
    let _s = stdout_str(&o);
    // The second result line (bare lookup) should contain '; defn'
    let results = result_lines(&o);
    assert!(
        results.len() >= 2,
        "expected defn result + lookup result, got: {results:?}"
    );
    assert!(
        results[1].contains("; defn"),
        "bare fn lookup should show '; defn' classification, got: {:?}",
        results[1]
    );
}

// spec: repl/spec.md §4.1.3 — bare type shows `; deftype` and `; match:` section
#[test]
fn e2e_s4_1_bare_type_match_section() {
    let o = run_repl(
        "(deftype Color Red Green Blue)\nColor\n",
        "s4_1_type_match",
    );
    let s = stdout_str(&o);
    assert!(
        s.contains("; deftype"),
        "bare type should show '; deftype' classification\n---\n{s}"
    );
    assert!(
        s.contains("; match:"),
        "bare type should show '; match:' section\n---\n{s}"
    );
}

// spec: repl/spec.md §4.1.4 — bare trait shows `; deftrait` and `; defn:` section
#[test]
fn e2e_s4_1_bare_trait_defn_section() {
    let o = run_repl(
        "(deftrait (Sizeable a) (size [a] Int))\nSizeable\n",
        "s4_1_trait_defn",
    );
    let s = stdout_str(&o);
    assert!(
        s.contains("; deftrait"),
        "bare trait should show '; deftrait' classification\n---\n{s}"
    );
    assert!(
        s.contains("; defn:"),
        "bare trait should show '; defn:' section\n---\n{s}"
    );
    assert!(
        s.contains("size"),
        "bare trait '; defn:' section should list 'size'\n---\n{s}"
    );
}

// spec: repl/spec.md §4.1.5 — bare special form shows `; special form` classification
#[test]
fn e2e_s4_1_bare_special_form_classification() {
    let o = run_repl("if\n", "s4_1_sf_class");
    let s = stdout_str(&o);
    assert!(
        s.contains("; special form"),
        "bare 'if' should show '; special form' classification\n---\n{s}"
    );
}

// spec: repl/spec.md §4.1.6 — bare macro shows `; defmacro` and clause signatures
#[test]
fn e2e_s4_1_bare_macro_defmacro() {
    let input = "(defmacro inc [x] `(add-i64 ~x 1))\ninc\n";
    let o = run_repl(input, "s4_1_macro_cls");
    let s = stdout_str(&o);
    assert!(
        s.contains("; defmacro"),
        "bare macro should show '; defmacro' classification\n---\n{s}"
    );
    assert!(
        s.contains("; [x] -> Sexp"),
        "bare macro should show clause signature\n---\n{s}"
    );
}

// spec: repl/spec.md §4.1.3 — bare builtin type Int shows `; type` classification
// Note: `; impl:` section only appears when traits are loaded (prelude).
// E2E tests run without prelude, so we only check the classification.
#[test]
fn e2e_s4_1_bare_builtin_type() {
    let o = run_repl("Int\n", "s4_1_int_type");
    let s = stdout_str(&o);
    assert!(
        s.contains("; type"),
        "bare 'Int' should show '; type' classification\n---\n{s}"
    );
    assert!(
        s.contains("primitives/Int"),
        "bare 'Int' should show 'primitives/Int'\n---\n{s}"
    );
}

// spec: repl/spec.md §4.1.2 — bare constructor shows `; deftype` classification
#[test]
fn e2e_s4_1_bare_constructor_classification() {
    let o = run_repl(
        "(deftype Color Red Green Blue)\nRed\n",
        "s4_1_ctor_class",
    );
    let s = stdout_str(&o);
    assert!(
        s.contains("; deftype"),
        "bare constructor 'Red' should show '; deftype' classification\n---\n{s}"
    );
}

// ===========================================================================
// Sprint 15 Wave 3: Negative tests — format boundary checks
// ===========================================================================

// spec: repl/spec.md §3.3 — /list neg: Fns category MUST NOT contain constructors
#[test]
fn e2e_s3_3_list_neg_ctors_not_in_fns() {
    let o = run_repl(
        "(deftype Color Red Green Blue)\n/list\n",
        "s3_3_neg_ctors_fns",
    );
    let s = stdout_str(&o);
    // Find the Fns section if it exists — it should NOT exist since no fns defined.
    // With only a deftype, only Types category should appear.
    assert!(
        !s.contains("Fns:"),
        "expected no 'Fns:' category when only deftype defined\n---\n{s}"
    );
}

// ===========================================================================
// Sprint 18 C3: Slash command tests — /doc, /source, /sexp, /ast, /clif,
// /disasm, /mod (repl/spec.md §3.1)
// ===========================================================================

// --- /doc (repl/spec.md §3.1 row: /doc <name>) ---

// spec: repl/spec.md §3.1 — /doc on user-defined function with docstring
#[test]
fn e2e_s3_1_doc_user_fn_with_docstring() {
    let input = "(defn greet \"Says hello\" [x] x)\n/doc greet\n";
    let o = run_repl(input, "s3_1_doc_fn_docstring");
    let s = stdout_str(&o);
    assert!(
        s.contains("Says hello"),
        "/doc should show docstring, got:\n{s}"
    );
}

// spec: repl/spec.md §3.1 — /doc on user-defined function without docstring
#[test]
fn e2e_s3_1_doc_user_fn_no_docstring() {
    let input = "(defn greet [x] x)\n/doc greet\n";
    let o = run_repl(input, "s3_1_doc_fn_no_docstring");
    let s = stdout_str(&o);
    assert!(
        s.contains("no docstring") || s.contains("greet"),
        "/doc on fn without docstring should mention name or 'no docstring', got:\n{s}"
    );
}

// spec: repl/spec.md §3.1 — /doc on builtin primitive shows docstring
#[test]
fn e2e_s3_1_doc_builtin() {
    let input = format!("{PRIMS}/doc add-i64\n");
    let o = run_repl(&input, "s3_1_doc_builtin");
    let s = stdout_str(&o);
    // Builtins have docstrings per spec/appendix-a-builtins.md §A.5
    assert!(
        s.contains("add-i64"),
        "/doc on builtin should mention the name, got:\n{s}"
    );
    assert!(
        !s.contains("unknown"),
        "/doc on builtin should not produce 'unknown' error, got:\n{s}"
    );
}

// spec: repl/spec.md §3.1 — /doc on nonexistent symbol gives error
#[test]
fn e2e_s3_1_doc_neg_nonexistent() {
    let input = "/doc nonexistent_sym\n";
    let o = run_repl(input, "s3_1_doc_neg_nonexistent");
    let s = stdout_str(&o);
    assert!(
        s.contains("unknown") || s.contains("Error") || s.contains("not found"),
        "/doc on nonexistent symbol should produce error, got:\n{s}"
    );
}

// spec: repl/spec.md §3.1 — /doc with no argument gives usage message
#[test]
fn e2e_s3_1_doc_neg_no_arg() {
    let input = "/doc\n";
    let o = run_repl(input, "s3_1_doc_neg_no_arg");
    let s = stdout_str(&o);
    assert!(
        s.contains("usage") || s.contains("/doc"),
        "/doc with no arg should show usage, got:\n{s}"
    );
}

// --- /source (repl/spec.md §3.1 row: /source <name>) ---

// spec: repl/spec.md §3.1 — /source shows original source text
#[test]
#[ignore] // /source not yet ported to v4 REPL
fn e2e_s3_1_source_user_fn() {
    let input = format!("{PRIMS}(defn double [x] (add-i64 x x))\n/source double\n");
    let o = run_repl(&input, "s3_1_source_fn");
    let s = stdout_str(&o);
    assert!(
        s.contains("defn double") || s.contains("(defn double"),
        "/source should show original source, got:\n{s}"
    );
}

// spec: repl/spec.md §3.1 — /source on nonexistent symbol gives error
#[test]
fn e2e_s3_1_source_neg_nonexistent() {
    let input = "/source nonexistent_sym\n";
    let o = run_repl(input, "s3_1_source_neg_nonexistent");
    let s = stdout_str(&o);
    assert!(
        s.contains("unknown") || s.contains("Error") || s.contains("not found"),
        "/source on nonexistent should produce error, got:\n{s}"
    );
}

// --- /sexp (repl/spec.md §3.1 row: /sexp <name>) ---

// spec: repl/spec.md §3.1 — /sexp shows parsed S-expression
#[test]
fn e2e_s3_1_sexp_user_fn() {
    let input = format!("{PRIMS}(defn double [x] (add-i64 x x))\n/sexp double\n");
    let o = run_repl(&input, "s3_1_sexp_fn");
    let s = stdout_str(&o);
    // /sexp should display the parsed S-expression tree (not an error)
    assert!(
        !s.contains("unknown command"),
        "/sexp should be a recognized command, got:\n{s}"
    );
    assert!(
        s.contains("double") || s.contains("defn"),
        "/sexp should show sexp structure mentioning the definition, got:\n{s}"
    );
}

// spec: repl/spec.md §3.1 — /sexp on nonexistent symbol gives error
#[test]
fn e2e_s3_1_sexp_neg_nonexistent() {
    let input = "/sexp nonexistent_sym\n";
    let o = run_repl(input, "s3_1_sexp_neg_nonexistent");
    let s = stdout_str(&o);
    assert!(
        s.contains("unknown") || s.contains("Error") || s.contains("not found"),
        "/sexp on nonexistent should produce error, got:\n{s}"
    );
}

// --- /ast (repl/spec.md §3.1 row: /ast <name>) ---

// spec: repl/spec.md §3.1 — /ast shows AST
#[test]
fn e2e_s3_1_ast_user_fn() {
    let input = format!("{PRIMS}(defn double [x] (add-i64 x x))\n/ast double\n");
    let o = run_repl(&input, "s3_1_ast_fn");
    let s = stdout_str(&o);
    assert!(
        !s.contains("unknown command"),
        "/ast should be a recognized command, got:\n{s}"
    );
    assert!(
        s.contains("double") || s.contains("Defn") || s.contains("defn"),
        "/ast should show AST structure, got:\n{s}"
    );
}

// spec: repl/spec.md §3.1 — /ast on nonexistent symbol gives error
#[test]
fn e2e_s3_1_ast_neg_nonexistent() {
    let input = "/ast nonexistent_sym\n";
    let o = run_repl(input, "s3_1_ast_neg_nonexistent");
    let s = stdout_str(&o);
    assert!(
        s.contains("unknown") || s.contains("Error") || s.contains("not found"),
        "/ast on nonexistent should produce error, got:\n{s}"
    );
}

// --- /clif (repl/spec.md §3.1 row: /clif <name>) ---

// spec: repl/spec.md §3.1 — /clif shows Cranelift IR
#[test]
fn e2e_s3_1_clif_user_fn() {
    let input = format!("{PRIMS}(defn double [x] (add-i64 x x))\n/clif double\n");
    let o = run_repl(&input, "s3_1_clif_fn");
    let s = stdout_str(&o);
    assert!(
        !s.contains("unknown command"),
        "/clif should be a recognized command, got:\n{s}"
    );
    // Cranelift IR typically contains 'block' or 'function' keywords
    assert!(
        s.contains("block") || s.contains("function") || s.contains("v"),
        "/clif should show Cranelift IR, got:\n{s}"
    );
}

// spec: repl/spec.md §3.1 — /clif on nonexistent symbol gives error
#[test]
fn e2e_s3_1_clif_neg_nonexistent() {
    let input = "/clif nonexistent_sym\n";
    let o = run_repl(input, "s3_1_clif_neg_nonexistent");
    let s = stdout_str(&o);
    assert!(
        s.contains("unknown") || s.contains("Error") || s.contains("not found"),
        "/clif on nonexistent should produce error, got:\n{s}"
    );
}

// --- /disasm (repl/spec.md §3.1 row: /disasm <name>) ---

// spec: repl/spec.md §3.1 — /disasm shows disassembled native code
#[test]
fn e2e_s3_1_disasm_user_fn() {
    let input = format!("{PRIMS}(defn double [x] (add-i64 x x))\n/disasm double\n");
    let o = run_repl(&input, "s3_1_disasm_fn");
    let s = stdout_str(&o);
    assert!(
        !s.contains("unknown command"),
        "/disasm should be a recognized command, got:\n{s}"
    );
}

// spec: repl/spec.md §3.1 — /disasm on nonexistent symbol gives error
#[test]
fn e2e_s3_1_disasm_neg_nonexistent() {
    let input = "/disasm nonexistent_sym\n";
    let o = run_repl(input, "s3_1_disasm_neg_nonexistent");
    let s = stdout_str(&o);
    assert!(
        s.contains("unknown") || s.contains("Error") || s.contains("not found"),
        "/disasm on nonexistent should produce error, got:\n{s}"
    );
}

// --- /mod (repl/spec.md §8 — Module Demo Scenarios) ---

// spec: repl/spec.md §8 Scenario 1 — /mod <name> switches namespace
#[test]
fn e2e_s8_mod_switch_namespace() {
    let input = "/mod math\n";
    let o = run_repl(input, "s8_mod_switch");
    let s = stdout_str(&o);
    // After /mod math, prompt should change to math>
    assert!(
        s.contains("math>"),
        "/mod math should switch prompt to 'math>', got:\n{s}"
    );
}

// spec: repl/spec.md §8 Scenario 6 — bare /mod shows current module
#[test]
fn e2e_s8_mod_show_current() {
    let input = "/mod\n";
    let o = run_repl(input, "s8_mod_show_current");
    let s = stdout_str(&o);
    // Bare /mod should display the current module name (default: user)
    assert!(
        s.contains("user"),
        "bare /mod should show current module 'user', got:\n{s}"
    );
}

// spec: repl/spec.md §8 Scenario 2 — /mod user switches back
#[test]
fn e2e_s8_mod_switch_back() {
    let input = "/mod math\n/mod user\n";
    let o = run_repl(input, "s8_mod_switch_back");
    let s = stdout_str(&o);
    // Should have math> at some point, then user> again
    assert!(
        s.contains("math>") && s.contains("user>"),
        "/mod should switch to math> then back to user>, got:\n{s}"
    );
}

// spec: repl/spec.md §3.3 — /list neg: empty categories omitted
#[test]
fn e2e_s3_3_list_neg_empty_categories_omitted() {
    let o = run_repl("(defn foo [x] x)\n/list\n", "s3_3_neg_empty_cats");
    let s = stdout_str(&o);
    // Only Fns should appear, not Types or Traits or Macros
    assert!(
        !s.contains("Types:"),
        "expected no 'Types:' when no types defined\n---\n{s}"
    );
    assert!(
        !s.contains("Traits:"),
        "expected no 'Traits:' when no traits defined\n---\n{s}"
    );
    assert!(
        !s.contains("Macros:"),
        "expected no 'Macros:' when no macros defined\n---\n{s}"
    );
}

// spec: 08-modules §8.3 — imported function as higher-order argument in REPL
// An imported function should be usable as a value (passed to higher-order fns).
// Bug: REPL codegen fails with "undefined variable" when an imported function
// is passed as an argument to a higher-order function.
#[test]
fn e2e_imported_fn_as_higher_order_arg_repl() {
    let input = "(import [num.int [even?]])\n(defn apply-fn [f x] (f x))\n(apply-fn even? 4)\n";
    let o = run_repl_with_test_prelude(input, "imported_fn_higher_order");
    let out = stdout_str(&o);
    assert!(
        !out.contains("Error:") && !out.contains("error:"),
        "imported fn as higher-order arg should not error in REPL:\n{out}"
    );
    assert!(
        out.contains("true"),
        "expected (apply-fn even? 4) = true, got:\n{out}"
    );
}
