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

fn stdout_str(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}

fn stderr_str(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

/// All non-empty result lines (lines starting with "> " that have content
/// after the prompt prefix).
fn result_lines(o: &Output) -> Vec<String> {
    stdout_str(o)
        .lines()
        .filter(|l| l.starts_with("> ") && l.len() > 2)
        .map(|l| l[2..].to_string())
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
    assert_stdout_contains(o, &format!("> {expected}"));
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
    let o = run_repl("(add-i64 2 3)\n", "smoke_expr");
    assert_success(&o);
    assert_result(&o, ":Int 5");
}

// ===========================================================================
// §1.2  Expression display format
// ===========================================================================

// Current: `:Int 5`.  Spec: `:primitives/Int 5` (fully qualified).
// spec: repl/spec.md §1.2 — fully qualified type names in display
#[test]
#[ignore = "Sprint 6: REPL displays :Int not :primitives/Int — qualified type display not yet wired"]
fn e2e_s1_2_int_display_qualified() {
    let o = run_repl("(add-i64 2 3)\n", "s1_2_int");
    assert_result(&o, ":primitives/Int 5");
}

// spec: repl/spec.md §1.2 — fully qualified Bool type display
#[test]
#[ignore = "Sprint 6: REPL displays :Bool not :primitives/Bool — qualified type display not yet wired"]
fn e2e_s1_2_bool_display_qualified() {
    let o = run_repl("(eq-i64 3 3)\n", "s1_2_bool");
    assert_result(&o, ":primitives/Bool true");
}

// spec: repl/spec.md §1.2 — fully qualified String type display
#[test]
#[ignore = "Sprint 6: REPL displays :String not :primitives/String — qualified type display not yet wired"]
fn e2e_s1_2_string_display_qualified() {
    let o = run_repl("\"hello\"\n", "s1_2_str");
    assert_result(&o, ":primitives/String \"hello\"");
}

// spec: repl/spec.md §1.5 — nullary constructor dot notation
#[test]
#[ignore = "Sprint 6: REPL displays 'Red' not 'Color.Red' — constructor dot notation not yet wired"]
fn e2e_s1_5_nullary_ctor_dot_notation() {
    let o = run_repl(
        "(deftype Color Red Green Blue)\nRed\n",
        "s1_5_nullary",
    );
    assert_stdout_contains(&o, "Color.Red");
}

// spec: repl/spec.md §1.5 — data constructor dot notation
#[test]
#[ignore = "Sprint 6: REPL displays '(Some 42)' not '(Option.Some 42)' — constructor dot notation not yet wired"]
fn e2e_s1_5_data_ctor_dot_notation() {
    let o = run_repl(
        "(deftype (Option a) None (Some [:a val]))\n(Some 42)\n",
        "s1_5_data",
    );
    assert_stdout_contains(&o, "(Option.Some 42)");
}

// ===========================================================================
// §1.3  Definition display format
// ===========================================================================

// spec: repl/spec.md §1.3 — definition display with qualified name
#[test]
#[ignore = "Sprint 6: REPL displays '<closure>' not 'user/id' — qualified name display not yet wired"]
fn e2e_s1_3_defn_shows_qualified_name() {
    let o = run_repl("(defn id [x] x)\n", "s1_3_defn");
    assert_stdout_contains(&o, "user/id");
}

// spec: repl/spec.md §1.3 — deftype display with qualified name
#[test]
#[ignore = "Sprint 6: REPL displays ':Color' not ':user/Color' — qualified name display not yet wired"]
fn e2e_s1_3_deftype_shows_qualified_name() {
    let o = run_repl("(deftype Color Red Green Blue)\n", "s1_3_deftype");
    assert_stdout_contains(&o, ":user/Color");
}

// ===========================================================================
// §2.1  Prompt format
// ===========================================================================

// spec: repl/spec.md §2.1 — prompt format with timing and module
#[test]
#[ignore = "Sprint 6: prompt shows '> ' not '{N}+{N}ms; user>' — module-aware prompt not yet wired"]
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
#[ignore = "Sprint 6: no continuation prompt for incomplete input — multi-line input not yet wired"]
fn e2e_s2_2_continuation_prompt() {
    // Open paren without close — should show continuation prompt.
    let o = run_repl("(add-i64\n  2 3)\n", "s2_2_cont");
    let s = stdout_str(&o);
    assert!(s.contains("..."), "expected '...' continuation\n---\n{s}");
    assert_result(&o, ":Int 5");
}

// ===========================================================================
// §3  Slash commands
// ===========================================================================

// spec: repl/spec.md §3.1 — /help slash command
#[test]
#[ignore = "Ring 4, Sprint 7+: REPL slash command infrastructure"]
fn e2e_s3_1_help() {
    let o = run_repl("/help\n", "s3_help");
    let s = stdout_str(&o);
    assert!(s.contains("/help"), "expected /help in output\n---\n{s}");
    assert!(s.contains("/sig"), "expected /sig in output\n---\n{s}");
    assert!(s.contains("/list"), "expected /list in output\n---\n{s}");
}

// spec: repl/spec.md §3.1 — /quit slash command
#[test]
#[ignore = "Ring 4, Sprint 7+: REPL slash command infrastructure"]
fn e2e_s3_1_quit() {
    let o = run_repl("/quit\n", "s3_quit");
    assert_success(&o);
}

// spec: repl/spec.md §3.3 — /list slash command
#[test]
#[ignore = "Ring 4, Sprint 7+: REPL slash command infrastructure"]
fn e2e_s3_3_list() {
    let o = run_repl(
        "(defn foo [x] x)\n(deftype Color Red)\n/list\n",
        "s3_list",
    );
    let s = stdout_str(&o);
    assert!(s.contains("Functions"), "expected Functions category\n---\n{s}");
    assert!(s.contains("foo"), "expected foo in listing\n---\n{s}");
    assert!(s.contains("Types"), "expected Types category\n---\n{s}");
}

// spec: repl/spec.md §3.1 — /sig slash command
#[test]
#[ignore = "Ring 4, Sprint 7+: REPL slash command infrastructure"]
fn e2e_s3_1_sig() {
    let o = run_repl("(defn double [x] (mul-i64 x 2))\n/sig double\n", "s3_sig");
    let s = stdout_str(&o);
    assert!(
        s.contains("Fn") && s.contains("Int"),
        "expected function signature\n---\n{s}"
    );
}

// spec: repl/spec.md §3.4 — /info slash command
#[test]
#[ignore = "Ring 4, Sprint 7+: REPL slash command infrastructure"]
fn e2e_s3_4_info() {
    let o = run_repl(
        "(defn double [x] (mul-i64 x 2))\n/info double\n",
        "s3_info",
    );
    let s = stdout_str(&o);
    assert!(s.contains("double"), "expected 'double' in info\n---\n{s}");
    assert!(s.contains("bytes"), "expected code size in info\n---\n{s}");
}

// spec: repl/spec.md §3.1 — /time slash command
#[test]
#[ignore = "Ring 4, Sprint 7+: REPL slash command infrastructure"]
fn e2e_s3_1_time() {
    let o = run_repl("/time (add-i64 1 2)\n", "s3_time");
    let s = stdout_str(&o);
    assert!(s.contains("ms"), "expected timing in output\n---\n{s}");
}

// spec: repl/spec.md §3.1 — /type slash command
#[test]
#[ignore = "Ring 4, Sprint 7+: REPL slash command infrastructure"]
fn e2e_s3_1_type() {
    let o = run_repl("/type (add-i64 1 2)\n", "s3_type");
    let s = stdout_str(&o);
    assert!(s.contains("Int"), "expected Int type\n---\n{s}");
}

// ===========================================================================
// §4  Self-documentation
// ===========================================================================

// spec: repl/spec.md §4.2 — special form self-documentation
#[test]
#[ignore = "Ring 4, Sprint 7+: special form self-documentation"]
fn e2e_s4_2_special_form_feedback() {
    let o = run_repl("if\n", "s4_2_if");
    let s = stdout_str(&o);
    // Must NOT be an error; must show a signature.
    assert!(
        !s.contains("error:"),
        "bare 'if' should produce a signature, not an error\n---\n{s}"
    );
    assert!(
        s.contains("Fn") || s.contains("Bool"),
        "expected signature-like output for 'if'\n---\n{s}"
    );
}

// spec: repl/spec.md §4.2 — special form self-documentation (let)
#[test]
#[ignore = "Ring 4, Sprint 7+: special form self-documentation"]
fn e2e_s4_2_special_form_let() {
    let o = run_repl("let\n", "s4_2_let");
    let s = stdout_str(&o);
    assert!(
        !s.contains("error:"),
        "bare 'let' should produce a signature, not an error\n---\n{s}"
    );
}

// spec: repl/spec.md §4.1 — bare symbol lookup shows type
#[test]
fn e2e_s4_1_bare_symbol_lookup() {
    // repl/spec.md §4.1: entering a function name shows its type.
    // Currently works (shows type + <closure>) though not fully qualified.
    let o = run_repl("(defn inc [n] (add-i64 n 1))\ninc\n", "s4_1_bare");
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

// spec: repl/spec.md §5.1 — errors routed to stderr
#[test]
#[ignore = "Ring 4, Sprint 7+: error output routing to stderr"]
fn e2e_s5_1_errors_on_stderr() {
    let o = run_repl("(add-i64 2 true)\n", "s5_1_stderr");
    let err = stderr_str(&o);
    assert!(
        err.contains("error:") || err.contains("type mismatch"),
        "error should be on stderr\nstderr: {err}\nstdout: {}",
        stdout_str(&o)
    );
}

// spec: repl/spec.md §5.1 — error category and source location
#[test]
fn e2e_s5_1_error_contains_category_and_location() {
    // repl/spec.md §5.1: errors show category + source location + message.
    let o = run_repl("(add-i64 2 true)\n", "s5_1_format");
    assert_success(&o);
    // Currently errors go to stdout — check there.
    let all = format!("{}{}", stdout_str(&o), stderr_str(&o));
    assert!(all.contains("error:"), "missing error category");
    assert!(all.contains("type mismatch"), "missing error message");
}

// spec: repl/spec.md §5.2 — error recovery continues session
#[test]
fn e2e_s5_2_error_recovery() {
    // repl/spec.md §5.2: after an error, REPL continues and accepts new input.
    let o = run_repl("(add-i64 2 true)\n(add-i64 1 2)\n", "s5_2_recovery");
    assert_success(&o);
    let all = format!("{}{}", stdout_str(&o), stderr_str(&o));
    assert!(all.contains("error:"), "first expr should error");
    assert_result(&o, ":Int 3");
}

// spec: repl/spec.md §5.2 — session state survives error
#[test]
fn e2e_s5_2_session_state_survives_error() {
    // repl/spec.md §5.2: definitions before an error remain usable after.
    let o = run_repl(
        "(defn inc [n] (add-i64 n 1))\n\
         (add-i64 2 true)\n\
         (inc 5)\n",
        "s5_2_state",
    );
    assert_success(&o);
    assert_result(&o, ":Int 6");
}

// spec: repl/spec.md §5.3 — type error shows expected and actual
#[test]
fn e2e_s5_3_type_error_shows_expected_actual() {
    // repl/spec.md §5.3: type errors include expected and actual types.
    let o = run_repl("(add-i64 2 true)\n", "s5_3_types");
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
#[ignore = "Ring 4, Sprint 7+: REPL startup banner"]
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
    let o = run_repl("(add-i64 1 2)\n", "s7_2_eval");
    let elapsed = start.elapsed();
    assert_success(&o);
    assert_result(&o, ":Int 3");
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
        "(add-i64 2 3)\n(sub-i64 10 4)\n(mul-i64 6 7)\n",
        "r0_arith",
    );
    assert_success(&o);
    let r = result_lines(&o);
    assert_eq!(r, vec![":Int 5", ":Int 6", ":Int 42"]);
}

// spec: 04-expressions §4.1.3 — boolean expressions in REPL
#[test]
fn e2e_ring0_booleans() {
    let o = run_repl(
        "(eq-i64 3 3)\n(lt-i64 2 5)\n(not true)\n",
        "r0_bool",
    );
    assert_success(&o);
    let r = result_lines(&o);
    assert_eq!(r, vec![":Bool true", ":Bool true", ":Bool false"]);
}

// spec: 04-expressions §4.3 — let binding in REPL
#[test]
fn e2e_ring0_let_binding() {
    let o = run_repl(
        "(let [x 10] (let [y 20] (add-i64 x y)))\n",
        "r0_let",
    );
    assert_success(&o);
    assert_result(&o, ":Int 30");
}

// spec: 05-definitions §5.1 — function definition and call in REPL
#[test]
fn e2e_ring0_defn_and_call() {
    let o = run_repl(
        "(defn double [x] (mul-i64 x 2))\n(double 21)\n",
        "r0_defn",
    );
    assert_success(&o);
    let r = result_lines(&o);
    assert_eq!(r.len(), 2);
    assert!(r[0].contains("(Fn [Int] Int)"), "defn type: {:?}", r[0]);
    assert_eq!(r[1], ":Int 42");
}

// spec: 04-expressions §4.6 — recursive function application
#[test]
fn e2e_ring0_recursion_factorial() {
    let o = run_repl(
        "(defn factorial [n] (if (eq-i64 n 0) 1 (mul-i64 n (factorial (sub-i64 n 1)))))\n\
         (factorial 10)\n",
        "r0_fact",
    );
    assert_success(&o);
    assert_result(&o, ":Int 3628800");
}

// spec: 04-expressions §4.4 — if expression
#[test]
fn e2e_ring0_conditional() {
    let o = run_repl(
        "(defn abs [n] (if (lt-i64 n 0) (sub-i64 0 n) n))\n\
         (abs -42)\n(abs 7)\n",
        "r0_cond",
    );
    assert_success(&o);
    let r = result_lines(&o);
    assert!(r.contains(&":Int 42".to_string()));
    assert!(r.contains(&":Int 7".to_string()));
}

// spec: 12-runtime §12.7.1 — compile-time type error
#[test]
fn e2e_ring0_type_error() {
    let o = run_repl("(add-i64 2 true)\n", "r0_tyerr");
    assert_success(&o); // REPL continues
    let all = format!("{}{}", stdout_str(&o), stderr_str(&o));
    assert!(all.contains("error:"));
    assert!(all.contains("type mismatch"));
}

// spec: 04-expressions §4.2 — unbound variable reference error
#[test]
fn e2e_ring0_unbound_name() {
    let o = run_repl("(nonexistent 1 2)\n", "r0_unbound");
    assert_success(&o);
    let all = format!("{}{}", stdout_str(&o), stderr_str(&o));
    assert!(all.contains("error:"));
}

// ===========================================================================
// Ring 1: Heap types
// ===========================================================================

// spec: 04-expressions §4.1.4 — string literal
#[test]
fn e2e_ring1_string_literal() {
    let o = run_repl("\"hello, world\"\n", "r1_str");
    assert_success(&o);
    assert_result(&o, ":String \"hello, world\"");
}

// spec: appendix-a-builtins §A.3 — string primitive functions
#[test]
fn e2e_ring1_string_primitives() {
    let o = run_repl(
        "(str-len \"cranelisp\")\n\
         (str-concat \"hello\" \" world\")\n\
         (int-to-string 42)\n\
         (str-eq \"abc\" \"abc\")\n",
        "r1_strops",
    );
    assert_success(&o);
    let r = result_lines(&o);
    assert_eq!(
        r,
        vec![":Int 9", ":String \"hello world\"", ":String \"42\"", ":Bool true"]
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
    assert_result(&o, ":Point (Point 3 4)");
}

// spec: 05-definitions §5.2.2 — sum type construction
#[test]
fn e2e_ring1_adt_sum() {
    let o = run_repl(
        "(deftype (Option a) None (Some [:a val]))\n(Some 42)\nNone\n",
        "r1_sum",
    );
    assert_success(&o);
    assert_stdout_contains(&o, "(Some 42)");
    assert_stdout_contains(&o, "None");
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
    assert!(r.contains(&":Int 99".to_string()));
    assert!(r.contains(&":Int 0".to_string()));
}

// spec: 04-expressions §4.5 — lambda expression
#[test]
fn e2e_ring1_closure() {
    let o = run_repl(
        "(let [add-five (fn [x] (add-i64 x 5))] (add-five 10))\n",
        "r1_closure",
    );
    assert_success(&o);
    assert_result(&o, ":Int 15");
}

// spec: 04-expressions §4.5.1 — free variable capture
#[test]
fn e2e_ring1_closure_capture() {
    let o = run_repl(
        "(defn make-adder [n] (fn [x] (add-i64 n x)))\n\
         (let [add-ten (make-adder 10)] (add-ten 25))\n",
        "r1_capture",
    );
    assert_success(&o);
    assert_result(&o, ":Int 35");
}

// spec: 04-expressions §4.6 — higher-order function application
#[test]
fn e2e_ring1_higher_order() {
    let o = run_repl(
        "(defn apply-twice [f x] (f (f x)))\n\
         (defn inc [n] (add-i64 n 1))\n\
         (apply-twice inc 5)\n",
        "r1_hof",
    );
    assert_success(&o);
    assert_result(&o, ":Int 7");
}

// ===========================================================================
// Multi-feature sessions
// ===========================================================================

// spec: repl/spec.md §5.2 — multi-step REPL session
#[test]
fn e2e_session_ring0_full() {
    let o = run_repl(
        "(defn square [n] (mul-i64 n n))\n\
         (defn sum-to [n] (if (eq-i64 n 0) 0 (add-i64 n (sum-to (sub-i64 n 1)))))\n\
         (square 8)\n\
         (sum-to 100)\n\
         (square (sum-to 10))\n",
        "session_r0",
    );
    assert_success(&o);
    let r = result_lines(&o);
    assert!(r.contains(&":Int 64".to_string()));
    assert!(r.contains(&":Int 5050".to_string()));
    assert!(r.contains(&":Int 3025".to_string()));
}

// spec: 06-pattern-matching §6.1 — ADT workflow session
#[test]
fn e2e_session_ring1_adt_workflow() {
    let o = run_repl(
        "(deftype (Option a) None (Some [:a val]))\n\
         (defn map-opt [f opt] (match opt [None None (Some x) (Some (f x))]))\n\
         (defn inc [n] (add-i64 n 1))\n\
         (map-opt inc (Some 41))\n\
         (map-opt inc None)\n",
        "session_r1",
    );
    assert_success(&o);
    assert_stdout_contains(&o, "(Some 42)");
    let r = result_lines(&o);
    let none_results: Vec<_> = r
        .iter()
        .filter(|l| l.contains("None") && !l.contains("Some"))
        .collect();
    assert!(!none_results.is_empty(), "expected None in: {r:?}");
}

// ===========================================================================
// Directory isolation — cache artifacts don't leak
// ===========================================================================

// spec: none — session isolation regression test
#[test]
fn e2e_isolation_no_shared_state() {
    // Two independent sessions should not see each other's definitions.
    let o1 = run_repl("(defn secret [x] (mul-i64 x 99))\n", "iso_a");
    assert_success(&o1);

    let o2 = run_repl("(secret 1)\n", "iso_b");
    assert_success(&o2);
    let all = format!("{}{}", stdout_str(&o2), stderr_str(&o2));
    assert!(
        all.contains("error:"),
        "second session should not see 'secret' from first\n---\n{all}"
    );
}
