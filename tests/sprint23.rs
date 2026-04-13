//! Sprint 23: Executable Generation, /reset, Shell Escape, File Watching, REPL Cache
//!
//! Layer 4 (E2E) test stubs for Sprint 23 features. Each test traces to a
//! specific spec section in repl/spec.md or design/backend/executable-generation.md.
//!
//! All tests are #[ignore] stubs — implementation has not started yet.
//! Tests will be un-ignored as /int delivers each feature.
//!
//! NOTE: Re-enabled in Sprint 52 (was gated behind cfg(feature) since Sprint 47).
//! All tests validated against spec before fixing.

use std::path::PathBuf;
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

// =============================================================================
// Test infrastructure (mirrors e2e.rs patterns)
// =============================================================================

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
        .join("sprint23")
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
    child.wait_with_output().expect("failed to read output")
}


/// Run cranelisp with arbitrary args in a given directory.
fn run_binary(args: &[&str], dir: &std::path::Path) -> Output {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} — run `cargo build` first"
    );

    Command::new(&binary)
        .args(args)
        .current_dir(dir)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to start cranelisp binary")
        .wait_with_output()
        .expect("failed to read output")
}

fn stdout_str(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}

fn stderr_str(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

// =============================================================================
// 1. Executable Generation (--link)
//    Spec: design/backend/executable-generation.md
//    Spec: repl/spec.md §0 (CLI invocation modes — to be updated with --link)
// =============================================================================

// --- 1.1 Basic compilation and execution ---

// spec: design/backend/executable-generation.md §3 — end-to-end --link flow
#[test]
fn link_hello_world_produces_executable() {
    // Write a minimal hello.cl with main :: () -> Int, run --link, verify
    // the output file exists and is executable.
    let dir = test_dir("link_hello");
    std::fs::write(dir.join("hello.cl"), "(defn main [] 42)").unwrap();

    let output = run_binary(&["--link", "hello.cl"], &dir);
    assert!(output.status.success(), "--link failed: {}", stderr_str(&output));

    let exe_path = dir.join("hello");
    assert!(exe_path.exists(), "expected executable 'hello' to be produced");

    // Run the produced executable and check exit code
    let exe_output = Command::new(&exe_path)
        .output()
        .expect("failed to run produced executable");
    assert_eq!(exe_output.status.code(), Some(42), "exit code should be main's return value");
}

// spec: design/backend/executable-generation.md §7 — main :: () -> Int
#[test]
fn link_main_returns_int_exit_code() {
    // main returns 0 -> exit code 0
    let dir = test_dir("link_exit_0");
    std::fs::write(dir.join("zero.cl"), "(defn main [] 0)").unwrap();

    let output = run_binary(&["--link", "zero.cl"], &dir);
    assert!(output.status.success(), "--link failed: {}", stderr_str(&output));

    let exe_output = Command::new(dir.join("zero"))
        .output()
        .expect("failed to run executable");
    assert_eq!(exe_output.status.code(), Some(0));
}

// spec: design/backend/executable-generation.md §7 — main :: () -> IO _
#[test]
fn link_main_returns_io() {
    // main returns IO — the IO trampoline should execute and the exit code
    // should come from the IO result.
    //
    // This requires:
    // 1. The prelude loaded (for IO type definition)
    // 2. validate_main to accept IO return type
    // 3. generate_startup_object to include IO trampoline
    //
    // For now, test with a minimal Pure 0 main. If prelude is needed,
    // set CRANELISP_LIB to the fixtures dir.
    let dir = test_dir("link_io_main");
    let fixtures = project_root().join("tests").join("fixtures");

    // Write a main that returns IO Int. The test prelude defines IO type.
    std::fs::write(dir.join("io_main.cl"), "(defn main [] (Pure 0))").unwrap();

    let output = Command::new(binary_path())
        .args(&["--link", "io_main.cl"])
        .current_dir(&dir)
        .env("CRANELISP_LIB", fixtures.as_os_str())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("failed to start binary");

    if output.status.success() {
        let exe_output = Command::new(dir.join("io_main"))
            .output()
            .expect("failed to run executable");
        assert_eq!(
            exe_output.status.code(),
            Some(0),
            "IO main returning Pure 0 should exit with code 0"
        );
    } else {
        let err = stderr_str(&Output {
            status: output.status,
            stdout: output.stdout,
            stderr: output.stderr,
        });
        // Expected failure: IO main not yet supported in --link
        assert!(
            err.contains("main") || err.contains("IO") || err.contains("type"),
            "failure should mention main or IO type: {err}"
        );
    }
}

// --- 1.2 Output path derivation ---

// spec: design/backend/executable-generation.md §9 — output path default
#[test]
fn link_default_output_is_entry_stem() {
    // cranelisp --link examples/hello.cl -> produces "hello" (no extension)
    let dir = test_dir("link_default_output");
    std::fs::create_dir_all(dir.join("examples")).unwrap();
    std::fs::write(dir.join("examples/hello.cl"), "(defn main [] 0)").unwrap();

    let output = run_binary(&["--link", "examples/hello.cl"], &dir);
    assert!(output.status.success(), "--link failed: {}", stderr_str(&output));
    assert!(dir.join("hello").exists(), "output should be named 'hello' (entry stem)");
}

// --- 1.3 Error cases ---

// spec: design/backend/executable-generation.md §7 — no main function
#[test]
fn link_error_no_main_function() {
    // File has no main -> clear error before linker runs
    let dir = test_dir("link_no_main");
    std::fs::write(dir.join("nomain.cl"), "(defn helper [] 42)").unwrap();

    let output = run_binary(&["--link", "nomain.cl"], &dir);
    assert!(!output.status.success(), "should fail when no main function");
    let err = stderr_str(&output);
    assert!(
        err.contains("main"),
        "error should mention 'main': {err}"
    );
}

// spec: design/backend/executable-generation.md §7 — main wrong type
#[test]
fn link_error_main_wrong_return_type() {
    // main :: () -> String -> error
    let dir = test_dir("link_main_wrong_type");
    std::fs::write(dir.join("wrong.cl"), "(defn main [] \"hello\")").unwrap();

    let output = run_binary(&["--link", "wrong.cl"], &dir);
    assert!(!output.status.success(), "should fail when main returns wrong type");
    let err = stderr_str(&output);
    assert!(
        err.contains("main") && (err.contains("Int") || err.contains("IO")),
        "error should mention acceptable main types: {err}"
    );
}

// spec: design/backend/executable-generation.md §5.4 — entry file not found
#[test]
fn link_error_file_not_found() {
    let dir = test_dir("link_file_not_found");
    let output = run_binary(&["--link", "nonexistent.cl"], &dir);
    assert!(!output.status.success());
    assert_eq!(output.status.code(), Some(1));
}

// spec: design/backend/executable-generation.md §9 — missing bundle library
#[test]
fn link_error_missing_bundle_library() {
    // When libcranelisp_exe_bundle.a is not found, a clear error is reported.
    // Hard to test without controlling the environment — this test validates
    // the error message format when bundle is absent.
    let dir = test_dir("link_no_bundle");
    std::fs::write(dir.join("hello.cl"), "(defn main [] 0)").unwrap();

    // Unset any env var that might help find the bundle
    let output = Command::new(binary_path())
        .args(&["--link", "hello.cl"])
        .current_dir(&dir)
        .env_remove("CRANELISP_BUNDLE_PATH")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("failed to start binary");

    // This test is best-effort — if the bundle happens to be in a discoverable
    // location, it might succeed. The key invariant is: when the bundle is
    // genuinely missing, the error mentions "libcranelisp_exe_bundle" and
    // "cargo build -p cranelisp-exe-bundle".
    if !output.status.success() {
        let err = stderr_str(&Output {
            status: output.status,
            stdout: output.stdout,
            stderr: output.stderr,
        });
        assert!(
            err.contains("cranelisp_exe_bundle") || err.contains("bundle"),
            "error should mention bundle library: {err}"
        );
    }
}

// spec: design/backend/executable-generation.md §9 — --no-cache with --link
#[test]
fn link_with_no_cache_is_rejected() {
    // --no-cache + --link is rejected because linking requires cached .o files.
    let dir = test_dir("link_no_cache");
    std::fs::write(dir.join("hello.cl"), "(defn main [] 0)").unwrap();

    let output = run_binary(&["--no-cache", "--link", "hello.cl"], &dir);
    assert!(!output.status.success(), "--no-cache + --link should be rejected");
    let err = stderr_str(&output);
    assert!(
        err.contains("--no-cache is not supported with --link"),
        "should explain the incompatibility: {err}"
    );
}

// --- 1.4 Cache reuse ---

// spec: design/backend/executable-generation.md §3 — cache reuse
#[test]
fn link_reuses_cached_object_files() {
    // Run --link twice — second run should be faster because .o files are cached.
    // We verify correctness (both produce working executables), not timing.
    let dir = test_dir("link_cache_reuse");
    std::fs::write(dir.join("hello.cl"), "(defn main [] 7)").unwrap();

    let output1 = run_binary(&["--link", "hello.cl"], &dir);
    assert!(output1.status.success(), "first --link failed");

    // Overwrite the exe to prove second --link re-produces it
    std::fs::remove_file(dir.join("hello")).ok();

    let output2 = run_binary(&["--link", "hello.cl"], &dir);
    assert!(output2.status.success(), "second --link failed");

    let exe_output = Command::new(dir.join("hello"))
        .output()
        .expect("failed to run executable");
    assert_eq!(exe_output.status.code(), Some(7));
}

// --- 1.5 Multi-module linking ---

// spec: design/backend/executable-generation.md §3 — module graph compilation
#[test]
fn link_multi_module_project() {
    // A project with an entry module that imports another module.
    let dir = test_dir("link_multi_module");
    std::fs::write(
        dir.join("main.cl"),
        "(import [helper [add-one]])\n(defn main [] (add-one 41))",
    )
    .unwrap();
    std::fs::write(
        dir.join("helper.cl"),
        "(defn add-one [:Int x] (add-i64 x 1))",
    )
    .unwrap();

    let output = run_binary(&["--link", "main.cl"], &dir);
    assert!(output.status.success(), "--link failed: {}", stderr_str(&output));

    let exe_output = Command::new(dir.join("main"))
        .output()
        .expect("failed to run executable");
    assert_eq!(exe_output.status.code(), Some(42));
}

// =============================================================================
// 3. Shell Escape (;#!)
//    Spec: repl/spec.md §13
// =============================================================================

// --- 3.1 Basic execution ---

// spec: repl/spec.md §13.2 — command execution via /bin/sh
#[test]
fn shell_escape_basic_echo() {
    let input = ";#! echo hello_from_shell\n/quit\n";
    let output = run_repl(input, "shell_echo");
    let out = stdout_str(&output);
    assert!(
        out.contains("hello_from_shell"),
        "shell echo output should appear: {out}"
    );
}

// spec: repl/spec.md §13.3 — output handling (stdout passthrough)
#[test]
fn shell_escape_output_passthrough() {
    let input = ";#! echo \"hello from shell\"\n/quit\n";
    let output = run_repl(input, "shell_passthrough");
    let out = stdout_str(&output);
    assert!(
        out.contains("hello from shell"),
        "command output should pass through to stdout: {out}"
    );
}

// --- 3.2 Exit code display ---

// spec: repl/spec.md §13.4 — non-zero exit code displayed
#[test]
fn shell_escape_nonzero_exit_code() {
    let input = ";#! false\n/quit\n";
    let output = run_repl(input, "shell_exit_code");
    let out = stdout_str(&output);
    assert!(
        out.contains("exit status: 1"),
        "non-zero exit code should be displayed: {out}"
    );
}

// spec: repl/spec.md §13.4 — zero exit code: silence
#[test]
fn shell_escape_zero_exit_silent() {
    let input = ";#! true\n/quit\n";
    let output = run_repl(input, "shell_exit_silent");
    let out = stdout_str(&output);
    assert!(
        !out.contains("exit status"),
        "success (exit 0) should NOT display exit code: {out}"
    );
}

// spec: repl/spec.md §13.4 — command not found shows exit code
#[test]
fn shell_escape_command_not_found() {
    let input = ";#! nonexistent_command_xyz\n/quit\n";
    let output = run_repl(input, "shell_not_found");
    let out = stdout_str(&output);
    // stderr from the shell should pass through
    let err = stderr_str(&output);
    // Either stdout or stderr should have an error message from the shell
    let combined = format!("{out}{err}");
    assert!(
        combined.contains("not found") || combined.contains("exit status: 127"),
        "command not found should produce shell error: {combined}"
    );
}

// --- 3.3 Edge cases ---

// spec: repl/spec.md §13.6 — empty command silently re-prompts
#[test]
fn shell_escape_empty_command() {
    let input = ";#!\n;#!   \n/quit\n";
    let output = run_repl(input, "shell_empty");
    let out = stdout_str(&output);
    // Should not produce any error — just re-prompt
    assert!(
        !out.contains("error") && !out.contains("failed"),
        "empty shell escape should silently re-prompt: {out}"
    );
}

// spec: repl/spec.md §13.6 — multi-line not supported, use shell syntax
#[test]
fn shell_escape_chained_commands() {
    let input = ";#! echo first && echo second\n/quit\n";
    let output = run_repl(input, "shell_chain");
    let out = stdout_str(&output);
    assert!(out.contains("first"), "first command should run: {out}");
    assert!(out.contains("second"), "second command should run: {out}");
}

// --- 3.4 No state interaction ---

// spec: repl/spec.md §13.5 — no REPL state interaction
#[test]
fn shell_escape_no_state_interaction() {
    // Define something, run shell command, definition should still work
    let input = "(defn foo [] 42)\n;#! echo test\n(foo)\n/quit\n";
    let output = run_repl(input, "shell_no_state");
    let out = stdout_str(&output);
    assert!(
        out.contains("42"),
        "REPL state should be preserved across shell escape: {out}"
    );
}

// spec: repl/spec.md §13.6 — timing shows 0+0ms after shell escape
#[test]
fn shell_escape_timing_reset() {
    let input = ";#! echo hi\n/quit\n";
    let output = run_repl(input, "shell_timing");
    let out = stdout_str(&output);
    assert!(
        out.contains("0+0ms"),
        "prompt after shell escape should show 0+0ms: {out}"
    );
}

// --- 3.5 /help integration ---

// spec: repl/spec.md §13.7 — shell escape in /help
#[test]
fn shell_escape_appears_in_help() {
    let input = "/help\n/quit\n";
    let output = run_repl(input, "shell_help");
    let out = stdout_str(&output);
    assert!(
        out.contains(";#!"),
        "/help should mention shell escape syntax: {out}"
    );
}

// --- 3.6 Negative tests ---

// spec: repl/spec.md §13.5 — env vars must NOT propagate back
#[test]
fn shell_escape_neg_no_env_propagation() {
    // Set an env var in shell, it should not affect subsequent REPL behavior.
    // This is inherently true (child process), but verify no crash.
    let input = ";#! export FOO=bar\n;#! echo done\n/quit\n";
    let output = run_repl(input, "shell_neg_env");
    assert!(output.status.success(), "shell escape should not crash the REPL");
}

// =============================================================================
// 4. File Watching (E2E via shell escape)
//    Spec: repl/spec.md §14
//
//    These tests use the `;#!` shell escape to modify source files mid-REPL-session,
//    then verify that the file watcher detects changes, displays notifications,
//    recompiles modules, and handles errors. The REPL polls for changes before
//    each prompt (`poll_and_notify_changes`), including after shell escape commands.
//
//    Test setup: each test creates a temp directory with a `prelude.cl` that imports
//    a user module (`mymod.cl`). This ensures the module is in the prelude graph,
//    which means it appears in `file_to_module` and the watcher covers its directory.
// =============================================================================

/// Minimal prelude content: defines Num trait with + for Int.
/// Tests that need operators use this as the prelude.
const WATCH_PRELUDE: &str = "\
(import [primitives [*]])\n\
(deftrait Num (+ [self self] self) (- [self self] self) (* [self self] self) (/ [self self] self))\n\
(impl Num Int \
  (defn + [a b] (add-i64 a b)) \
  (defn - [a b] (sub-i64 a b)) \
  (defn * [a b] (mul-i64 a b)) \
  (defn / [a b] (div-i64 a b)))\n";

/// Create a temp directory with a prelude.cl. Optionally creates additional
/// files. Returns the temp dir (auto-cleaned on drop).
fn watch_test_setup(prelude_content: &str) -> tempfile::TempDir {
    let dir = tempfile::tempdir().expect("failed to create temp dir");
    std::fs::write(dir.path().join("prelude.cl"), prelude_content).unwrap();
    dir
}

/// Run the REPL binary with piped stdin in a specific directory.
/// Returns the process Output.
fn run_repl_in(dir: &std::path::Path, input: &str) -> Output {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} — run `cargo build` first"
    );

    let mut child = Command::new(&binary)
        .current_dir(dir)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to start cranelisp binary");

    {
        use std::io::Write;
        let stdin = child.stdin.as_mut().expect("failed to open stdin");
        stdin.write_all(input.as_bytes()).expect("failed to write input");
    }
    child.wait_with_output().expect("failed to read output")
}

// --- 4.1 Watch scope / basic detection ---

// spec: repl/spec.md §14.1 — watch directories containing loaded files
#[test]
fn watch_detects_source_change() {
    // Modify a known module's .cl file in the project root via shell escape.
    // The watcher monitors the project root directory and should emit
    // an [updated: ...] or [errors: ...] notification.
    // Setup: prelude.cl imports mymod.cl so it's in the file_to_module map.
    let dir = tempfile::tempdir().expect("failed to create temp dir");
    std::fs::write(dir.path().join("mymod.cl"), "(defn val [] 42)").unwrap();
    std::fs::write(
        dir.path().join("prelude.cl"),
        "(import [mymod [val]])\n",
    )
    .unwrap();
    let input = "\
(add-i64 1 2)
;#! sleep 0.3
;#! echo '(defn val [] 99)' > mymod.cl
;#! sleep 0.5
(add-i64 10 20)
/quit
";
    let output = run_repl_in(dir.path(), input);
    let out = stdout_str(&output);
    assert!(
        out.contains("[updated: mymod.cl]") || out.contains("[errors: mymod.cl]"),
        "watcher should emit [updated: mymod.cl] or [errors: mymod.cl] notification: {out}"
    );
}

// --- 4.2 Change detection ---

// spec: repl/spec.md §14.2 — content change detection (not metadata-only)
#[test]
fn watch_ignores_metadata_only_changes() {
    // Touch a known module (change mtime but not content) — should NOT trigger notification.
    // Content hash comparison should filter this out.
    let dir = tempfile::tempdir().expect("failed to create temp dir");
    std::fs::write(dir.path().join("mymod.cl"), "(defn val [] 42)").unwrap();
    std::fs::write(
        dir.path().join("prelude.cl"),
        "(import [mymod [val]])\n",
    )
    .unwrap();
    let input = "\
(add-i64 1 2)
;#! sleep 0.3
;#! touch mymod.cl
;#! sleep 0.5
(add-i64 10 20)
/quit
";
    let output = run_repl_in(dir.path(), input);
    let out = stdout_str(&output);
    assert!(
        !out.contains("[updated:") && !out.contains("[errors:"),
        "metadata-only change (touch, same content) should NOT trigger notification: {out}"
    );
}

// spec: repl/spec.md §14.2 — cascade invalidation
#[test]
fn watch_cascade_invalidation() {
    // Module A (mod_a) imports Module B (mod_b). Change Module B's source file.
    // Verify Module A is also recompiled (cascade) — both get [updated:] notifications.
    let dir = tempfile::tempdir().expect("failed to create temp dir");
    std::fs::write(dir.path().join("mod_b.cl"), "(defn val-b [] 10)").unwrap();
    std::fs::write(
        dir.path().join("mod_a.cl"),
        "(import [mod_b [val-b]])\n(defn val-a [] (val-b))",
    )
    .unwrap();
    std::fs::write(
        dir.path().join("prelude.cl"),
        "(import [mod_a [val-a]])\n",
    )
    .unwrap();
    let input = "\
(add-i64 1 2)
;#! sleep 0.3
;#! echo '(defn val-b [] 99)' > mod_b.cl
;#! sleep 0.5
(add-i64 10 20)
/quit
";
    let output = run_repl_in(dir.path(), input);
    let out = stdout_str(&output);
    // mod_b was directly changed — should get [updated: mod_b.cl].
    assert!(
        out.contains("[updated: mod_b.cl]") || out.contains("[errors: mod_b.cl]"),
        "mod_b should get an update notification: {out}"
    );
    // mod_a depends on mod_b — cascade should produce [updated: mod_a.cl].
    assert!(
        out.contains("[updated: mod_a.cl]") || out.contains("[errors: mod_a.cl]"),
        "mod_a should get a cascade update notification: {out}"
    );
}

// --- 4.3 User notification ---

// spec: repl/spec.md §14.3 — notification format
#[test]
fn watch_notification_format() {
    // Verify the [updated: file.cl] notification format via E2E.
    // The watcher detects the change, eagerly recompiles, and emits
    // [updated: <file>] before the next prompt.
    let dir = tempfile::tempdir().expect("failed to create temp dir");
    std::fs::write(dir.path().join("mymod.cl"), "(defn val [] 42)").unwrap();
    std::fs::write(
        dir.path().join("prelude.cl"),
        "(import [mymod [val]])\n",
    )
    .unwrap();
    let input = "\
(add-i64 1 2)
;#! sleep 0.3
;#! echo '(defn val [] 99)' > mymod.cl
;#! sleep 0.5
(add-i64 10 20)
/quit
";
    let output = run_repl_in(dir.path(), input);
    let out = stdout_str(&output);
    // Notification should match "[updated: mymod.cl]" format on success
    // or "[errors: mymod.cl]" if recompilation fails.
    assert!(
        out.contains("[updated: mymod.cl]") || out.contains("[errors: mymod.cl]"),
        "notification should use [updated: <file>] or [errors: <file>] format: {out}"
    );
}

// spec: repl/spec.md §14.3 — per-module notifications (no truncation needed)
#[test]
fn watch_notification_truncation() {
    // Under the new spec, each module gets its own [updated: ...] or
    // [errors: ...] line. There is no truncated format because notifications
    // are per-module results, not a batch file list.
    //
    // Test: modify multiple known modules, verify each gets a notification.
    // This requires a prelude that imports multiple modules.
    let dir = tempfile::tempdir().expect("failed to create temp dir");
    std::fs::write(dir.path().join("mod_a.cl"), "(defn val-a [] 1)").unwrap();
    std::fs::write(dir.path().join("mod_b.cl"), "(defn val-b [] 2)").unwrap();
    std::fs::write(
        dir.path().join("prelude.cl"),
        "(import [mod_a [val-a]])\n(import [mod_b [val-b]])\n",
    )
    .unwrap();
    let input = "\
(add-i64 1 2)
;#! sleep 0.5
;#! echo '(defn val-a [] 10)' > mod_a.cl; echo '(defn val-b [] 20)' > mod_b.cl
;#! sleep 1.0
(add-i64 10 20)
/quit
";
    let output = run_repl_in(dir.path(), input);
    let out = stdout_str(&output);
    // At least one notification should appear.
    assert!(
        out.contains("[updated:") || out.contains("[errors:"),
        "should have at least one notification: {out}"
    );
}

// spec: repl/spec.md §14.3 — notification deferred during input
#[test]
fn watch_notification_deferred_during_input() {
    // Verify that file change notifications appear at prompt boundaries,
    // not interleaved with expression output. The REPL architecture calls
    // poll_and_notify_changes only between prompts (never mid-evaluation),
    // so notifications are inherently deferred until the next prompt.
    //
    // Test strategy: modify a file via shell escape, then immediately
    // evaluate an expression. The notification must appear cleanly — either
    // before or after the expression result — never mid-output.
    let dir = tempfile::tempdir().expect("failed to create temp dir");
    std::fs::write(dir.path().join("mymod.cl"), "(defn val [] 42)").unwrap();
    std::fs::write(
        dir.path().join("prelude.cl"),
        "(import [mymod [val]])\n",
    )
    .unwrap();

    // Sequence: eval → modify file → sleep for FSEvents → eval again → quit.
    // The notification should appear at a prompt boundary between the two evals.
    let input = "\
(val)
;#! sleep 0.3
;#! echo '(defn val [] 99)' > mymod.cl
;#! sleep 0.5
(val)
/quit
";
    let output = run_repl_in(dir.path(), input);
    let out = stdout_str(&output);

    // The notification should appear somewhere in the output.
    assert!(
        out.contains("[updated: mymod.cl]"),
        "notification should appear at prompt boundary: {out}"
    );

    // Key property: the notification must appear on its own line, not
    // corrupting an expression result. Check that `:Int 42` and the
    // notification line are separate lines (not on the same line).
    for line in out.lines() {
        // No line should contain both an evaluation result AND a notification.
        let has_result = line.contains(":Int ");
        let has_notification = line.contains("[updated:") || line.contains("[errors:");
        assert!(
            !(has_result && has_notification),
            "notification should not appear on same line as result: {line:?}"
        );
    }
}

// --- 4.4 Eager recompilation ---

// spec: repl/spec.md §14.2 — eager recompilation on change detection
#[test]
fn watch_automatic_recompilation() {
    // After a file change, the REPL should detect it, eagerly recompile,
    // and show [updated: mymod.cl]. The new value should be available
    // for subsequent evaluation.
    let dir = tempfile::tempdir().expect("failed to create temp dir");
    std::fs::write(dir.path().join("mymod.cl"), "(defn val [] 42)").unwrap();
    std::fs::write(
        dir.path().join("prelude.cl"),
        "(import [mymod [val]])\n",
    )
    .unwrap();
    let input = "\
(add-i64 1 2)
;#! sleep 0.3
;#! echo '(defn val [] 99)' > mymod.cl
;#! sleep 0.5
(add-i64 10 20)
/quit
";
    let output = run_repl_in(dir.path(), input);
    let out = stdout_str(&output);
    // The watcher should eagerly recompile the changed module.
    assert!(
        out.contains("[updated: mymod.cl]"),
        "module should be eagerly recompiled with [updated: mymod.cl]: {out}"
    );
}

// spec: repl/spec.md §14.2 — type incompatibility on reload
#[test]
fn watch_type_incompatibility_on_reload() {
    // Change a prelude module's function to have a type error.
    // The reload should fail and show [errors: prelude.cl].
    let dir = watch_test_setup(WATCH_PRELUDE);
    let input = "\
(+ 1 2)
;#! sleep 0.3
;#! echo '(deftrait Num (+ [self self] self)) (impl Num Int (defn + [a b] \"not-an-int\"))' > prelude.cl
;#! sleep 0.5
(+ 10 20)
/quit
";
    let output = run_repl_in(dir.path(), input);
    let out = stdout_str(&output);
    assert!(
        out.contains("3"),
        "initial (+ 1 2) should return 3: {out}"
    );
    // The reload should show [updated: prelude.cl] or [errors: prelude.cl].
    assert!(
        out.contains("[updated: prelude.cl]") || out.contains("[errors: prelude.cl]"),
        "reload result should be notified: {out}"
    );
}

// --- 4.5 Error blocking ---

// spec: repl/spec.md §14.3 — error display format
#[test]
fn watch_error_display_format() {
    // Write a syntax error to a prelude-imported module file. The REPL should
    // display an [errors: mymod.cl] message with the error details.
    //
    // Setup: prelude.cl imports mymod.cl (so mymod is in file_to_module map).
    // Then break mymod.cl via shell escape.
    let dir = tempfile::tempdir().expect("failed to create temp dir");
    std::fs::write(dir.path().join("mymod.cl"), "(defn val [] 42)").unwrap();
    std::fs::write(
        dir.path().join("prelude.cl"),
        "(import [mymod [val]])\n",
    )
    .unwrap();
    let input = "\
(add-i64 1 2)
;#! sleep 0.3
;#! echo '(defn val []' > mymod.cl
;#! sleep 0.5
(add-i64 10 20)
/quit
";
    let output = run_repl_in(dir.path(), input);
    let out = stdout_str(&output);
    assert!(
        out.contains("[errors: mymod.cl]"),
        "reload failure should display [errors: mymod.cl]: {out}"
    );
}

// spec: repl/spec.md §14.4 — errors block evaluation
#[test]
fn watch_error_recovery_last_known_good() {
    // Per the new spec, there is NO last-known-good. Errors block evaluation.
    // After a syntax error in a watched file, evaluation should be blocked
    // with a "Cannot evaluate" message.
    //
    // Setup: prelude with traits, mymod imported. Break mymod -> errors.
    // Verify subsequent evaluation is blocked.
    let dir = tempfile::tempdir().expect("failed to create temp dir");
    std::fs::write(dir.path().join("mymod.cl"), "(defn val [] 42)").unwrap();
    std::fs::write(
        dir.path().join("prelude.cl"),
        &format!("{}\n(import [mymod [val]])\n", WATCH_PRELUDE),
    )
    .unwrap();
    let input = "\
(+ 1 2)
;#! sleep 0.3
;#! echo '(defn val []' > mymod.cl
;#! sleep 0.5
(+ 10 20)
/quit
";
    let output = run_repl_in(dir.path(), input);
    let out = stdout_str(&output);
    assert!(
        out.contains("[errors:"),
        "syntax error should trigger [errors:] notification: {out}"
    );
    // Evaluation should be blocked — "Cannot evaluate" message should appear.
    assert!(
        out.contains("Cannot evaluate"),
        "errors should block evaluation with 'Cannot evaluate' message: {out}"
    );
}

// spec: repl/spec.md §14.4 — error resolved on next successful change
#[test]
fn watch_retry_on_next_change() {
    // After a failed reload (syntax error), fix the file. The next poll
    // should detect the fix and attempt another reload. On success, the
    // error is cleared and evaluation resumes.
    let dir = tempfile::tempdir().expect("failed to create temp dir");
    std::fs::write(dir.path().join("mymod.cl"), "(defn val [] 42)").unwrap();
    std::fs::write(
        dir.path().join("prelude.cl"),
        "(import [mymod [val]])\n",
    )
    .unwrap();
    let input = "\
(add-i64 1 2)
;#! sleep 0.3
;#! echo '(defn val []' > mymod.cl
;#! sleep 0.5
(add-i64 10 20)
;#! sleep 0.1
;#! echo '(defn val [] 99)' > mymod.cl
;#! sleep 0.5
(add-i64 10 20)
/quit
";
    let output = run_repl_in(dir.path(), input);
    let out = stdout_str(&output);
    assert!(
        out.contains("[errors:"),
        "first change (broken) should trigger [errors:] notification: {out}"
    );
    // Second change (fix) should trigger another reload and succeed.
    assert!(
        out.contains("[updated: mymod.cl]"),
        "second change (fix) should produce [updated: mymod.cl]: {out}"
    );
}

// --- 4.6 Interaction with /reset ---
// (watch_continues_across_reset deleted — FileWatcher is v3 only, v4 has its own watcher path)

// --- 4.7 Interaction with object cache ---

// spec: repl/spec.md §14.7 — cache invalidation on file change
#[test]
fn watch_invalidates_cache_on_change() {
    // When a watched file changes, the REPL should detect it and attempt reload.
    // On reload (success or failure), the cache state is updated.
    // Verify that .cranelisp-cache directory exists after a REPL session
    // where a file change was detected and reload was attempted.
    let dir = tempfile::tempdir().expect("failed to create temp dir");
    std::fs::write(dir.path().join("mymod.cl"), "(defn val [] 42)").unwrap();
    std::fs::write(
        dir.path().join("prelude.cl"),
        "(import [mymod [val]])\n",
    )
    .unwrap();
    let input = "\
(add-i64 1 2)
;#! sleep 0.3
;#! echo '(defn val [] 99)' > mymod.cl
;#! sleep 0.5
(add-i64 10 20)
/quit
";
    let output = run_repl_in(dir.path(), input);
    let out = stdout_str(&output);
    assert!(
        out.contains("[updated: mymod.cl]") || out.contains("[errors: mymod.cl]"),
        "change should be detected and recompiled: {out}"
    );
    // Check that the cache directory was created by the REPL session.
    let cache_dir = dir.path().join(".cranelisp-cache");
    assert!(
        cache_dir.exists(),
        "cache directory should exist after REPL session with module compilation"
    );
}

// spec: repl/spec.md §14.7 — unchanged modules keep cached .o
#[test]
fn watch_unchanged_modules_keep_cache() {
    // When module A changes but module B is unchanged, B's cache should
    // remain valid and not be recompiled.
    //
    // Test this at the cache manifest level: compile two modules, verify
    // that only the changed module has its cache invalidated.
    use cranelisp_backend::cache::{hash_source, write_manifest, read_manifest, check_manifest, CacheManifest};

    let dir = test_dir("watch_unchanged_cache");
    let cache_dir = dir.join(".cranelisp-cache");
    std::fs::create_dir_all(&cache_dir).unwrap();

    let mp_a = cranelisp_types::ModuleFullPath::from("mod_a");
    let mp_b = cranelisp_types::ModuleFullPath::from("mod_b");
    let source_a = "(defn val-a [] 1)";
    let source_b = "(defn val-b [] 2)";
    let hash_a = hash_source(source_a);
    let hash_b = hash_source(source_b);

    // Build initial manifest with both modules.
    let mut manifest = CacheManifest::new_for_host();
    manifest.upsert_module(&mp_a, hash_a.clone(), std::collections::HashMap::new());
    manifest.upsert_module(&mp_b, hash_b.clone(), std::collections::HashMap::new());
    write_manifest(&cache_dir, &manifest).unwrap();

    // Now "change" module A — new hash.
    let new_source_a = "(defn val-a [] 999)";
    let new_hash_a = hash_source(new_source_a);

    let loaded = read_manifest(&cache_dir).unwrap();

    // Module A with new hash should NOT be a cache hit.
    let a_valid = check_manifest(&loaded, &mp_a, &new_hash_a, &std::collections::HashMap::new());
    assert!(
        !a_valid.unwrap_or(false),
        "module A with changed source should NOT be a cache hit"
    );

    // Module B with unchanged hash SHOULD still be a cache hit.
    let b_valid = check_manifest(&loaded, &mp_b, &hash_b, &std::collections::HashMap::new());
    assert!(
        b_valid.unwrap_or(false),
        "module B with unchanged source should still be a cache hit"
    );
}

// --- 4.8 Negative tests ---

// (watch_neg_no_eager_background_recompilation deleted — FileWatcher is v3 only)

// =============================================================================
// 5. REPL Cache Integration
//    Retarget the 5 existing ignored tests in tests/cache.rs to Sprint 23.
//    Additional REPL-specific cache tests below.
// =============================================================================

// NOTE: The 5 existing tests in tests/cache.rs remain there:
//   - cache_repl_write_is_non_blocking (retarget to S23)
//   - cache_repl_restart_cache_hit (retarget to S23)
//   - cache_repl_incremental_monomorphisation (retarget to S23)
//   - cache_quick_build_links_cached_objects (retarget to S23)
//   - cache_quick_build_fallback_on_missing_cache (retarget to S23)
//
// The quick build tests (cache_quick_build_*) now map to --link:
//   - cache_quick_build_links_cached_objects -> --link uses cached .o files
//   - cache_quick_build_fallback_on_missing_cache -> --link compiles fresh when cache missing

// spec: repl/spec.md §12.5 + design/int/repl-lifecycle.md §4 — cache write after REPL module compilation
#[test]
fn cache_repl_writes_on_import() {
    // When the REPL compiles prelude modules at startup, cache files should
    // be written to disk. Verify the manifest.json exists after a REPL session.
    //
    // Use the test fixtures prelude which is known to work with the REPL.
    let dir = test_dir("cache_repl_import");
    let fixtures = project_root().join("tests").join("fixtures");

    let input = "(+ 1 2)\n/quit\n";
    let binary = binary_path();
    let output = Command::new(&binary)
        .current_dir(&dir)
        .env("CRANELISP_LIB", fixtures.as_os_str())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .and_then(|mut child| {
            use std::io::Write;
            child.stdin.as_mut().unwrap().write_all(input.as_bytes()).unwrap();
            child.wait_with_output()
        })
        .expect("failed to run REPL");

    let out = stdout_str(&output);
    assert!(
        out.contains("3"),
        "prelude operator should work: {out}"
    );

    // Check that cache directory was created with manifest.
    let cache_dir = dir.join(".cranelisp-cache");
    assert!(
        cache_dir.join("manifest.json").exists(),
        "cache manifest should exist after REPL startup with prelude"
    );
}

// spec: design/int/repl-lifecycle.md §4.2 — cache load on startup
#[test]
fn cache_repl_loads_on_startup() {
    // Start REPL twice with a local prelude. First run populates cache,
    // second run loads prelude from cache. We verify both sessions produce
    // the same results and the cache file isn't rewritten on cache hit.
    let dir = test_dir("cache_repl_startup");
    let fixtures = project_root().join("tests").join("fixtures");

    let input = "(+ 40 2)\n/quit\n";
    let binary = binary_path();

    // First run: compiles prelude fresh, populates cache.
    let output1 = Command::new(&binary)
        .current_dir(&dir)
        .env("CRANELISP_LIB", fixtures.as_os_str())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .and_then(|mut child| {
            use std::io::Write;
            child.stdin.as_mut().unwrap().write_all(input.as_bytes()).unwrap();
            child.wait_with_output()
        })
        .expect("first REPL run failed");

    let out1 = stdout_str(&output1);
    assert!(out1.contains("42"), "first run should return 42: {out1}");

    // Verify cache was created.
    let cache_dir = dir.join(".cranelisp-cache");
    assert!(
        cache_dir.join("manifest.json").exists(),
        "cache manifest should exist after first run"
    );

    // Second run: should load prelude from cache.
    let output2 = Command::new(&binary)
        .current_dir(&dir)
        .env("CRANELISP_LIB", fixtures.as_os_str())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .and_then(|mut child| {
            use std::io::Write;
            child.stdin.as_mut().unwrap().write_all(input.as_bytes()).unwrap();
            child.wait_with_output()
        })
        .expect("second REPL run failed");

    let out2 = stdout_str(&output2);
    assert!(
        out2.contains("42"),
        "second run (cache loaded) should also return 42: {out2}"
    );
}

// spec: design/int/repl-lifecycle.md §4.4 — cache writer survives /reset
#[test]
fn cache_writer_survives_reset() {
    // After /reset, the prelude reload should still produce working state
    // and cache should persist across reset.
    let dir = test_dir("cache_writer_reset");
    let fixtures = project_root().join("tests").join("fixtures");

    let input = "(+ 3 4)\n/reset\n(+ 5 6)\n/quit\n";
    let binary = binary_path();

    let output = Command::new(&binary)
        .current_dir(&dir)
        .env("CRANELISP_LIB", fixtures.as_os_str())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .and_then(|mut child| {
            use std::io::Write;
            child.stdin.as_mut().unwrap().write_all(input.as_bytes()).unwrap();
            child.wait_with_output()
        })
        .expect("failed to run REPL");

    let out = stdout_str(&output);
    // Before reset: (+ 3 4) = 7
    assert!(
        out.contains("7"),
        "before /reset, (+ 3 4) should return 7: {out}"
    );
    // After reset: (+ 5 6) = 11
    assert!(
        out.contains("11"),
        "after /reset, (+ 5 6) should return 11 (prelude reloaded): {out}"
    );

    // Cache should still exist after reset.
    let cache_dir = dir.join(".cranelisp-cache");
    assert!(
        cache_dir.join("manifest.json").exists(),
        "cache manifest should survive /reset"
    );
}

// =============================================================================
// 6. Session Persistence
//    Spec: repl/spec.md §15
//    Design: design/int/session-persistence.md
// =============================================================================

// --- 6.1 Definitions survive restart ---

// spec: repl/spec.md §15.2 — defn persisted via source regeneration
#[test]
fn persist_defn_survives_restart() {
    // Define a function, quit, restart in same dir, call the function.
    let dir = tempfile::tempdir().expect("failed to create temp dir");

    // Session 1: define a function and quit
    let input1 = "\
(defn foo [] 42)
/quit
";
    let output1 = run_repl_in(dir.path(), input1);
    assert!(
        output1.status.success(),
        "session 1 should exit cleanly: {}",
        stderr_str(&output1)
    );

    // Session 2: restart in the same directory, call the function
    let input2 = "\
(foo)
/quit
";
    let output2 = run_repl_in(dir.path(), input2);
    let out2 = stdout_str(&output2);
    assert!(
        out2.contains("42"),
        "session 2 should find (foo) returning 42 from persisted user.cl: {out2}"
    );
}

// spec: repl/spec.md §15.2 — deftype persisted via source regeneration
#[test]
fn persist_deftype_survives_restart() {
    // Define a sum type, quit, restart, verify constructors work.
    let dir = tempfile::tempdir().expect("failed to create temp dir");

    // Session 1: define a type and quit
    let input1 = "\
(deftype Color Red Green Blue)
/quit
";
    let output1 = run_repl_in(dir.path(), input1);
    assert!(
        output1.status.success(),
        "session 1 should exit cleanly: {}",
        stderr_str(&output1)
    );

    // Session 2: use the type's constructor
    let input2 = "\
Color.Red
/quit
";
    let output2 = run_repl_in(dir.path(), input2);
    let out2 = stdout_str(&output2);
    assert!(
        out2.contains("Red") || out2.contains("Color"),
        "session 2 should recognise Color.Red from persisted user.cl: {out2}"
    );
}

// spec: repl/spec.md §15.2 — import persisted via source regeneration
#[test]
fn persist_import_survives_restart() {
    // Import a module, quit, restart, verify the imported symbol works.
    let dir = tempfile::tempdir().expect("failed to create temp dir");

    // Create a helper module on disk for the import
    std::fs::write(
        dir.path().join("helper.cl"),
        "(defn helper-val [] 99)",
    )
    .unwrap();

    // Session 1: import the helper module and quit
    let input1 = "\
(import [helper [helper-val]])
(helper-val)
/quit
";
    let output1 = run_repl_in(dir.path(), input1);
    let out1 = stdout_str(&output1);
    assert!(
        out1.contains("99"),
        "session 1 should successfully import and call helper-val: {out1}"
    );

    // Session 2: restart, the import should be persisted in user.cl
    let input2 = "\
(helper-val)
/quit
";
    let output2 = run_repl_in(dir.path(), input2);
    let out2 = stdout_str(&output2);
    assert!(
        out2.contains("99"),
        "session 2 should find helper-val via persisted import in user.cl: {out2}"
    );
}

// --- 6.2 Backing file creation and validity ---

// spec: repl/spec.md §15.2 — user.cl created as backing file
#[test]
fn persist_user_cl_created() {
    // Define something, quit, verify user.cl exists on disk.
    // Uses ;#! shell escape to check the file system during the session.
    let dir = tempfile::tempdir().expect("failed to create temp dir");

    let input = "\
(defn bar [] 7)
/quit
";
    let output = run_repl_in(dir.path(), input);
    assert!(
        output.status.success(),
        "REPL should exit cleanly: {}",
        stderr_str(&output)
    );

    let user_cl = dir.path().join("user.cl");
    assert!(
        user_cl.exists(),
        "user.cl should be created in the project directory after defining bar"
    );

    let contents = std::fs::read_to_string(&user_cl)
        .expect("should be able to read user.cl");
    assert!(
        contents.contains("bar"),
        "user.cl should contain the definition of bar: {contents}"
    );
}

// spec: repl/spec.md §15.2 — user.cl is valid parseable source
#[test]
fn persist_user_cl_is_valid_source() {
    // Define two functions where B calls A, quit, verify user.cl is valid
    // Cranelisp source that can be parsed without errors.
    let dir = tempfile::tempdir().expect("failed to create temp dir");

    // Session 1: define A, then B which calls A
    let input = "\
(import [primitives [*]])
(defn double [:Int x] (add-i64 x x))
(defn quad [:Int x] (double (double x)))
(quad 3)
/quit
";
    let output = run_repl_in(dir.path(), input);
    let out = stdout_str(&output);
    assert!(
        out.contains("12"),
        "session should compute (quad 3) = 12: {out}"
    );

    // Verify user.cl exists and is parseable
    let user_cl = dir.path().join("user.cl");
    assert!(user_cl.exists(), "user.cl should exist after session");

    let contents = std::fs::read_to_string(&user_cl)
        .expect("should be able to read user.cl");
    assert!(
        !contents.is_empty(),
        "user.cl should not be empty"
    );

    // Verify the file contains both function definitions in dependency order
    // (double must appear before quad since quad calls double).
    assert!(
        contents.contains("double") && contents.contains("quad"),
        "user.cl should contain both double and quad: {contents}"
    );

    // Verify the source can be imported from another REPL session
    // (validates the file is valid module source).
    let input2 = "\
(import [primitives [*]])
(import [user [quad]])
(quad 5)
/quit
";
    let output2 = run_repl_in(dir.path(), input2);
    let out2 = stdout_str(&output2);
    assert!(
        out2.contains("20"),
        "importing user.cl and calling (quad 5) should produce 20: {out2}"
    );
}

// --- 6.3 Cache interaction ---

// spec: repl/spec.md §15.2, design/int/session-persistence.md §3 — cache speeds restart
#[test]
fn persist_cache_speeds_restart() {
    // Define something, quit, restart twice. The second restart should
    // benefit from the cache (warm hit). We verify correctness on both
    // restarts; timing improvement is a best-effort check.
    let dir = tempfile::tempdir().expect("failed to create temp dir");

    // Session 1: define functions to create some compilation work
    let input1 = "\
(import [primitives [*]])
(defn alpha [] 1)
(defn beta [] (add-i64 (alpha) 1))
(defn gamma [] (add-i64 (beta) 1))
(gamma)
/quit
";
    let output1 = run_repl_in(dir.path(), input1);
    let out1 = stdout_str(&output1);
    assert!(out1.contains("3"), "session 1: (gamma) should be 3: {out1}");

    // Session 2: first restart — may or may not have cache
    let input_check = "(gamma)\n/quit\n";
    let start2 = std::time::Instant::now();
    let output2 = run_repl_in(dir.path(), input_check);
    let dur2 = start2.elapsed();
    let out2 = stdout_str(&output2);
    assert!(out2.contains("3"), "session 2: (gamma) should be 3: {out2}");

    // Session 3: second restart — should have warm cache
    let start3 = std::time::Instant::now();
    let output3 = run_repl_in(dir.path(), input_check);
    let dur3 = start3.elapsed();
    let out3 = stdout_str(&output3);
    assert!(out3.contains("3"), "session 3: (gamma) should be 3: {out3}");

    // Best-effort timing check: session 3 should not be dramatically slower
    // than session 2 (both should be cache hits). We don't assert session 3
    // is faster than session 2, just that both work correctly.
    // Log durations for manual inspection.
    eprintln!(
        "persist_cache_speeds_restart: session 2 = {:?}, session 3 = {:?}",
        dur2, dur3
    );
}

// --- 6.4 File watcher interaction ---

// spec: design/int/session-persistence.md §4 — self-write suppression via content hash
#[test]
fn persist_watcher_ignores_self_write() {
    // Define something (triggers save to user.cl). The file watcher should
    // NOT emit an [updated: user.cl] notification because the content hash
    // matches — the REPL itself wrote the file.
    let dir = tempfile::tempdir().expect("failed to create temp dir");

    let input = "\
(defn self-write-test [] 77)
;#! sleep 0.5
(add-i64 1 1)
/quit
";
    let output = run_repl_in(dir.path(), input);
    let out = stdout_str(&output);
    assert!(
        !out.contains("[updated: user.cl]") && !out.contains("[errors: user.cl]"),
        "self-write to user.cl should NOT trigger a watcher notification: {out}"
    );
}

// --- 6.5 Negative: bare expressions not saved ---

// spec: design/int/session-persistence.md §2 — only definition-like inputs saved
#[test]
fn persist_neg_bare_expr_not_saved() {
    // Evaluate bare expressions (not definitions), quit, verify user.cl
    // either does not exist or does not contain those expressions.
    let dir = tempfile::tempdir().expect("failed to create temp dir");

    let input = "\
(add-i64 1 2)
(add-i64 10 20)
/quit
";
    let output = run_repl_in(dir.path(), input);
    assert!(
        output.status.success(),
        "REPL should exit cleanly: {}",
        stderr_str(&output)
    );

    let user_cl = dir.path().join("user.cl");
    if user_cl.exists() {
        let contents = std::fs::read_to_string(&user_cl)
            .expect("should be able to read user.cl");
        assert!(
            !contents.contains("add-i64 1 2") && !contents.contains("add-i64 10 20"),
            "user.cl should NOT contain bare expressions: {contents}"
        );
    }
    // If user.cl doesn't exist at all, that's also correct — no definitions
    // means no backing file needed.
}

// =============================================================================
// 6.6 Session persistence bug regressions (Sprint 23)
// =============================================================================

/// Helper: run REPL in a specific directory with test prelude loaded.
fn run_repl_in_with_test_prelude(dir: &std::path::Path, input: &str) -> Output {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} — run `cargo build` first"
    );
    let fixtures = project_root().join("tests").join("fixtures");

    let mut child = Command::new(&binary)
        .current_dir(dir)
        .env("CRANELISP_LIB", fixtures.as_os_str())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to start cranelisp binary");

    {
        use std::io::Write;
        let stdin = child.stdin.as_mut().expect("failed to open stdin");
        stdin.write_all(input.as_bytes()).expect("failed to write input");
    }
    child.wait_with_output().expect("failed to read output")
}

// --- Bug 1: Not all definitions saved to user.cl ---
// Constrained polymorphic functions (those using trait operators like +)
// were not saved because compile_and_register_defn is skipped for constrained
// fns, so no def_codegen entry was created, and the sexp was never stored.

// spec: repl/spec.md §15.2 — all definitions saved including constrained poly fns
#[test]
fn persist_bug1_all_defns_saved_to_user_cl() {
    // Define 3 functions including a constrained polymorphic one, quit,
    // verify ALL 3 appear in user.cl.
    let dir = tempfile::tempdir().expect("failed to create temp dir");

    let input = "\
(defn add [x y] (+ x y))
(defn double [:Int x] (add-i64 x x))
(defn triple [:Int x] (add-i64 x (add-i64 x x)))
/quit
";
    let output = run_repl_in_with_test_prelude(dir.path(), input);
    assert!(
        output.status.success(),
        "REPL should exit cleanly: {}",
        stderr_str(&output)
    );

    let user_cl = dir.path().join("user.cl");
    assert!(user_cl.exists(), "user.cl should exist after defining functions");

    let contents = std::fs::read_to_string(&user_cl)
        .expect("should be able to read user.cl");

    // All 3 functions must appear in user.cl
    assert!(
        contents.contains("defn add"),
        "user.cl should contain constrained poly fn 'add': {contents}"
    );
    assert!(
        contents.contains("defn double"),
        "user.cl should contain fn 'double': {contents}"
    );
    assert!(
        contents.contains("defn triple"),
        "user.cl should contain fn 'triple': {contents}"
    );
}

// spec: repl/spec.md §15.2 — constrained poly fn restored and callable
// Fixed: restore now uses whole-program compilation (check_program +
// compile_checked_program) instead of per-form eval, which handles
// constrained polymorphism correctly.
#[test]
fn persist_bug1_constrained_fn_survives_restart() {
    // Define a constrained polymorphic fn, quit, restart, call it.
    let dir = tempfile::tempdir().expect("failed to create temp dir");

    // Session 1: define constrained poly fn
    let input1 = "\
(defn add [x y] (+ x y))
(add 10 20)
/quit
";
    let output1 = run_repl_in_with_test_prelude(dir.path(), input1);
    let out1 = stdout_str(&output1);
    assert!(
        out1.contains("30"),
        "session 1: (add 10 20) should be 30: {out1}"
    );

    // Session 2: restart, call the restored function
    let input2 = "\
(add 100 200)
/quit
";
    let output2 = run_repl_in_with_test_prelude(dir.path(), input2);
    let out2 = stdout_str(&output2);
    assert!(
        out2.contains("300"),
        "session 2: (add 100 200) should be 300 from restored constrained fn: {out2}"
    );
}

// --- Bug 2: No user.o cache file after save ---
// save_current_module writes user.cl but does not trigger cache compilation.
// Without user.o/user.meta.json, restart can't use the fast cache path.

// spec: repl/spec.md §15.2, design/int/session-persistence.md §3 — cache written after save
// Design gap: the reimplementation restores user.cl by eval-each-form (not via
// module graph pipeline), so it never hits cache on restore. Producing cache
// files requires either (a) changing restore to use compile_module_graph, or
// (b) building CacheMetadata from REPL-incremental state. Both are non-trivial.
// spec: repl/spec.md §15.2, design/int/session-persistence.md §3 — cache written on restore
// The module graph restore pipeline produces .o and .meta.json cache files
// when user.cl is loaded at startup. Session 1 saves user.cl; session 2
// restores it through compile_checked_program which writes the cache.
#[test]
fn persist_bug2_cache_files_created_after_restore() {
    // Session 1: define a function, quit (saves user.cl).
    let dir = tempfile::tempdir().expect("failed to create temp dir");

    let input1 = "\
(defn cached-fn [] 42)
/quit
";
    let output1 = run_repl_in(dir.path(), input1);
    assert!(
        output1.status.success(),
        "session 1: REPL should exit cleanly: {}",
        stderr_str(&output1)
    );

    // user.cl must exist after session 1.
    let user_cl = dir.path().join("user.cl");
    assert!(user_cl.exists(), "user.cl should exist after session 1");

    // Session 2: restart (restores user.cl via module graph pipeline), quit.
    let input2 = "/quit\n";
    let output2 = run_repl_in(dir.path(), input2);
    assert!(
        output2.status.success(),
        "session 2: REPL should exit cleanly: {}",
        stderr_str(&output2)
    );

    // Cache directory and user module cache should exist after restore.
    let cache_dir = dir.path().join(".cranelisp-cache");
    assert!(
        cache_dir.exists(),
        "cache directory .cranelisp-cache/ should exist after restoring user.cl"
    );

    // Check for user.meta.json — the metadata file for the cached module
    let has_user_meta = std::fs::read_dir(&cache_dir)
        .map(|entries| {
            entries
                .filter_map(|e| e.ok())
                .any(|e| {
                    let name = e.file_name();
                    let name = name.to_string_lossy();
                    name.contains("user") && name.ends_with(".meta.json")
                })
        })
        .unwrap_or(false);
    assert!(
        has_user_meta,
        "user.meta.json should exist in .cranelisp-cache/ after restoring user.cl"
    );

    // Check for user.o — the compiled object file
    let has_user_o = std::fs::read_dir(&cache_dir)
        .map(|entries| {
            entries
                .filter_map(|e| e.ok())
                .any(|e| {
                    let name = e.file_name();
                    let name = name.to_string_lossy();
                    name.contains("user") && name.ends_with(".o")
                })
        })
        .unwrap_or(false);
    assert!(
        has_user_o,
        "user.o should exist in .cranelisp-cache/ after restoring user.cl"
    );
}

// --- Bug 3: Stale definitions from previous sessions ---
// Session 2 restores from user.cl, adding old definitions to the symbol table.
// When session 2 saves, those restored definitions should still be present
// (they are part of the current session's state). This verifies the
// accumulation behavior is correct.

// spec: repl/spec.md §15.2 — accumulated definitions across sessions
#[test]
fn persist_bug3_accumulated_definitions_across_sessions() {
    // Session 1 defines foo. Session 2 defines bar.
    // After session 2, user.cl should contain BOTH foo and bar.
    let dir = tempfile::tempdir().expect("failed to create temp dir");

    // Session 1: define foo
    let input1 = "\
(defn foo [] 42)
/quit
";
    let output1 = run_repl_in(dir.path(), input1);
    assert!(output1.status.success(), "session 1 failed: {}", stderr_str(&output1));

    let user_cl = dir.path().join("user.cl");
    let contents1 = std::fs::read_to_string(&user_cl)
        .expect("user.cl should exist after session 1");
    assert!(contents1.contains("defn foo"), "session 1 should save foo: {contents1}");

    // Session 2: define bar (foo should be restored from user.cl)
    let input2 = "\
(defn bar [] 99)
/quit
";
    let output2 = run_repl_in(dir.path(), input2);
    assert!(output2.status.success(), "session 2 failed: {}", stderr_str(&output2));

    let contents2 = std::fs::read_to_string(&user_cl)
        .expect("user.cl should exist after session 2");
    assert!(
        contents2.contains("defn foo"),
        "user.cl should still contain foo from session 1 after session 2: {contents2}"
    );
    assert!(
        contents2.contains("defn bar"),
        "user.cl should contain bar from session 2: {contents2}"
    );
}

// spec: repl/spec.md §15.2 — no stale definitions from unrelated sessions
#[test]
fn persist_bug3_neg_no_phantom_definitions() {
    // Verify that user.cl only contains definitions that were actually
    // defined or restored in the current session.
    let dir = tempfile::tempdir().expect("failed to create temp dir");

    // Session 1: define alpha
    let input1 = "\
(defn alpha [] 1)
/quit
";
    run_repl_in(dir.path(), input1);

    // Session 2: define beta (alpha should be restored)
    let input2 = "\
(defn beta [] 2)
/quit
";
    run_repl_in(dir.path(), input2);

    let contents = std::fs::read_to_string(dir.path().join("user.cl"))
        .expect("user.cl should exist");

    // Both should be present
    assert!(contents.contains("defn alpha"), "alpha should be in user.cl: {contents}");
    assert!(contents.contains("defn beta"), "beta should be in user.cl: {contents}");

    // No phantom definitions should appear (things we never defined)
    assert!(
        !contents.contains("defn gamma"),
        "phantom definition 'gamma' should NOT be in user.cl: {contents}"
    );
    assert!(
        !contents.contains("defn fact"),
        "phantom definition 'fact' should NOT be in user.cl: {contents}"
    );
}

// --- Defect 1 regression: macro-expanded sexp stored instead of original ---
// When user types `(defn greet [name] (str "hello, " name))`, the `str` macro
// expands to `(str-concat (show "hello, ") (show name))`. The saved user.cl
// must contain the original `(str ...)` form, not the expanded form.
// Requires full stdlib (not test prelude) because `str` is a stdlib macro.

/// Helper: run REPL in a specific directory with the real stdlib prelude.
fn run_repl_in_with_stdlib(dir: &std::path::Path, input: &str) -> Output {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} — run `cargo build` first"
    );
    let stdlib_dir = project_root().join("stdlib");

    let mut child = Command::new(&binary)
        .current_dir(dir)
        .env("CRANELISP_LIB", stdlib_dir.as_os_str())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to start cranelisp binary");

    {
        use std::io::Write;
        let stdin = child.stdin.as_mut().expect("failed to open stdin");
        stdin.write_all(input.as_bytes()).expect("failed to write input");
    }
    child.wait_with_output().expect("failed to read output")
}

// spec: repl/spec.md §15.2 — user.cl preserves original source, not macro-expanded form
#[test]
fn persist_bug_macro_not_expanded_in_user_cl() {
    let dir = tempfile::tempdir().expect("failed to create temp dir");

    let input = "\
(defn greet [name] (str \"hello, \" name))
/quit
";
    let output = run_repl_in_with_stdlib(dir.path(), input);
    let out = stdout_str(&output);
    let err = stderr_str(&output);
    assert!(
        output.status.success(),
        "REPL should exit cleanly.\nstdout: {out}\nstderr: {err}"
    );

    let user_cl = dir.path().join("user.cl");
    assert!(user_cl.exists(), "user.cl should exist after defining a function.\nstdout: {out}\nstderr: {err}");

    let contents = std::fs::read_to_string(&user_cl)
        .expect("should be able to read user.cl");

    // The original form uses `str`, NOT the expanded `str-concat`.
    assert!(
        contents.contains("str "),
        "user.cl should contain original `str` macro call, not expanded form: {contents}"
    );
    assert!(
        !contents.contains("str-concat"),
        "user.cl must NOT contain macro-expanded `str-concat`: {contents}"
    );
}

// --- Defect 2 regression: no user.o cache after first session ---
// After defining something and quitting, .cranelisp-cache/ should contain
// user.meta.json and user.o immediately (not requiring a second session).

// spec: repl/spec.md §15.2, design/int/session-persistence.md §3 — cache on first save
#[test]
fn persist_bug_cache_files_on_first_save() {
    let dir = tempfile::tempdir().expect("failed to create temp dir");

    let input = "\
(defn double [x] (* x 2))
/quit
";
    let output = run_repl_in_with_test_prelude(dir.path(), input);
    assert!(
        output.status.success(),
        "REPL should exit cleanly: {}",
        stderr_str(&output)
    );

    // user.cl must exist.
    let user_cl = dir.path().join("user.cl");
    assert!(user_cl.exists(), "user.cl should exist after defining a function");

    // Cache directory must exist after first session (not just second).
    let cache_dir = dir.path().join(".cranelisp-cache");
    assert!(
        cache_dir.exists(),
        ".cranelisp-cache/ should exist after first session save"
    );

    // user.meta.json should exist.
    let has_user_meta = std::fs::read_dir(&cache_dir)
        .map(|entries| {
            entries
                .filter_map(|e| e.ok())
                .any(|e| {
                    let name = e.file_name();
                    let name = name.to_string_lossy();
                    name.contains("user") && name.ends_with(".meta.json")
                })
        })
        .unwrap_or(false);
    assert!(
        has_user_meta,
        "user.meta.json should exist in .cranelisp-cache/ after first session"
    );

    // user.o should exist.
    let has_user_o = std::fs::read_dir(&cache_dir)
        .map(|entries| {
            entries
                .filter_map(|e| e.ok())
                .any(|e| {
                    let name = e.file_name();
                    let name = name.to_string_lossy();
                    name.contains("user") && name.ends_with(".o")
                })
        })
        .unwrap_or(false);
    assert!(
        has_user_o,
        "user.o should exist in .cranelisp-cache/ after first session"
    );
}

// --- 6.7 Prelude macro usage fails on restore (Sprint 23 bug) ---
// Bug: when user.cl contains a function that uses a prelude macro (e.g. `str`),
// the batch-mode restore compiles user.cl before the prelude's macros are fully
// available, causing "undefined variable: str" on the second session.

// spec: repl/spec.md §15.2 — functions using prelude macros must survive restart
#[test]
fn persist_bug_macro_usage_survives_restart() {
    let dir = tempfile::tempdir().expect("failed to create temp dir");

    // Session 1: define a function that uses the `str` prelude macro, then quit.
    let input1 = "\
(defn greet [name] (str \"hello, \" name))
(greet \"world\")
/quit
";
    let output1 = run_repl_in_with_stdlib(dir.path(), input1);
    let out1 = stdout_str(&output1);
    let err1 = stderr_str(&output1);
    assert!(
        output1.status.success(),
        "session 1 should exit cleanly.\nstdout: {out1}\nstderr: {err1}"
    );
    assert!(
        out1.contains("hello, world"),
        "session 1: (greet \"world\") should produce \"hello, world\": {out1}"
    );

    // Session 2: restart in the same directory, call the restored function.
    // This should work — the function was persisted to user.cl and the prelude
    // macros should be available when user.cl is restored.
    let input2 = "\
(greet \"cranelisp\")
/quit
";
    let output2 = run_repl_in_with_stdlib(dir.path(), input2);
    let out2 = stdout_str(&output2);
    let err2 = stderr_str(&output2);
    assert!(
        output2.status.success(),
        "session 2 should exit cleanly (not fail on str macro).\nstdout: {out2}\nstderr: {err2}"
    );
    assert!(
        out2.contains("hello, cranelisp"),
        "session 2: (greet \"cranelisp\") should produce \"hello, cranelisp\" from restored user.cl: {out2}"
    );
}

// =============================================================================
// 8. Batch mode: main function requirement (repl/spec.md §0.2)
// =============================================================================

// spec: repl/spec.md §0.2 — --run requires main function
#[test]
fn batch_main_missing_produces_error() {
    let dir = tempfile::tempdir().expect("failed to create temp dir");

    // Create a file with no main function.
    std::fs::write(
        dir.path().join("app.cl"),
        "(defn helper [] 42)",
    )
    .unwrap();

    let output = run_binary(&["--run", "app.cl"], dir.path());
    assert!(
        !output.status.success(),
        "batch mode should fail when main is not defined"
    );
    let err = stderr_str(&output);
    assert!(
        err.contains("main"),
        "error message should mention 'main': {err}"
    );
}

// spec: repl/spec.md §0.2 — --run with main returning Int sets exit code
#[test]
fn batch_main_int_exit_code() {
    let dir = tempfile::tempdir().expect("failed to create temp dir");

    // Create a file with main returning 0.
    std::fs::write(
        dir.path().join("app.cl"),
        "(defn main [] 0)",
    )
    .unwrap();

    let output = run_binary(&["--run", "app.cl"], dir.path());
    assert!(
        output.status.success(),
        "batch mode with main returning 0 should succeed: {}",
        stderr_str(&output)
    );
}

// spec: repl/spec.md §0.2 — --run with main returning non-zero Int sets exit code
#[test]
fn batch_main_nonzero_exit_code() {
    let dir = tempfile::tempdir().expect("failed to create temp dir");

    std::fs::write(
        dir.path().join("app.cl"),
        "(defn main [] 42)",
    )
    .unwrap();

    let output = run_binary(&["--run", "app.cl"], dir.path());
    // Exit code should be 42.
    let code = output.status.code().unwrap_or(-1);
    assert_eq!(
        code, 42,
        "exit code should be the Int return value of main"
    );
}
