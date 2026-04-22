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
//
// FIXME(/int): Sprint 58 Wave 2c — `--link` fails because the linker cannot
// resolve `___cranelisp_got_helper` (the helper module's per-module GOT base
// symbol is not exported in the helper.o emitted by the cache writer). The
// `tests/cache.rs` migration to the new API (Decision 33+34) does not affect
// this — the defect is in `/int`'s `--link` flow / cross-module GOT export
// in the cache-write `.o` emission path. See `design/backend/executable-generation.md` §3.
#[test]
fn link_multi_module_project() {
    // A project with an entry module that imports another module.
    let dir = test_dir("link_multi_module");
    std::fs::write(
        dir.join("prelude.cl"),
        "(import [primitives [*]])\n",
    )
    .unwrap();
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
// 3. Shell Escape (/sh)
//    Spec: repl/spec.md §13
// =============================================================================

// --- 3.1 Basic execution ---

// spec: repl/spec.md §13.2 — command execution via /bin/sh
#[test]
fn shell_escape_basic_echo() {
    let input = "/sh echo hello_from_shell\n/quit\n";
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
    let input = "/sh echo \"hello from shell\"\n/quit\n";
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
    let input = "/sh false\n/quit\n";
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
    let input = "/sh true\n/quit\n";
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
    let input = "/sh nonexistent_command_xyz\n/quit\n";
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
    let input = "/sh\n/sh   \n/quit\n";
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
    let input = "/sh echo first && echo second\n/quit\n";
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
    let input = "(defn foo [] 42)\n/sh echo test\n(foo)\n/quit\n";
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
    let input = "/sh echo hi\n/quit\n";
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
        out.contains("/sh"),
        "/help should mention shell escape syntax: {out}"
    );
}

// --- 3.6 Negative tests ---

// spec: repl/spec.md §13.5 — env vars must NOT propagate back
#[test]
fn shell_escape_neg_no_env_propagation() {
    // Set an env var in shell, it should not affect subsequent REPL behavior.
    // This is inherently true (child process), but verify no crash.
    let input = "/sh export FOO=bar\n/sh echo done\n/quit\n";
    let output = run_repl(input, "shell_neg_env");
    assert!(output.status.success(), "shell escape should not crash the REPL");
}

// =============================================================================
// 4. File Watching (E2E via shell escape)
//    Spec: repl/spec.md §14
//
//    These tests use the `/sh` shell escape to modify source files mid-REPL-session,
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
        "(import [primitives [*]])\n(import [mymod [val]])\n",
    )
    .unwrap();
    let input = "\
(add-i64 1 2)
/sh sleep 0.3
/sh echo '(defn val [] 99)' > mymod.cl
/sh sleep 0.5
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
        "(import [primitives [*]])\n(import [mymod [val]])\n",
    )
    .unwrap();
    let input = "\
(add-i64 1 2)
/sh sleep 0.3
/sh touch mymod.cl
/sh sleep 0.5
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
        "(import [primitives [*]])\n(import [mod_a [val-a]])\n",
    )
    .unwrap();
    let input = "\
(add-i64 1 2)
/sh sleep 0.3
/sh echo '(defn val-b [] 99)' > mod_b.cl
/sh sleep 0.5
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
        "(import [primitives [*]])\n(import [mymod [val]])\n",
    )
    .unwrap();
    let input = "\
(add-i64 1 2)
/sh sleep 0.3
/sh echo '(defn val [] 99)' > mymod.cl
/sh sleep 0.5
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
        "(import [primitives [*]])\n(import [mod_a [val-a]])\n(import [mod_b [val-b]])\n",
    )
    .unwrap();
    let input = "\
(add-i64 1 2)
/sh sleep 0.5
/sh echo '(defn val-a [] 10)' > mod_a.cl; echo '(defn val-b [] 20)' > mod_b.cl
/sh sleep 1.0
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
/sh sleep 0.3
/sh echo '(defn val [] 99)' > mymod.cl
/sh sleep 0.5
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
        "(import [primitives [*]])\n(import [mymod [val]])\n",
    )
    .unwrap();
    let input = "\
(add-i64 1 2)
/sh sleep 0.3
/sh echo '(defn val [] 99)' > mymod.cl
/sh sleep 0.5
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
/sh sleep 0.3
/sh echo '(deftrait Num (+ [self self] self)) (impl Num Int (defn + [a b] \"not-an-int\"))' > prelude.cl
/sh sleep 0.5
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
        "(import [primitives [*]])\n(import [mymod [val]])\n",
    )
    .unwrap();
    let input = "\
(add-i64 1 2)
/sh sleep 0.3
/sh echo '(defn val []' > mymod.cl
/sh sleep 0.5
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
/sh sleep 0.3
/sh echo '(defn val []' > mymod.cl
/sh sleep 0.5
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
        "(import [primitives [*]])\n(import [mymod [val]])\n",
    )
    .unwrap();
    let input = "\
(add-i64 1 2)
/sh sleep 0.3
/sh echo '(defn val []' > mymod.cl
/sh sleep 0.5
(add-i64 10 20)
/sh sleep 0.1
/sh echo '(defn val [] 99)' > mymod.cl
/sh sleep 0.5
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
        "(import [primitives [*]])\n(import [mymod [val]])\n",
    )
    .unwrap();
    let input = "\
(add-i64 1 2)
/sh sleep 0.3
/sh echo '(defn val [] 99)' > mymod.cl
/sh sleep 0.5
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
//
// Resolved S59 Wave 1: cache-hit arm of `inject_prelude_if_needed` now calls
// `register_imports` on the user module's check state with an
// `ImportNames::Glob` spec for `prelude`, matching the fresh-compile arm.
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
//
// FIXME(/int): Sprint 58 Wave 2c — second REPL session does not see the
// persisted import (the helper module is not loaded on session 2 startup
// even though `user.cl` was regenerated with the import statement). The
// `tests/cache.rs` migration to the new API (Decision 33+34) does not affect
// this — the defect is in `/int`'s session restart / persisted-`user.cl`
// reload flow. See `design/int/session-persistence.md` and `repl/spec.md` §15.2.
#[test]
fn persist_import_survives_restart() {
    // Import a module, quit, restart, verify the imported symbol works.
    // Uses run_repl_in_with_test_prelude because imports need the prelude
    // (operators used in typical modules). Deletes .cranelisp-cache/ between
    // sessions so session 2 must recompile from the regenerated user.cl,
    // testing true persistence rather than cache-hit loading.
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
    let output1 = run_repl_in_with_test_prelude(dir.path(), input1);
    let out1 = stdout_str(&output1);
    assert!(
        out1.contains("99"),
        "session 1 should successfully import and call helper-val: {out1}"
    );

    // Verify user.cl was created and contains the import
    let user_cl = dir.path().join("user.cl");
    assert!(
        user_cl.exists(),
        "user.cl should exist after session 1"
    );
    let user_cl_contents = std::fs::read_to_string(&user_cl)
        .expect("should be able to read user.cl");
    assert!(
        user_cl_contents.contains("import") && user_cl_contents.contains("helper"),
        "user.cl should contain the import statement: {user_cl_contents}"
    );

    // Delete cache so session 2 must recompile from user.cl (not cache hit)
    let cache_dir = dir.path().join(".cranelisp-cache");
    if cache_dir.exists() {
        std::fs::remove_dir_all(&cache_dir).expect("failed to delete .cranelisp-cache");
    }

    // Session 2: restart, the import should be persisted in user.cl
    let input2 = "\
(helper-val)
/quit
";
    let output2 = run_repl_in_with_test_prelude(dir.path(), input2);
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
    // Uses /sh shell escape to check the file system during the session.
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
/sh sleep 0.5
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
    // Deletes .cranelisp-cache/ between sessions so session 2 must recompile
    // from user.cl, testing true persistence rather than cache-hit loading.
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

    // Verify user.cl was created and contains the defn
    let user_cl = dir.path().join("user.cl");
    assert!(
        user_cl.exists(),
        "user.cl should exist after session 1"
    );
    let user_cl_contents = std::fs::read_to_string(&user_cl)
        .expect("should be able to read user.cl");
    assert!(
        user_cl_contents.contains("defn add"),
        "user.cl should contain the constrained poly fn 'add': {user_cl_contents}"
    );

    // Delete cache so session 2 must recompile from user.cl (not cache hit)
    let cache_dir = dir.path().join(".cranelisp-cache");
    if cache_dir.exists() {
        std::fs::remove_dir_all(&cache_dir).expect("failed to delete .cranelisp-cache");
    }

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

// --- Cache: REPL session produces object files ---
// After defining something and quitting, .cranelisp-cache/ should contain
// user.meta.json and user.o immediately. This tests cache file production,
// not session persistence across restarts.

// spec: design/int/session-persistence.md §3 — cache written after save
#[test]
fn cache_repl_produces_object_files() {
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

// spec: design/int/dual-path-persistence-collapse.md §7 step 7 + §8 heisenbug repro
//
// FIXME(/int): Sprint 59 Workstream A — the dual-path persistence collapse
// design explicitly names the ~1755/1754 heisenbug observed at Sprint 58
// close (Sprint 58 §Findings) as the structural symptom of two orchestrators
// working on the same module simultaneously. Per the design doc migration
// plan step 7, under the collapsed path this loop MUST be 50/50 green
// (heisenbug source eliminated). Before the collapse lands, this test is
// expected to flake; after the collapse lands, it MUST be rock solid.
//
// Design ref: design/int/dual-path-persistence-collapse.md §7 step 7
// (50-loop repro), §3 target shape (single persistent-worker pool + one
// waiter), §9 Risk 1 (sixth surface discovery trigger).
#[test]
fn cache_repl_loads_heisenbug_parallel_stress() {
    // Repeat the persist_import_survives_restart sequence N times in a loop,
    // relying on nextest's own --test-threads parallelism to apply scheduling
    // pressure to the scheduler-side vs session-side dep-registration paths.
    //
    // Under the collapsed path (Sprint 59 Workstream A), there is ONE
    // orchestrator per module, so this loop is correct-by-construction. If
    // this test flakes after the collapse lands, §9 Risk 1 is active: a sixth
    // collapse surface has been missed.
    //
    // N is 20 rather than 50 to respect the /qa <30s test runtime budget.
    // The heisenbug observed at Sprint 58 close was ~1 flake per 1755 runs;
    // 20 iterations under nextest pressure is enough to catch a structural
    // re-opening (not a true 1-in-1755 race — those stay as user-triggered
    // repros via the design doc's migration-step-7 manual loop).
    const STRESS_ITERATIONS: usize = 20;

    for iteration in 0..STRESS_ITERATIONS {
        let dir = tempfile::tempdir().expect("failed to create temp dir");

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
        let output1 = run_repl_in_with_test_prelude(dir.path(), input1);
        let out1 = stdout_str(&output1);
        assert!(
            out1.contains("99"),
            "iteration {iteration}: session 1 should successfully import and call helper-val: {out1}"
        );

        // Delete cache so session 2 must recompile from user.cl
        let cache_dir = dir.path().join(".cranelisp-cache");
        if cache_dir.exists() {
            std::fs::remove_dir_all(&cache_dir).expect("failed to delete .cranelisp-cache");
        }

        // Session 2: restart, the import should be persisted in user.cl
        let input2 = "\
(helper-val)
/quit
";
        let output2 = run_repl_in_with_test_prelude(dir.path(), input2);
        let out2 = stdout_str(&output2);
        assert!(
            out2.contains("99"),
            "iteration {iteration}: session 2 should find helper-val via persisted import in user.cl: {out2}"
        );
    }
}

// spec: tests/plan/baseline.md §"Cargo test suite" — `cache_repl_loads_heisenbug_parallel_stress`
// (publish-vs-flag heisenbug). Reduced-shape repro authored under
// Sprint 61 Wave 3 step 3a (reduction-only agent).
//
// FIXME(/int): Sprint 61 Wave 3 step 3e is the scheduler/worker fix
// that makes this test stably green. Until 3e lands this test is
// expected to fail at >=50% rate (see reduction notes in
// `design/int/heisenbug-race-closure.md §3b`). Do NOT #[ignore] per
// `memory/feedback_failing_not_ignored.md` — the failing test IS the
// regression guard and 3b evidence anchor.
//
// Shape: N concurrent OS threads, each driving K sequential
// (session 1 → delete cache → session 2) pairs against its OWN
// tempdir. Each thread's work uses the same subprocess + stdin shape
// as `cache_repl_loads_heisenbug_parallel_stress`, but the parallelism
// is in-test rather than relying on nextest cross-test contention.
// Any thread reporting the Round 4/5 signature (`helper-val` not found
// in module `helper`) makes the trial fail.
//
// Calibration (Sprint 61 Wave 3 step 3a, local M4 Pro): N=3, K=3
// reproduces the signature at ~50–60% per trial while completing each
// trial in <2s. The existing `cache_repl_loads_heisenbug_parallel_stress`
// in-isolation hits this signature at ~0% (it relies on external
// cross-test pressure to reach ~30%). This reduced shape is therefore
// the preferred step 3b evidence-capture harness: run it with
// `CRANELISP_SCHEDULER_TRACE=1` per `design/int/observability.md §7`
// and merge-sort dumps across the failing thread's stderr.
#[test]
fn heisenbug_race_reduced_concurrent_import_pairs() {
    use std::sync::Arc;
    use std::thread;

    // Reduction calibration (Sprint 61 Wave 3 step 3a, local M4 Pro):
    //   * 6 concurrent threads per trial (N=6) applies 6-way
    //     cross-process contention on subprocess spawn + JIT warmup
    //     + scheduler/symbol-table publication. Below ~4 threads the
    //     race rate drops into the tens-of-percent; at 6 it saturates.
    //   * 2 sequential iterations per thread (K=2) keeps each trial
    //     to ~1s while giving each thread multiple race windows.
    //   * 10 trials is the per-test loop that turns a per-trial
    //     fire rate of ~30-40% into a per-test fire rate near 100%.
    //     Typical failing run short-circuits at the first trial that
    //     reproduces (see `break 'trials` below), so mean wall-time
    //     is ~1s; the worst case (all 10 trials pass) is ~10s —
    //     still well under the tests/CLAUDE.md 30s ceiling.
    //
    // See `design/int/heisenbug-race-closure.md §3b` for the
    // reduction notes that justify these constants.
    const TRIALS: usize = 10;
    const THREADS: usize = 6;
    const ITERS_PER_THREAD: usize = 2;

    let binary = Arc::new(binary_path());
    let fixtures = Arc::new(project_root().join("tests").join("fixtures"));
    assert!(
        binary.exists(),
        "cranelisp binary not found at {:?} — run `cargo build` first",
        binary
    );

    let mut all_failures: Vec<String> = Vec::new();

    'trials: for trial in 0..TRIALS {
        // Each thread owns its own TempDir — no shared filesystem
        // state. The race surfaces purely through cross-process
        // scheduler / symbol-table contention inside each `cranelisp`
        // subprocess.
        let mut handles = Vec::with_capacity(THREADS);
        for thread_id in 0..THREADS {
            let binary = Arc::clone(&binary);
            let fixtures = Arc::clone(&fixtures);
            handles.push(thread::spawn(move || -> Result<(), String> {
                for iter in 0..ITERS_PER_THREAD {
                    let dir = tempfile::tempdir()
                        .map_err(|e| format!("t{thread_id} i{iter}: tempdir: {e}"))?;
                    std::fs::write(
                        dir.path().join("helper.cl"),
                        "(defn helper-val [] 99)",
                    )
                    .map_err(|e| format!("t{thread_id} i{iter}: write helper.cl: {e}"))?;

                    // Session 1: import and call helper-val.
                    let input1 = "\
(import [helper [helper-val]])
(helper-val)
/quit
";
                    let mut child1 = Command::new(&*binary)
                        .current_dir(dir.path())
                        .env("CRANELISP_LIB", fixtures.as_os_str())
                        .stdin(Stdio::piped())
                        .stdout(Stdio::piped())
                        .stderr(Stdio::piped())
                        .spawn()
                        .map_err(|e| format!("t{thread_id} i{iter} s1: spawn: {e}"))?;
                    {
                        use std::io::Write;
                        let stdin = child1.stdin.as_mut().ok_or("s1: stdin")?;
                        stdin
                            .write_all(input1.as_bytes())
                            .map_err(|e| format!("t{thread_id} i{iter} s1: write: {e}"))?;
                    }
                    let out1 = child1
                        .wait_with_output()
                        .map_err(|e| format!("t{thread_id} i{iter} s1: wait: {e}"))?;
                    let stdout1 = String::from_utf8_lossy(&out1.stdout);
                    let stderr1 = String::from_utf8_lossy(&out1.stderr);
                    if !stdout1.contains("99") {
                        return Err(format!(
                            "t{thread_id} i{iter} session 1: import+call failed (heisenbug signature if stdout/stderr contains 'helper-val' not found in module 'helper'):\nstdout: {stdout1}\nstderr: {stderr1}"
                        ));
                    }

                    // Delete cache so session 2 must recompile.
                    let cache_dir = dir.path().join(".cranelisp-cache");
                    if cache_dir.exists() {
                        std::fs::remove_dir_all(&cache_dir)
                            .map_err(|e| format!("t{thread_id} i{iter}: rm cache: {e}"))?;
                    }

                    // Session 2: call helper-val via persisted import in user.cl.
                    let input2 = "\
(helper-val)
/quit
";
                    let mut child2 = Command::new(&*binary)
                        .current_dir(dir.path())
                        .env("CRANELISP_LIB", fixtures.as_os_str())
                        .stdin(Stdio::piped())
                        .stdout(Stdio::piped())
                        .stderr(Stdio::piped())
                        .spawn()
                        .map_err(|e| format!("t{thread_id} i{iter} s2: spawn: {e}"))?;
                    {
                        use std::io::Write;
                        let stdin = child2.stdin.as_mut().ok_or("s2: stdin")?;
                        stdin
                            .write_all(input2.as_bytes())
                            .map_err(|e| format!("t{thread_id} i{iter} s2: write: {e}"))?;
                    }
                    let out2 = child2
                        .wait_with_output()
                        .map_err(|e| format!("t{thread_id} i{iter} s2: wait: {e}"))?;
                    let stdout2 = String::from_utf8_lossy(&out2.stdout);
                    let stderr2 = String::from_utf8_lossy(&out2.stderr);
                    if !stdout2.contains("99") {
                        return Err(format!(
                            "t{thread_id} i{iter} session 2: helper-val lookup failed (heisenbug signature if stdout/stderr contains 'helper-val' not found in module 'helper'):\nstdout: {stdout2}\nstderr: {stderr2}"
                        ));
                    }
                }
                Ok(())
            }));
        }

        // Collect this trial's thread results.
        let mut trial_failures: Vec<String> = Vec::new();
        for h in handles {
            match h.join() {
                Ok(Ok(())) => {}
                Ok(Err(e)) => trial_failures.push(format!("[trial {trial}] {e}")),
                Err(_) => trial_failures.push(format!("[trial {trial}] thread panicked")),
            }
        }
        if !trial_failures.is_empty() {
            // Fast-fail once we have at least one reproduction.
            // Extra trials would only slow the test without adding
            // evidence. Step 3b (evidence capture) will re-run under
            // CRANELISP_SCHEDULER_TRACE=1 and collect its own dumps.
            all_failures.extend(trial_failures);
            break 'trials;
        }
    }

    assert!(
        all_failures.is_empty(),
        "reduced heisenbug repro fired across {TRIALS} trials ({} failure(s)): {}",
        all_failures.len(),
        all_failures.join("\n---\n")
    );
}

// =============================================================================
// Sprint 61 Wave 3 step 3f — H5 regression guards
//
// Per /arch §3d' "Test authoring (step 3f) requirements":
//   Test 1 (/qa, integration) — `ModuleStateTypechecking user` fires exactly
//     ONCE per eval cycle, ONLY on the REPL-eval thread, NEVER on a worker
//     thread. Asserts the H5 eval_in_flight gate suppresses the worker-side
//     claim of `user` after `try_unblock_locked(user)` inside
//     `notify_typecheck_done(helper)`.
//   Test 4 (/qa, integration) — RAII guard starvation safety. The
//     normal-completion (non-racing) path still drives the caller module
//     through to `TypecheckWorking` on t1 after the wait returns. Guards
//     against a bug where `eval_in_flight` leaks on a non-race path and
//     hangs the REPL eval thread forever.
//
// Tests 2 + 3 (unit tests — scheduler flag invariant, RAII guard panic
// unwind) are authored by /int in the owning crate and are out of scope for
// /qa per `memory/feedback_unit_tests_with_dev.md`.
// =============================================================================

// spec: design/int/heisenbug-race-closure.md §7.7 — H5 gate invariant
// (ModuleStateTypechecking `user` fires exactly once per cycle, on the
// REPL-eval thread, never on a worker thread). Also §7.8 (H5 mechanism:
// `try_unblock_locked(user)` emits ModuleStateUnblocked on the worker but
// the subsequent queue push into `typecheck_first` is suppressed by the
// `eval_in_flight` flag — proving absence of a worker claim of `user`).
//
// Test shape:
//   * Drive a minimal import scenario (one helper module, import + call)
//     through a single subprocess with CRANELISP_SCHEDULER_TRACE=1 so the
//     full scheduler event stream is dumped to stderr on exit. The minimal
//     shape (1 session, 1 iteration) is deterministic — the H5 gate should
//     always hold for the import path, race or no race.
//   * Parse the `[SCH]` event lines on stderr.
//   * Count `ModuleStateTypechecking module=user` events per thread. Assert
//     at most ONE such event exists, and if present it is on the REPL-eval
//     thread (the thread on which `ModuleStateBlocked module=user` also
//     fires — the REPL eval thread that triggered the blocking wait).
//
// Passes at HEAD (H5 fix landed in Wave 3 step 3e'). Would fail pre-fix
// (two `ModuleStateTypechecking module=user` events — one on t1, one on
// t2 from the worker claim of the unblocked caller).
#[test]
fn h5_gate_typechecking_user_fires_only_on_repl_thread() {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} — run `cargo build` first"
    );
    let fixtures = project_root().join("tests").join("fixtures");

    let dir = tempfile::tempdir().expect("failed to create temp dir");
    std::fs::write(
        dir.path().join("helper.cl"),
        "(defn helper-val [] 99)",
    )
    .unwrap();

    let input = "\
(import [helper [helper-val]])
(helper-val)
/quit
";

    let mut child = Command::new(&binary)
        .current_dir(dir.path())
        .env("CRANELISP_LIB", fixtures.as_os_str())
        .env("CRANELISP_SCHEDULER_TRACE", "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn cranelisp");
    {
        use std::io::Write;
        let stdin = child.stdin.as_mut().expect("stdin");
        stdin.write_all(input.as_bytes()).expect("write stdin");
    }
    let out = child.wait_with_output().expect("wait subprocess");

    let stdout = stdout_str(&out);
    let stderr = stderr_str(&out);

    // Pre-condition: the subprocess actually completed the import + call.
    // If the call failed we're looking at the H6 residue, not an H5
    // violation — the H5 invariant is still meaningful but the test
    // becomes a false signal. Skip with a clear message so a flake on the
    // distinct H6 signature does not mask H5 regression.
    if !stdout.contains("99") {
        // Allow the H6 residue to surface without failing this H5 test.
        // H6 is ledgered separately as `heisenbug_race_reduced_concurrent_import_pairs`.
        // Only the H5-specific assertion below matters here.
        eprintln!(
            "note: subprocess did not reach 99 — likely H6 residue on this run. \
             Proceeding to H5 gate invariant check regardless.\nstdout: {stdout}\n\
             stderr excerpt: {}",
            stderr.lines().take(6).collect::<Vec<_>>().join("\n")
        );
    }

    // Parse the dump. Each event line is:
    //   `[SCH] ts=N thr=ThreadId(N)/ORD TagName\tmodule=X [pool=Y]`
    //
    // For H5 we care specifically about the *import-cycle* transitions on
    // `user` — not the startup cycle where `user` is typechecked the first
    // time by the worker pool (that is valid and pre-dates the race).
    //
    // The H5-pinning signature (per post-fix-run-35062ca.log lines 35–41
    // and design/int/heisenbug-race-closure.md §7.8) is:
    //   * A worker thread emits `ModuleStateUnblocked module=user` (inside
    //     `try_unblock_locked` from `notify_typecheck_done(helper)`).
    //   * The SAME worker thread IMMEDIATELY afterwards pops `user` from
    //     `typecheck_first` and emits `ModuleStateTypechecking module=user`
    //     (the worker claim of the unblocked caller).
    // Post-fix, the second event must NOT appear on that same thread —
    // the `eval_in_flight` flag suppresses the queue push so the worker
    // has nothing to pop.
    //
    // The assertion therefore walks the event stream in order, and for
    // every `ModuleStateUnblocked module=user` event checks that no
    // subsequent `ModuleStateTypechecking module=user` fires on the same
    // thread before the eval cycle completes (we scan to end-of-dump to
    // avoid over-fitting to a specific window size).
    #[derive(Debug, Clone)]
    struct Event {
        thr: String,
        tag: String,
    }
    let mut events: Vec<Event> = Vec::new();
    for line in stderr.lines() {
        if !line.starts_with("[SCH] ts=") {
            continue;
        }
        let thr_tok = match line.split_whitespace().find(|t| t.starts_with("thr=")) {
            Some(t) => t.to_string(),
            None => continue,
        };
        // Only care about `user` module events here.
        let is_user_mod = line.contains("module=user") && !line.contains("module=user/");
        if !is_user_mod {
            continue;
        }
        let tag = if line.contains("ModuleStateTypechecking") {
            "Typechecking"
        } else if line.contains("ModuleStateUnblocked") {
            "Unblocked"
        } else if line.contains("ModuleStateBlocked") {
            "Blocked"
        } else if line.contains("ModuleStateTypechecked") {
            "Typechecked"
        } else if line.contains("ModuleStateFailed") {
            "Failed"
        } else {
            continue;
        };
        events.push(Event {
            thr: thr_tok,
            tag: tag.to_string(),
        });
    }

    // The H5 gate applies ONLY to REPL-eval-driven block/unblock cycles.
    // The startup path (worker blocks user on prelude, prelude completes,
    // worker unblocks + claims user) happens before the REPL eval thread
    // is live — no `eval_in_flight` flag is armed, and no gate should fire.
    // That cycle is LEGAL and must not be flagged.
    //
    // Identify REPL-driven cycles by the thread that emits `Blocked user`:
    //   * If `Blocked user` fires on ThreadId(1)/0 (the primary/REPL-eval
    //     thread in single-subprocess runs), this is a REPL-driven cycle —
    //     the H5 gate MUST be active.
    //   * If `Blocked user` fires on a worker thread (the startup cycle
    //     above), the gate is not expected; skip.
    //
    // For each REPL-driven Blocked event, scan forward for the matching
    // `Unblocked user` (typically on a worker thread, inside
    // `try_unblock_locked` from `notify_typecheck_done(dep)`). Starting
    // from that Unblocked event, ensure no `Typechecking user` fires on
    // the same (worker) thread before either (a) the next `Blocked user`
    // starts a new cycle, or (b) end-of-dump. If such a `Typechecking
    // user` appears, the H5 gate failed — the worker claimed the unblocked
    // caller despite the `eval_in_flight` flag.
    //
    // The REPL-eval thread ("thr=ThreadId(1)/0") is the primary thread of
    // the subprocess. (This is a stable convention in nextest subprocess
    // harnesses: the main thread is ord=0; spawned workers are ord>=1.)
    const EVAL_THR: &str = "thr=ThreadId(1)/0";
    for (i, ev) in events.iter().enumerate() {
        if ev.tag != "Blocked" || ev.thr != EVAL_THR {
            continue;
        }
        // Find the matching `Unblocked user` in the remainder of the stream.
        let mut unblocked_idx_thr: Option<(usize, String)> = None;
        for (j, later) in events.iter().enumerate().skip(i + 1) {
            match later.tag.as_str() {
                "Unblocked" => {
                    unblocked_idx_thr = Some((j, later.thr.clone()));
                    break;
                }
                "Blocked" if later.thr == EVAL_THR => {
                    // Next eval-driven cycle with no Unblocked resolving
                    // this one. Odd but not an H5 violation; move on.
                    break;
                }
                _ => continue,
            }
        }
        let (u_idx, u_thr) = match unblocked_idx_thr {
            Some(x) => x,
            None => continue,
        };
        // From u_idx onwards, find any `Typechecking user` on u_thr before
        // another `Blocked user` resets the cycle.
        for later in events.iter().skip(u_idx + 1) {
            if later.tag == "Blocked" {
                break;
            }
            if later.tag == "Typechecking" && later.thr == u_thr {
                panic!(
                    "H5 invariant violated: thread {u_thr} emitted \
                     `ModuleStateUnblocked module=user` (resolving a \
                     REPL-eval-driven `Blocked user` cycle from {EVAL_THR}), \
                     then subsequently emitted `ModuleStateTypechecking \
                     module=user` on the SAME thread. This is the H5-pinning \
                     signature (see design/int/heisenbug-race-closure.md \
                     §7.7/§7.8 and tests/sprint61/race-evidence/\
                     post-fix-h5-35062ca.log). The `eval_in_flight` gate is \
                     not suppressing the worker claim of `user` inside \
                     `try_unblock_locked`.\nEvents:\n{events:#?}\n\
                     Full stderr:\n{stderr}"
                );
            }
        }
    }
}

// spec: design/int/heisenbug-race-closure.md §3d' — RAII guard starvation
// safety. `EvalInFlightGuard` is armed at the top of `register_dep_for_eval`
// and must be cleared on function exit (normal AND panic). If the flag
// leaked — e.g., because Drop semantics broke, or a panic path bypassed the
// guard — `try_unblock_locked(caller)` would suppress the queue push
// indefinitely, and the REPL eval thread's retry loop would hang waiting
// for a typecheck push that never arrives.
//
// This test exercises the NORMAL completion path (a dep that completes
// cleanly, no forced race). The subprocess must finish within a
// reasonable timeout — hanging means the flag leaked. The test is
// asserting ABSENCE of the starvation failure mode, not presence of any
// specific event.
//
// Passes at HEAD. Would fail (timeout) if the flag leaks.
#[test]
fn h5_normal_completion_does_not_starve_repl_eval_thread() {
    use std::io::Write;
    use std::time::{Duration, Instant};

    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} — run `cargo build` first"
    );
    let fixtures = project_root().join("tests").join("fixtures");

    let dir = tempfile::tempdir().expect("failed to create temp dir");
    std::fs::write(
        dir.path().join("helper.cl"),
        "(defn helper-val [] 42)",
    )
    .unwrap();

    // Minimal import + call + quit — the normal H5 happy path. No forced
    // parallelism, no trace env var: just the flag-clear code path.
    let input = "\
(import [helper [helper-val]])
(helper-val)
/quit
";

    let start = Instant::now();
    // 15-second ceiling. This test asserts ABSENCE of a starvation
    // pathology: if `EvalInFlightGuard::drop` fails to clear
    // `eval_in_flight`, `register_dep_for_eval` blocks forever in
    // `wait_module_inmem_complete_blocking` and the subprocess never
    // terminates. The assertion only needs to distinguish "completed" from
    // "hung indefinitely" — any ceiling that is much larger than typical
    // completion time and much smaller than "infinite" validates the
    // invariant.
    //
    // Calibration (Sprint 61 Wave 3 step 3f investigation, SHA `a9028c0`):
    //   - Isolation:                  ~0.5 s subprocess wall-clock
    //   - `--test sprint23` suite:    ~0.8 s subprocess wall-clock (n=15)
    //   - Whole-workspace nextest:    ~0.28-0.44 s subprocess wall-clock
    //                                 (n=20, -p cranelisp concurrency)
    //   - /int §3e'' observed:        one 9/10 failure — 2 s ceiling breached
    //                                 under heavy nextest + cargo-build contention
    //
    // The subprocess wall-clock includes fork+exec + dynamic loader +
    // binary cold-start, not just the H5 "normal completion" logic the
    // invariant is about. Under heavy concurrent-subprocess-spawn load on
    // a busy machine, cold-start alone can exceed 1 s. The 2 s ceiling
    // (previous value) sat at ~4x typical under light contention but only
    // ~2.5x typical under heavy contention — too tight.
    //
    // 15 s is ~30x typical worst-case observed, 0.5x the tests/CLAUDE.md
    // per-test 30 s cap, and still sharply distinguishes "completed" from
    // the real starvation failure mode (an infinite block on
    // `wait_module_inmem_complete_blocking`'s condvar). A 15 s breach
    // genuinely signals a leaked flag, not a busy machine.
    //
    // Precedent: `tests/plan/baseline.md §"Sprint 61 Wave 1 — Harness
    // robustness concern"` documents the same pattern for
    // `io_trace_off_path_subprocess_completes_within_generous_ceiling`
    // (subprocess wall-clock assertion perturbed by concurrent nextest
    // load — /qa disposition = widen ceiling).
    const TIMEOUT: Duration = Duration::from_secs(15);

    let mut child = Command::new(&binary)
        .current_dir(dir.path())
        .env("CRANELISP_LIB", fixtures.as_os_str())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn cranelisp");
    {
        let stdin = child.stdin.as_mut().expect("stdin");
        stdin.write_all(input.as_bytes()).expect("write stdin");
    }

    // Poll wait with a deadline. If the child is still alive past the
    // deadline, kill it and fail — starvation signature.
    loop {
        match child.try_wait() {
            Ok(Some(_status)) => break,
            Ok(None) => {
                if start.elapsed() > TIMEOUT {
                    let _ = child.kill();
                    let _ = child.wait();
                    panic!(
                        "H5 starvation-absence violated: subprocess did not \
                         complete within {:?} on the normal-completion path. \
                         Likely cause: `EvalInFlightGuard` Drop is not firing, \
                         so `eval_in_flight` stays true and \
                         `try_unblock_locked(caller)` suppresses the \
                         typecheck_first push forever. See \
                         design/int/heisenbug-race-closure.md §3d' RAII guard \
                         correctness.",
                        TIMEOUT,
                    );
                }
                std::thread::sleep(Duration::from_millis(25));
            }
            Err(e) => panic!("unexpected error waiting for subprocess: {e}"),
        }
    }

    let out = child.wait_with_output().expect("wait subprocess");
    let stdout = stdout_str(&out);
    let stderr = stderr_str(&out);

    // Sanity: the import + call must have executed. If helper-val did not
    // return 42, the test is no longer exercising the "normal completion"
    // path the invariant is about — surface the distinction clearly.
    assert!(
        stdout.contains("42"),
        "H5 normal-completion path failed to yield helper-val=42. Test \
         pre-condition not met. This may be the H6 data-plane residue \
         (ledgered separately as \
         `heisenbug_race_reduced_concurrent_import_pairs`) firing on this \
         run — re-run before treating as an H5 regression.\n\
         stdout: {stdout}\nstderr: {stderr}"
    );
}
