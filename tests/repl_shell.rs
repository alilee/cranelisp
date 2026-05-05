//! Sprint 64 Wave 6 batch 2 Part A carry-forward — `/sh` Shell Escape cluster.
//!
//! Per the Wave 6 batch 2 audit (`tests/plan/wave-6-batch-2-audit.md` §2),
//! these 11 tests carry forward the `/sh` shell-escape surface from
//! `tests/sprint23.rs` (lines 386–527). The audit notes
//! `repl/spec.md §13` has zero existing `[Tested]` annotations across
//! the carry-forward suite — these tests are the first §13 coverage.
//!
//! Spec anchors:
//!   - `repl/spec.md §13.2` — Execution
//!   - `repl/spec.md §13.3` — Output Handling (passthrough)
//!   - `repl/spec.md §13.4` — Exit Code Display
//!   - `repl/spec.md §13.5` — No REPL State Interaction
//!   - `repl/spec.md §13.6` — Edge Cases
//!   - `repl/spec.md §13.7` — `/help` Integration
//!
//! Mode: subprocess REPL via the `Cranelisp` builder with piped stdin.
//! Each test pipes `/sh <cmd>\n…/quit\n` and inspects stdout/stderr.
//!
//! Note on stdout/stderr coupling: per spec §13.3, the child shell's
//! stdout passes through to the user's terminal directly; the harness
//! pipes child stdout via `Stdio::piped()`, so the shell command's
//! output appears in the captured `out.stdout` (passthrough is captured
//! to the same fd the parent inherits). Where the test asserts
//! "stdout contains <needle>", that needle covers both the REPL's own
//! prompt/output and the shell command's piped output.

#[path = "helpers/e2e.rs"]
mod e2e;

use e2e::Cranelisp;

/// Quit the REPL cleanly after the test input.
const QUIT: &str = "/quit\n";

/// Helper: pipe `body` (with trailing `/quit`) to a bare REPL session.
fn run(body: &str) -> e2e::CrOutput {
    let mut input = String::from(body);
    if !input.ends_with('\n') {
        input.push('\n');
    }
    input.push_str(QUIT);
    Cranelisp::repl_capture(&input)
}

// =============================================================================
// 1. Basic execution
// =============================================================================

// spec: repl/spec.md §13.2 — command execution via /bin/sh.
//   `/sh echo hello_from_shell` runs the command; output appears.
//
// (carry: legacy/sprint23.rs::shell_escape_basic_echo)
#[test]
fn shell_escape_basic_echo_command_runs() {
    let out = run("/sh echo hello_from_shell");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("hello_from_shell"),
        "shell echo output should appear: stdout={:?} stderr={:?}",
        out.stdout, out.stderr
    );
}

// spec: repl/spec.md §13.3 — Output Handling (stdout passthrough).
//   Quoted args + passthrough: `echo "hello from shell"` produces
//   the literal phrase in output.
//
// (carry: legacy/sprint23.rs::shell_escape_output_passthrough)
#[test]
fn shell_escape_quoted_args_pass_through_to_stdout() {
    let out = run("/sh echo \"hello from shell\"");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("hello from shell"),
        "command output should pass through: stdout={:?} stderr={:?}",
        out.stdout, out.stderr
    );
}

// =============================================================================
// 2. Exit code display
// =============================================================================

// spec: repl/spec.md §13.4 — non-zero exit code displayed.
//   `/sh false` → `exit status: 1` printed by the REPL.
//
// (carry: legacy/sprint23.rs::shell_escape_nonzero_exit_code)
#[test]
fn shell_escape_nonzero_exit_code_is_displayed() {
    let out = run("/sh false");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("exit status: 1"),
        "non-zero exit should display 'exit status: 1': stdout={:?} stderr={:?}",
        out.stdout, out.stderr
    );
}

// spec: repl/spec.md §13.4 — zero exit: silence.
//   `/sh true` → no `exit status` line. Negative-shape regression.
//
// (carry: legacy/sprint23.rs::shell_escape_zero_exit_silent)
#[test]
fn shell_escape_neg_zero_exit_does_not_display_exit_status() {
    let out = run("/sh true");
    assert!(
        !out.stdout.contains("exit status") && !out.stderr.contains("exit status"),
        "success (exit 0) must NOT print 'exit status': stdout={:?} stderr={:?}",
        out.stdout, out.stderr
    );
}

// spec: repl/spec.md §13.4 — command not found.
//   The shell's own error message is passed through; exit code 127
//   is displayed.
//
// (carry: legacy/sprint23.rs::shell_escape_command_not_found)
#[test]
fn shell_escape_command_not_found_propagates_shell_error() {
    let out = run("/sh nonexistent_command_xyz");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("not found") || combined.contains("exit status: 127"),
        "command-not-found should produce shell error or exit-127: stdout={:?} stderr={:?}",
        out.stdout, out.stderr
    );
}

// =============================================================================
// 3. Edge cases
// =============================================================================

// spec: repl/spec.md §13.6 — Edge Cases / No arguments.
//   `/sh` with no command (or only whitespace) MUST print
//   `Usage: /sh <command>` per §13.6, and MUST NOT crash. The legacy
//   test asserted only the absence of "error"/"failed"; we preserve
//   that invariant (silent re-prompt or usage hint, no crash).
//
// (carry: legacy/sprint23.rs::shell_escape_empty_command)
#[test]
fn shell_escape_neg_empty_command_does_not_error_or_crash() {
    let out = run("/sh\n/sh   ");
    // No crash: REPL must have terminated cleanly via /quit.
    assert!(
        out.status.success(),
        "REPL should not crash on empty /sh: status={:?} stderr={:?}",
        out.status, out.stderr
    );
    // Either silent re-prompt or §13.6 usage hint — neither is an
    // "error" / "failed" message.
    let has_error_word = out.stdout.contains("error") || out.stdout.contains("failed");
    assert!(
        !has_error_word,
        "empty /sh should not produce an error message: {:?}",
        out.stdout
    );
}

// spec: repl/spec.md §13.6 — Edge Cases / Multi-line.
//   Multi-line not supported, use shell syntax. `/sh echo a && echo b`
//   runs both commands.
//
// (carry: legacy/sprint23.rs::shell_escape_chained_commands)
#[test]
fn shell_escape_chained_commands_via_shell_syntax_run_both() {
    let out = run("/sh echo first && echo second");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(combined.contains("first"), "first command should run: {combined}");
    assert!(combined.contains("second"), "second command should run: {combined}");
}

// =============================================================================
// 4. No state interaction
// =============================================================================

// spec: repl/spec.md §13.5 — No REPL State Interaction.
//   Define `foo`, run `/sh`, call `foo` — defn still works (state
//   survives shell escape).
//
// (carry: legacy/sprint23.rs::shell_escape_no_state_interaction)
#[test]
fn shell_escape_does_not_disturb_repl_state() {
    let out = run("(defn foo [] 42)\n/sh echo test\n(foo)");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("42"),
        "defn should survive /sh escape: stdout={:?}",
        out.stdout
    );
}

// spec: repl/spec.md §13.6 — Edge Cases / Timing.
//   The prompt after a shell escape MUST show `0+0ms` — shell commands
//   are not Cranelisp evaluations.
//
// (carry: legacy/sprint23.rs::shell_escape_timing_reset)
#[test]
fn shell_escape_prompt_shows_zero_zero_ms_timing() {
    let out = run("/sh echo hi");
    assert!(
        out.stdout.contains("0+0ms"),
        "prompt after /sh should show '0+0ms': stdout={:?}",
        out.stdout
    );
}

// =============================================================================
// 5. /help integration
// =============================================================================

// spec: repl/spec.md §13.7 — `/help` Integration.
//   `/sh` MUST appear in `/help` output.
//
// (carry: legacy/sprint23.rs::shell_escape_appears_in_help)
#[test]
fn shell_escape_listed_in_help_output() {
    let out = run("/help");
    assert!(
        out.stdout.contains("/sh"),
        "/help should list /sh: stdout={:?}",
        out.stdout
    );
}

// =============================================================================
// 6. Negative tests — child-process isolation
// =============================================================================

// spec: repl/spec.md §13.5 — env vars set by the command MUST NOT propagate
//   back to the REPL process. `/sh export FOO=bar` is a child-process
//   `export` that has no effect on the parent — invariant: REPL does
//   not crash, and the second `/sh echo done` runs successfully.
//
// (carry: legacy/sprint23.rs::shell_escape_neg_no_env_propagation)
#[test]
fn shell_escape_neg_child_env_changes_do_not_propagate_or_crash_repl() {
    let out = run("/sh export FOO=bar\n/sh echo done");
    assert!(
        out.status.success(),
        "REPL should not crash on child-env mutation: status={:?} stderr={:?}",
        out.status, out.stderr
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("done"),
        "second /sh should still run: stdout={:?}",
        out.stdout
    );
}
