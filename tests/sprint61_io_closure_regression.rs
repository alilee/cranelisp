//! Sprint 61 Wave 4 Slice 4 — regression guard for the IO trampoline /
//! closure capture double-free bug (H(4-1'')).
//!
//! Ref: `design/backend/slice-4-21-hello-io-investigation.md`
//!
//! ## What this test guards
//!
//! Before the fix, a user-defined combinator of the shape `(fn [_] b)`
//! — where `b` is a captured heap-typed IO value — would double-free the
//! captured value. The closure body returned `b` directly; the closure's
//! drop-glue then dec'd `b` (driven by the trampoline's
//! `consume_closure` path for fresh-produced closures), freeing the node
//! the outer trampoline was about to read as `new_current`. The process
//! then read a poisoned tag and aborted with a variety of surface exit
//! codes (101 panic / 133 SIGTRAP / 201 i32-trunc-of-abort / SIGABRT),
//! all tied to the same root cause.
//!
//! The fix is a backend-side `emit_capture_return_inc` helper in
//! `crates/cranelisp-backend/src/compiler/control_flow.rs` that emits an
//! `rc_inc` on the returned capture before `return`, balancing the
//! drop-glue's upcoming dec so the caller-visible pointer stays live.
//!
//! ## Minimum repro (7 source lines, 100% crash pre-fix, 100% clean post-fix)
//!
//! See `design/backend/slice-4-21-hello-io-investigation.md §"Reduction
//! narrative"`. The repro does NOT import `platform.stdio` and does NOT
//! call any platform IO — the bug is purely in Pure/Bind closure
//! semantics. Expected main return: `1 + (999+8 → 50 via (fn [_] b) →
//! 50) = 51`. Process exit code is 51.
//!
//! ## Layering
//!
//! Layer 4 subprocess test (per `tests/CLAUDE.md §Layer 4`): invokes the
//! `cranelisp` binary via `--run` with stdin closed. The compiled binary
//! path is the same as other sprint61 IO tests.

use std::os::unix::process::ExitStatusExt;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

// spec: design/backend/slice-4-21-hello-io-investigation.md §4e
// (H(4-1'') capture-return-inc fix, landed 2026-04-22)
//
// The 7-line minimum repro. Pre-fix: 100% crash (exit 101/133/201 or
// SIGABRT). Post-fix: exit 51 (= 1 + 50), no panic, no signal.
const REPRO_SOURCE: &str = "\
(import [primitives [Pure bind add-i64]])

(defn then [a b]
  (bind a (fn [_] b)))

(defn test-then []
  (bind (then (Pure 999) (Pure 42))
    (fn [x] (Pure (add-i64 x 8)))))

(defn main []
  (bind (Pure 1) (fn [r1]
    (bind (test-then) (fn [r2]
      (Pure (add-i64 r1 r2)))))))
";

fn project_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn binary_path() -> PathBuf {
    project_root().join("target").join("debug").join("cranelisp")
}

/// Write REPRO_SOURCE to a fresh TempDir and invoke `cranelisp --run` on
/// it, capturing stdout/stderr/exit. Per `tests/CLAUDE.md §Test
/// Isolation` — each test run uses a fresh TempDir (no shared state).
fn run_repro_with_env(env: &[(&str, &str)]) -> (Output, tempfile::TempDir) {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} — run `cargo build` first"
    );
    let tmp = tempfile::Builder::new()
        .prefix("sprint61_io_closure_")
        .tempdir()
        .expect("TempDir creation");
    let src_path = tmp.path().join("repro.cl");
    std::fs::write(&src_path, REPRO_SOURCE).expect("write repro source");

    let mut cmd = Command::new(&binary);
    cmd.args(["--run", src_path.to_str().unwrap()])
        .current_dir(tmp.path())
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    // Scope the cache to the TempDir so concurrent test runs don't collide.
    cmd.env("CRANELISP_CACHE_DIR", tmp.path());
    cmd.env_remove("CRANELISP_IO_TRACE");
    for (k, v) in env {
        cmd.env(k, v);
    }
    let out = cmd.output().expect("failed to run cranelisp");
    (out, tmp)
}

/// Normalise `ExitStatus` to a shell-convention integer so signal-
/// terminated children surface as 128+N rather than `None`.
fn exit_code_of(out: &Output) -> i32 {
    match out.status.code() {
        Some(c) => c,
        None => match out.status.signal() {
            Some(sig) => 128 + sig,
            None => -1,
        },
    }
}

fn stderr_of(out: &Output) -> String {
    String::from_utf8_lossy(&out.stderr).to_string()
}

// spec: design/backend/slice-4-21-hello-io-investigation.md §4e
// (H(4-1'') capture-return-inc fix, landed 2026-04-22)
//
// Primary regression guard. The 7-line repro MUST exit with code 51
// (= 1 + 50), MUST NOT panic, MUST NOT SIGABRT/SIGTRAP, and MUST NOT
// exit with the pre-fix surface codes 101/133/201.
#[test]
fn io_trampoline_then_combinator_does_not_double_free_capture() {
    let (out, _tmp) = run_repro_with_env(&[]);
    let code = exit_code_of(&out);
    let stderr = stderr_of(&out);

    // Pre-fix surface exit codes. Each is a DIFFERENT failure mode tied
    // to the same root cause. Calling them out individually gives a
    // pointed diagnostic if the fix regresses.
    assert_ne!(
        code, 101,
        "pre-fix panic signature (exit 101) — capture-return inc \
         regressed. stderr:\n{stderr}"
    );
    assert_ne!(
        code, 133,
        "pre-fix SIGTRAP signature (exit 133) — capture-return inc \
         regressed. stderr:\n{stderr}"
    );
    assert_ne!(
        code, 201,
        "pre-fix abort-trunc signature (exit 201) — capture-return inc \
         regressed. stderr:\n{stderr}"
    );
    assert_ne!(
        code, 134,
        "pre-fix SIGABRT signature (exit 134 = 128+6) — capture-return \
         inc regressed. stderr:\n{stderr}"
    );

    // Post-fix expectation: exact exit code 51 per /backend's
    // computation (1 + (999 → discarded via (fn [_] b) → 42 → +8 = 50)
    // = 51).
    assert_eq!(
        code, 51,
        "expected exit=51 (1 + 50) post-fix; got {code}. stderr:\n{stderr}"
    );

    // Additional discriminator: no Rust panic shape in stderr. The
    // pre-fix crash emitted `panicked: cranelisp_run_io: unknown IO
    // tag` (see §"Reduction narrative" in the investigation doc).
    assert!(
        !stderr.contains("panicked"),
        "unexpected Rust panic in stderr post-fix — capture-return inc \
         regressed. stderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("unknown IO tag"),
        "unexpected `unknown IO tag` signature in stderr — the exact \
         pre-fix crash shape has regressed. stderr:\n{stderr}"
    );
}

// spec: design/backend/slice-4-21-hello-io-investigation.md §4e
// (post-fix trace shape — see tests/sprint61/race-evidence/
// 21-hello-io-post-fix-776a6cf.log line 23: `TrampolineExit result=51`)
//
// Secondary guard using IO-trace observability. If the trampoline
// completes cleanly post-fix, the event log MUST include a
// `TrampolineExit result=51` line and MUST NOT truncate mid-stream.
// This is a stronger signal than exit code alone because it proves the
// trampoline reached its normal exit path, not a stray exit from a
// spurious panic that happened to yield the right integer.
#[test]
fn io_trampoline_then_combinator_trace_shows_clean_trampoline_exit() {
    let (out, _tmp) = run_repro_with_env(&[("CRANELISP_IO_TRACE", "1")]);
    let code = exit_code_of(&out);
    let stderr = stderr_of(&out);

    assert_eq!(
        code, 51,
        "expected exit=51 under CRANELISP_IO_TRACE=1; got {code}. \
         stderr:\n{stderr}"
    );

    // The IO trace dump MUST contain a TrampolineExit carrying the
    // correct result. Pre-fix the process aborted between
    // TrampolineEnter and TrampolineExit; this assertion would fail
    // loudly in that case.
    assert!(
        stderr.contains("TrampolineExit"),
        "expected TrampolineExit event in IO trace dump; stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("result=51"),
        "expected TrampolineExit to carry result=51; stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("TrampolineEnter"),
        "expected TrampolineEnter event in IO trace dump; stderr:\n{stderr}"
    );
}
