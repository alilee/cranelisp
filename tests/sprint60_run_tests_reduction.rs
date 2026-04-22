//! Sprint 60 Wave 2 Round 3 — reduction of `run_tests_batched_invocation_no_crash`.
//!
//! Starting point (`tests/wave6_demo_repros.rs`):
//!   Running `/run-tests html` in the exemplar with an empty `user.cl`
//!   produces exit 1 and the REPL stderr tail includes
//!   `module error at 0..0: module 'user' failed: module error at 0..0:
//!   no parsed sexps for module 'user'`.
//!
//! Reduction finding: `/run-tests`, the exemplar, html.cl, and the
//! discover-tests/run-test builtins are all OFF THE HOT PATH. The ten
//! html tests run cleanly (`10 passed in 7.21ms`) — the REPL writes that
//! banner to stdout BEFORE the shutdown path emits the "no parsed sexps"
//! error. The defect is in the REPL shutdown path, not the test runner.
//!
//! Minimal crashing shape (19 LOC across two tiny files):
//!   - `tiny.cl`:  `(defn answer [] 42)`
//!   - no `user.cl` at all
//!   - stdin: `(import [tiny [answer]])\n`  (then EOF)
//!
//! Exit behaviour: 1 (not signal-crashed). The REPL banner prints, the
//! import succeeds, the prompt prints, EOF is read (OR /quit runs, OR
//! another form is typed then EOF), the loop breaks, and then
//! `main::run()` calls `CompilerSession::wait_object_complete()` which
//! observes `user` in `ModulePool::Failed` state and returns
//! `SchedulerError::ModuleFailed{ message: "no parsed sexps for module 'user'" }`.
//! `main()` catches the error and `process::exit(1)`s.
//!
//! The `user` module was registered at REPL startup with empty sexps
//! (entry module, user.cl missing or empty). The REPL-time eval of
//! `(import [tiny ...])` drives tiny to inmem-done, adds the import to
//! user's symbol table, calls `regenerate_backing_file()` (writes a
//! populated user.cl), then returns. At that point user is in
//! `TypecheckBlocked` state because `block_for_typecheck(user -> tiny, '*')`
//! was called during import processing (worker.rs:1271), and nothing on
//! the REPL-eval retry path transitions user out of that state for an
//! Additive-strategy eval that resolved in a single retry. When
//! `wait_object_complete` fires, the persistent worker pool observes a
//! Typecheck(user) work item (user was re-queued after tiny completed),
//! attempts to look up user's sexps in `shared.module_sexps`, and fails
//! the module — the sexps user was registered with at startup were an
//! empty Vec (from the missing user.cl) and the REPL-side import didn't
//! republish updated sexps (it writes them to user.cl but doesn't insert
//! them into shared.module_sexps).
//!
//! Correction from an earlier framing: /quit and "typing one more form"
//! do NOT save the failure. Only having user.cl populated at session
//! startup (so it parses to non-empty sexps) avoids the defect. This
//! rules out watcher-ordering and EOF-vs-/quit as variables.
//!
//! Distinction from the "pre-existing" label: the S59 stash-verification
//! treated this as unrelated to the drop-glue/dual-GOT cluster. It is
//! — it's a persistence-collapse residue (user module scheduler state
//! left half-transitioned when the REPL's synthetic `user.cl` is empty),
//! not an RC/codegen defect. But per user directive "pre-existing doesn't
//! matter. Clean and green." — the reduction commits these narrow tests
//! so `/int` (module lifecycle) or `/backend` (scheduler) can pick up the
//! fix next.
//!
//! Files:
//!   - `s60_run_tests_reduction_1_exemplar_batched_failing` — original
//!     wave6 shape (10 html tests pass, then exit 1 on "no parsed sexps")
//!   - `s60_run_tests_reduction_2_repl_import_empty_user_failing` — minimal
//!     shape: 1 defn + 1 REPL import + fresh dir ⇒ same failure
//!   - `s60_run_tests_reduction_3_quit_variant_failing` — /quit variant:
//!     confirms the bug is NOT EOF-specific; /quit hits the same shutdown
//!     path and the same failure (one more loop iteration doesn't save us)
//!   - `s60_run_tests_reduction_4_second_form_variant_failing` — second-form
//!     variant: even typing another expression after the import doesn't
//!     clear the scheduler state — the failure persists through
//!     wait_object_complete
//!   - `s60_run_tests_reduction_5_import_in_file_passes_control` — CONTROL:
//!     when the import is IN user.cl (not typed at REPL), exit 0.
//!     Confirms the defect is REPL-specific, not a general local-import bug.
//!
//! Per memory/feedback_repros_join_suite.md: four reductions are failing
//! tests (each bounds the defect shape). The fifth is a passing negative
//! control that proves the defect is specific to REPL-eval'd imports.
//! All five are regression guards.
//!
//! FIXME(/int) or FIXME(/backend) — pick up from `defects-456-reduction.md`
//! §"Sprint 60 Wave 2 Round 3 — run-tests batched reduction".

use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

fn project_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn binary_path() -> PathBuf {
    project_root().join("target").join("debug").join("cranelisp")
}

fn stdlib_dir() -> PathBuf {
    project_root().join("stdlib")
}

fn platform_dir() -> PathBuf {
    project_root().join("target").join("debug")
}

/// Drive the REPL binary from `cwd`, piping `stdin_input`, and return the Output.
fn run_repl_in(cwd: &std::path::Path, stdin_input: &str) -> Output {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not built at {binary:?} — run `cargo build` first"
    );
    let mut child = Command::new(&binary)
        .current_dir(cwd)
        .env("CRANELISP_LIB", stdlib_dir())
        .env("CRANELISP_PLATFORM_PATH", platform_dir())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn cranelisp REPL");
    {
        use std::io::Write;
        if let Some(stdin) = child.stdin.as_mut() {
            let _ = stdin.write_all(stdin_input.as_bytes());
        }
    }
    child.wait_with_output().expect("failed to read REPL output")
}

fn combined_out(o: &Output) -> String {
    format!(
        "{}{}",
        String::from_utf8_lossy(&o.stdout),
        String::from_utf8_lossy(&o.stderr),
    )
}

/// Recursively copy a directory tree. Skips entries matching
/// `.cranelisp-cache` and hidden files that would differ between runs.
fn copy_dir_recursive(src: &std::path::Path, dst: &std::path::Path) -> std::io::Result<()> {
    std::fs::create_dir_all(dst)?;
    for entry in std::fs::read_dir(src)? {
        let entry = entry?;
        let ft = entry.file_type()?;
        let name = entry.file_name();
        // Skip cache trees and hidden dotfiles (e.g. `.cranelisp-cache`).
        if let Some(s) = name.to_str()
            && s.starts_with('.')
        {
            continue;
        }
        let from = entry.path();
        let to = dst.join(&name);
        if ft.is_dir() {
            copy_dir_recursive(&from, &to)?;
        } else if ft.is_file() {
            std::fs::copy(&from, &to)?;
        }
    }
    Ok(())
}

// spec: repl/spec.md §16.3 + root CLAUDE.md "Defects" — /run-tests on a
// module with N test functions MUST exit cleanly. Starting shape from
// tests/wave6_demo_repros.rs — reproduces to confirm the failure signature
// before reduction.
//
// STATUS: FAILING (exit 1, "no parsed sexps for module 'user'" at shutdown).
#[test]
fn s60_run_tests_reduction_1_exemplar_batched_failing() {
    // Sprint 61 Slice 5 E-1: was writing to `exemplar/user.cl` (checked-in
    // path). Copy the exemplar tree into a fresh TempDir and drive from
    // there so the test can never pollute the checked-in exemplar. See
    // `tests/CLAUDE.md §"Fresh Temp Directory per Test"`.
    let exemplar_src = project_root().join("exemplar");
    if !exemplar_src.exists() {
        eprintln!("exemplar/ missing — skipping this reduction");
        return;
    }
    let td = tempfile::tempdir().expect("tempdir for exemplar copy");
    copy_dir_recursive(&exemplar_src, td.path()).expect("copy exemplar tree");
    // Empty user.cl matches the original shape (wave6 test) — the defect
    // triggers only when user.cl is empty at session start.
    std::fs::write(td.path().join("user.cl"), "").unwrap();

    let input = "(import [html [test-wrap-tag]])\n/run-tests html\n";
    let out = run_repl_in(td.path(), input);
    let exit = out.status.code();
    let combined = combined_out(&out);

    // The 10 html tests run and pass; the process THEN fails exit 1 with
    // "no parsed sexps for module 'user'" — the shutdown-path defect.
    let tests_all_ran = combined.contains("10 passed in");
    let load_err = combined.contains("no parsed sexps for module 'user'");
    let clean_exit = exit == Some(0);

    assert!(
        clean_exit && tests_all_ran && !load_err,
        "exemplar /run-tests html: exit={exit:?} (want 0). \
         tests_all_ran={tests_all_ran}. load_err_tail={load_err}. \
         --- combined ---\n{combined}"
    );
}

// spec: (same anchor) — MINIMAL REPRO of the shutdown-path defect.
// 19 LOC total (2-file tempdir). Any REPL session that imports from a
// local file-on-disk module while the current user.cl is absent/empty
// fails exit 1 at shutdown after EOF. No test runner, no exemplar, no
// html. This is the `run_tests_batched_invocation_no_crash` failure with
// /run-tests + exemplar + ADTs + str-concat removed.
//
// STATUS: FAILING (exit 1, same "no parsed sexps for module 'user'" tail).
#[test]
fn s60_run_tests_reduction_2_repl_import_empty_user_failing() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let cwd = dir.path();

    // `tiny.cl` — one trivial defn.
    std::fs::write(cwd.join("tiny.cl"), "(defn answer [] 42)\n").unwrap();
    // NO user.cl — the entry module sources to "" (empty sexps).

    // Single REPL form: import from the local module. Then EOF.
    let input = "(import [tiny [answer]])\n";
    let out = run_repl_in(cwd, input);
    let exit = out.status.code();
    let combined = combined_out(&out);

    let load_err = combined.contains("no parsed sexps for module 'user'");
    let clean_exit = exit == Some(0);

    assert!(
        clean_exit && !load_err,
        "minimal REPL-import shape: exit={exit:?} (want 0). load_err={load_err}. \
         --- combined ---\n{combined}"
    );
}

// spec: (same anchor) — `/quit` variant: initial observation suggested
// /quit would avoid the failure (one more loop iteration before break),
// but fresh-dir testing shows /quit hits the SAME failure. The defect
// is NOT EOF-vs-/quit; both paths break to `wait_object_complete` which
// reports `user` module Failed. Commit the variant as a failing test to
// prove the shutdown path is unconditional.
//
// STATUS: FAILING. Rules out EOF-ordering as the cause.
#[test]
fn s60_run_tests_reduction_3_quit_variant_failing() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let cwd = dir.path();
    std::fs::write(cwd.join("tiny.cl"), "(defn answer [] 42)\n").unwrap();

    let input = "(import [tiny [answer]])\n/quit\n";
    let out = run_repl_in(cwd, input);
    let exit = out.status.code();
    let combined = combined_out(&out);

    let load_err = combined.contains("no parsed sexps for module 'user'");
    let clean_exit = exit == Some(0);

    assert!(
        clean_exit && !load_err,
        "REPL with /quit after import should exit 0 and not emit load_err. \
         exit={exit:?} load_err={load_err}. \
         --- combined ---\n{combined}"
    );
}

// spec: (same anchor) — second-form variant: typing another expression
// after the import runs one extra iteration of the REPL loop, giving
// `poll_and_reload` a chance to observe the watcher event from
// `regenerate_backing_file`. Still fails. Rules out watcher-ordering
// and "one more iteration" as the cause.
//
// STATUS: FAILING. The user-module scheduler state is not recoverable
// from subsequent REPL forms — only from having user.cl populated at
// session start.
#[test]
fn s60_run_tests_reduction_4_second_form_variant_failing() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let cwd = dir.path();
    std::fs::write(cwd.join("tiny.cl"), "(defn answer [] 42)\n").unwrap();

    // Import then a bare literal — the second iteration gives the watcher
    // a chance to observe the regenerate_backing_file write.
    let input = "(import [tiny [answer]])\n42\n";
    let out = run_repl_in(cwd, input);
    let exit = out.status.code();
    let combined = combined_out(&out);

    let load_err = combined.contains("no parsed sexps for module 'user'");
    let clean_exit = exit == Some(0);

    assert!(
        clean_exit && !load_err,
        "REPL with second form after import should exit 0 and not emit load_err. \
         exit={exit:?} load_err={load_err}. \
         --- combined ---\n{combined}"
    );
}

// CONTROL — the same import form placed IN user.cl (as-a-file) rather
// than typed at the REPL prompt does NOT trigger the failure. This
// confirms the bug is specific to the REPL-eval path's interaction with
// the scheduler's user-module state — not a general local-import failure.
//
// STATUS: PASSING today (exit 0). Negative control — same symbolic work,
// different entry path, passes cleanly. If this ever fails, the defect
// has spread into the entry-module load path.
#[test]
fn s60_run_tests_reduction_5_import_in_file_passes_control() {
    let dir = tempfile::tempdir().expect("create tempdir");
    let cwd = dir.path();
    std::fs::write(cwd.join("tiny.cl"), "(defn answer [] 42)\n").unwrap();
    // user.cl HAS the import up-front.
    std::fs::write(cwd.join("user.cl"), "(import [tiny [answer]])\n").unwrap();

    // Empty stdin — entry module resolution alone drives the import.
    let out = run_repl_in(cwd, "");
    let exit = out.status.code();
    let combined = combined_out(&out);

    assert_eq!(
        exit,
        Some(0),
        "REPL with import in user.cl (not typed at prompt) should exit 0. \
         exit={exit:?}. --- combined ---\n{combined}"
    );
}
