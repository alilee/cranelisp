//! Sprint 60 Workstream B — CLIF-dump observability (integration).
//!
//! Subprocess-level integration coverage for the `CRANELISP_CODEGEN_DUMP`
//! env-var filter wired in `crates/cranelisp-backend/src/lib.rs`. Unit tests
//! for the filter grammar live with `/backend` (see `clif_dump_matches_*`
//! and `write_clif_dump_*` tests in `crates/cranelisp-backend/src/lib.rs`
//! `#[cfg(test)]`). These tests prove the env var is actually plumbed through
//! to a user-visible dump on stderr when a program is compiled via the
//! `cranelisp` binary — the surface that Workstream A's H3 audit relies on.
//!
//! Test plan reference: tests/plan/ring4.md §G.20.2.

use std::path::PathBuf;
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

static TEST_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn project_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn binary_path() -> PathBuf {
    project_root().join("target").join("debug").join("cranelisp")
}

fn test_dir(label: &str) -> PathBuf {
    let n = TEST_COUNTER.fetch_add(1, Ordering::SeqCst);
    let dir = project_root()
        .join("tests")
        .join("sprint60")
        .join(".runs")
        .join(format!("obs_{n}_{label}"));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn run_with_env(source: &str, label: &str, env: &[(&str, &str)]) -> Output {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} — run `cargo build` first"
    );
    let dir = test_dir(label);
    // File stem drives the module path — use `user.cl` so tests can anchor
    // expectations on the `user` module name.
    let source_path = dir.join("user.cl");
    std::fs::write(&source_path, source).unwrap();
    let mut cmd = Command::new(&binary);
    cmd.args(["--run", source_path.to_str().unwrap()])
        .current_dir(&dir)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    for (k, v) in env {
        cmd.env(k, v);
    }
    cmd.output().expect("failed to run cranelisp")
}

fn stderr_of(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).to_string()
}

/// A trivial program that defines one zero-arg `main` in the `user` module so
/// the CLIF dump has a stable name to match (`user::main`).
// spec §12.6: program exit code is `main`'s Int return value. Using 0 here
// keeps assert_status_success() matching across operating systems.
const TRIVIAL_SRC: &str = "(defn main [] 0)";

// spec: tests/plan/ring4.md §G.20.2 — `CRANELISP_CODEGEN_DUMP=*` emits CLIF
// for every freshly-compiled function. The frame-markers (`; === CLIF ... ===`)
// come from `write_clif_dump` in `crates/cranelisp-backend/src/lib.rs`.
#[test]
fn codegen_dump_star_emits_clif_for_every_function() {
    let out = run_with_env(TRIVIAL_SRC, "star", &[("CRANELISP_CODEGEN_DUMP", "*")]);
    assert!(
        out.status.success(),
        "binary must exit 0; stderr={}",
        stderr_of(&out)
    );
    let stderr = stderr_of(&out);
    assert!(
        stderr.contains("; === CLIF"),
        "CLIF dump header missing from stderr under `*` filter; stderr was:\n{stderr}"
    );
    assert!(
        stderr.contains("user::main"),
        "expected `user::main` in CLIF dump frame; stderr was:\n{stderr}"
    );
    // Negative guard: the dump must contain CLIF body content, not just the
    // framing header — `function ` is the Cranelift IR signature prefix.
    assert!(
        stderr.contains("function "),
        "CLIF body (expected `function ` signature line) missing; stderr was:\n{stderr}"
    );
}

// spec: tests/plan/ring4.md §G.20.2 — per-module filter matches only the
// named module. Compiles two modules and filters to one; the other MUST NOT
// appear in the dump.
#[test]
fn codegen_dump_per_module_filters_to_that_module_only() {
    let out = run_with_env(
        TRIVIAL_SRC,
        "per_module",
        &[("CRANELISP_CODEGEN_DUMP", "user")],
    );
    assert!(
        out.status.success(),
        "binary must exit 0; stderr={}",
        stderr_of(&out)
    );
    let stderr = stderr_of(&out);
    assert!(
        stderr.contains("; === CLIF user::"),
        "expected `user` CLIF dump; stderr was:\n{stderr}"
    );
    // Negative: frames must NOT appear for other module paths the compiler
    // may have codegen'd (e.g., `primitives`, `runtime`). The filter is an
    // equality check — anything other than `user` must be silent.
    for foreign in ["primitives::", "runtime::", "main::"] {
        let needle = format!("; === CLIF {foreign}");
        assert!(
            !stderr.contains(&needle),
            "filter `user` leaked dump for {foreign}; stderr was:\n{stderr}"
        );
    }
}

// spec: tests/plan/ring4.md §G.20.2 — with the env var UNSET, no CLIF
// dump appears. This is the silent-by-default negative guard; any regression
// that flips the default to noisy breaks the release experience.
#[test]
fn codegen_dump_unset_emits_no_clif() {
    // We intentionally pass an empty env slice AND explicitly remove the var
    // from the child process environment via Command::env_remove below.
    let binary = binary_path();
    assert!(binary.exists(), "cranelisp binary not found at {binary:?}");
    let dir = test_dir("unset");
    // File stem drives the module path — use `user.cl` so tests can anchor
    // expectations on the `user` module name.
    let source_path = dir.join("user.cl");
    std::fs::write(&source_path, TRIVIAL_SRC).unwrap();

    let out = Command::new(&binary)
        .args(["--run", source_path.to_str().unwrap()])
        .current_dir(&dir)
        .env_remove("CRANELISP_CODEGEN_DUMP")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("failed to run cranelisp");

    assert!(
        out.status.success(),
        "binary must exit 0; stderr={}",
        stderr_of(&out)
    );
    let stderr = stderr_of(&out);
    assert!(
        !stderr.contains("; === CLIF"),
        "CLIF dump frame leaked when env var unset; stderr was:\n{stderr}"
    );
}

// spec: tests/plan/ring4.md §G.20.2 — explicit empty value also means
// disabled (matches `clif_dump_matches(Some(""), …) == false`).
#[test]
fn codegen_dump_empty_value_emits_no_clif() {
    let out = run_with_env(TRIVIAL_SRC, "empty", &[("CRANELISP_CODEGEN_DUMP", "")]);
    assert!(
        out.status.success(),
        "binary must exit 0; stderr={}",
        stderr_of(&out)
    );
    let stderr = stderr_of(&out);
    assert!(
        !stderr.contains("; === CLIF"),
        "empty env value must be silent; stderr was:\n{stderr}"
    );
}
