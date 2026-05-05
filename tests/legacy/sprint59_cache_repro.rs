// QUARANTINED Sprint 64 Wave 6 batch 3 — FIXME 0145 — owning skill /backend
// Source archive — not built by Cargo (nested under tests/legacy/).
// Awaiting harvest into cranelisp-backend/src/ #[cfg(test)] unit tests.
//
// Carry-forward: 2 tests in 1 file:
//   - tests/cache.rs::cache_repl_minimal_plain_fn_prelude_restored_on_session_2
//     (carry: s59_cache_hit_plain_prelude_fn_not_restored)
//   - tests/cache.rs::cache_repl_empty_prelude_session_2_evaluates_literal
//     (carry: s59_cache_hit_empty_prelude_basic_eval_works)
//
// No inline FIXMEs in this file — the docstring is descriptive prose
// only and references design/int/cache-prelude-restoration-repro.md
// as the Sprint 59 Workstream A diagnosis anchor.

//! Sprint 59 Wave 1 — cache-hit prelude-restoration bug isolation.
//!
//! Symptom: when the `cranelisp` REPL starts twice in the same project
//! directory with a local prelude, session 2 hits the disk cache
//! (`.cranelisp-cache/prelude.{o,meta.json}`) but does NOT rebind the
//! prelude's exported symbols into the new session — so a form that
//! resolves against them (`(+ 40 2)`, or any call to a prelude-defined
//! function) fails with `undefined variable: …`.
//!
//! This reduces `sprint23::cache_repl_loads_on_startup` to the smallest
//! possible prelude that still triggers the failure, in order to
//! discriminate:
//!   - does the bug depend on operator/trait machinery (overloads, impls)?
//!   - or on ANY cached prelude binding (plain fn)?
//!   - or only a fully-populated prelude?
//!
//! Each test runs the shipped `cranelisp` binary as a subprocess so we
//! exercise the same startup flow that fails on the carried test. The
//! harness intentionally mirrors sprint23.rs:1133 rather than using the
//! library API — an attempted library-level repro is noted in the
//! diagnosis document: `design/int/cache-prelude-restoration-repro.md`.

use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

static TEST_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn project_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn binary_path() -> PathBuf {
    project_root().join("target").join("debug").join("cranelisp")
}

fn fresh_dir(label: &str) -> PathBuf {
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
        .join("sprint59")
        .join(".runs")
        .join(&*RUN_TS)
        .join(format!("{n}_{label}"));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn stdout_of(output: &std::process::Output) -> String {
    String::from_utf8_lossy(&output.stdout).to_string()
}

fn stderr_of(output: &std::process::Output) -> String {
    String::from_utf8_lossy(&output.stderr).to_string()
}

/// Run the REPL twice in `dir`, with `lib_dir` as the prelude lib.
/// Feed `input` to both sessions. Returns (out1, out2, err2, manifest_exists).
fn run_twice(
    dir: &std::path::Path,
    lib_dir: &std::path::Path,
    input: &str,
) -> (String, String, String, bool) {
    let binary = binary_path();
    let spawn = || {
        Command::new(&binary)
            .current_dir(dir)
            .env("CRANELISP_LIB", lib_dir.as_os_str())
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .and_then(|mut child| {
                use std::io::Write;
                child
                    .stdin
                    .as_mut()
                    .unwrap()
                    .write_all(input.as_bytes())
                    .unwrap();
                child.wait_with_output()
            })
            .expect("failed to run REPL")
    };

    let o1 = spawn();
    let manifest_exists = dir.join(".cranelisp-cache").join("manifest.json").exists();
    let o2 = spawn();
    (stdout_of(&o1), stdout_of(&o2), stderr_of(&o2), manifest_exists)
}

// -----------------------------------------------------------------------------
// Reduction A: smallest possible prelude — single plain (defn f [] 42).
// No traits, no impls, no operators. If this fails, cache-hit prelude
// restoration is broken for EVERY binding — not operator-specific.
// -----------------------------------------------------------------------------
#[test]
fn s59_cache_hit_plain_prelude_fn_not_restored() {
    let dir = fresh_dir("plain_prelude_fn");
    let lib = dir.join("lib");
    std::fs::create_dir_all(&lib).unwrap();
    std::fs::write(lib.join("prelude.cl"), "(defn f [] 42)\n").unwrap();

    let (out1, out2, err2, manifest) = run_twice(&dir, &lib, "(f)\n/quit\n");

    assert!(
        out1.contains("42"),
        "session 1 should print 42 (fresh compile): out1={out1}"
    );
    assert!(
        manifest,
        "session 1 should populate cache manifest for a prelude with at least one export"
    );
    assert!(
        out2.contains("42"),
        "session 2 (cache hit) should also print 42, but got: out2={out2} err2={err2}"
    );
}

// -----------------------------------------------------------------------------
// Reduction B: empty prelude. No bindings at all. Only exercises the
// cache-hit registration pathway without any symbols to rebind.
// If this passes, the bug is specifically about symbol rebinding.
// If this fails, the cache-hit path is broken at the module-level.
// -----------------------------------------------------------------------------
#[test]
fn s59_cache_hit_empty_prelude_basic_eval_works() {
    let dir = fresh_dir("empty_prelude");
    let lib = dir.join("lib");
    std::fs::create_dir_all(&lib).unwrap();
    std::fs::write(lib.join("prelude.cl"), ";; empty\n").unwrap();

    // Use a form that does NOT need prelude: an integer literal.
    let (out1, out2, err2, _manifest) = run_twice(&dir, &lib, "42\n/quit\n");

    assert!(
        out1.contains("42"),
        "session 1 should print 42: out1={out1}"
    );
    assert!(
        out2.contains("42"),
        "session 2 with empty prelude should also print 42: out2={out2} err2={err2}"
    );
}
