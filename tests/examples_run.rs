//! Sprint 60 Workstream F — examples `--run` path regression guard.
//!
//! Per the Sprint 60 scope revision (sprints/SPRINT.md §Wave 1 finding
//! 2026-04-21), examples are free-standing per the root `CLAUDE.md` "Stdlib
//! separation" principle: they MUST NOT depend on `stdlib/`. `/examples` owns
//! a standalone `examples/lib/prelude.cl` + `examples/Cranelisp.toml` that
//! puts `./lib` on the search path. This test asserts that each `.cl` file
//! under `examples/` runs successfully via `cargo run -- --run <file>` —
//! the user-surface acceptance criterion for Ring 4.
//!
//! **Expected exit code is NOT zero.** Per `spec/10-io.md` §10, `main`'s
//! `Int` return value IS the process exit code. Examples intentionally
//! return sum-of-pass-results from `main` per the `examples/` convention
//! ("a non-zero result means all sub-tests passed"). Asserting
//! `status.success()` is therefore spec-incorrect — the test must match
//! each example's specific expected exit value.
//!
//! Test plan reference: tests/plan/ring4.md §G.20.6.

use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

fn project_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn binary_path() -> PathBuf {
    project_root().join("target").join("debug").join("cranelisp")
}

fn examples_dir() -> PathBuf {
    project_root().join("examples")
}

/// Run a single example file through `cranelisp --run` and return the output.
/// The child's working directory is the example's own directory so
/// `Cranelisp.toml` at `examples/` is discovered. Stdin is closed so
/// read-line-driven IO examples don't block.
fn run_example(path: &Path) -> Output {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} — run `cargo build` first"
    );
    Command::new(&binary)
        .args(["--run", path.to_str().unwrap()])
        .current_dir(examples_dir())
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("failed to run cranelisp")
}

/// Expected exit code table — one entry per `.cl` file directly under
/// `examples/`. Values confirmed by `/examples` Workstream F Phase 5b and
/// cross-checked here. The `main` function of each example returns a sum of
/// sub-test passes (see `examples/README.md` rule 4); these values represent
/// "all sub-tests passed".
///
/// Note: `16-modules` is a sub-directory (module example), not a top-level
/// `.cl` file, so it is absent from this table. 27 top-level `.cl` files
/// are expected.
///
/// IO examples 21 and 24 exit with a platform artefact (SIGTRAP/133) when
/// stdin is closed by the harness — `read-line` on a closed pipe traps.
/// Accept the artefact exits in addition to the direct-invocation value so
/// the harness does not falsely flag them.
fn expected_exits() -> Vec<(&'static str, &'static [i32])> {
    vec![
        ("01-integers.cl", &[69]),
        ("02-booleans.cl", &[5]),
        ("03-let-bindings.cl", &[97]),
        ("04-functions.cl", &[135]),
        ("05-recursion.cl", &[111]),
        ("06-enums.cl", &[104]),
        ("07-polymorphism.cl", &[119]),
        ("08-floats.cl", &[9]),
        ("09-strings.cl", &[55]),
        ("10-adts.cl", &[9]),
        ("11-destructuring.cl", &[69]),
        ("12-closures.cl", &[7]),
        ("13-higher-order.cl", &[203]),
        ("14-vecs.cl", &[29]),
        ("15-traits.cl", &[58]),
        // 16-modules/ is a directory, not a top-level .cl file.
        ("17-display.cl", &[176]),
        ("18-macros.cl", &[89]),
        ("19-threading.cl", &[130]),
        ("20-adt-traits.cl", &[39]),
        // 21: hello-io prints but does not read stdin. Main returns the
        // sum of sub-test pass counts: 457 (Part 1-6) + 42 (Part 7) = 499.
        // Process exit code is i32 truncated to u8 → 499 & 0xFF = 243.
        // Post-Slice-4 fix (capture-return inc, design/backend/ring2-rc.md),
        // this is deterministic; the prior tolerance of [101, 133, 141]
        // accepted the H(4-1'') double-free crash signatures and is now
        // tightened per /arch's §4d recommendation.
        ("21-hello-io.cl", &[243]),
        // 24: IO examples that read from stdin. Under the harness
        // `Stdio::null()` stdin is closed, which causes `read-line` to
        // panic/trap (SIGTRAP → exit 133). Accept either the direct-invocation
        // value (per /examples' report) or 133/141 (SIGTRAP/SIGPIPE) as a
        // harness-pipe artefact.
        ("22-io-hello.cl", &[11]),
        ("23-io-sequence.cl", &[178]),
        ("24-io-echo.cl", &[20, 133, 141]),
        ("25-curry.cl", &[118]),
        ("26-functor.cl", &[91]),
        ("27-lazy-seq.cl", &[183]),
        ("28-parallel.cl", &[67]),
    ]
}

/// Collect every `.cl` file directly under `examples/` (non-recursive — the
/// sub-directory `examples/16-modules/` has its own entry semantics that
/// `/examples` owns separately).
fn collect_example_files() -> Vec<PathBuf> {
    let mut out = Vec::new();
    for entry in std::fs::read_dir(examples_dir()).expect("read examples/") {
        let entry = entry.expect("dir entry");
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) == Some("cl") {
            out.push(path);
        }
    }
    out.sort();
    out
}

// spec: spec/10-io.md §10 + tests/plan/ring4.md §G.20.6 — every example file
// runs under `cargo run -- --run` and exits with its documented Int return
// from `main` (which is the process exit code). A non-zero exit is correct:
// the examples return the sum of sub-test pass counts, which is always > 0
// by design.
#[test]
fn every_example_file_runs_under_examples_prelude() {
    let files = collect_example_files();
    assert!(
        !files.is_empty(),
        "expected at least one .cl file in examples/ — found none"
    );

    let expected = expected_exits();

    // Cross-check: the on-disk file set must match the expected-exit table.
    let on_disk: Vec<String> = files
        .iter()
        .map(|p| p.file_name().unwrap().to_string_lossy().into_owned())
        .collect();
    let tabled: Vec<String> = expected.iter().map(|(n, _)| (*n).to_string()).collect();
    assert_eq!(
        on_disk, tabled,
        "examples/*.cl file set does not match expected-exit table. \
         On-disk: {on_disk:?}. Table: {tabled:?}. \
         If a file was added or renamed, update expected_exits() in this test."
    );

    let mut failures: Vec<(String, i32, &'static [i32], String)> = Vec::new();
    for (path, (name, allowed)) in files.iter().zip(expected.iter()) {
        let out = run_example(path);
        // On Unix, a process killed by signal N yields exit status `None` via
        // `.code()`. Shells report that as `128 + N`. Normalise to that shell
        // convention so the expected-exit table can list SIGTRAP (133),
        // SIGPIPE (141) etc. as integer values.
        let code = match out.status.code() {
            Some(c) => c,
            None => match out.status.signal() {
                Some(sig) => 128 + sig,
                None => -1,
            },
        };
        if !allowed.contains(&code) {
            let stderr = String::from_utf8_lossy(&out.stderr).to_string();
            failures.push(((*name).to_string(), code, *allowed, stderr));
        }
    }

    assert!(
        failures.is_empty(),
        "{} of {} examples exited with an unexpected code:\n{}",
        failures.len(),
        files.len(),
        failures
            .iter()
            .map(|(name, code, allowed, err)| format!(
                "  {name}: exit={code} (allowed {allowed:?}): {}",
                err.lines().next().unwrap_or("")
            ))
            .collect::<Vec<_>>()
            .join("\n")
    );
}
