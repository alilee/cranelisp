//! Sprint 64 Wave 6 batch 1 carry-forward — examples `--run` umbrella.
//!
//! (carry: legacy/examples.rs + legacy/examples_run.rs umbrella)
//!
//! This is the canonical regression-guard for `examples/*.cl` programs.
//! Per the Wave 6 batch 1 audit (tests/plan/wave-6-batch-1-audit.md),
//! the 15 row-tests in `legacy/examples.rs` were strictly subsumed by
//! `legacy/examples_run.rs`'s 27-row subprocess umbrella; the new shape
//! adopts that umbrella + on-disk parity guard + signal-aware exit
//! normalisation as a single table-driven test.
//!
//! Per `examples/README.md` rule (cited inline in the legacy file):
//! a non-zero `main` Int return is the program's exit code, and the
//! integer is the sum of in-program sub-test pass counts. The exit
//! checksum is therefore the regression-guard surface — if compilation
//! or codegen regresses for any sub-test, the example's exit drops to
//! a smaller integer.
//!
//! Subprocess-driven (Command + current_dir) rather than the `Cranelisp`
//! builder because each example must run with `examples/` as cwd so
//! the example's `Cranelisp.toml` + local `lib/` are discovered. The
//! builder's per-test fresh TempDir is the wrong cwd for this shape.
//! That makes this file a deliberate exception to the "use the builder"
//! convention (Wave 1's pure-quarantine pattern of preserving subprocess
//! shape applies here too).
//!
//! FIXME(/spec): the "non-zero exit = sub-test pass count" convention is
//! documented only in `examples/plan-examples.md` (an /examples plan
//! doc), not in any spec/*.md file. The convention is a project-level
//! testing pattern, not a language-level normative requirement.

use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::Once;

fn project_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn binary_path() -> PathBuf {
    project_root().join("target").join("debug").join("cranelisp")
}

fn examples_dir() -> PathBuf {
    project_root().join("examples")
}

/// Absolute `<repo>/target/debug` — the platform search path (Tier-3,
/// `CRANELISP_PLATFORM_PATH`). `resolve_platform_path`'s `check_dir` resolves
/// cargo's `libcranelisp_{name}.{ext}` artifacts here directly, so the IO
/// examples (`21`-`24`) find `stdio` / `test-capture` with zero symlinks,
/// `cfg`-correct on every OS. Mirrors the `use_workspace_platforms()` helper
/// in `tests/helpers/e2e.rs` (which sets the same env for the platform e2e
/// tests). Replaces the dead `examples/platforms/*.dylib` symlink discovery.
fn platform_search_path() -> PathBuf {
    project_root().join("target").join("debug")
}

/// No-op: the platform cdylibs/rlibs are built suite-wide by the nextest setup
/// script (`tests/scripts/build-link-prereqs.sh`), the single owner of that
/// artifact-set invariant (`tests/CLAUDE.md` §"`--link` prerequisites" — "A test
/// MUST NOT shell out to `cargo build`").
///
/// The former per-test `cargo build -p cranelisp-stdio -p cranelisp-test-capture`
/// band-aid is RETIRED: under the single-ABI cutover it rebuilt the platform
/// rlib against a `cranelisp-platform` variant resolved over a different
/// dep-subgraph than the setup script's, yielding a mismatched crate
/// disambiguator that broke concurrent `--link` tests with `undefined reference`
/// errors. The setup script builds a profile-consistent artifact set once.
fn ensure_platform_cdylibs_built() {
    // qa-ratified S96 B1: the A4c neutralization is sound — no coverage hole. The
    // platforms this helper formerly built (stdio, test-capture) are both in
    // `tests/scripts/build-link-prereqs.sh`'s single `cargo build -p …` (9
    // platforms incl. them), so the IO examples (21-24) still resolve their DLLs;
    // the call sites are preserved (inert) so the structure reads unchanged. The
    // forbidden per-test `cargo build` band-aid (which broke parallel `--link`
    // with mismatched crate disambiguators under the single-ABI cutover) is gone.
    // Intentionally empty — see the doc comment above. The setup script owns it.
    static BUILT: Once = Once::new();
    BUILT.call_once(|| {});
}

fn run_example(path: &Path) -> Output {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} — run `cargo build` first"
    );
    ensure_platform_cdylibs_built();
    Command::new(&binary)
        .args(["--run", path.to_str().unwrap()])
        // Put target/debug on the platform search path so the IO examples
        // resolve `libcranelisp_{stdio,test-capture}.{ext}` directly.
        .env("CRANELISP_PLATFORM_PATH", platform_search_path())
        .current_dir(examples_dir())
        // Null stdin so the stdin-reading example `24-io-echo` is
        // deterministic (it lands on exit 20 with closed stdin).
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("failed to run cranelisp")
}

/// Expected exit-code table — one entry per top-level `examples/*.cl`.
/// Carried forward verbatim from `legacy/examples_run.rs::expected_exits`
/// (the more recent, more comprehensive version per audit recommendation A).
/// `16-modules` is a sub-directory, not a top-level file, so it is absent.
fn expected_exits() -> Vec<(&'static str, &'static [i32])> {
    vec![
        ("01-integers.cl", &[69]),
        ("02-booleans.cl", &[5]),
        ("03-let-bindings.cl", &[97]),
        ("04-functions.cl", &[135]),
        ("05-recursion.cl", &[111]),
        ("06-enums.cl", &[104]),
        ("07-polymorphism.cl", &[119]),
        ("08-floats.cl", &[10]),
        ("09-strings.cl", &[55]),
        ("10-adts.cl", &[9]),
        ("11-destructuring.cl", &[69]),
        ("12-closures.cl", &[7]),
        ("13-higher-order.cl", &[203]),
        // 14: vecs. S101 6b added a vec-ops-as-values section (one
        // instantiation per HOF per FIXME 0483); sum of sub-test pass
        // counts 29 → 81.
        ("14-vecs.cl", &[81]),
        ("15-traits.cl", &[58]),
        // 16-modules/ is a directory, not a top-level .cl file.
        ("17-display.cl", &[176]),
        ("18-macros.cl", &[89]),
        ("19-threading.cl", &[130]),
        ("20-adt-traits.cl", &[39]),
        // 21: hello-io prints but does not read stdin. Sum-of-pass-counts
        // = 499; truncated to u8 by process exit = 243.
        ("21-hello-io.cl", &[243]),
        ("22-io-hello.cl", &[99]),
        ("23-io-sequence.cl", &[178]),
        // 24: read-line on closed (null) stdin lands on exit 20. With the
        // platform search path wired (`CRANELISP_PLATFORM_PATH=target/debug`)
        // + stdin nulled in `run_example`, the run is a clean 20. The old
        // 133/141 (SIGTRAP/SIGPIPE) were artifacts of the symlink-era harness.
        ("24-io-echo.cl", &[20]),
        ("25-curry.cl", &[118]),
        ("26-functor.cl", &[91]),
        ("27-lazy-seq.cl", &[183]),
        ("28-parallel.cl", &[67]),
        // 29: type annotations (:Type binds the following form). Sum of
        // sub-test pass counts = 42 + 42 + 11 + 7 + 17 = 119.
        ("29-annotations.cl", &[119]),
        // 30: self-parallelising map-reduce (lenient eval). main returns
        // 8 * fib(38) / 1_000_000 = 312; process exit truncates to u8 => 56.
        ("30-parallel-map-reduce.cl", &[56]),
        // 31: bitwise integer operations. main returns the sum of sub-test
        // pass counts = 19 → exit 19.
        ("31-bitwise.cl", &[19]),
        // 32: explicit-control concurrency combinators (race / select / sleep +
        // the inline timeout pattern). main returns the sum of 6 sub-test pass
        // counts = 6 → exit 6.
        ("32-concurrency-combinators.cl", &[6]),
        // 33: redefinition (batch-observable rebind semantics; S101 6b).
        // Sum of sub-test pass counts = 136 — a normal exit(136), NOT a
        // 128+signal encoding: `ExitStatus::code()` returns Some(136) for a
        // normal exit, so the harness observes 136 directly (verified
        // round-tripping through run_example at authoring, 2026-07-03).
        ("33-redefinition.cl", &[136]),
        // 34: async-io platform-leaf demo (poll-shape reactor via the
        // `async-demo` DLL, built suite-wide by build-link-prereqs.sh; the
        // harness sets CRANELISP_PLATFORM_PATH=target/debug). main returns the
        // sum of sub-test pass counts = 4 → exit 4 (verified by /examples on the
        // direct run and reproduced under the harness, 2026-07-10).
        ("34-async-io-leaf.cl", &[4]),
    ]
}

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

// spec: examples/plan-examples.md §"Learning Sequence Design" (sub-test
//       exit-code convention is a project-level testing pattern; FIXME(/spec)
//       above flags lack of normative spec for it). Each example's `main`
//       returns the sum of its sub-test pass counts; that integer IS the
//       process exit code per spec/10-io.md §10.
//
// (carry: legacy/examples.rs::example_NN_* x15 + legacy/examples_run.rs::every_example_file_runs_under_examples_prelude)
#[test]
fn every_example_runs_with_documented_exit() {
    let files = collect_example_files();
    assert!(
        !files.is_empty(),
        "expected at least one .cl file in examples/ — found none"
    );

    let expected = expected_exits();

    // Cross-check: the on-disk file set MUST match the expected-exit table.
    // Catches added/renamed examples that would silently bypass the umbrella.
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
        // Normalise signal-killed status to 128 + signal so the table can
        // list SIGTRAP/SIGPIPE etc. as integer values.
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

// =============================================================================
// 0337 CI-coverage corrective — multi-file DIRECTORY example
//
// The `every_example_runs_with_documented_exit` umbrella above only covers
// top-level single-file `examples/*.cl`; it explicitly EXCLUDES `16-modules/`
// ("a directory, not a top-level .cl file"). That exclusion is exactly why the
// multi-file module-resolution breakage behind FIXME 0337 sailed through every
// per-crate sweep undetected — there was ZERO CI coverage for a multi-file
// directory project run end-to-end.
//
// This test closes that gap with a self-contained NESTED multi-file project
// (per §8.2.5 nested-only resolution, ruled by FIXME 0345). It is intentionally
// NOT coupled to `examples/16-modules/` — that example is not yet relaid out to
// the nested shape (a Phase-6 /examples task), so coupling to it would make
// this guard depend on user-proxy churn. A self-contained `tempfile::TempDir`
// nested fixture is the durable, decoupled regression guard per
// tests/CLAUDE.md §"Repros live in tests/, not exemplar/ or examples/".
//
// It is a real, durable CI extension (green, not a failing defect guard): it
// runs a directory-entry program through `--run` and asserts its documented
// exit, so future multi-file-module regressions are caught going forward.
// =============================================================================

// spec: spec/08-modules.md §8.2.5 — a multi-file directory project whose entry
//       declares bare `(mod child)` resolves the NESTED child `{stem}/child.cl`
//       and runs end-to-end. CI coverage corrective for FIXME 0337.
#[test]
fn multi_file_nested_directory_example_runs_with_documented_exit() {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} — run `cargo build` first"
    );

    // Self-contained nested project: entry `main.cl` declares `(mod math)` +
    // `(mod util)`; both resolve to NESTED children under `main/`. main sums
    // their results: (square 5)=25 + (double 4)=8 + literal 0 = 33 → exit 33.
    let td = tempfile::tempdir().expect("TempDir creation");
    let root = td.path();
    std::fs::create_dir_all(root.join("main")).expect("mkdir main/");
    std::fs::write(
        root.join("main.cl"),
        "(import [primitives [Pure add-i64]])\n\
         (mod math)\n\
         (mod util)\n\
         (defn main [] (Pure (add-i64 (math/square 5) (util/double 4))))\n",
    )
    .expect("write main.cl");
    std::fs::write(
        root.join("main").join("math.cl"),
        "(import [primitives [mul-i64]])\n\
         (defn square [x] (mul-i64 x x))\n",
    )
    .expect("write main/math.cl");
    std::fs::write(
        root.join("main").join("util.cl"),
        "(import [primitives [add-i64]])\n\
         (defn double [x] (add-i64 x x))\n",
    )
    .expect("write main/util.cl");

    let out = Command::new(&binary)
        .args(["--run", root.join("main.cl").to_str().unwrap()])
        .current_dir(root)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("failed to run cranelisp");

    // 25 + 8 = 33. The exit code is `main`'s Int return per spec/10-io.md §10.
    let code = out.status.code();
    assert_eq!(
        code,
        Some(33),
        "multi-file nested-directory project should exit 33 (square(5)=25 + \
         double(4)=8); got {code:?}\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );
}
