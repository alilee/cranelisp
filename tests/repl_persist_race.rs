//! Sprint 64 Wave 6 batch 2 Part B carry-forward — Heisenbug + H5 gate
//! race-shape regression cluster.
//!
//! Per the Wave 6 batch 2 audit (`tests/plan/wave-6-batch-2-audit.md` §7),
//! these 4 tests are race-shape regression probes that pin specific
//! Sprint 58/59/61 concurrency defects. They are intentionally subprocess
//! stress / scheduler-trace tests; the empirical calibration constants
//! (THREADS=6, ITERS=2, TRIALS=10, TIMEOUT=15s, STRESS_ITERATIONS=20) were
//! tuned against documented per-trial fire-rates and are preserved
//! verbatim from `tests/sprint23.rs`. See the per-test comments for the
//! calibration rationale.
//!
//! Mode: subprocess-driven via `Command::new(binary_path())` rather than
//! the `Cranelisp` builder. Reasons:
//!   - The reduced heisenbug repro spawns N concurrent OS threads, each
//!     driving its own subprocess pair against its own `TempDir`. The
//!     thread-spawn shape sits cleanly on the `binary_path`/`Command`
//!     primitives without re-introducing internal-API helpers.
//!   - The H5 gate test depends on `CRANELISP_SCHEDULER_TRACE=1` and
//!     parses `[SCH]` event lines on stderr — finer-grained than the
//!     `Cranelisp::env(...)` + `assert_stderr_contains(...)` loop, but
//!     directly expressible as raw subprocess work.
//!   - The H5 starvation test polls `child.try_wait()` against a
//!     deadline — outside the harness's fire-and-block timeout shape.
//!
//! Spec anchors:
//!   - `design/int/dual-path-persistence-collapse.md §7` — heisenbug repro
//!     (the migration plan step 7 50-loop loop-repro).
//!   - `design/int/heisenbug-race-closure.md §3b` — reduced repro
//!     calibration (N=6, K=2, 10 trials).
//!   - `design/int/s77-int-restructure.md §3.5` — the S60–S62 heisenbugs
//!     (incl. H5) cannot recur once in-progress cluster state is stack-local.
//!     The H5-replay gate + the regrounded liveness/positive-outcome tests
//!     EVIDENCE this observable parity property (they no longer probe the
//!     `eval_in_flight`/`EvalInFlightGuard`/`module_sexps` internals that the
//!     Sprint 78 OQ-3 restructure deletes — see the per-test reground notes).
//!
//! Sprint 78 Wave 1 regrounding (plan §1/§4): the three previously
//! mechanism-pinned tests were regrounded to observable outcomes BEFORE /dev
//! touches the source, so the suite stops referencing the soon-deleted
//! internals up front:
//!   - `h5_gate_typechecking_user_fires_only_on_repl_thread` (parsed `[SCH]`
//!     for the `eval_in_flight`-suppressed push) → RETIRED, subsumed by
//!     `h5_replay_gate_deterministic_under_scheduler_stress` (observable
//!     determinism under scheduler-trace stress; gates the OQ-3 deletion).
//!   - `h5_normal_completion_does_not_starve_repl_eval_thread` (RAII
//!     `EvalInFlightGuard` Drop) → `h5_normal_completion_liveness_yields_dep_value`
//!     (terminates + yields 42).
//!   - `repl_dep_load_no_race_with_persistent_workers` (absence of the
//!     `module_sexps`-produced "no parsed sexps" string) → positive
//!     Cons-list-result assertion (strictly stronger).
//!
//! Race rate notes (from ledger):
//!   - `cache_repl_loads_heisenbug_parallel_stress` — RESOLVED by H5 fix
//!     (Sprint 61 Wave 3 step 3e'); passes 58/59 in full sprint23 suite.
//!   - `heisenbug_race_reduced_concurrent_import_pairs` — H5 closed,
//!     H6 ALSO fixed; ledger documents residual H6/H7 surface fires
//!     ~5–10% under `--test-threads=6` after H6 fix. Test is the
//!     active regression surface; failures here may indicate H7
//!     residue rather than an H5 regression.
//!
//! Per the failing-not-ignored rule (`memory/feedback_failing_not_ignored.md`),
//! intermittent failures of `heisenbug_race_reduced_concurrent_import_pairs`
//! are the regression guard themselves and the H6/H7 evidence anchor — do
//! NOT `#[ignore]` to silence them.

use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

#[path = "helpers/e2e.rs"]
mod e2e;
use e2e::{Cranelisp, PreludeVariant};

fn project_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn binary_path() -> PathBuf {
    project_root().join("target").join("debug").join("cranelisp")
}

fn stdout_str(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}

fn stderr_str(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

/// Run the REPL binary with piped stdin, an isolated CWD, and the test
/// fixtures directory exposed via `CRANELISP_LIB`.
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
        stdin
            .write_all(input.as_bytes())
            .expect("failed to write input");
    }
    child.wait_with_output().expect("failed to read output")
}

// =============================================================================
// 1. Heisenbug parallel-stress repro (Sprint 58/59 dual-path collapse loop)
// =============================================================================

// spec: design/int/dual-path-persistence-collapse.md §7 — migration plan
//   step 7 (heisenbug verification: 50-loop loop-repro). The dual-path
//   persistence collapse design explicitly names the ~1755/1754 heisenbug
//   observed at Sprint 58 close as the structural symptom of two
//   orchestrators working on the same module simultaneously. Under the
//   collapsed path this loop MUST be rock-solid; before the collapse this
//   test was expected to flake.
//
//   Disposition (see crate ledger entry): RESOLVED — passes 58/59 in
//   the full sprint23 suite at SHA `35062ca` after the H5 scheduler-side
//   worker-claim suppression fix landed. The reduced harness
//   (`heisenbug_race_reduced_concurrent_import_pairs` below) is now the
//   active regression surface for the residual H6/H7 data-plane race.
//
//   Inline `FIXME(/int)` from the legacy file (Sprint 59 Workstream A)
//   migrated to `design/arch/fixmes/0145-sprint23-heisenbug-stress-fixme.md`
//   with the Sprint-59 narrative preserved.
//
// (carry: legacy/sprint23.rs::cache_repl_loads_heisenbug_parallel_stress)
#[test]
fn cache_repl_loads_heisenbug_parallel_stress() {
    // Repeat the persist_import_survives_restart sequence N times in a loop,
    // relying on nextest's own --test-threads parallelism to apply scheduling
    // pressure to the scheduler-side vs session-side dep-registration paths.
    //
    // Under the collapsed path (Sprint 59 Workstream A), there is ONE
    // orchestrator per module, so this loop is correct-by-construction. If
    // this test flakes, §9 Risk 1 is active: a sixth collapse surface has
    // been missed.
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

// =============================================================================
// 2. Reduced concurrent-import-pairs heisenbug repro (Wave 3 step 3a)
// =============================================================================

// spec: design/int/heisenbug-race-closure.md §3b — reduced-shape repro
//   (Sprint 61 Wave 3 step 3a). N=6 concurrent threads, K=2 sequential
//   pairs per thread, 10 trials, fast-fail on first reproduction.
//
//   Disposition (see crate ledger entry): H5 closed (Wave 3 step 3e'),
//   H6 closed (Wave 3 step 3e''). Residual H6/H7 surface fires
//   ~5–10% under `--test-threads=6` after H6 fix; carried as active
//   regression surface to S62. Per the failing-not-ignored rule, do
//   NOT `#[ignore]` — the test IS the residue evidence anchor.
//
//   Inline `FIXME(/int)` from the legacy file (Sprint 61 Wave 3 step 3e)
//   migrated to `design/arch/fixmes/0146-sprint23-heisenbug-reduced-fixme.md`
//   preserving the calibration narrative.
//
// (carry: legacy/sprint23.rs::heisenbug_race_reduced_concurrent_import_pairs)
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
// 3. H5-replay gate (load-bearing — gates OQ-3 `eval_in_flight` guard deletion)
// =============================================================================

// spec: design/int/s77-int-restructure.md §3.5 — the S60–S62 heisenbugs
//   (incl. H5) cannot recur once in-progress cluster state is stack-local.
//   This test EVIDENCES that soundness claim (it does not assert the
//   mechanism): it replays the H5 two-input shape under CRANELISP_SCHEDULER_
//   TRACE stress and proves the OBSERVABLE outcome (import + call → 99) is
//   deterministic across the iteration budget.
//
// Gating relationship (Sprint 78 plan §1 / gate-map §5):
//   * BEFORE the OQ-3 guard deletion (Step 3): MUST be green with the
//     `eval_in_flight` guard still present — this establishes the baseline
//     the deletion must preserve.
//   * AFTER Step 3 deletes the guard: MUST stay green. Green-here-too is the
//     soundness evidence that the guard's reason-for-being evaporated. If this
//     test ever fails post-deletion, OQ-3 is WRONG and Step 3 must revert.
//
// "Flaky" is a banned disposition on this project (feedback_failing_not_ignored,
// feedback_repros_join_suite). Determinism = ZERO failures across all
// iterations: no N-of-M tolerance, no retry. A single iteration without `99`
// fails the test loudly with the iteration index + the captured `[SCH]` stream.
//
// This test SUBSUMES the retired mechanism-probing
// `h5_gate_typechecking_user_fires_only_on_repl_thread`: that test parsed
// `[SCH]` events to assert the `eval_in_flight`-suppressed worker-queue-push
// signature — a mechanism Step 3 deletes (no flag to gate, the `[SCH]`
// signature may legitimately change shape). The observable-outcome assertion
// here is the durable H5 guard; the mechanism probe regrounds into it.
//
// Iteration count (50) calibration (Sprint 78 plan §1): one subprocess per
// iteration (lighter than the 2-session cache-delete shape of
// `cache_repl_loads_heisenbug_parallel_stress` at 20 iter). 50 is a
// structural-reopening tripwire, not statistical proof — the historical H5
// flake was ~1/1755. Measured wall-time in isolation is recorded in the
// Wave 1 report; if it ever threatens the <30s /qa suite budget, reduce to
// the largest count that stays well under and note it here.
#[test]
fn h5_replay_gate_deterministic_under_scheduler_stress() {
    // 50 fresh-tmpdir subprocesses, each under CRANELISP_SCHEDULER_TRACE=1.
    // The trace plumbing changes timing — running UNDER the trace IS the
    // stress condition the soundness obligation names (plan §1). On any
    // failure the captured `[SCH]` stderr stream is dumped for diagnosis.
    const ITERATIONS: usize = 50;

    for iteration in 0..ITERATIONS {
        // Fresh Cranelisp builder + tmpdir per iteration (the builder is
        // single-shot; fresh tmpdir is the isolation discipline from
        // tests/CLAUDE.md §"Fresh Temp Directory per Test").
        //
        // PreludeVariant::None: the import + bare-call shape needs only the
        // helper module; no operators are load-bearing (reduction discipline
        // — plan §1 prefers None if it reproduces, and it does).
        let out = Cranelisp::new()
            .repl()
            .with_prelude(PreludeVariant::None)
            .file("helper.cl", "(defn helper-val [] 99)")
            .env("CRANELISP_SCHEDULER_TRACE", "1")
            .stdin(
                "(import [helper [helper-val]])\n\
                 (helper-val)\n\
                 /quit\n",
            )
            .output();

        assert!(
            out.stdout.contains("99"),
            "H5-replay gate FAILED at iteration {iteration}/{ITERATIONS}: the \
             two-input import sequence did not produce 99. This is the H5 race \
             re-surfacing — if it fires AFTER the OQ-3 guard deletion (Step 3), \
             OQ-3 is wrong and Step 3 must revert (design/int/\
             s77-int-restructure.md §3.5).\n\
             === stdout ===\n{}\n=== [SCH] stderr stream ===\n{}",
            out.stdout, out.stderr
        );
    }
}

// =============================================================================
// 4. H5 normal-completion liveness — import + call terminates and yields its
//    value (REGROUNDED from RAII-guard mechanism to observable liveness)
// =============================================================================

// spec: design/int/s77-int-restructure.md §3.5 — in-call-stack cluster state
//   is stack-local, so the normal import→call→complete path neither races nor
//   stalls. This test EVIDENCES the observable property that matters to the
//   user: the import + call subprocess TERMINATES (does not hang) and yields
//   the dependency's value (42). It does NOT probe the `EvalInFlightGuard`
//   RAII mechanism — that guard deletes in OQ-3 Step 3, so an assertion on it
//   would break the build the moment /dev lands the deletion. The liveness +
//   value outcome holds today AND after the deletion.
//
// Regrounded in Sprint 78 Wave 1 (plan §4 item 2): the prior version asserted
// the same observable outcome but justified the timeout via `EvalInFlightGuard`
// Drop correctness + `eval_in_flight` flag leakage. Those internals are gone in
// Step 3; the observable property (terminates + 42) is the durable guard.
//
// (carry: legacy/sprint23.rs::h5_normal_completion_does_not_starve_repl_eval_thread)
#[test]
fn h5_normal_completion_liveness_yields_dep_value() {
    use std::time::Duration;

    // 15-second ceiling. The assertion only needs to distinguish "completed"
    // from "hung indefinitely": a regression that re-introduces a stall on the
    // normal-completion path surfaces as a Timeout, not an infinitely-hanging
    // test. 15 s is far above typical completion (~0.3–0.8 s observed) and
    // half the tests/CLAUDE.md per-test 30 s cap. The `Cranelisp` builder's
    // `.timeout(...)` enforces it: on breach, `.output()` panics with
    // `CrError::Timeout` (the builder kills the child first), which IS the
    // liveness-failure signal.
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::None)
        .file("helper.cl", "(defn helper-val [] 42)")
        .stdin(
            "(import [helper [helper-val]])\n\
             (helper-val)\n\
             /quit\n",
        )
        .timeout(Duration::from_secs(15))
        .output();

    // The import + call must have executed and yielded 42. If it did not,
    // the normal-completion path produced a wrong/missing value.
    assert!(
        out.stdout.contains("42"),
        "H5 normal-completion liveness: import + call did not yield \
         helper-val=42. The normal completion path must terminate AND produce \
         the dependency's value (design/int/s77-int-restructure.md §3.5).\n\
         === stdout ===\n{}\n=== stderr ===\n{}",
        out.stdout, out.stderr
    );
}

// =============================================================================
// Sprint 64 Wave 6 batch 5 — Defect 1: REPL dep-load race in compile_dep_inline
// =============================================================================
//
// Per /int Wave 6 FIXME #3 diagnosis (Sprint 58 Wave 6 demo finding):
//   src/session_v4.rs::compile_dep_inline registered a dep with the
//   scheduler BEFORE publishing dep_sexps to shared.module_sexps.
//   Persistent priority workers (Sprint 57 W4) wake on the scheduler
//   notify, dequeue Typecheck(<dep>), find no parsed sexps, and emit
//   "no parsed sexps for module '<dep>'". The REPL's REPL-import + bare
//   call shape consistently triggered the race when --priority-workers
//   was raised to 4.
//
// Spec anchor: implicit Principle 11 (REPL and --run produce the same
// semantics). Defects per root CLAUDE.md "Defects" §1: REPL/--run
// divergence is a defect.
//
// REGRESSION-GUARD: Sprint 58 Wave 6 Defect 1 — race resolved post-S58 W6;
// this test is the durable record. Owning skill /int (session_v4
// dep-load ordering invariant).
// (carry: legacy/wave6_demo_repros.rs::repl_dep_load_no_race_with_persistent_workers)

// spec: repl/spec.md §0.2 — Run Mode parity: REPL `(import ...)` of a
//       stdlib module MUST produce the same outcome as the equivalent
//       `--run` invocation (root CLAUDE.md "Defects" §1 — REPL/--run
//       divergence is a defect)
//
// REGROUNDED in Sprint 78 Wave 1 (plan §4 item 3): the prior version asserted
// the ABSENCE of the error string "no parsed sexps for module" — a symptom
// produced by the `module_sexps` shared map when a worker dequeued a Typecheck
// task before the dep's sexps were published. Step 2 deletes `module_sexps`,
// so that error string can no longer be produced and a "wrong-string-absent"
// assertion becomes vacuously true (guards nothing). Regrounded to assert the
// POSITIVE observable outcome: the import + constructor call produces a
// successful Cons-list result. This is strictly stronger than absence-of-
// symptom and survives the map deletion.
#[test]
fn repl_dep_load_no_race_with_persistent_workers() {
    use std::io::Write;

    // Setup: an isolated project root with the repo stdlib symlinked in.
    // Drive the REPL with `--priority-workers 4` so multiple persistent
    // workers wake on the scheduler notify — the configuration that
    // consistently triggered the dep-load race per /int's FIXME #3 diagnosis.
    let td = tempfile::tempdir().expect("create tempdir");
    let cwd = td.path();
    let proj_stdlib = cwd.join("stdlib");
    if !proj_stdlib.exists() {
        #[cfg(unix)]
        std::os::unix::fs::symlink(project_root().join("stdlib"), &proj_stdlib).unwrap();
        #[cfg(not(unix))]
        std::fs::create_dir_all(&proj_stdlib).unwrap();
    }

    // The REPL imports a stdlib module and constructs a value from it — the
    // same dep-load shape /repl saw in Wave 6 demos.
    let repl_input = "(import [collections.list [Cons Nil]])\n(Cons 1 Nil)\n";

    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} — run `cargo build` first"
    );
    let mut child = Command::new(&binary)
        .current_dir(cwd)
        .args(["--priority-workers", "4"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to start cranelisp binary");
    {
        let stdin = child.stdin.as_mut().expect("failed to open stdin");
        stdin
            .write_all(repl_input.as_bytes())
            .expect("failed to write input");
    }
    let out = child.wait_with_output().expect("failed to read output");

    let stdout = stdout_str(&out);
    let stderr = stderr_str(&out);
    // POSITIVE outcome: the import + `(Cons 1 Nil)` constructor call resolves
    // and produces a Cons-list result. The REPL self-documenting display shows
    // the constructed value's type/value; a successful run names `Cons`.
    assert!(
        stdout.contains("Cons"),
        "REPL dep-load: (import [collections.list [Cons Nil]]) followed by \
         (Cons 1 Nil) under --priority-workers 4 did NOT produce a successful \
         Cons-list result. Under the in-call-stack dep-drive (Sprint 78) the \
         dep's sexps never leave the processing worker's stack frame, so a \
         persistent worker cannot observe a half-published module. A failure \
         here is a real dep-load-ordering regression.\n\
         === stdout ===\n{stdout}\n=== stderr ===\n{stderr}"
    );
}
