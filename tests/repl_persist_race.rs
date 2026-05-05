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
//!   - `design/int/heisenbug-race-closure.md §7.7` — H5 gate invariant
//!     (`ModuleStateTypechecking user` fires only on REPL-eval thread).
//!   - `design/int/heisenbug-race-closure.md §7.8` — H5 mechanism
//!     (`eval_in_flight` flag suppresses worker queue push).
//!
//! Race rate notes (from ledger):
//!   - `cache_repl_loads_heisenbug_parallel_stress` — RESOLVED by H5 fix
//!     (Sprint 61 Wave 3 step 3e'); passes 58/59 in full sprint23 suite.
//!   - `heisenbug_race_reduced_concurrent_import_pairs` — H5 closed,
//!     H6 ALSO fixed; ledger documents residual H6/H7 surface fires
//!     ~5–10% under `--test-threads=6` after H6 fix. Test is the
//!     active regression surface; failures here may indicate H7
//!     residue rather than an H5 regression.
//!   - `h5_gate_typechecking_user_fires_only_on_repl_thread` — passes
//!     5/5 post-fix (Wave 3 step 3e' SHA `35062ca`).
//!   - `h5_normal_completion_does_not_starve_repl_eval_thread` — the
//!     RAII guard / `EvalInFlightGuard` Drop correctness regression
//!     guard. Passes at HEAD; would fail (timeout) if the flag leaks.
//!
//! Per the failing-not-ignored rule (`memory/feedback_failing_not_ignored.md`),
//! intermittent failures of `heisenbug_race_reduced_concurrent_import_pairs`
//! are the regression guard themselves and the H6/H7 evidence anchor — do
//! NOT `#[ignore]` to silence them.

use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

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
// 3. H5 gate invariant — `ModuleStateTypechecking user` fires only on REPL thread
// =============================================================================

// spec: design/int/heisenbug-race-closure.md §7.7 — H5 gate invariant
//   (ModuleStateTypechecking `user` fires exactly once per cycle, on the
//   REPL-eval thread, never on a worker thread). Also §7.8 (H5 mechanism:
//   `try_unblock_locked(user)` emits ModuleStateUnblocked on the worker
//   but the subsequent queue push into `typecheck_first` is suppressed by
//   the `eval_in_flight` flag — proving absence of a worker claim of `user`).
//
// Test shape:
//   * Drive a minimal import scenario (one helper module, import + call)
//     through a single subprocess with CRANELISP_SCHEDULER_TRACE=1 so the
//     full scheduler event stream is dumped to stderr on exit. The minimal
//     shape (1 session, 1 iteration) is deterministic — the H5 gate should
//     always hold for the import path, race or no race.
//   * Parse the `[SCH]` event lines on stderr.
//   * Walk `Blocked user` (REPL-eval-thread) → matching `Unblocked user`
//     (worker thread) → ensure no subsequent `Typechecking user` fires on
//     the same worker thread before another `Blocked user` resets the cycle.
//
// Passes at HEAD (H5 fix landed in Wave 3 step 3e'). Would fail pre-fix
// (two `ModuleStateTypechecking module=user` events — one on t1, one on
// t2 from the worker claim of the unblocked caller).
//
// (carry: legacy/sprint23.rs::h5_gate_typechecking_user_fires_only_on_repl_thread)
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
    // The H5-pinning signature is:
    //   * A worker thread emits `ModuleStateUnblocked module=user` (inside
    //     `try_unblock_locked` from `notify_typecheck_done(helper)`).
    //   * The SAME worker thread IMMEDIATELY afterwards pops `user` from
    //     `typecheck_first` and emits `ModuleStateTypechecking module=user`
    //     (the worker claim of the unblocked caller).
    // Post-fix, the second event must NOT appear on that same thread —
    // the `eval_in_flight` flag suppresses the queue push so the worker
    // has nothing to pop.
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
                     §7.7/§7.8). The `eval_in_flight` gate is not \
                     suppressing the worker claim of `user` inside \
                     `try_unblock_locked`.\nEvents:\n{events:#?}\n\
                     Full stderr:\n{stderr}"
                );
            }
        }
    }
}

// =============================================================================
// 4. H5 starvation safety — RAII guard correctness on normal completion path
// =============================================================================

// spec: design/int/heisenbug-race-closure.md §7.8 — `eval_in_flight` flag
//   is armed at the top of `register_dep_for_eval` and must be cleared on
//   function exit (normal AND panic) via `EvalInFlightGuard`'s `Drop`. If
//   the flag leaked — e.g., because Drop semantics broke, or a panic path
//   bypassed the guard — `try_unblock_locked(caller)` would suppress the
//   queue push indefinitely, and the REPL eval thread's retry loop would
//   hang waiting for a typecheck push that never arrives.
//
// This test exercises the NORMAL completion path (a dep that completes
// cleanly, no forced race). The subprocess must finish within a
// reasonable timeout — hanging means the flag leaked. The test is
// asserting ABSENCE of the starvation failure mode, not presence of any
// specific event.
//
// Passes at HEAD. Would fail (timeout) if the flag leaks.
//
// (carry: legacy/sprint23.rs::h5_normal_completion_does_not_starve_repl_eval_thread)
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
    // 15 s is ~30x typical worst-case observed, 0.5x the tests/CLAUDE.md
    // per-test 30 s cap, and still sharply distinguishes "completed" from
    // the real starvation failure mode (an infinite block on
    // `wait_module_inmem_complete_blocking`'s condvar). A 15 s breach
    // genuinely signals a leaked flag, not a busy machine.
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
                         design/int/heisenbug-race-closure.md §7.8 RAII guard \
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
