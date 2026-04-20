//! Sprint 58 Wave 6 — failing integration tests for demo-surfaced defects.
//!
//! Per the project-wide principle in root `CLAUDE.md` §"Usability Findings
//! and Defects": user-proxy skills (`/repl`, `/port`) are NOT finished
//! when they discover defects. Documentation alone is not closure for a
//! defect; a failing test is the durable record + the trigger for the
//! owning compiler skill to resolve.
//!
//! This file captures the seven defects surfaced by `/repl` and `/port`
//! during Sprint 58 Wave 6 demos. Each test:
//!
//! - Fails (intentionally — failing tests are the durable record per
//!   `feedback_failing_not_ignored.md`)
//! - Carries a `// spec:` annotation naming the section of the spec the
//!   defect violates
//! - Carries a `FIXME(/owning-skill)` note pointing to the resolver
//! - Has a name that describes the spec violation, not the implementation
//!   bug
//!
//! Defects 4 + 5 (html and form `/run-tests` batched crashes) collapse
//! into a single narrow reproduction (`run_tests_batched_invocation_no_crash`)
//! because both manifest the same shape: discovering a list of tests and
//! executing them in sequence segfaults/traps. The owning skill resolves
//! the underlying RC/codegen issue once.
//!
//! Defect 7 (three puzzle tests body-disabled in exemplar/solver.cl)
//! folds into Defect 6: the durable record is the narrow segfault repro
//! for the solver. Re-enabling the puzzle tests in exemplar/solver.cl
//! is `/port`'s acceptance criteria once Defect 6 is fixed.

#[path = "helpers/mod.rs"]
mod helpers;

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

// ---------------------------------------------------------------------------
// Subprocess helpers (mirror the conventions in tests/v4_repl_eval.rs)
// ---------------------------------------------------------------------------

static TEST_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn project_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn binary_path() -> PathBuf {
    project_root().join("target").join("debug").join("cranelisp")
}

fn stdlib_dir() -> PathBuf {
    project_root().join("stdlib")
}

/// Allocate an isolated working directory for one subprocess test under
/// `tests/wave6_demo_repros/.runs/{timestamp}/`.
fn isolated_dir(label: &str) -> PathBuf {
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
        .join("wave6_demo_repros")
        .join(".runs")
        .join(&*RUN_TS)
        .join(format!("{n}_{label}"));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Run the cranelisp binary with the given args, piped stdin, in `cwd`.
fn run_binary(cwd: &Path, args: &[&str], stdin_input: &str) -> Output {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} -- run `cargo build` first"
    );

    let mut child = Command::new(&binary)
        .current_dir(cwd)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to start cranelisp binary");

    {
        use std::io::Write;
        if let Some(stdin) = child.stdin.as_mut() {
            stdin
                .write_all(stdin_input.as_bytes())
                .expect("failed to write input");
        }
    }
    child.wait_with_output().expect("failed to read output")
}

fn stdout_str(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}

fn stderr_str(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

// =============================================================================
// Defect 1 — REPL dep-load race in compile_dep_inline
// =============================================================================
//
// Per /int Wave 6 FIXME #3 diagnosis:
//   src/session_v4.rs:1938-1982 compile_dep_inline registers a dep with
//   the scheduler at line 1943 BEFORE publishing dep_sexps to
//   shared.module_sexps. Persistent priority workers (Sprint 57 W4) wake
//   on the scheduler notify, dequeue Typecheck(<dep>), hit
//   worker.rs:3320-3328, find no parsed sexps, and emit
//   "no parsed sexps for module '<dep>'" — instead of typechecking the
//   dep against the sexps the inline loop holds locally.
//
// Spec anchor: implicit Principle 11 (REPL and --run produce the same
// semantics). Documented in repl/spec.md §"Self-documenting REPL" and
// root CLAUDE.md "Defects" criterion (REPL/--run divergence is a defect).
//
// FIXME(/int) — fix in src/session_v4.rs::compile_dep_inline by publishing
// dep_sexps to shared.module_sexps BEFORE scheduler.register_module so
// any persistent worker that wakes between the two operations finds the
// sexps it needs.

// spec: implicit — REPL `(import [<m> [...]])` of a stdlib module must
// produce the same outcome as the equivalent `--run` invocation
// (root CLAUDE.md "Defects" §1; repl/spec.md §"Self-documenting REPL")
#[test]
fn repl_dep_load_no_race_with_persistent_workers() {
    // Setup: an isolated project root with the repo stdlib symlinked in.
    // Drive the REPL with `--priority-workers 4` so multiple persistent
    // workers wake on the scheduler notify — this is the configuration
    // that consistently triggers the compile_dep_inline race per /int's
    // FIXME #3 diagnosis. The race symptom is the literal error string
    // "no parsed sexps for module" emitted when a worker dequeues a
    // Typecheck task before compile_dep_inline has published the dep's
    // sexps to shared.module_sexps.
    let cwd = isolated_dir("dep_load_race");
    let proj_stdlib = cwd.join("stdlib");
    if !proj_stdlib.exists() {
        #[cfg(unix)]
        std::os::unix::fs::symlink(stdlib_dir(), &proj_stdlib).unwrap();
        #[cfg(not(unix))]
        std::fs::create_dir_all(&proj_stdlib).unwrap();
    }

    // Drive the REPL through piped stdin with multiple priority workers.
    // The REPL evaluates a bare expression that requires the prelude
    // graph to be loaded — the same shape /repl saw in Wave 6 demos.
    let repl_input = "(import [collections.list [Cons Nil]])\n(Cons 1 Nil)\n";
    let repl_out = run_binary(&cwd, &["--priority-workers", "4"], repl_input);
    let combined = format!("{}{}", stdout_str(&repl_out), stderr_str(&repl_out));
    assert!(
        !combined.contains("no parsed sexps for module"),
        "REPL emitted dep-load race symptom 'no parsed sexps for module'. \
         Per /int FIXME #3 this means compile_dep_inline registered the dep \
         with the scheduler (line ~1943) before publishing the dep's sexps \
         to shared.module_sexps (line ~1945-1946). A persistent worker woke \
         on the notify, dequeued the Typecheck task, and hit the empty map. \
         Fix: publish dep_sexps to shared.module_sexps BEFORE \
         scheduler.register_module. Combined output:\n{combined}"
    );
}

// =============================================================================
// Defect 2 — stdlib seq/lazy.cl missing imports
// =============================================================================
//
// Per /int Wave 6 FIXME #3 diagnosis:
//   stdlib/seq/lazy.cl:9 declares (import [prelude []]) — the null
//   import per spec §8.3.6 suppresses the implicit prelude glob. Lines
//   131-132 reference Nil/Cons from collections.list and (transitively)
//   Some/None from fn.option without explicit imports. Both REPL and
//   --run hit this once the dep-load race (Defect 1) is fixed.
//
// Spec anchor: spec/08-modules.md §8.3.6 (null import suppresses prelude
// glob) + the implicit contract that any module references its
// dependencies. Stdlib convention (stdlib/CLAUDE.md): all stdlib modules
// use only primitives + explicit imports, never bare prelude symbols.
//
// FIXME(/stdlib) — add explicit imports to stdlib/seq/lazy.cl:
//   (import [collections.list [Nil Cons]])
//   (import [fn.option [None Some]])

// spec: spec/08-modules.md §8.3.6 — module that suppresses prelude glob
// MUST resolve every name through explicit imports
#[test]
fn stdlib_seq_lazy_imports_resolve_nil_cons() {
    // Drive the stdlib seq.lazy module through batch compilation by
    // importing it from a small entry file. If seq/lazy.cl is missing
    // its Nil/Cons imports, the typechecker fails with "undefined
    // variable: Nil" (line 131). The test passes when seq.lazy
    // typechecks cleanly — i.e., when /stdlib has added the missing
    // imports.
    let dir = tempfile::tempdir().unwrap();
    let entry = dir.path().join("entry.cl");
    std::fs::write(
        &entry,
        "(import [seq.lazy [iterate take]])\n\
         (defn main [] 0)\n",
    )
    .unwrap();
    let result = helpers::batch_run_file(&entry, &[stdlib_dir()]);
    match result {
        Ok((value, _ty)) => assert_eq!(value, 0, "main should return 0"),
        Err(e) => {
            let msg = e.to_string();
            // The exact symptom (`undefined variable: Nil`) is the
            // signature of Defect 2. Any other failure is also a defect
            // — but this assertion is intentionally precise so the test
            // becomes green only when /stdlib's fix actually lands.
            assert!(
                !msg.contains("undefined variable: Nil")
                    && !msg.contains("undefined variable: Cons")
                    && !msg.contains("undefined variable: Some")
                    && !msg.contains("undefined variable: None"),
                "stdlib/seq/lazy.cl references Nil/Cons/Some/None without \
                 importing them. Per spec §8.3.6 a module that suppresses \
                 the prelude glob (via `(import [prelude []])`) MUST resolve \
                 every name through explicit imports. Error: {msg}"
            );
            panic!("seq.lazy import failed for unrelated reason: {msg}");
        }
    }
}

// =============================================================================
// Defect 3 — Docstring separator divergence
// =============================================================================
//
// Per /repl Wave 6 finding:
//   repl/spec.md §1.1 mandates `; {classification} - {docstring}`
//   (DASH separator). src/session_v4.rs::append_docstring_comment
//   (line 3487) emits `; {classification} ; {docstring}` (SEMICOLON
//   separator). Visible in the ring4p.demo Wave 6 multi-sig output
//   (`pick` line shows `; defn ; Pick first arg` where spec requires
//   `; defn - Pick first arg`).
//
// Spec anchor: repl/spec.md §1.1.
//
// FIXME(/int) — fix src/session_v4.rs::append_docstring_comment format
// string to use ` - ` instead of ` ; ` between classification and
// docstring.

// spec: repl/spec.md §1.1 — REPL output format `:Type {value|name} ;
// {classification} - {docstring}` mandates a DASH separator between the
// classification word and the docstring's first line, NOT a semicolon
#[test]
fn display_defn_with_docstring_uses_dash_separator() {
    let cwd = isolated_dir("docstring_dash");
    // Pipe a defn-with-docstring then a bare reference to introspect it.
    let input = "(import [primitives [*]])\n(defn double \"Multiply by 2\" [:Int x] (add-i64 x x))\ndouble\n";
    let out = run_binary(&cwd, &[], input);
    let combined = format!("{}{}", stdout_str(&out), stderr_str(&out));

    // The spec format requires the classification + dash + docstring:
    //   `; defn - Multiply by 2`
    // The current implementation emits a second semicolon:
    //   `; defn ; Multiply by 2`
    let has_dash = combined.contains("; defn - Multiply by 2");
    let has_semicolon = combined.contains("; defn ; Multiply by 2");
    assert!(
        has_dash,
        "REPL output must use DASH separator per repl/spec.md §1.1 \
         (`; defn - Multiply by 2`); found semicolon-separator form \
         (`; defn ; Multiply by 2`)={has_semicolon}. \
         Combined output:\n{combined}"
    );
}

// =============================================================================
// Defect 4+5 — /run-tests batched crash (html exit 139, form exit 133)
// =============================================================================
//
// Per /port Wave 6 finding:
//   `/run-tests html` segfaults the REPL (exit 139). Single test
//   invocations work and return Option.None. The failure surfaces during
//   the batched run_test_by_name loop. `/run-tests form` is the same
//   shape but traps (exit 133, SIGTRAP). html.cl + form.cl test
//   functions were body-disabled before Wave 0 — Wave 0 enabled them, so
//   the crashes are runtime failures in test bodies that were never
//   exercised before.
//
// Defects 4 and 5 collapse into one narrow reproduction: running
// multiple test functions in sequence via `run-test` MUST NOT crash the
// process. The shared symptom (consecutive run-test invocations crash
// where individual ones succeed) is the durable record.
//
// Spec anchor: repl/spec.md §16.3 (run-tests builtins).
//
// FIXME(/backend) or FIXME(/int) — likely an RC / last-use issue
// surfacing across consecutive run_test_by_name invocations. Investigate
// run_test_by_name in src/session_v4.rs and the IO trampoline RC paths
// in cranelisp-runtime.

// spec: repl/spec.md §16.3 — run-test special form returns
// `:(IO TestResult)` and MUST be safely composable — `/run-tests <module>`
// over a module's full set of test functions MUST NOT crash the process,
// AND MUST actually run the discovered test functions (not silently
// fail to find them due to a load-path defect)
#[test]
fn run_tests_batched_invocation_no_crash() {
    // Run `/run-tests html` from the exemplar directory — this is the
    // exact shape /port hit in Wave 6 (exit 139 for html, exit 133 for
    // form). Trivial test bodies (e.g., (defn test-a [] None)) do NOT
    // reproduce the crash; the bug surfaces with the real exemplar's
    // str-concat / contains? / ADT-using test bodies.
    //
    // Defects 1 (dep-load race) and 2 (seq.lazy missing imports) are
    // gating: they currently prevent the html module from loading at
    // all, hiding the runtime crash. After Defects 1+2 are fixed and the
    // html module loads, the existing /port-observed SIGSEGV / SIGTRAP
    // becomes visible. This assertion treats BOTH the race-symptom error
    // AND the signal-crash exit codes as failure modes — the spec
    // requires the tests to run and complete.
    let exemplar_dir = project_root().join("exemplar");
    if !exemplar_dir.exists() {
        panic!("exemplar/ directory missing; cannot reproduce /port Wave 6 finding");
    }
    // Empty user.cl avoids stale REPL session state polluting the run.
    let user_cl = exemplar_dir.join("user.cl");
    std::fs::write(&user_cl, "").unwrap();

    let input = "(import [html [test-wrap-tag]])\n/run-tests html\n";
    let binary = binary_path();
    assert!(binary.exists(), "cranelisp binary not built");
    let out = Command::new(&binary)
        .current_dir(&exemplar_dir)
        .env("CRANELISP_LIB", project_root().join("stdlib"))
        .env("CRANELISP_PLATFORM_PATH", project_root().join("target/debug"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .and_then(|mut child| {
            use std::io::Write;
            if let Some(stdin) = child.stdin.as_mut() {
                let _ = stdin.write_all(input.as_bytes());
            }
            child.wait_with_output()
        })
        .expect("failed to drive REPL");

    let exit = out.status.code();
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );
    // Failure mode 1: SIGSEGV / SIGTRAP from the JIT'd test bodies
    let signal_crash = matches!(exit, Some(139) | Some(133)) || exit.is_none();
    // Failure mode 2: race symptom hides the test discovery
    let no_tests_found = combined.contains("No test-* functions found");
    // Failure mode 3: load fails outright before tests are discovered
    let load_failed = combined.contains("no parsed sexps for module")
        || combined.contains("undefined variable: Nil");
    // Success: at least one test ran and reported `ok` or `FAILED:`
    let test_ran = combined.contains("test-wrap-tag")
        && (combined.contains(" ok") || combined.contains("FAILED:"));

    assert!(
        !signal_crash && !no_tests_found && !load_failed && test_ran,
        "/run-tests html did not complete cleanly. exit={exit:?}. \
         signal_crash={signal_crash} (Defect 4: html SIGSEGV; \
         Defect 5: form SIGTRAP). no_tests_found={no_tests_found} \
         (Defect 1 race symptom hides discovery). \
         load_failed={load_failed} (Defects 1+2 prevent module load). \
         test_ran={test_ran}. Per repl/spec.md §16.3, /run-tests on a \
         module with N test functions must execute all N and report \
         pass/fail without crashing.\n--- combined ---\n{combined}"
    );
}

// =============================================================================
// Defect 6 — Sprint 19 solver stack-overflow
// =============================================================================
//
// Pre-existing per exemplar/CLAUDE.md "Known Issues":
//   propagate/solve crash on full 81-cell puzzles (likely stack overflow
//   from deep recursive Grid/Vec copying). The elimination unit tests
//   (small hand-built grids) work. Full-puzzle solver tests crash.
//
// Defect 7 folds into this test: exemplar/solver.cl has three puzzle
// tests body-disabled (test-easy-puzzle, test-hard-puzzle,
// test-unsolvable). Per the new principle they should be re-enabled
// once Defect 6 is fixed. The narrow defect-6 reproduction here is the
// durable record; re-enabling the puzzle tests is /port's acceptance
// criteria.
//
// Spec anchor: implicit (exemplar validation, not language conformance).
//
// FIXME(/backend) — solve/propagate stack-overflow on 81-cell puzzles.
// Likely propagate/solve recursion depth or stack frame size issue.
// Investigate Grid/Vec copy-on-write semantics in deep recursion.
//
// FIXME(/port) — once Defect 6 is fixed, re-enable test-easy-puzzle,
// test-hard-puzzle, test-unsolvable in exemplar/solver.cl (currently
// body-disabled to avoid this segfault).

// spec: implicit (exemplar validation) — solving an 81-cell Sudoku
// puzzle via the exemplar solve function must return a SolveResult,
// not segfault the process
#[test]
fn exemplar_solver_does_not_stack_overflow_on_small_puzzle() {
    // Use a subprocess so a SIGSEGV in the JIT'd solver crashes only
    // the child. We invoke `cranelisp --run exemplar/solver.cl` from the
    // project root: solver.cl's main attempts to solve an easy puzzle.
    // A graceful exit (status 0 or any non-signal exit) means the solver
    // returned a result; a SIGSEGV (139) or signal-kill (None) means
    // Defect 6 is unresolved.
    let cwd = project_root();
    let solver_path = cwd.join("exemplar").join("solver.cl");
    if !solver_path.exists() {
        // Defensive — if the exemplar layout changes, surface a clear
        // diagnostic rather than a misleading pass.
        panic!("exemplar/solver.cl not found at {solver_path:?}");
    }

    // Use --run with the entry pointing to solver.cl. The CRANELISP_LIB
    // env var points to the workspace stdlib so prelude resolves.
    let binary = binary_path();
    assert!(binary.exists(), "cranelisp binary not built");
    let out = Command::new(&binary)
        .current_dir(&cwd)
        .args(["--run", "exemplar/solver.cl"])
        .env("CRANELISP_LIB", "stdlib")
        .env("CRANELISP_PLATFORM_PATH", "target/debug")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("failed to invoke binary");

    let exit = out.status.code();
    let signal_segv = exit == Some(139);
    let killed_by_signal = exit.is_none();
    assert!(
        !signal_segv && !killed_by_signal,
        "exemplar solver crashed with exit={exit:?}. Per Defect 6 \
         (exemplar/CLAUDE.md Known Issues) propagate/solve stack-overflow \
         on full 81-cell grids. Once /backend resolves this, /port can \
         re-enable test-easy-puzzle, test-hard-puzzle, test-unsolvable \
         in exemplar/solver.cl. \
         stdout=\n{}\nstderr=\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );
}
