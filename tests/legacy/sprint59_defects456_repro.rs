// QUARANTINED Sprint 64 Wave 6 batch 3 — FIXME 0145 — owning skill /backend
// Source archive — not built by Cargo (nested under tests/legacy/).
// Awaiting harvest into cranelisp-backend/src/ #[cfg(test)] unit tests.
//
// Carry-forward: 34 tests in 1 file (all in tests/regression.rs):
//   §A synthetic single-file /run-tests:
//     - d45_baseline_trivial_run_tests_no_crash
//     - d45_single_str_concat_contains_run_tests_no_crash
//     - d45_wrap_tag_html_verbatim_run_tests_no_crash
//     - d45_multiple_tests_with_contains_run_tests_no_crash
//     - d45_form_shaped_body_run_tests_no_crash
//     - d45_two_trivial_tests_run_tests_no_crash
//     - d45_ten_str_bodies_run_tests_no_crash
//   §B cross-module synthetic /run-tests:
//     - d45_cross_module_adt_basic_no_crash
//     - d45_cross_module_import_but_no_use_no_crash
//     - d45_cross_module_grid_build_in_test_no_crash
//     - d45_cross_module_html_like_batch_no_crash
//     - d45_cross_module_html_full_10_tests_no_crash
//   §C real exemplar /run-tests:
//     - d45_real_exemplar_html_run_tests_no_crash
//     - d45_real_exemplar_html_single_run_test_no_crash
//     - d45_real_html_with_trimmed_grid_no_crash
//   §D html-source reduction ladder:
//     - d45_html_no_css_no_crash
//     - d45_html_solution_tests_only_no_crash
//     - d45_html_one_test_no_crash
//     - d45_html_two_tests_no_crash
//     - d45_html_three_tests_mixed_no_crash
//     - d45_html_two_arg_solution_no_crash
//     - d45_html_min_v1_no_crash
//     - d45_html_min_v2_no_crash
//     - d45_solution_cell_single_call_no_rc_underflow
//   §E synthetic Vec/ADT/Grid COW (--run mode):
//     - d6_vec_cow_int_loop_does_not_segv
//     - d6_vec_cow_adt_loop_does_not_segv
//     - d6_grid_wrapper_cow_does_not_segv
//     - d6_solve_recursive_adt_does_not_segv
//   §F real-exemplar (FAILING — open Defect 6 ledger):
//     - d6_exemplar_solve_minimal_puzzle_no_io_does_not_segv [FAILING]
//     - d6_exemplar_propagate_only_does_not_segv             [FAILING]
//     - d6_exemplar_solve_all_dots_does_not_segv             [FAILING]
//     - d6_exemplar_propagate_single_pass_does_not_segv      [FAILING]
//   §G real-exemplar (PASSING):
//     - d6_exemplar_eliminate_from_peers_does_not_segv
//     - d6_exemplar_make_grid_only_does_not_segv
//
// Inline FIXMEs preserved (verify during harvest — 24 inline
// `// FIXME(/backend)` markers, line-anchored. Each preserves a
// hypothesis comment documenting the regression-discrimination
// calibration. Resolved-by-passing-carry-forward when the corresponding
// test in tests/regression.rs passes; remaining open FIXMEs (the four
// d6_exemplar_* failing cases) close together when /backend resolves
// Defect 6):
//   - line 184: d45_baseline_trivial_run_tests_no_crash
//   - line 214: d45_single_str_concat_contains_run_tests_no_crash
//   - line 248: d45_wrap_tag_html_verbatim_run_tests_no_crash
//   - line 278: d45_multiple_tests_with_contains_run_tests_no_crash
//   - line 300: d45_form_shaped_body_run_tests_no_crash
//   - line 316: d45_real_exemplar_html_run_tests_no_crash
//   - line 354: d45_real_exemplar_html_single_run_test_no_crash
//   - line 409: d6_vec_cow_int_loop_does_not_segv
//   - line 445: d6_vec_cow_adt_loop_does_not_segv
//   - line 491: d6_grid_wrapper_cow_does_not_segv
//   - line 542: d6_solve_recursive_adt_does_not_segv
//   - line 786: d45_ten_str_bodies_run_tests_no_crash
//   - line 833: d45_cross_module_adt_basic_no_crash
//   - line 875: d45_cross_module_import_but_no_use_no_crash
//   - line 903: d45_cross_module_grid_build_in_test_no_crash
//   - line 985: d45_cross_module_html_like_batch_no_crash
//   - line 1116: d45_cross_module_html_full_10_tests_no_crash
//   - line 1167: d45_real_html_with_trimmed_grid_no_crash
//   - line 1328: d45_html_no_css_no_crash
//   - line 1420: d45_html_solution_tests_only_no_crash
//   - line 1468: d45_html_one_test_no_crash
//   - line 1519: d45_html_two_tests_no_crash
//   - line 1586: d45_html_three_tests_mixed_no_crash
//   - line 1653: d45_html_two_arg_solution_no_crash
//   - line 1695: d45_html_min_v1_no_crash
//   - line 1726: d45_html_min_v2_no_crash
// Plus 1 // spec: annotation on d45_solution_cell_single_call_no_rc_underflow
// (line 1748) — already migrated to spec/12-runtime.md §12.3 anchor in
// the carry-forward.

//! Sprint 59 Wave 1 follow-on — reduction tests for Defects 4+5 and 6.
//!
//! Per root `CLAUDE.md` §"Usability Findings and Defects": a defect is not
//! closed until `/qa` has authored a narrow reproduction. This file holds
//! the *reduced* failing tests; the *original* demo-level reproductions
//! stay in `tests/wave6_demo_repros.rs`. These smaller tests are additional
//! regression guards that each pin a specific construct-level variant of
//! the underlying defect.
//!
//! All reductions are subprocess tests driving the `cranelisp` binary so
//! that a JIT'd SIGSEGV crashes only the child process, not the Rust
//! test-runner. Failure modes asserted:
//!
//!   - exit 139 (SIGSEGV)
//!   - exit 133 (SIGTRAP)
//!   - exit None (killed by signal; other signals reported by `wait_with_output`)
//!   - stderr containing a runtime panic or RC underflow
//!
//! Each test carries a `// FIXME(/backend)` with a focused hypothesis —
//! what the reduction rules IN as a likely source of the crash, what it
//! rules OUT. The owning skill (`/backend` in every case here) closes the
//! FIXME when the defect is resolved by deleting it and annotating the
//! test with `// spec:` pointing to a spec section.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

// ---------------------------------------------------------------------------
// Subprocess helpers
// ---------------------------------------------------------------------------

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

/// Write `contents` to `<tempdir>/<name>` and return the tempdir.
/// The tempdir is kept alive via the returned handle.
fn module_dir(files: &[(&str, &str)]) -> tempfile::TempDir {
    let td = tempfile::tempdir().unwrap();
    for (name, body) in files {
        std::fs::write(td.path().join(name), body).unwrap();
    }
    td
}

/// Recursively copy `src` into `dst`, creating `dst` if needed. Skips
/// `.cranelisp-cache`/dotfiles. Used by Sprint 61 Slice 5 E-1 to replace
/// in-place writes of repro `.cl` files under `exemplar/`.
fn copy_exemplar_tree(src: &Path, dst: &Path) -> std::io::Result<()> {
    std::fs::create_dir_all(dst)?;
    for entry in std::fs::read_dir(src)? {
        let entry = entry?;
        let name = entry.file_name();
        if let Some(s) = name.to_str()
            && s.starts_with('.')
        {
            continue;
        }
        let from = entry.path();
        let to = dst.join(&name);
        let ft = entry.file_type()?;
        if ft.is_dir() {
            copy_exemplar_tree(&from, &to)?;
        } else if ft.is_file() {
            std::fs::copy(&from, &to)?;
        }
    }
    Ok(())
}

/// Drive the REPL with piped stdin. `cwd` is the project root (where the
/// user is "in"). `lib_dirs` on CRANELISP_LIB points to stdlib so prelude
/// resolves.
fn drive_repl(cwd: &Path, stdin_input: &str) -> Output {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} -- run `cargo build` first"
    );

    let mut child = Command::new(&binary)
        .current_dir(cwd)
        .env("CRANELISP_LIB", stdlib_dir())
        .env("CRANELISP_PLATFORM_PATH", platform_dir())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to start cranelisp binary");

    {
        use std::io::Write;
        if let Some(stdin) = child.stdin.as_mut() {
            stdin.write_all(stdin_input.as_bytes()).unwrap();
        }
    }
    child.wait_with_output().expect("failed to read output")
}

/// Run `cranelisp --run <path>` on a single file.
fn run_file(cwd: &Path, entry: &str) -> Output {
    let binary = binary_path();
    assert!(binary.exists(), "cranelisp binary not built");
    Command::new(&binary)
        .current_dir(cwd)
        .args(["--run", entry])
        .env("CRANELISP_LIB", stdlib_dir())
        .env("CRANELISP_PLATFORM_PATH", platform_dir())
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("failed to invoke binary")
}

fn stdout_str(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}

fn stderr_str(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

/// Assert that the given subprocess invocation did NOT die from SIGSEGV /
/// SIGTRAP / any other signal. Used by all reduction tests — any of these
/// exit codes signal that the reduction reproduces the underlying defect.
fn assert_no_signal_crash(label: &str, o: &Output) {
    let exit = o.status.code();
    let signal_crash = matches!(exit, Some(139) | Some(133)) || exit.is_none();
    if signal_crash {
        panic!(
            "{label}: child process crashed with exit={exit:?} \
             (139=SIGSEGV, 133=SIGTRAP, None=killed by signal). \
             This is the reduced reproduction of the underlying defect.\n\
             --- stdout ---\n{}\n--- stderr ---\n{}",
            stdout_str(o),
            stderr_str(o),
        );
    }
}

// =============================================================================
// Defect 4+5 reductions — /run-tests on minimal modules
// =============================================================================
//
// Earlier /backend reduction (now discarded, reconstituted here): 1/2/10
// simple test-* fns in a synthesized module pass cleanly when run via
// `/run-tests <mod>`. The crash surfaces once the test bodies exercise
// exemplar-style string building (`str-concat` chains) and `contains?`
// queries against those chains. That's the first axis probed below.
//
// Shared defect shape: `/run-tests <mod>` discovers the test-* fns,
// iterates them via `run_test_by_name`, and the JIT'd body of one of the
// tests crashes the process. Because individual invocation
// `(run-test <name>)` works in the /port repro, the defect is either in
// the batched iteration (consecutive run_test_by_name calls leaking RC
// state?) OR in the specific shape of the test body (str-concat + contains?
// + the Option-returning pattern).
//
// All tests below run `/run-tests mymod` from a tempdir.

const TRIVIAL_MOD: &str = r#";; Trivial test module — sanity check that the subprocess harness works
;; for /run-tests at all. Should pass (no crash).
(import [primitives [*]])

(defn test-none-ok [] None)
"#;

// FIXME(/backend) — If this test PASSES consistently, the crash is not a
// bare "/run-tests dispatches N tests" issue. Narrows attention to body
// shape. If this test FAILS (crashes), then the defect is in the batched
// dispatch loop itself, independent of body content.
#[test]
fn d45_baseline_trivial_run_tests_no_crash() {
    let td = module_dir(&[("mymod.cl", TRIVIAL_MOD)]);
    // Must import first to load the module into the session — `/run-tests mymod`
    // does not lazy-load. Use a bare ref to test-none-ok to force load.
    let input = "(import [mymod [test-none-ok]])\n/run-tests mymod\n";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_baseline_trivial", &out);
    // Extra assertion: the test must actually run, not silently vanish
    // (prevents the test from becoming a vacuous pass if discovery breaks).
    let combined = format!("{}{}", stdout_str(&out), stderr_str(&out));
    assert!(
        combined.contains("test-none-ok") && (combined.contains(" ok") || combined.contains("passed")),
        "baseline trivial test did not run — discovery broke.\n{combined}"
    );
}

// One test body that does a 2-link str-concat + contains? (html.cl's
// test-form-page-has-inputs shape minimized — no Option ADT in body,
// no wrap-tag, no css).
const SIMPLE_CONTAINS_MOD: &str = r#";; One test body with a simple str-concat + contains? — no Grid, no ADT.
;; This is the smallest shape of html.cl's tests.
(import [primitives [*]])

(defn test-simple-contains []
  (if (contains? (str-concat "hello" "world") "world") None
    (Some "expected 'world' in concatenation")))
"#;

// FIXME(/backend) — Isolates whether a single str-concat+contains? test
// body through /run-tests is enough to crash. If PASS: need to widen to
// multiple tests or a deeper string. If FAIL: this one test shape is
// sufficient — the defect is in str-concat / contains? / run_test_by_name
// dispatch for Option-returning bodies.
#[test]
fn d45_single_str_concat_contains_run_tests_no_crash() {
    let td = module_dir(&[("mymod.cl", SIMPLE_CONTAINS_MOD)]);
    let input = "(import [mymod [test-simple-contains]])\n/run-tests mymod\n";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_single_str_concat_contains", &out);
    let combined = format!("{}{}", stdout_str(&out), stderr_str(&out));
    assert!(
        combined.contains("test-simple-contains"),
        "test did not run — discovery broke.\n{combined}"
    );
}

// html.cl's wrap-tag uses 5-deep nested str-concats. This test keeps the
// body from test-wrap-tag verbatim (but with no dep on html.cl's wrap-tag
// function — inlined here so we don't need to import grid.cl / css).
const WRAP_TAG_MOD: &str = r#";; Inlined wrap-tag — 5-deep nested str-concat, then str-eq compare.
(import [primitives [*]])

(defn wrap-tag [tag content]
  (str-concat (str-concat (str-concat "<" tag) ">")
    (str-concat content
      (str-concat (str-concat "</" tag) ">"))))

(defn test-wrap-tag []
  (if (str-eq (wrap-tag "b" "hello") "<b>hello</b>") None
    (Some "wrap-tag should produce <b>hello</b>")))
"#;

// FIXME(/backend) — Copies html.cl test-wrap-tag verbatim minus the
// exemplar imports. If this test FAILS (crashes), the defect reproduces
// on a single 5-deep str-concat composition + str-eq. That pinpoints the
// likely culprit to either (a) the nested str-concat RC accounting for
// intermediate strings, (b) str-eq's consuming convention for one-shot
// strings, or (c) the Option return-value handling in run_test_by_name
// when the body produces a heap value (None/Some) as last op.
#[test]
fn d45_wrap_tag_html_verbatim_run_tests_no_crash() {
    let td = module_dir(&[("mymod.cl", WRAP_TAG_MOD)]);
    let input = "(import [mymod [test-wrap-tag]])\n/run-tests mymod\n";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_wrap_tag_html_verbatim", &out);
}

// Multiple tests in the same module, each doing a str-concat+contains?.
// Tests if iteration across tests is the trigger, or body shape alone.
const MULTI_CONTAINS_MOD: &str = r#";; Three tests each with str-concat + contains? bodies.
(import [primitives [*]])

(defn mk-str [] (str-concat "aa" (str-concat "bb" "cc")))

(defn test-a []
  (if (contains? (mk-str) "aa") None (Some "no aa")))
(defn test-b []
  (if (contains? (mk-str) "bb") None (Some "no bb")))
(defn test-c []
  (if (contains? (mk-str) "cc") None (Some "no cc")))
"#;

// FIXME(/backend) — If d45_single passes but this fails, the defect is
// the *second* run_test_by_name invocation in the batch leaking or
// double-free'ing the first test's return value. Classic last-use / RC
// decrement interaction with the batched dispatch loop.
#[test]
fn d45_multiple_tests_with_contains_run_tests_no_crash() {
    let td = module_dir(&[("mymod.cl", MULTI_CONTAINS_MOD)]);
    let input = "(import [mymod [test-a]])\n/run-tests mymod\n";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_multiple_tests_with_contains", &out);
}

// form.cl's simplest test shape — process-pair / substring / split are not
// under suspicion here; this is just a minimal let + str-eq + Option.
const FORM_LIKE_MOD: &str = r#";; form.cl-like test shape minimized: let + str-eq + Option.
(import [primitives [*]])

(defn test-url-decode-like []
  (if (str-eq (str-concat "hello" " world") "hello world") None
    (Some "str-concat should produce 'hello world'")))
"#;

// FIXME(/backend) — form.cl uses substring/split which are additional
// RC-sensitive primitives. This minimal form-shaped body probes whether
// the Option(Some "...") form itself — heap-string argument to Some
// constructor — is the crash surface.
#[test]
fn d45_form_shaped_body_run_tests_no_crash() {
    let td = module_dir(&[("mymod.cl", FORM_LIKE_MOD)]);
    let input = "(import [mymod [test-url-decode-like]])\n/run-tests mymod\n";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_form_shaped_body", &out);
}

// Now load the REAL exemplar/html.cl via /run-tests. Since the synthetic
// reductions above all pass, something specific to html.cl reproduces
// the crash. Load it in-situ from the exemplar dir.
//
// FIXME(/backend) — Runs /run-tests against the real exemplar/html.cl.
// Because all synthetic reductions above pass, this test isolates the
// defect to something load-bearing that html.cl has but the synthetic
// modules don't:
//   (a) html.cl imports grid.cl which defines its own Cell/Grid ADTs
//       — synthetic module has no dep chain. Cross-module ADT RC?
//   (b) html.cl has 15+ defns including build-all-ones-helper + Grid
//       constructor usage — something about size / JIT finalize batch?
//   (c) html.cl's test bodies use make-all-ones-grid which calls Grid
//       + vec-push in a loop — the ADT-wrapped Vec flow is unique to
//       html.cl vs. the synthetic modules.
//
// Resolver must strip html.cl further — try removing test-solution-page-*
// tests (those that touch Grid), then test-td / test-wrap-tag (which
// are pure strings). The mid-point determines whether (a), (b), or (c)
// is the axis.
#[test]
fn d45_real_exemplar_html_run_tests_no_crash() {
    // Sprint 61 Slice 5 E-1: was writing `exemplar/user.cl` (checked-in
    // path). Copy exemplar tree into a fresh TempDir so the test cannot
    // pollute the checked-in source. See `tests/CLAUDE.md §"Fresh Temp
    // Directory per Test"`.
    let exemplar_src = project_root().join("exemplar");
    let td = tempfile::tempdir().expect("tempdir");
    copy_exemplar_tree(&exemplar_src, td.path()).expect("copy exemplar");
    std::fs::write(td.path().join("user.cl"), "").unwrap();
    // Pull in html's first test via import, then run /run-tests html
    // (triggers batch dispatch of ALL html test-* fns).
    let input = "(import [html [test-wrap-tag]])\n/run-tests html\n";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_real_exemplar_html", &out);
}

// Single-test variant: just invoke (run-test "test-wrap-tag"). The
// earlier /port Wave 6 finding said single run-test invocations work;
// only batched /run-tests crash. This test pins that finding — expected
// to pass if the defect is strictly in the batched loop.
//
// FIXME(/backend) — If this test passes and
// d45_real_exemplar_html_run_tests_no_crash fails, defect is in the
// /run-tests dispatch loop, not the individual run-test call. If this
// ALSO fails, the defect is in evaluating a single html.cl test body
// (narrower).
#[test]
fn d45_real_exemplar_html_single_run_test_no_crash() {
    // Sprint 61 Slice 5 E-1: fresh TempDir copy of exemplar tree.
    let exemplar_src = project_root().join("exemplar");
    let td = tempfile::tempdir().expect("tempdir");
    copy_exemplar_tree(&exemplar_src, td.path()).expect("copy exemplar");
    std::fs::write(td.path().join("user.cl"), "").unwrap();
    // Single (run-test) call — not /run-tests batch.
    let input = "(import [html [test-wrap-tag]])\n(run-test \"html/test-wrap-tag\")\n";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_real_exemplar_html_single", &out);
}

// =============================================================================
// Defect 6 reductions — solver SIGSEGV, NOT a stack overflow
// =============================================================================
//
// /backend confirmed 64MB stack did not help. CRANELISP_RC_TRACE shows
// 20875 allocs / 18396 frees (delta +2479) with no debug_assert firing
// before the segv. That alloc/dealloc delta is a strong signal that
// something is allocated but never freed — likely Grid/Vec COW leaking
// the original on a mutated path.
//
// Reduction axis: strip the solver to the smallest shape that still
// segfaults. Start with a Vec-of-ADT + recursive "set-cell" loop (the
// essence of Grid updates), no match nesting, no propagate, no peers.

// Minimal: push a 100-element Vec, then repeatedly `vec-set` an index in
// a recursive helper. No match, no ADT, just Int.
const VEC_COW_LOOP_MOD: &str = r#";; Minimal Vec COW stress — build, then recursively update in place.
;; No ADTs, no match, no strings. Just Int Vec.
(import [primitives [*]])

(defn fill [v i]
  (if (eq-i64 i 81) v
    (fill (vec-push v 0) (add-i64 i 1))))

(defn updates [v i]
  (if (eq-i64 i 400) v
    (updates (vec-set v (rem-i64 i 81) i) (add-i64 i 1))))

(defn rem-i64 [a b]
  (sub-i64 a (mul-i64 b (div-i64 a b))))

(defn main []
  (let [g (fill [] 0)
        g2 (updates g 0)]
    (vec-get g2 0)))
"#;

// FIXME(/backend) — If this test PASSES (no segv), plain Vec COW with Int
// elements is not the defect. Next axis: move to Vec of ADT elements
// (Candidates mask | Given v | Solved v). If this FAILS, the defect is in
// the vec-set COW primitive's RC logic for non-uniquely-owned elements.
#[test]
fn d6_vec_cow_int_loop_does_not_segv() {
    let td = module_dir(&[("repro.cl", VEC_COW_LOOP_MOD)]);
    let out = run_file(td.path(), "repro.cl");
    assert_no_signal_crash("d6_vec_cow_int_loop", &out);
}

// Now add ADT cells. The exemplar's Grid is (Grid (Vec Cell)) where Cell
// is a sum type {Given Int | Solved Int | Candidates Int}. Without the
// Grid wrapper, exercise Vec of Cell with updates.
const VEC_ADT_COW_MOD: &str = r#";; Vec of ADT + COW updates (no Grid wrapper, no match outside main).
(import [primitives [*]])

(deftype Cell (Given [:Int v]) (Solved [:Int v]) (Candidates [:Int mask]))

(defn fill [v i]
  (if (eq-i64 i 81) v
    (fill (vec-push v (Candidates 511)) (add-i64 i 1))))

(defn updates [v i]
  (if (eq-i64 i 400) v
    (updates (vec-set v (rem-i64 i 81) (Solved (rem-i64 i 9))) (add-i64 i 1))))

(defn rem-i64 [a b]
  (sub-i64 a (mul-i64 b (div-i64 a b))))

(defn main []
  (let [g (fill [] 0)
        g2 (updates g 0)]
    0))
"#;

// FIXME(/backend) — If d6_vec_cow_int passes but this fails, the defect
// is in COW + ADT cells. Likely the old cell at the replaced index isn't
// getting RC-dec'd on vec-set, causing a leak (explains +2479 alloc/dealloc
// delta). If this ALSO passes, the defect needs the Grid ADT wrapper and/or
// recursive match nesting to surface.
#[test]
fn d6_vec_cow_adt_loop_does_not_segv() {
    let td = module_dir(&[("repro.cl", VEC_ADT_COW_MOD)]);
    let out = run_file(td.path(), "repro.cl");
    assert_no_signal_crash("d6_vec_cow_adt_loop", &out);
}

// Wrap the Vec in a Grid ADT (1-field product type). Exemplar does
// (Grid (Vec Cell)) and set-cell rebuilds the Grid wrapper on every
// update. This stresses the Grid ADT's RC handling: unpack the Vec,
// vec-set into it, wrap back into Grid.
const GRID_WRAPPER_MOD: &str = r#";; Grid wraps Vec of Cells; set-cell unwraps, updates, rewraps.
;; This matches the exemplar's set-cell shape and Grid ADT handling.
(import [primitives [*]])

(deftype Cell (Given [:Int v]) (Solved [:Int v]) (Candidates [:Int mask]))
(deftype Grid [:(Vec Cell) cells])

(defn cells-of [g]
  (match g [(Grid cs) cs]))

(defn set-cell [g idx c]
  (Grid (vec-set (cells-of g) idx c)))

(defn fill [v i]
  (if (eq-i64 i 81) v
    (fill (vec-push v (Candidates 511)) (add-i64 i 1))))

(defn updates [g i]
  (if (eq-i64 i 400) g
    (updates (set-cell g (rem-i64 i 81) (Solved (rem-i64 i 9))) (add-i64 i 1))))

(defn rem-i64 [a b]
  (sub-i64 a (mul-i64 b (div-i64 a b))))

(defn main []
  (let [g (Grid (fill [] 0))
        g2 (updates g 0)]
    0))
"#;

// FIXME(/backend) — Grid ADT wrapper adds one level of boxing (and a
// match to unpack). If this fails but d6_vec_cow_adt passes, the defect
// is at the Grid level — likely the match (Grid cs) arm dropping the
// old Vec while a new Grid wraps the same Vec; or the Grid's inner Vec
// RC isn't inc'd when cells-of returns it.
#[test]
fn d6_grid_wrapper_cow_does_not_segv() {
    let td = module_dir(&[("repro.cl", GRID_WRAPPER_MOD)]);
    let out = run_file(td.path(), "repro.cl");
    assert_no_signal_crash("d6_grid_wrapper_cow", &out);
}

// Exemplar's actual solve function: recursive `solve g` that builds new
// grids via `propagate` and descends via `try-digits`. Dropping the peers
// list and the real propagation logic — just the recursive solve-like
// shape that builds N grids on the stack.
const SOLVE_RECURSIVE_MOD: &str = r#";; Recursive solver-shaped function that builds/discards Grids at depth.
;; No propagate (which would be huge) — just the branching search shape.
(import [primitives [*]])

(deftype Cell (Given [:Int v]) (Solved [:Int v]) (Candidates [:Int mask]))
(deftype Grid [:(Vec Cell) cells])
(deftype SolveResult (Success [:Grid g]) Unsolvable)

(defn cells-of [g]
  (match g [(Grid cs) cs]))

(defn set-cell [g idx c]
  (Grid (vec-set (cells-of g) idx c)))

(defn fill [v i]
  (if (eq-i64 i 81) v
    (fill (vec-push v (Candidates 511)) (add-i64 i 1))))

;; Recursive "try digits" with a depth limit — models backtracking search.
(defn solve [g depth]
  (if (eq-i64 depth 0) (Success g)
    (let [g2 (set-cell g (rem-i64 depth 81) (Solved (rem-i64 depth 9)))]
      (match (solve g2 (sub-i64 depth 1))
        [(Success s) (Success s)
         Unsolvable Unsolvable]))))

(defn rem-i64 [a b]
  (sub-i64 a (mul-i64 b (div-i64 a b))))

(defn main []
  (let [g (Grid (fill [] 0))
        r (solve g 30)]
    0))
"#;

// FIXME(/backend) — Recursive Grid-building with 30 levels of match
// nesting on SolveResult. If passes, increase depth or add peers-list
// (Vec of Int) handling. If fails, the defect is in the match-over-ADT
// return-value dropping interaction with deep recursion. The +2479
// alloc/dealloc delta in /backend's original trace is about this order
// of magnitude for a 30-depth recursion.
#[test]
fn d6_solve_recursive_adt_does_not_segv() {
    let td = module_dir(&[("repro.cl", SOLVE_RECURSIVE_MOD)]);
    let out = run_file(td.path(), "repro.cl");
    assert_no_signal_crash("d6_solve_recursive_adt", &out);
}

// Real-world reduction: import the exemplar's actual grid.cl + solver.cl
// and just call (solve g) on a minimal puzzle. This proves the defect is
// specifically in the propagate/solve interaction, not something I
// reconstructed incorrectly in the synthetic reductions above.
//
// Unlike `exemplar_solver_does_not_stack_overflow_on_small_puzzle` which
// relies on the IO trampoline, this reduction avoids IO — it calls solve
// directly and returns the count of determined cells as an Int. Exemplar
// gives us the pre-existing grid.cl + solver.cl; this file just adds a
// pure main.
#[test]
fn d6_exemplar_solve_minimal_puzzle_no_io_does_not_segv() {
    // Sprint 61 Slice 5 E-1: was writing `exemplar/d6_repro_no_io.cl`
    // with a best-effort Drop cleanup (loses on panic). Copy exemplar
    // tree into TempDir and place the repro inside. See `tests/CLAUDE.md
    // §"Fresh Temp Directory per Test"`.
    let td = tempfile::tempdir().expect("tempdir");
    copy_exemplar_tree(&project_root().join("exemplar"), &td.path().join("exemplar"))
        .expect("copy exemplar");
    let repro_source = r#";; D6 reduction — solve without IO. Returns determined-cell count.
(import [primitives [*]])
(import [grid [Grid Cell Given Solved Candidates SolveResult Success Unsolvable
               make-grid cell-at cell-determined?]])
(import [solver [solve]])

(defn count-determined-helper [g i acc]
  (if (eq-i64 i 81) acc
    (if (cell-determined? (cell-at g i))
      (count-determined-helper g (add-i64 i 1) (add-i64 acc 1))
      (count-determined-helper g (add-i64 i 1) acc))))

(defn main []
  (match (make-grid "003020600900305001001806400008102900700000008006708200002609500800203009005010300")
    [None -1
     (Some g)
       (match (solve g)
         [(Success sol) (count-determined-helper sol 0 0)
          Unsolvable 0])]))
"#;
    std::fs::write(td.path().join("exemplar").join("d6_repro_no_io.cl"), repro_source)
        .unwrap();
    let out = run_file(td.path(), "exemplar/d6_repro_no_io.cl");
    assert_no_signal_crash("d6_exemplar_solve_minimal_puzzle_no_io", &out);
}

// Even shorter: call only propagate (no solve recursion), one time.
// If propagate itself crashes, the defect is in the single-pass elim logic
// not in the backtracking. If propagate returns cleanly, it's in the
// try-digits/solve recursion.
#[test]
fn d6_exemplar_propagate_only_does_not_segv() {
    // Sprint 61 Slice 5 E-1: fresh-TempDir exemplar copy.
    let td = tempfile::tempdir().expect("tempdir");
    copy_exemplar_tree(&project_root().join("exemplar"), &td.path().join("exemplar"))
        .expect("copy exemplar");
    let repro_source = r#";; D6 reduction — propagate once, no backtracking.
(import [primitives [*]])
(import [grid [Grid Cell Given Solved Candidates make-grid]])
(import [solver [propagate]])

(defn main []
  (match (make-grid "003020600900305001001806400008102900700000008006708200002609500800203009005010300")
    [None -1
     (Some g)
       (match (propagate g)
         [None 0
          (Some _) 1])]))
"#;
    std::fs::write(
        td.path().join("exemplar").join("d6_propagate_only.cl"),
        repro_source,
    )
    .unwrap();
    let out = run_file(td.path(), "exemplar/d6_propagate_only.cl");
    assert_no_signal_crash("d6_exemplar_propagate_only", &out);
}

// All-dots puzzle (maximally empty) — tests whether the crash is
// data-dependent. A near-empty grid forces heavy propagation; near-full
// grid converges fast.
#[test]
fn d6_exemplar_solve_all_dots_does_not_segv() {
    // Sprint 61 Slice 5 E-1: fresh-TempDir exemplar copy.
    let td = tempfile::tempdir().expect("tempdir");
    copy_exemplar_tree(&project_root().join("exemplar"), &td.path().join("exemplar"))
        .expect("copy exemplar");
    let repro_source = r#";; D6 reduction — solve on an all-dots (empty) puzzle.
(import [primitives [*]])
(import [grid [Grid Cell Given Solved Candidates SolveResult Success Unsolvable
               make-grid]])
(import [solver [solve]])

(defn main []
  (match (make-grid ".................................................................................")
    [None -1
     (Some g)
       (match (solve g)
         [(Success _) 1
          Unsolvable 0])]))
"#;
    std::fs::write(td.path().join("exemplar").join("d6_all_dots.cl"), repro_source).unwrap();
    let out = run_file(td.path(), "exemplar/d6_all_dots.cl");
    assert_no_signal_crash("d6_exemplar_solve_all_dots", &out);
}

// Finer reduction: just propagate-pass-helper ONCE, no fixpoint loop.
// Exercises eliminate-from-peers for every Given cell. If this crashes,
// the defect is in the single-pass scan itself. If it doesn't, the defect
// is in propagate's fixpoint loop (grids-differ-helper + recursion).
//
// This depends on exemplar/solver.cl exposing propagate-pass-helper —
// which it does (it's a top-level defn at line 73).
#[test]
fn d6_exemplar_propagate_single_pass_does_not_segv() {
    // Sprint 61 Slice 5 E-1: fresh-TempDir exemplar copy.
    let td = tempfile::tempdir().expect("tempdir");
    copy_exemplar_tree(&project_root().join("exemplar"), &td.path().join("exemplar"))
        .expect("copy exemplar");
    let repro_source = r#";; D6 reduction — one call to propagate-pass-helper, no fixpoint loop.
(import [primitives [*]])
(import [grid [Grid Cell Given Solved Candidates make-grid]])
(import [solver [propagate-pass-helper]])

(defn main []
  (match (make-grid "003020600900305001001806400008102900700000008006708200002609500800203009005010300")
    [None -1
     (Some g)
       (match (propagate-pass-helper g 0)
         [None 0
          (Some _) 1])]))
"#;
    std::fs::write(td.path().join("exemplar").join("d6_one_pass.cl"), repro_source).unwrap();
    let out = run_file(td.path(), "exemplar/d6_one_pass.cl");
    assert_no_signal_crash("d6_exemplar_propagate_single_pass", &out);
}

// Finer still: just one eliminate-from-peers call on ONE cell.
// peers returns a Vec of 20 Int indices; eliminate-from-peers iterates
// them calling eliminate which does match + set-cell (Grid COW). If
// this one call crashes, the defect reduces to a single eliminate-from-peers
// invocation with a concrete puzzle — the smallest trigger.
#[test]
fn d6_exemplar_eliminate_from_peers_does_not_segv() {
    // Sprint 61 Slice 5 E-1: fresh-TempDir exemplar copy.
    let td = tempfile::tempdir().expect("tempdir");
    copy_exemplar_tree(&project_root().join("exemplar"), &td.path().join("exemplar"))
        .expect("copy exemplar");
    let repro_source = r#";; D6 reduction — one eliminate-from-peers call on cell 0.
(import [primitives [*]])
(import [grid [Grid Cell Given Solved Candidates make-grid]])
(import [solver [eliminate-from-peers]])

(defn main []
  (match (make-grid "003020600900305001001806400008102900700000008006708200002609500800203009005010300")
    [None -1
     (Some g)
       (match (eliminate-from-peers g 2 3)
         [None 0
          (Some _) 1])]))
"#;
    std::fs::write(td.path().join("exemplar").join("d6_elim_peers.cl"), repro_source).unwrap();
    let out = run_file(td.path(), "exemplar/d6_elim_peers.cl");
    assert_no_signal_crash("d6_exemplar_eliminate_from_peers", &out);
}

// A reduction that exercises make-grid alone. make-grid is 10 nested
// str-eq + vec-push loops; even if only make-grid crashes, it tells us
// the defect is in the initial grid construction not the solver.
#[test]
fn d6_exemplar_make_grid_only_does_not_segv() {
    // Sprint 61 Slice 5 E-1: fresh-TempDir exemplar copy.
    let td = tempfile::tempdir().expect("tempdir");
    copy_exemplar_tree(&project_root().join("exemplar"), &td.path().join("exemplar"))
        .expect("copy exemplar");
    let repro_source = r#";; D6 reduction — construct a Grid via make-grid, return None/Some discriminant.
(import [primitives [*]])
(import [grid [Grid make-grid]])

(defn main []
  (match (make-grid "003020600900305001001806400008102900700000008006708200002609500800203009005010300")
    [None 0
     (Some _) 1]))
"#;
    std::fs::write(td.path().join("exemplar").join("d6_make_grid.cl"), repro_source).unwrap();
    let out = run_file(td.path(), "exemplar/d6_make_grid.cl");
    assert_no_signal_crash("d6_exemplar_make_grid_only", &out);
}

// =============================================================================
// Additional D4/5 reductions — narrow the batched /run-tests culprit
// =============================================================================
//
// Two batched /run-tests invocations in a row on html — does the
// count of test bodies matter? Build a progressively smaller html-like
// module that still crashes.

// Two trivial tests (no str work): proves that batched /run-tests with
// two test bodies alone is OK. (If this crashes, the defect is in batched
// dispatch of any 2+ tests.)
const TWO_TRIVIAL_MOD: &str = r#"(import [primitives [*]])
(defn test-a [] None)
(defn test-b [] None)
"#;

#[test]
fn d45_two_trivial_tests_run_tests_no_crash() {
    let td = module_dir(&[("mymod.cl", TWO_TRIVIAL_MOD)]);
    let input = "(import [mymod [test-a]])\n/run-tests mymod\n";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_two_trivial_tests", &out);
}

// Ten tests with str-concat bodies returning None. The key question:
// is the issue about THE NUMBER OF tests in the batch, or specifically
// about html.cl's content?
const TEN_STR_BODIES_MOD: &str = r#"(import [primitives [*]])

(defn mk [] (str-concat (str-concat "aa" "bb") "cc"))

(defn test-01 [] (if (contains? (mk) "aa") None (Some "no aa")))
(defn test-02 [] (if (contains? (mk) "bb") None (Some "no bb")))
(defn test-03 [] (if (contains? (mk) "cc") None (Some "no cc")))
(defn test-04 [] (if (contains? (mk) "aabb") None (Some "no aabb")))
(defn test-05 [] (if (contains? (mk) "aabbcc") None (Some "no aabbcc")))
(defn test-06 [] (if (contains? (mk) "bbcc") None (Some "no bbcc")))
(defn test-07 [] (if (contains? (mk) "a") None (Some "no a")))
(defn test-08 [] (if (contains? (mk) "b") None (Some "no b")))
(defn test-09 [] (if (contains? (mk) "c") None (Some "no c")))
(defn test-10 [] (if (contains? (mk) "abc") (Some "abc present?") None))
"#;

// FIXME(/backend) — If this passes but d45_real_exemplar_html fails,
// the defect is NOT batch-size driven: it specifically needs html.cl's
// imports (grid.cl) or one of its specific helpers (build-all-ones-helper
// constructs a Vec of 81 Grid cells). The presence of the grid.cl dep
// chain — and specifically the Grid ADT and Vec of Cell work — may be
// load-bearing.
#[test]
fn d45_ten_str_bodies_run_tests_no_crash() {
    let td = module_dir(&[("mymod.cl", TEN_STR_BODIES_MOD)]);
    let input = "(import [mymod [test-01]])\n/run-tests mymod\n";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_ten_str_bodies", &out);
}

// ---------------------------------------------------------------------------
// Phase-2 reductions: cross-module fixture probing (the untested axis)
// ---------------------------------------------------------------------------
//
// The prior agent's 8 passing reductions all used a SINGLE synthetic .cl
// file. The real exemplar crash requires html.cl + grid.cl — a 2-file
// situation with cross-module ADT import. That axis was never tested in
// isolation. These reductions fill that gap.

/// Two synthetic files: `lib.cl` exports an ADT + a function; `mymod.cl`
/// imports them and defines test-* fns. Progressively dial up the shape.
fn two_file_dir(lib_body: &str, mymod_body: &str) -> tempfile::TempDir {
    let td = tempfile::tempdir().unwrap();
    std::fs::write(td.path().join("lib.cl"), lib_body).unwrap();
    std::fs::write(td.path().join("mymod.cl"), mymod_body).unwrap();
    td
}

// Minimum cross-module shape: lib exports an ADT; mymod imports it + uses
// it in ONE test body. This is the smallest "two-file" reduction.
const LIB_SIMPLE_ADT: &str = r#"(import [primitives [*]])
(deftype Cell (Given [:Int v]) (Solved [:Int v]) (Candidates [:Int mask]))
"#;

const MYMOD_USES_CELL: &str = r#"(import [primitives [*]])
(import [lib [Cell Given]])

(defn test-cell-ctor []
  (match (Given 5)
    [(Given v) (if (eq-i64 v 5) None (Some "wrong v"))
     _ (Some "wrong variant")]))
"#;

// FIXME(/backend) — cross-module ADT constructor + match in a test body.
// If PASS: cross-module ADT alone is not enough; need Vec or Grid wrapper.
#[test]
fn d45_cross_module_adt_basic_no_crash() {
    let td = two_file_dir(LIB_SIMPLE_ADT, MYMOD_USES_CELL);
    let input = "(import [mymod [test-cell-ctor]])\n/run-tests mymod\n";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_cross_module_adt_basic", &out);
}

// Add a Grid-wrapper type in lib, and a cross-module helper that builds
// `(Grid (Vec Cell))`. This mirrors html.cl's make-all-ones-grid /
// build-all-ones-helper shape but stripped.
const LIB_GRID_ADT: &str = r#"(import [primitives [*]])
(deftype Cell (Given [:Int v]) (Solved [:Int v]) (Candidates [:Int mask]))
(deftype Grid [:(Vec Cell) cells])

(defn cell-at [g idx]
  (match g [(Grid cs) (vec-get cs idx)]))

(defn cell-value [c]
  (match c [(Given v) v (Solved v) v (Candidates _) 0]))
"#;

const MYMOD_USES_GRID_NO_TESTS_THAT_BUILD: &str = r#"(import [primitives [*]])
(import [lib [Cell Grid Given Solved Candidates cell-at cell-value]])

(defn wrap-tag [tag content]
  (str-concat (str-concat (str-concat "<" tag) ">")
    (str-concat content
      (str-concat (str-concat "</" tag) ">"))))

;; Two pure-string tests, no Grid build.
(defn test-wrap-tag []
  (if (str-eq (wrap-tag "b" "hello") "<b>hello</b>") None
    (Some "wrong")))

(defn test-contains []
  (if (contains? (wrap-tag "b" "hello") "b") None
    (Some "wrong")))
"#;

// FIXME(/backend) — mymod imports Grid-ADT symbols but never builds one;
// tests are pure-string. If PASS: the IMPORT alone doesn't trigger. Crash
// requires test bodies to actually USE the cross-module ADT.
#[test]
fn d45_cross_module_import_but_no_use_no_crash() {
    let td = two_file_dir(LIB_GRID_ADT, MYMOD_USES_GRID_NO_TESTS_THAT_BUILD);
    let input = "(import [mymod [test-wrap-tag]])\n/run-tests mymod\n";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_cross_module_import_but_no_use", &out);
}

// Now mymod actually BUILDS a Grid via a helper, mirroring make-all-ones-grid
// in html.cl. But the test bodies still only return simple None/Some.
const MYMOD_BUILDS_GRID_IN_TEST: &str = r#"(import [primitives [*]])
(import [lib [Cell Grid Given Solved Candidates cell-at cell-value]])

(defn build-helper [v i]
  (if (eq-i64 i 9) v
    (build-helper (vec-push v (Given 1)) (add-i64 i 1))))

(defn make-grid [] (Grid (build-helper [] 0)))

(defn test-grid-build []
  (let [g (make-grid)]
    (if (eq-i64 (cell-value (cell-at g 0)) 1) None
      (Some "wrong"))))
"#;

// FIXME(/backend) — one test that builds (Grid (Vec Cell)) using a
// cross-module constructor. If FAIL: cross-module Grid-build via
// batched /run-tests is the trigger. If PASS: needs MORE in the test body
// (string concat + Grid use combined).
#[test]
fn d45_cross_module_grid_build_in_test_no_crash() {
    let td = two_file_dir(LIB_GRID_ADT, MYMOD_BUILDS_GRID_IN_TEST);
    let input = "(import [mymod [test-grid-build]])\n/run-tests mymod\n";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_cross_module_grid_build_in_test", &out);
}

// Now combine: html-like mix of tests — some pure string (wrap-tag),
// some build a Grid via a helper and do `contains?` on a derived string.
// This closely mirrors html.cl's test block layout.
const MYMOD_HTML_LIKE: &str = r#"(import [primitives [*]])
(import [lib [Cell Grid Given Solved Candidates cell-at cell-value]])

(defn wrap-tag [tag content]
  (str-concat (str-concat (str-concat "<" tag) ">")
    (str-concat content
      (str-concat (str-concat "</" tag) ">"))))

(defn td [cls content]
  (str-concat
    (str-concat (str-concat "<td class=\"" cls) "\">")
    (str-concat content "</td>")))

(defn solution-cell [g idx]
  (let [c (cell-at g idx)
        digit (int-to-string (cell-value c))]
    (match c
      [(Given _) (td "given" digit)
       _ (td "solved" digit)])))

(defn solution-row-helper [g row col acc]
  (if (eq-i64 col 9) acc
    (let [idx (add-i64 (mul-i64 row 9) col)]
      (solution-row-helper g row (add-i64 col 1)
        (str-concat acc (solution-cell g idx))))))

(defn solution-row [g row]
  (wrap-tag "tr" (solution-row-helper g row 0 "")))

(defn solution-rows-helper [g row acc]
  (if (eq-i64 row 9) acc
    (solution-rows-helper g (add-i64 row 1)
      (str-concat acc (solution-row g row)))))

(defn solution-page [g]
  (str-concat "<table>"
    (str-concat (solution-rows-helper g 0 "")
      "</table>")))

(defn build-all-ones-helper [v i]
  (if (eq-i64 i 81) v
    (build-all-ones-helper (vec-push v (Given 1)) (add-i64 i 1))))

(defn make-all-ones-grid [] (Grid (build-all-ones-helper [] 0)))

(defn test-wrap-tag []
  (if (str-eq (wrap-tag "b" "hello") "<b>hello</b>") None
    (Some "wrong")))

(defn test-td []
  (let [result (td "given" "5")]
    (if (contains? result "given")
      (if (contains? result "5") None
        (Some "no 5"))
      (Some "no given"))))

(defn test-solution-page-has-digits []
  (let [g (make-all-ones-grid)]
    (if (contains? (solution-page g) "1") None
      (Some "no 1"))))

(defn test-solution-page-given-class []
  (let [g (make-all-ones-grid)]
    (if (contains? (solution-page g) "given") None
      (Some "no given"))))
"#;

// FIXME(/backend) — 4 tests including Grid-build + cross-module match +
// deep str-concat nesting. Closely mirrors html.cl's test surface.
#[test]
fn d45_cross_module_html_like_batch_no_crash() {
    let td = two_file_dir(LIB_GRID_ADT, MYMOD_HTML_LIKE);
    let input = "(import [mymod [test-wrap-tag]])\n/run-tests mymod\n";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_cross_module_html_like_batch", &out);
}

// Expand to 10 tests, matching html.cl's test count, with the same mix:
// small pure-string + Grid-build + page-derivation (contains?).
const MYMOD_HTML_FULL: &str = r#"(import [primitives [*]])
(import [lib [Cell Grid Given Solved Candidates cell-at cell-value]])

(defn wrap-tag [tag content]
  (str-concat (str-concat (str-concat "<" tag) ">")
    (str-concat content
      (str-concat (str-concat "</" tag) ">"))))

(defn td [cls content]
  (str-concat
    (str-concat (str-concat "<td class=\"" cls) "\">")
    (str-concat content "</td>")))

(defn input-field [row col]
  (let [name (str-concat "c" (str-concat (int-to-string row) (int-to-string col)))]
    (str-concat
      (str-concat "<td><input type=\"text\" name=\"" name)
      "\" maxlength=\"1\"></td>")))

(defn form-row-helper [row col acc]
  (if (eq-i64 col 9) acc
    (form-row-helper row (add-i64 col 1)
      (str-concat acc (input-field row col)))))

(defn form-row [row] (wrap-tag "tr" (form-row-helper row 0 "")))

(defn form-rows-helper [row acc]
  (if (eq-i64 row 9) acc
    (form-rows-helper (add-i64 row 1)
      (str-concat acc (form-row row)))))

(defn form-page [] (str-concat "<form>" (str-concat (form-rows-helper 0 "") "</form>")))

(defn error-page [message]
  (str-concat "<h1>Error</h1><p>"
    (str-concat message "</p>")))

(defn solution-cell [g idx]
  (let [c (cell-at g idx)
        digit (int-to-string (cell-value c))]
    (match c
      [(Given _) (td "given" digit)
       _ (td "solved" digit)])))

(defn solution-row-helper [g row col acc]
  (if (eq-i64 col 9) acc
    (let [idx (add-i64 (mul-i64 row 9) col)]
      (solution-row-helper g row (add-i64 col 1)
        (str-concat acc (solution-cell g idx))))))

(defn solution-row [g row]
  (wrap-tag "tr" (solution-row-helper g row 0 "")))

(defn solution-rows-helper [g row acc]
  (if (eq-i64 row 9) acc
    (solution-rows-helper g (add-i64 row 1)
      (str-concat acc (solution-row g row)))))

(defn solution-page [g]
  (str-concat "<table>"
    (str-concat (solution-rows-helper g 0 "") "</table>")))

(defn build-all-ones-helper [v i]
  (if (eq-i64 i 81) v
    (build-all-ones-helper (vec-push v (Given 1)) (add-i64 i 1))))

(defn make-all-ones-grid [] (Grid (build-all-ones-helper [] 0)))

(defn build-mixed-helper [v i]
  (if (eq-i64 i 81) v
    (if (eq-i64 i 0)
      (build-mixed-helper (vec-push v (Given 5)) (add-i64 i 1))
      (if (eq-i64 i 1)
        (build-mixed-helper (vec-push v (Solved 3)) (add-i64 i 1))
        (build-mixed-helper (vec-push v (Given 1)) (add-i64 i 1))))))

(defn make-mixed-grid [] (Grid (build-mixed-helper [] 0)))

(defn test-form-page-has-inputs []
  (if (contains? (form-page) "<input") None (Some "no input")))

(defn test-form-page-has-action []
  (if (contains? (form-page) "form") None (Some "no form")))

(defn test-form-page-has-table []
  (if (contains? (form-page) "tr") None (Some "no tr")))

(defn test-wrap-tag []
  (if (str-eq (wrap-tag "b" "hello") "<b>hello</b>") None (Some "wrong")))

(defn test-td []
  (let [result (td "given" "5")]
    (if (contains? result "given")
      (if (contains? result "5") None (Some "no 5"))
      (Some "no given"))))

(defn test-error-page-has-message []
  (if (contains? (error-page "No solution") "No solution") None
    (Some "no message")))

(defn test-error-page-has-link []
  (if (contains? (error-page "oops") "Error") None (Some "no Error")))

(defn test-solution-page-has-digits []
  (let [g (make-all-ones-grid)]
    (if (contains? (solution-page g) "1") None (Some "no 1"))))

(defn test-solution-page-given-class []
  (let [g (make-all-ones-grid)]
    (if (contains? (solution-page g) "given") None (Some "no given"))))

(defn test-solution-page-mixed []
  (let [g (make-mixed-grid)
        page (solution-page g)]
    (if (contains? page "given")
      (if (contains? page "solved") None (Some "no solved"))
      (Some "no given"))))
"#;

// FIXME(/backend) — 10-test synthetic batch closely matching html.cl's shape.
// If FAIL: we've reduced to a synthetic 2-file pair. If PASS: something more
// specific to html.cl (perhaps the exact dependency on grid.cl's additional
// symbols / 20 test-* defns sitting in the grid module even though they're
// not called) is load-bearing.
#[test]
fn d45_cross_module_html_full_10_tests_no_crash() {
    let td = two_file_dir(LIB_GRID_ADT, MYMOD_HTML_FULL);
    let input = "(import [mymod [test-wrap-tag]])\n/run-tests mymod\n";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_cross_module_html_full_10_tests", &out);
}

// Copy real html.cl + a trimmed grid.cl (only the symbols html.cl imports)
// to a temp dir. If this still crashes, the defect is driven by some
// interaction involving the REAL html.cl source shape — but in an isolated
// module set under our control (temp dir), so we can iterate on it.
//
// Imports from grid in html: Grid Cell Given Solved Candidates cell-at cell-value
const GRID_TRIMMED: &str = r#";; Trimmed grid.cl — only the symbols html.cl imports.
(import [primitives [*]])

(deftype Cell
  (Given [:Int value])
  (Solved [:Int value])
  (Candidates [:Int bitmask]))

(deftype Grid [cells])

(defn cell-at [g idx]
  (match g [(Grid cells) (vec-get cells idx)]))

(defn cell-value [c]
  (match c
    [(Given v) v
     (Solved v) v
     (Candidates _) 0]))
"#;

/// Read real html.cl from the exemplar directory and pair it with the
/// trimmed grid.cl fixture. Returns (tempdir, "html" module name).
fn html_with_trimmed_grid() -> tempfile::TempDir {
    let td = tempfile::tempdir().unwrap();
    std::fs::write(td.path().join("grid.cl"), GRID_TRIMMED).unwrap();
    let html_body = std::fs::read_to_string(
        project_root().join("exemplar").join("html.cl"),
    ).unwrap();
    std::fs::write(td.path().join("html.cl"), html_body).unwrap();
    td
}

// FIXME(/backend) — real html.cl + trimmed grid.cl. If this crashes, the
// defect is isolated from grid.cl's 20 test-* defns + bitmask helpers —
// we've pinned the crash to html.cl + {Grid, Cell, Given, Solved,
// Candidates, cell-at, cell-value} alone.
#[test]
fn d45_real_html_with_trimmed_grid_no_crash() {
    let td = html_with_trimmed_grid();
    let input = "(import [html [test-wrap-tag]])\n/run-tests html\n";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_real_html_with_trimmed_grid", &out);
}

/// Generic 2-file driver for html-like reductions against a trimmed grid.
fn html_reduction(html_body: &str) -> tempfile::TempDir {
    let td = tempfile::tempdir().unwrap();
    std::fs::write(td.path().join("grid.cl"), GRID_TRIMMED).unwrap();
    std::fs::write(td.path().join("html.cl"), html_body).unwrap();
    td
}

// Keep ALL 10 tests but remove the `css` function (giant str-concat) and
// simplify form-page / error-page / solution-page so they don't invoke css.
// This probes whether the deeply nested `css` function is load-bearing.
const HTML_NO_CSS: &str = r#"(import [primitives [*]])
(import [grid [Grid Cell Given Solved Candidates cell-at cell-value]])

(defn wrap-tag [tag content]
  (str-concat (str-concat (str-concat "<" tag) ">")
    (str-concat content
      (str-concat (str-concat "</" tag) ">"))))

(defn td [cls content]
  (str-concat
    (str-concat (str-concat "<td class=\"" cls) "\">")
    (str-concat content "</td>")))

(defn input-field [row col]
  (let [name (str-concat "c" (str-concat (int-to-string row) (int-to-string col)))]
    (str-concat
      (str-concat "<td><input type=\"text\" name=\"" name)
      "\" maxlength=\"1\" size=\"1\"></td>")))

(defn form-row-helper [row col acc]
  (if (eq-i64 col 9) acc
    (form-row-helper row (add-i64 col 1)
      (str-concat acc (input-field row col)))))

(defn form-row [row] (wrap-tag "tr" (form-row-helper row 0 "")))

(defn form-rows-helper [row acc]
  (if (eq-i64 row 9) acc
    (form-rows-helper (add-i64 row 1)
      (str-concat acc (form-row row)))))

(defn form-rows [] (form-rows-helper 0 ""))

(defn form-page []
  (str-concat "<html><body><form>" (str-concat (form-rows) "</form></body></html>")))

(defn solution-cell [original solved idx]
  (let [orig-cell (cell-at original idx)
        solved-cell (cell-at solved idx)
        digit (int-to-string (cell-value solved-cell))]
    (match orig-cell
      [(Given _) (td "given" digit)
       _ (td "solved" digit)])))

(defn solution-row-helper [original solved row col acc]
  (if (eq-i64 col 9) acc
    (let [idx (add-i64 (mul-i64 row 9) col)]
      (solution-row-helper original solved row (add-i64 col 1)
        (str-concat acc (solution-cell original solved idx))))))

(defn solution-row [original solved row]
  (wrap-tag "tr" (solution-row-helper original solved row 0 "")))

(defn solution-rows-helper [original solved row acc]
  (if (eq-i64 row 9) acc
    (solution-rows-helper original solved (add-i64 row 1)
      (str-concat acc (solution-row original solved row)))))

(defn solution-rows [original solved]
  (solution-rows-helper original solved 0 ""))

(defn solution-page [solved original]
  (str-concat "<html><body><table>"
    (str-concat (solution-rows original solved)
      "</table></body></html>")))

(defn error-page [message]
  (str-concat "<html><body><p>"
    (str-concat message "</p></body></html>")))

(defn test-form-page-has-inputs []
  (if (contains? (form-page) "<input") None
    (Some "form-page should contain <input elements")))

(defn test-form-page-has-action []
  (if (contains? (form-page) "form") None
    (Some "form-page should contain form")))

(defn test-form-page-has-table []
  (if (contains? (form-page) "tr") None
    (Some "form-page should contain tr")))

(defn test-wrap-tag []
  (if (str-eq (wrap-tag "b" "hello") "<b>hello</b>") None
    (Some "wrap-tag should produce <b>hello</b>")))

(defn test-td []
  (let [result (td "given" "5")]
    (if (contains? result "given")
      (if (contains? result "5") None
        (Some "td result should contain content '5'"))
      (Some "td result should contain class 'given'"))))

(defn test-error-page-has-message []
  (if (contains? (error-page "No solution exists") "No solution exists") None
    (Some "error-page should contain the supplied message")))

(defn test-error-page-has-link []
  (if (contains? (error-page "oops") "oops") None
    (Some "error-page should contain 'oops'")))

(defn build-all-ones-helper [v i]
  (if (eq-i64 i 81) v
    (build-all-ones-helper (vec-push v (Given 1)) (add-i64 i 1))))

(defn make-all-ones-grid []
  (Grid (build-all-ones-helper [] 0)))

(defn test-solution-page-has-digits []
  (let [g (make-all-ones-grid)]
    (if (contains? (solution-page g g) "1") None
      (Some "solution-page should contain digit '1'"))))

(defn test-solution-page-given-class []
  (let [g (make-all-ones-grid)]
    (if (contains? (solution-page g g) "given") None
      (Some "solution-page should contain 'given' CSS class"))))

(defn build-mixed-helper [v i]
  (if (eq-i64 i 81) v
    (if (eq-i64 i 0)
      (build-mixed-helper (vec-push v (Given 5)) (add-i64 i 1))
      (if (eq-i64 i 1)
        (build-mixed-helper (vec-push v (Solved 3)) (add-i64 i 1))
        (build-mixed-helper (vec-push v (Given 1)) (add-i64 i 1))))))

(defn make-mixed-grid []
  (Grid (build-mixed-helper [] 0)))

(defn test-solution-page-mixed []
  (let [g (make-mixed-grid)
        page (solution-page g g)]
    (if (contains? page "given")
      (if (contains? page "solved") None
        (Some "solution-page should contain 'solved' CSS class"))
      (Some "solution-page should contain 'given' CSS class"))))
"#;

// FIXME(/backend) — real html.cl minus the css function. If STILL crashes,
// css is not the culprit. If PASS, css's massive str-concat depth is the
// trigger.
#[test]
fn d45_html_no_css_no_crash() {
    let td = html_reduction(HTML_NO_CSS);
    let input = "(import [html [test-wrap-tag]])\n/run-tests html\n";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_html_no_css", &out);
}

// Strip: remove form-page tests + test-td + test-wrap-tag + test-error-page-*.
// Keep ONLY the 3 solution-page tests (which touch Grid via cross-module
// match). Cross-module-ADT-in-test-body is the remaining axis.
const HTML_SOLUTION_TESTS_ONLY: &str = r#"(import [primitives [*]])
(import [grid [Grid Cell Given Solved Candidates cell-at cell-value]])

(defn wrap-tag [tag content]
  (str-concat (str-concat (str-concat "<" tag) ">")
    (str-concat content
      (str-concat (str-concat "</" tag) ">"))))

(defn td [cls content]
  (str-concat
    (str-concat (str-concat "<td class=\"" cls) "\">")
    (str-concat content "</td>")))

(defn solution-cell [original solved idx]
  (let [orig-cell (cell-at original idx)
        solved-cell (cell-at solved idx)
        digit (int-to-string (cell-value solved-cell))]
    (match orig-cell
      [(Given _) (td "given" digit)
       _ (td "solved" digit)])))

(defn solution-row-helper [original solved row col acc]
  (if (eq-i64 col 9) acc
    (let [idx (add-i64 (mul-i64 row 9) col)]
      (solution-row-helper original solved row (add-i64 col 1)
        (str-concat acc (solution-cell original solved idx))))))

(defn solution-row [original solved row]
  (wrap-tag "tr" (solution-row-helper original solved row 0 "")))

(defn solution-rows-helper [original solved row acc]
  (if (eq-i64 row 9) acc
    (solution-rows-helper original solved (add-i64 row 1)
      (str-concat acc (solution-row original solved row)))))

(defn solution-rows [original solved]
  (solution-rows-helper original solved 0 ""))

(defn solution-page [solved original]
  (str-concat "<html><body><table>"
    (str-concat (solution-rows original solved)
      "</table></body></html>")))

(defn build-all-ones-helper [v i]
  (if (eq-i64 i 81) v
    (build-all-ones-helper (vec-push v (Given 1)) (add-i64 i 1))))

(defn make-all-ones-grid [] (Grid (build-all-ones-helper [] 0)))

(defn test-solution-page-has-digits []
  (let [g (make-all-ones-grid)]
    (if (contains? (solution-page g g) "1") None
      (Some "solution-page should contain digit '1'"))))

(defn test-solution-page-given-class []
  (let [g (make-all-ones-grid)]
    (if (contains? (solution-page g g) "given") None
      (Some "solution-page should contain 'given' CSS class"))))

(defn build-mixed-helper [v i]
  (if (eq-i64 i 81) v
    (if (eq-i64 i 0)
      (build-mixed-helper (vec-push v (Given 5)) (add-i64 i 1))
      (if (eq-i64 i 1)
        (build-mixed-helper (vec-push v (Solved 3)) (add-i64 i 1))
        (build-mixed-helper (vec-push v (Given 1)) (add-i64 i 1))))))

(defn make-mixed-grid [] (Grid (build-mixed-helper [] 0)))

(defn test-solution-page-mixed []
  (let [g (make-mixed-grid)
        page (solution-page g g)]
    (if (contains? page "given")
      (if (contains? page "solved") None
        (Some "solution-page should contain 'solved' CSS class"))
      (Some "solution-page should contain 'given' CSS class"))))
"#;

// FIXME(/backend) — only 3 Grid-touching tests. If crashes, we've pinned
// the axis to solution-page tests. If PASS, need to keep other tests.
#[test]
fn d45_html_solution_tests_only_no_crash() {
    let td = html_reduction(HTML_SOLUTION_TESTS_ONLY);
    let input = "(import [html [test-solution-page-has-digits]])\n/run-tests html\n";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_html_solution_tests_only", &out);
}

// Radical strip: ONE test, minimal solution-page (inline the row helpers
// flat). All that remains: build a grid, call a function that matches on
// cross-module ADT + str-concats, `contains?` the result.
const HTML_ONE_TEST: &str = r#"(import [primitives [*]])
(import [grid [Grid Cell Given Solved Candidates cell-at cell-value]])

(defn solution-cell [g idx]
  (let [c (cell-at g idx)
        digit (int-to-string (cell-value c))]
    (match c
      [(Given _) (str-concat "g:" digit)
       _ (str-concat "s:" digit)])))

(defn row-helper [g row col acc]
  (if (eq-i64 col 9) acc
    (let [idx (add-i64 (mul-i64 row 9) col)]
      (row-helper g row (add-i64 col 1)
        (str-concat acc (solution-cell g idx))))))

(defn rows-helper [g row acc]
  (if (eq-i64 row 9) acc
    (rows-helper g (add-i64 row 1)
      (str-concat acc (row-helper g row 0 "")))))

(defn page [g] (rows-helper g 0 ""))

(defn build-helper [v i]
  (if (eq-i64 i 81) v
    (build-helper (vec-push v (Given 1)) (add-i64 i 1))))

(defn make-grid [] (Grid (build-helper [] 0)))

(defn test-page []
  (let [g (make-grid)]
    (if (contains? (page g) "1") None
      (Some "no 1"))))
"#;

// FIXME(/backend) — one test, one function that builds a nested string
// via cross-module match. Simplified solution-cell signature.
#[test]
fn d45_html_one_test_no_crash() {
    let td = html_reduction(HTML_ONE_TEST);
    let input = "(import [html [test-page]])\n/run-tests html\n";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_html_one_test", &out);
}

// Two tests sharing the same make-grid + page. If crashes, batched
// dispatch of 2 Grid-building tests reproduces. If PASS, the crash
// also needs the test-solution-page-mixed shape (build-mixed-helper).
const HTML_TWO_TESTS: &str = r#"(import [primitives [*]])
(import [grid [Grid Cell Given Solved Candidates cell-at cell-value]])

(defn solution-cell [g idx]
  (let [c (cell-at g idx)
        digit (int-to-string (cell-value c))]
    (match c
      [(Given _) (str-concat "g:" digit)
       _ (str-concat "s:" digit)])))

(defn row-helper [g row col acc]
  (if (eq-i64 col 9) acc
    (let [idx (add-i64 (mul-i64 row 9) col)]
      (row-helper g row (add-i64 col 1)
        (str-concat acc (solution-cell g idx))))))

(defn rows-helper [g row acc]
  (if (eq-i64 row 9) acc
    (rows-helper g (add-i64 row 1)
      (str-concat acc (row-helper g row 0 "")))))

(defn page [g] (rows-helper g 0 ""))

(defn build-helper [v i]
  (if (eq-i64 i 81) v
    (build-helper (vec-push v (Given 1)) (add-i64 i 1))))

(defn make-grid [] (Grid (build-helper [] 0)))

(defn test-page-a []
  (let [g (make-grid)]
    (if (contains? (page g) "1") None (Some "no 1"))))

(defn test-page-b []
  (let [g (make-grid)]
    (if (contains? (page g) "g:") None (Some "no g:"))))
"#;

// FIXME(/backend) — 2 tests doing same Grid-build + page. If crashes,
// the batched dispatch with shared make-grid trampoline reproduces.
#[test]
fn d45_html_two_tests_no_crash() {
    let td = html_reduction(HTML_TWO_TESTS);
    let input = "(import [html [test-page-a]])\n/run-tests html\n";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_html_two_tests", &out);
}

// Add a second make-grid variant building MIXED cells (Given 5, Solved 3,
// Given 1) via a nested if-chain. A third test uses it.
const HTML_THREE_TESTS_MIXED: &str = r#"(import [primitives [*]])
(import [grid [Grid Cell Given Solved Candidates cell-at cell-value]])

(defn solution-cell [g idx]
  (let [c (cell-at g idx)
        digit (int-to-string (cell-value c))]
    (match c
      [(Given _) (str-concat "g:" digit)
       _ (str-concat "s:" digit)])))

(defn row-helper [g row col acc]
  (if (eq-i64 col 9) acc
    (let [idx (add-i64 (mul-i64 row 9) col)]
      (row-helper g row (add-i64 col 1)
        (str-concat acc (solution-cell g idx))))))

(defn rows-helper [g row acc]
  (if (eq-i64 row 9) acc
    (rows-helper g (add-i64 row 1)
      (str-concat acc (row-helper g row 0 "")))))

(defn page [g] (rows-helper g 0 ""))

(defn build-helper [v i]
  (if (eq-i64 i 81) v
    (build-helper (vec-push v (Given 1)) (add-i64 i 1))))

(defn make-grid [] (Grid (build-helper [] 0)))

(defn build-mixed-helper [v i]
  (if (eq-i64 i 81) v
    (if (eq-i64 i 0)
      (build-mixed-helper (vec-push v (Given 5)) (add-i64 i 1))
      (if (eq-i64 i 1)
        (build-mixed-helper (vec-push v (Solved 3)) (add-i64 i 1))
        (build-mixed-helper (vec-push v (Given 1)) (add-i64 i 1))))))

(defn make-mixed-grid [] (Grid (build-mixed-helper [] 0)))

(defn test-page-a []
  (let [g (make-grid)]
    (if (contains? (page g) "1") None (Some "no 1"))))

(defn test-page-b []
  (let [g (make-grid)]
    (if (contains? (page g) "g:") None (Some "no g:"))))

(defn test-page-mixed []
  (let [g (make-mixed-grid)
        p (page g)]
    (if (contains? p "g:5")
      (if (contains? p "s:3") None (Some "no s:3"))
      (Some "no g:5"))))
"#;

// FIXME(/backend) — 3 tests, third uses a SECOND grid-build function
// (build-mixed-helper — nested if picking among 3 variants). If crashes,
// two distinct Vec-of-ADT-building functions in same module is the trigger.
#[test]
fn d45_html_three_tests_mixed_no_crash() {
    let td = html_reduction(HTML_THREE_TESTS_MIXED);
    let input = "(import [html [test-page-a]])\n/run-tests html\n";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_html_three_tests_mixed", &out);
}

// Add: wrap-tag + td + solution-cell takes TWO grid params.
// This mirrors html.cl's signature closely: solution-cell original solved idx,
// and solution-page solved original (two grid args, used g g).
const HTML_TWO_ARG_SOLUTION: &str = r#"(import [primitives [*]])
(import [grid [Grid Cell Given Solved Candidates cell-at cell-value]])

(defn wrap-tag [tag content]
  (str-concat (str-concat (str-concat "<" tag) ">")
    (str-concat content
      (str-concat (str-concat "</" tag) ">"))))

(defn td [cls content]
  (str-concat
    (str-concat (str-concat "<td class=\"" cls) "\">")
    (str-concat content "</td>")))

(defn solution-cell [original solved idx]
  (let [orig-cell (cell-at original idx)
        solved-cell (cell-at solved idx)
        digit (int-to-string (cell-value solved-cell))]
    (match orig-cell
      [(Given _) (td "given" digit)
       _ (td "solved" digit)])))

(defn row-helper [original solved row col acc]
  (if (eq-i64 col 9) acc
    (let [idx (add-i64 (mul-i64 row 9) col)]
      (row-helper original solved row (add-i64 col 1)
        (str-concat acc (solution-cell original solved idx))))))

(defn row [original solved r]
  (wrap-tag "tr" (row-helper original solved r 0 "")))

(defn rows-helper [original solved r acc]
  (if (eq-i64 r 9) acc
    (rows-helper original solved (add-i64 r 1)
      (str-concat acc (row original solved r)))))

(defn page [solved original]
  (str-concat "<table>" (str-concat (rows-helper original solved 0 "") "</table>")))

(defn build-helper [v i]
  (if (eq-i64 i 81) v
    (build-helper (vec-push v (Given 1)) (add-i64 i 1))))

(defn make-grid [] (Grid (build-helper [] 0)))

(defn test-page-digits []
  (let [g (make-grid)]
    (if (contains? (page g g) "1") None (Some "no 1"))))

(defn test-page-given []
  (let [g (make-grid)]
    (if (contains? (page g g) "given") None (Some "no given"))))
"#;

// FIXME(/backend) — 2 tests, solution-cell takes two grid params (2
// cell-at calls), wraps via td + wrap-tag.
#[test]
fn d45_html_two_arg_solution_no_crash() {
    let td = html_reduction(HTML_TWO_ARG_SOLUTION);
    let input = "(import [html [test-page-digits]])\n/run-tests html\n";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_html_two_arg_solution", &out);
}

// Strip to: 1 test, solution-cell takes two-grid params, no td/wrap-tag
// (flat str-concat). Smaller grid size (9 cells). No 9x9 outer loop.
const HTML_MIN_V1: &str = r#"(import [primitives [*]])
(import [grid [Grid Cell Given Solved Candidates cell-at cell-value]])

(defn solution-cell [original solved idx]
  (let [orig-cell (cell-at original idx)
        solved-cell (cell-at solved idx)
        digit (int-to-string (cell-value solved-cell))]
    (match orig-cell
      [(Given _) (str-concat "g:" digit)
       _ (str-concat "s:" digit)])))

(defn row-helper [original solved col acc]
  (if (eq-i64 col 9) acc
    (row-helper original solved (add-i64 col 1)
      (str-concat acc (solution-cell original solved col)))))

(defn page [original solved]
  (row-helper original solved 0 ""))

(defn build-helper [v i]
  (if (eq-i64 i 9) v
    (build-helper (vec-push v (Given 1)) (add-i64 i 1))))

(defn make-grid [] (Grid (build-helper [] 0)))

(defn test-page []
  (let [g (make-grid)]
    (if (contains? (page g g) "g:1") None (Some "no g:1"))))
"#;

// FIXME(/backend) — 1 test, 9-cell grid, flat str-concat (no wrap-tag/td),
// but retained: two-grid-param solution-cell, 2 cell-at calls, match in
// tail of let.
#[test]
fn d45_html_min_v1_no_crash() {
    let td = html_reduction(HTML_MIN_V1);
    let input = "(import [html [test-page]])\n/run-tests html\n";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_html_min_v1", &out);
}

// Even smaller: 1-cell grid, 1 call to solution-cell (no row-helper loop).
// This tests whether the iteration matters, or just one call pattern.
const HTML_MIN_V2: &str = r#"(import [primitives [*]])
(import [grid [Grid Cell Given Solved Candidates cell-at cell-value]])

(defn solution-cell [original solved idx]
  (let [orig-cell (cell-at original idx)
        solved-cell (cell-at solved idx)
        digit (int-to-string (cell-value solved-cell))]
    (match orig-cell
      [(Given _) (str-concat "g:" digit)
       _ (str-concat "s:" digit)])))

(defn make-grid [] (Grid (vec-push [] (Given 1))))

(defn test-one []
  (let [g (make-grid)]
    (if (str-eq (solution-cell g g 0) "g:1") None (Some "nope"))))
"#;

// FIXME(/backend) — 1 test, single-cell Grid, no loop, one solution-cell
// call. If crashes, the iteration loop is not needed — just calling a
// cross-module let+2xcell-at+match helper crashes.
#[test]
fn d45_html_min_v2_no_crash() {
    let td = html_reduction(HTML_MIN_V2);
    let input = "(import [html [test-one]])\n/run-tests html\n";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_html_min_v2", &out);
}

// Smallest possible form of the d45 crash: a single direct call to
// `solution-cell g g 0` from the REPL. No /run-tests harness, no Option
// wrapper, no contains?, no str-eq — just the let+2xcell-at+match body
// that returns a String, called with the same Grid passed as both args.
// This is the construct that provokes the RC-ABI bug: the polymorphic
// cell-at dispatch captures each grid arg into a closure env (inc + later
// dec on closure free), and the scope cleanup also decs the named bindings
// — but the closure-env inc is not being accounted for as an independent
// owning reference, so the combined dec count exceeds the live-ref count.
//
// spec: 12-runtime §12.3 — consuming convention RC balance across
// polymorphic dispatch with captured heap args.
#[test]
fn d45_solution_cell_single_call_no_rc_underflow() {
    let td = html_reduction(HTML_MIN_V2);
    // Two consecutive invocations: the first produces the string cleanly,
    // but the JIT artefact left over after the first call (an over-inc on
    // the string return value plus an already-freed grid param whose RC
    // has gone negative) tips into SIGTRAP on the second. A single call is
    // insufficient to observe the crash because the REPL's own displayed-
    // value dec doesn't fire before /quit.
    let input = "\
(import [html [make-grid solution-cell]])
(let [g (make-grid)] (solution-cell g g 0))
(let [g (make-grid)] (solution-cell g g 0))
/quit
";
    let out = drive_repl(td.path(), input);
    assert_no_signal_crash("d45_solution_cell_single_call", &out);
}
