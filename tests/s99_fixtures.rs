//! Sprint 99 Wave 0.3 — parallel-contention measurement fixtures (F1–F4).
//!
//! These are the committed, free-standing (zero-stdlib) regression guards for
//! the measurement ladder in `tests/fixtures/s99/`. The *timing* numbers are
//! produced out-of-band by `tests/perf/s99_measure.py` (not part of this
//! canonical suite — scheduling-dependent, flaky as hard asserts). What IS a
//! durable correctness guard, and lives here, is the **parallel ≡ serial**
//! invariant on the reshaped nested-ADT workloads: because the code is pure,
//! the speculative-parallel default and the genuinely-serial
//! `CRANELISP_NO_LENIENT=1` run MUST produce byte-identical results (here, the
//! process exit code = the fixture's checksum). A divergence is a real defect
//! (a lost-update / RC / codegen bug in the spark path). Per arch R5, these
//! land regardless of the mechanism-wave funding decision.
//!
//! spec: design/backend/lenient-eval.md §2.1 — the sparkability algorithm
//! (`find_sparkable_bindings`) produces the speculative-parallel path whose
//! result, because the code is pure, MUST equal the serial result.

#[path = "helpers/e2e.rs"]
mod e2e;
#[path = "helpers/marginal.rs"]
mod marginal;

use e2e::{Cranelisp, PreludeVariant};
use marginal::{Child, Instrument, MarginalPair};

/// Run a fixture under the given lenient mode; return (exit_code, stderr).
fn run_mode(name: &str, src: &str, serial: bool) -> (i32, String) {
    let mut c = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .file(name, src);
    if serial {
        c = c.env("CRANELISP_NO_LENIENT", "1");
    }
    let out = c.run(name).output();
    let code = out
        .status
        .code()
        .unwrap_or_else(|| panic!("{name} terminated by signal; stderr:\n{}", out.stderr));
    (code, out.stderr)
}

/// Assert the fixture compiles+runs cleanly and that the speculative-parallel
/// default and the serial (`CRANELISP_NO_LENIENT=1`) run agree.
fn assert_parallel_equals_serial(name: &str, src: &str) {
    let (par_code, par_err) = run_mode(name, src, false);
    let (ser_code, _ser_err) = run_mode(name, src, true);
    assert!(
        !par_err.contains("error"),
        "{name} produced a compile/runtime error:\n{par_err}"
    );
    assert_eq!(
        par_code, ser_code,
        "{name}: parallel exit {par_code} != serial exit {ser_code} (lost-update / RC / codegen defect in the spark path)"
    );
}

/// Run a fixture with an arbitrary env set; return (exit_code, stderr). Panics
/// (fails the test) if the child is terminated by a SIGNAL — a SIGABRT/SIGSEGV
/// from a double-free / use-after-free has no exit code, so this doubles as the
/// heap-corruption guard for the capture-borrow path.
fn run_with_env(name: &str, src: &str, envs: &[(&str, &str)]) -> (i32, String) {
    let mut c = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .file(name, src);
    for (k, v) in envs {
        c = c.env(k, v);
    }
    let out = c.run(name).output();
    let code = out.status.code().unwrap_or_else(|| {
        panic!(
            "{name} terminated by SIGNAL (heap corruption / crash) — env {envs:?}; stderr:\n{}",
            out.stderr
        )
    });
    (code, out.stderr)
}

/// Parse `rc_inc` from a `[RC_STATS] rc_inc=N rc_dec=N allocs=N deallocs=N` line.
fn rc_inc_of(stderr: &str) -> u64 {
    stderr
        .lines()
        .find_map(|l| l.split("rc_inc=").nth(1))
        .and_then(|rest| rest.split_whitespace().next())
        .and_then(|n| n.parse().ok())
        .unwrap_or_else(|| panic!("no [RC_STATS] rc_inc= line in stderr:\n{stderr}"))
}

/// Assert the fixture runs clean under the **capture-borrow toggle**
/// (`CRANELISP_CAPTURE_BORROW=1`, Sprint 99 Wave 1b, FIXME 0461) and that the
/// borrow-elided parallel run agrees with the genuinely-serial run. Because the
/// code is pure, borrowing a structurally-joined spark's captures MUST NOT
/// change the result — a divergence (or a signal) is a borrow-elision UAF /
/// lost-update defect (the S98 bug-#2 class).
fn assert_borrow_parallel_equals_serial(name: &str, src: &str) {
    let (borrow_code, borrow_err) = run_with_env(name, src, &[("CRANELISP_CAPTURE_BORROW", "1")]);
    let (serial_code, _) = run_with_env(name, src, &[("CRANELISP_NO_LENIENT", "1")]);
    assert!(
        !borrow_err.contains("error"),
        "{name} capture-borrow run produced a compile/runtime error:\n{borrow_err}"
    );
    assert_eq!(
        borrow_code, serial_code,
        "{name}: capture-borrow parallel exit {borrow_code} != serial exit \
         {serial_code} — a borrow/retain misclassification (UAF / lost update) in \
         the structurally-joined spark path (ring2-rc.md §5.5.2)"
    );
}

// spec: design/backend/ring2-rc.md §5.5.2.6 — the parallel≡serial correctness +
//       no-corruption guard for capture-by-borrow, with the toggle ON, on the
//       F1–F4 shared-grid copy-per-guess fixtures (captured `Grid`).
#[test]
fn s99_f1_capture_borrow_parallel_equals_serial() {
    assert_borrow_parallel_equals_serial("f1.cl", include_str!("fixtures/s99/f1_machinery.cl"));
}

// spec: design/backend/ring2-rc.md §5.5.2.6
#[test]
fn s99_f2_capture_borrow_parallel_equals_serial() {
    assert_borrow_parallel_equals_serial("f2.cl", include_str!("fixtures/s99/f2_contention.cl"));
}

// spec: design/backend/ring2-rc.md §5.5.2.6
#[test]
fn s99_f3_capture_borrow_parallel_equals_serial() {
    assert_borrow_parallel_equals_serial(
        "f3.cl",
        include_str!("fixtures/s99/f3_inverted_search.cl"),
    );
}

// spec: design/backend/ring2-rc.md §5.5.2.6
#[test]
fn s99_f4_capture_borrow_parallel_equals_serial() {
    assert_borrow_parallel_equals_serial("f4.cl", include_str!("fixtures/s99/f4_sudoku.cl"));
}

// spec: design/backend/ring2-rc.md §5.5.2.6 — the inc-count-drop WITNESS. With
//       the toggle ON, the per-copy shared-grid captures of F2's structurally-
//       joined apply-arg sparks become borrows, so `CRANELISP_RC_STATS`' `rc_inc`
//       drops materially vs the toggle OFF. Asserts a scheduling-independent
//       strict drop (not an exact number): borrow only ever *removes* capture
//       incs, and F2's D&C reduce reliably sparks its top-level apply-arg halves,
//       so no-borrow > borrow with a stable margin (observed ≥59 across runs;
//       the borrow count is deterministic == the serial count).
#[test]
fn s99_f2_capture_borrow_drops_rc_inc() {
    let src = include_str!("fixtures/s99/f2_contention.cl");
    let (nb_code, nb_err) = run_with_env("f2.cl", src, &[("CRANELISP_RC_STATS", "1")]);
    let (bo_code, bo_err) = run_with_env(
        "f2.cl",
        src,
        &[
            ("CRANELISP_RC_STATS", "1"),
            ("CRANELISP_CAPTURE_BORROW", "1"),
        ],
    );
    assert_eq!(
        nb_code, bo_code,
        "capture-borrow changed F2's result ({nb_code} != {bo_code}) — a correctness defect"
    );
    let no_borrow = rc_inc_of(&nb_err);
    let borrow = rc_inc_of(&bo_err);
    assert!(
        borrow < no_borrow,
        "capture-borrow must DROP rc_inc on F2 (the shared-grid spark captures \
         become borrows): no_borrow={no_borrow} borrow={borrow} (drop={})",
        no_borrow as i64 - borrow as i64
    );
}

/// Assert the fixture runs clean under the **saturation-gate toggle**
/// (`CRANELISP_SATURATION_GATE=1`, Sprint 99 Wave 1c, FIXME 0459) and that the
/// gated parallel run agrees with the genuinely-serial run. The gate is a pure
/// scheduling choice (spark iff spare worker capacity; else inline the branch via
/// the create-gate's already-correct direct arm), so it MUST NOT change the
/// result — a divergence (or a SIGNAL, caught by `run_with_env`) would be a
/// codegen/scheduling defect, not a scheduling no-op.
fn assert_saturation_gate_parallel_equals_serial(name: &str, src: &str) {
    let (gate_code, gate_err) = run_with_env(name, src, &[("CRANELISP_SATURATION_GATE", "1")]);
    let (serial_code, _) = run_with_env(name, src, &[("CRANELISP_NO_LENIENT", "1")]);
    assert!(
        !gate_err.contains("error"),
        "{name} saturation-gate run produced a compile/runtime error:\n{gate_err}"
    );
    assert_eq!(
        gate_code, serial_code,
        "{name}: saturation-gate parallel exit {gate_code} != serial exit \
         {serial_code} — inlining a saturated branch must be result-equivalent to \
         sparking it (scheduling-only; both arms produce identical values)"
    );
}

// spec: design/backend/lenient-eval.md §3.6 — the parallel≡serial + no-corruption
//       guard for the saturation-shaped spark gate, toggle ON, on F1–F4. Inlining
//       the overflow branch (direct arm) must be byte-identical to sparking it.
#[test]
fn s99_f1_saturation_gate_parallel_equals_serial() {
    assert_saturation_gate_parallel_equals_serial(
        "f1.cl",
        include_str!("fixtures/s99/f1_machinery.cl"),
    );
}

// spec: design/backend/lenient-eval.md §3.6
#[test]
fn s99_f2_saturation_gate_parallel_equals_serial() {
    assert_saturation_gate_parallel_equals_serial(
        "f2.cl",
        include_str!("fixtures/s99/f2_contention.cl"),
    );
}

// spec: design/backend/lenient-eval.md §3.6
#[test]
fn s99_f3_saturation_gate_parallel_equals_serial() {
    assert_saturation_gate_parallel_equals_serial(
        "f3.cl",
        include_str!("fixtures/s99/f3_inverted_search.cl"),
    );
}

// spec: design/backend/lenient-eval.md §3.6
#[test]
fn s99_f4_saturation_gate_parallel_equals_serial() {
    assert_saturation_gate_parallel_equals_serial(
        "f4.cl",
        include_str!("fixtures/s99/f4_sudoku.cl"),
    );
}

#[test]
fn s99_f1_machinery_parallel_equals_serial() {
    assert_parallel_equals_serial("f1.cl", include_str!("fixtures/s99/f1_machinery.cl"));
}

#[test]
fn s99_f2_contention_parallel_equals_serial() {
    assert_parallel_equals_serial("f2.cl", include_str!("fixtures/s99/f2_contention.cl"));
}

#[test]
fn s99_f3_inverted_search_parallel_equals_serial() {
    assert_parallel_equals_serial("f3.cl", include_str!("fixtures/s99/f3_inverted_search.cl"));
}

#[test]
fn s99_f4_sudoku_parallel_equals_serial() {
    assert_parallel_equals_serial("f4.cl", include_str!("fixtures/s99/f4_sudoku.cl"));
}

// spec: spec/12-runtime.md §12.3.1 — completed solved-grid workloads release
// their unreachable heap ownership.
// defect: class=rc-miscount locus=crates/cranelisp-typecheck/src/ownership/fixpoint.rs::compute_cluster_with_cap found=S121 owner=/dev fixed=S121
// Historical reproduction fixed in S121: the ownership-result correction plus
// schema-27 cache invalidation made all 23 cells GREEN; repeated solves balance
// at 4,140/4,140 and 8,279/8,279.
#[test]
fn s99_f4_solved_grid_releases_repeated_workloads() {
    let source = include_str!("fixtures/s99/f4_sudoku.cl");
    let (declarations, main_body) = source
        .split_once("(defn main []")
        .expect("f4 fixture has a main entry");
    let program = |body: &str, count: i32| {
        format!(
            "{declarations}(defn solve-once []{body}\n\
             (defn repeat-work [n]\n\
               (if (eq-i64 n 0) 0\n\
                 (match (solve-once)\n\
                   [(Pure value)\n\
                    (add-i64 (if (eq-i64 value 154) 1 0)\n\
                             (repeat-work (sub-i64 n 1)))\n\
                    _ 0])))\n\
             (defn main [] (Pure (repeat-work {count})))\n"
        )
    };
    let [once, twice] = [1, 2].map(|count| {
        let m = MarginalPair::new(
            &format!("solved-grid workload versus no-work driver, {count} executions"),
            Child::new(&program(" (Pure 154))", count)),
            Child::new(&program(main_body, count)),
        )
        .instrument(Instrument::RcStats)
        .measure();
        assert_eq!(
            m.control().exit_code(),
            Some(count),
            "{}",
            m.control().stderr
        );
        assert_eq!(
            m.subject().exit_code(),
            Some(count),
            "{}",
            m.subject().stderr
        );
        m
    });
    let report = format!("{}\n{}", once.report(), twice.report());
    assert_eq!(
        twice.control().residual() - once.control().residual(),
        0,
        "the consuming driver must not add unreachable retention\n{report}"
    );
    assert_eq!(
        twice.residual() - once.residual(),
        0,
        "an additional completed solved-grid workload must not retain unreachable owners\n{report}"
    );
}

// spec: spec/12-runtime.md §12.3.1 — a recursive vector builder releases its
// unreachable owners when its result is wrapped before returning.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/vec_codegen.rs::retain_reused_source found=S121 owner=/dev
// Identical source and compiler emitted both retaining and non-retaining COW
// paths across captures. This conditional reduction does not replace the full
// f4 guard; the source of that emission difference remains unresolved.
#[test]
fn nested_result_vec_builder_releases_repeated_workloads() {
    let program = |build_call: &str, count: i32| {
        format!(
            "(import [primitives [*]])\n\
             (deftype Grid [:(Vec Int) cells])\n\
             (defn raw [n xs]\n\
               (if (eq-i64 n 0) xs\n\
                 (raw (sub-i64 n 1) (vec-push xs 1))))\n\
             (defn boxed [n xs]\n\
               (if (eq-i64 n 0) (Some (Grid xs))\n\
                 (boxed (sub-i64 n 1) (vec-push xs 1))))\n\
             (defn repeat-work [n]\n\
               (if (eq-i64 n 0) 0\n\
                 (match {build_call}\n\
                   [(Some g) (match g [(Grid xs)\n\
                     (add-i64 (vec-len xs) (repeat-work (sub-i64 n 1)))])\n\
                    None 0])))\n\
             (defn main [] (Pure (repeat-work {count})))\n"
        )
    };
    let [once, twice] = [1, 2].map(|count| {
        let m = MarginalPair::new(
            &format!("wrapping inside versus after the vector builder, {count} executions"),
            Child::new(&program("(Some (Grid (raw 8 [])))", count)),
            Child::new(&program("(boxed 8 [])", count)),
        )
        .instrument(Instrument::RcStats)
        .measure();
        assert_eq!(
            m.control().exit_code(),
            Some(8 * count),
            "{}",
            m.control().stderr
        );
        assert_eq!(
            m.subject().exit_code(),
            Some(8 * count),
            "{}",
            m.subject().stderr
        );
        m
    });
    let report = format!("{}\n{}", once.report(), twice.report());
    assert_eq!(
        twice.control().residual() - once.control().residual(),
        0,
        "wrapping after the builder must not retain unreachable owners\n{report}"
    );
    assert_eq!(
        twice.residual() - once.residual(),
        0,
        "wrapping inside the builder must not add unreachable retention\n{report}"
    );
}

// =============================================================================
// S121 — the parameter-permuting self-call witnesses.
//
// QA allocation: `tests/plan/s121-test-plan.md` §14.2 ("Independent crash
// isolation" — retain a meaningful minimal crash reduction beside the existing
// partial witness before routing a fix), against the S121 crash attribution
// (`qa`, 2026-09-07).
//
// Both witnesses were committed FAILING-NOT-IGNORED per root `CLAUDE.md`
// §"Usability Findings and Defects"; the S121 ownership-result correction
// (`design/typecheck/ownership-inference.md` §19) flipped them, and they stay as
// the permanent regression guard for the class. Per that rule no numbered FIXME
// accompanies them, and their `// defect:` lines ride the corpus green
// (`tests/CLAUDE.md` §"Defect-repro notation").
//
// WHAT THE CELLS ASSERT: only what the language guarantees — the correct value
// under the DEFAULT configuration. `CRANELISP_NO_OWNERSHIP=1` also produced the
// correct value on every witness here (154 3/3 and 190 3/3); that knob is
// deliberately NOT asserted.
//
// PRE-CORRECTION OBSERVATIONS (measured 2026-09-07 on `18bca20d` before §19; all
// source-level plus compiler-native traces, no native debugger on this host, so
// no faulting PC was captured). Retained because they are what makes each face a
// sound oracle rather than a garbage-value assertion (`tests/CLAUDE.md`
// §"Forbidden dispositions"), not as a change history.
//
//   Merely DECLARING a self-recursive callable whose self-call PERMUTED a scalar
//   parameter into a parameter position flowing to the result made EVERY
//   callable in the module publish the ⊤ ownership summary
//   (`modes=[Owned…] result=Fresh flow=[Retained…]`, under
//   `CRANELISP_OWNERSHIP_TRACE=1`) — 5/5 callables on the reduction below,
//   including Int-only helpers and `primitives/IO.Pure$Int`; 41/41 on the
//   committed `fixtures/s99/f4_sudoku.cl` (`qa`). Un-permuting that one
//   self-call converged the same cluster instead (`mk: result=MayAliasOf(1)`;
//   the control cell below). A PRESENT `result=Fresh` is the documented
//   condition under which the callee-side return protect is elided. The CLIF for
//   the crashing frame showed an epilogue that released the accumulator and then
//   returned it, against a passing sibling that retained first (`qa`, not
//   re-measured here). The non-convergence mechanism inferred from these
//   observations is the one §19 corrects; the `// defect:` loci below name it.
//
//   * the f4 peer-list reduction died by SIGSEGV 20/20 runs with empty stdout
//     and stderr. A signal death carries no exit code, so `154` cannot be
//     reached by accident while that failure stands.
//   * the REPL face of the minimal reduction returned a pointer-shaped 64-bit
//     word — 25/25 runs distinct, every one of them ≥ 10^17 in magnitude, never
//     the small correct value. The full word makes `190` a reliable RED there
//     with no repetition.
//   * the `--run` face truncates that same word mod 256 (40/40 observed runs
//     wrong, spread over 0..249; no signal death was recorded on THIS face), so
//     a single run could land on the correct exit by coincidence. Correct
//     behaviour is deterministic — every run yields 190 — so that cell states
//     the exit over eight independent runs, which is a sound strengthening of
//     the exit-code oracle. It is NOT a quantified accidental-green probability:
//     neither the per-run distribution of the truncated byte nor independence
//     across runs is measured. The deterministic REDs for the class are the REPL
//     face and the crash cell. No `--link` face is committed: it truncates the
//     same word (5/5 runs wrong, spread 45..237).
// =============================================================================

/// The committed f4 declarations and the puzzle its `main` embeds. Composed the
/// same way `s99_f4_solved_grid_releases_repeated_workloads` composes them, so
/// the reduction below stays bound to the committed fixture rather than to a
/// copy of it.
fn f4_declarations_and_puzzle() -> (&'static str, &'static str) {
    let source = include_str!("fixtures/s99/f4_sudoku.cl");
    let (declarations, main_body) = source
        .split_once("(defn main []")
        .expect("f4 fixture has a main entry");
    let puzzle = main_body
        .split('"')
        .nth(1)
        .expect("f4 main embeds its puzzle as a string literal");
    (declarations, puzzle)
}

/// Run a source under `--run` with no prelude; return the raw `CrOutput`.
fn run_source(name: &str, src: &str) -> e2e::CrOutput {
    Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .file(name, src)
        .run(name)
        .output()
}

/// Assert a `--run` child reached `expected`, naming a signal death explicitly:
/// a use-after-free that faults has no exit code at all, and reporting it as
/// "expected N, got None" hides which failure mode was observed.
fn assert_run_exit(name: &str, src: &str, expected: i32, why: &str) {
    let out = run_source(name, src);
    match out.status.code() {
        Some(code) if code == expected => {}
        Some(code) => panic!(
            "{name}: expected exit {expected}, got {code} — {why}\nstdout:\n{}\nstderr:\n{}",
            out.stdout, out.stderr
        ),
        None => panic!(
            "{name}: expected exit {expected}, but the child was KILLED BY A SIGNAL \
             (status={:?}) — {why}\nstdout:\n{}\nstderr:\n{}",
            out.status, out.stdout, out.stderr
        ),
    }
}

/// The last `:primitives/Int N` value rendered by a piped REPL capture.
fn last_repl_int(stdout: &str) -> i64 {
    let line = stdout
        .lines()
        .rev()
        .find(|l| l.contains(":primitives/Int"))
        .unwrap_or_else(|| panic!("no `:primitives/Int` value line in:\n{stdout}"));
    line.rsplit(":primitives/Int ")
        .next()
        .and_then(|tail| tail.split_whitespace().next())
        .and_then(|tok| tok.parse::<i64>().ok())
        .unwrap_or_else(|| panic!("could not parse the Int value from line: {line:?}"))
}

/// The builder/consumer pair under test, shared by the witness and its control.
/// `mk` pushes 0..19 onto its accumulator and RETURNS that accumulator — the
/// callable whose return protect the ⊤ summary elides. `sum` folds it, so the
/// program's value is 0+1+…+19 = 190.
const S121_BUILDER_AND_CONSUMER: &str = concat!(
    "(defn mk [i acc] (if (eq-i64 i 20) acc (mk (add-i64 i 1) (vec-push acc i))))\n",
    "(defn sum [pl i acc]\n",
    "  (if (eq-i64 i (vec-len pl)) acc (sum pl (add-i64 i 1) (add-i64 acc (vec-get pl i)))))\n"
);

/// The expected fold of `mk`'s vector: 0+1+…+19.
const S121_BUILDER_SUM: i32 = 190;

/// The QA-allocated minimal reduction (`cases/v23.cl`, verbatim). `f` is never
/// CALLED — declaring it is enough — so nothing about `f`'s own runtime
/// behaviour is under test here; the value under test is the ordinary
/// builder/consumer pair beside it.
fn permuting_self_call_program(tail: &str) -> String {
    format!(
        "(import [primitives [*]])\n\
         (defn f [i b] (if (eq-i64 i 0) b (f b i)))\n\
         {S121_BUILDER_AND_CONSUMER}{tail}"
    )
}

// spec: spec/12-runtime.md §12.3.1 — Requirements (2): freed memory MUST NOT be
// accessed after deallocation. `eliminate-from-peers-helper` walks a peer list
// produced by a recursive `vec-push` builder that returns its own accumulator
// parameter. On the committed already-solved grid, eliminating digit 0 from a
// two-element peer list leaves every cell untouched, so the program's checksum
// is the fixture's own solved-grid checksum, 154 — the same value
// `s99_f4_sudoku_parallel_equals_serial` pins. Before the §19 correction the
// builder's vector was released to zero immediately after construction and the
// consumer read it: SIGSEGV, 20/20 runs, empty stdout and stderr.
// defect: class=uaf locus=crates/cranelisp-typecheck/src/ownership/fixpoint.rs::compute_cluster_with_cap found=S121 owner=/dev
#[test]
fn s99_f4_recursive_peer_list_builder_returns_the_solved_checksum() {
    let (declarations, puzzle) = f4_declarations_and_puzzle();
    let program = format!(
        "{declarations}\
         (defn mk [i acc]\n\
         \x20 (if (eq-i64 i 2) acc (mk (add-i64 i 1) (vec-push acc (add-i64 i 1)))))\n\
         (defn efp-mk [g idx d] (eliminate-from-peers-helper g (mk 0 []) d 0))\n\
         (defn main []\n\
         \x20 (match (make-grid \"{puzzle}\")\n\
         \x20   [None (Pure 0)\n\
         \x20    (Some g)\n\
         \x20      (match (efp-mk g 0 0)\n\
         \x20        [None (Pure 1)\n\
         \x20         (Some g2) (Pure (rem-i64 (checksum g2) 251))])]))\n"
    );
    assert_run_exit(
        "f4_peer_list_reduction.cl",
        &program,
        154,
        "a peer list returned by a recursive `vec-push` builder MUST stay live for \
         its consumer; today the builder's return protect is elided under the \
         module-wide ⊤ ownership summary and the vector is freed before \
         `eliminate-from-peers-helper` reads it",
    );
}

// spec: spec/12-runtime.md §12.3.1 — Requirements (2): freed memory MUST NOT be
// accessed after deallocation. The REPL face of the minimal reduction, and the
// DETERMINISTIC one: the pre-correction freed-heap read rendered a
// pointer-shaped 64-bit word (25/25 runs, all ≥ 10^17), never the correct 190.
// defect: class=uaf locus=crates/cranelisp-typecheck/src/ownership/fixpoint.rs::compute_cluster_with_cap found=S121 owner=/dev
#[test]
fn parameter_permuting_self_call_repl_yields_the_builder_sum() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::None)
        .stdin(&permuting_self_call_program("(sum (mk 0 []) 0 0)\n"))
        .output();
    let value = last_repl_int(&out.stdout);
    assert_eq!(
        i64::from(S121_BUILDER_SUM),
        value,
        "a vector returned by a recursive builder through its own accumulator \
         parameter MUST stay live for its consumer: `(sum (mk 0 []) 0 0)` MUST \
         render 190. Got the pointer-shaped word {value} — merely DECLARING the \
         parameter-permuting `f` beside the pair publishes the ⊤ ownership \
         summary for every callable in the module, whose present `result=Fresh` \
         elides `mk`'s return protect.\nstdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/12-runtime.md §12.6 — Entry Point: the program's exit code is the
// integer inside the `IO Int` returned by `main`, here the fixed fold 190. The
// `--run` face of the same reduction, preserving the exit-code oracle QA
// allocated. Stated over eight independent runs because the defect's wrong value
// is this same freed-heap word truncated mod 256, and correct behaviour is
// deterministic (every run yields 190) — a sound strengthening of the oracle,
// not a quantified accidental-green probability (see the basket header).
// Pre-correction: 40/40 runs wrong, spread over 0..249, no signal death on this
// face; the signal deaths belong to the f4 peer-list cell above.
// defect: class=uaf locus=crates/cranelisp-typecheck/src/ownership/fixpoint.rs::compute_cluster_with_cap found=S121 owner=/dev
#[test]
fn parameter_permuting_self_call_run_yields_the_builder_sum() {
    let program = permuting_self_call_program("(defn main [] (Pure (sum (mk 0 []) 0 0)))\n");
    for attempt in 1..=8 {
        assert_run_exit(
            "permuting_self_call.cl",
            &program,
            S121_BUILDER_SUM,
            &format!(
                "run {attempt}/8 — the builder's vector MUST survive its return; \
                 today the module-wide ⊤ summary elides `mk`'s return protect and \
                 the exit code is a freed-heap word truncated mod 256"
            ),
        );
    }
}

// spec: spec/12-runtime.md §12.6 — Entry Point: the same builder/consumer pair
// beside a self-recursive `f` whose self-call does NOT permute its parameters
// MUST also yield 190 — and does, 20/20 runs (GREEN control).
//
// This is the discriminating sibling for the two witnesses above: it holds the
// builder, the consumer, the arity of `f`, and `f`'s result-is-a-parameter shape
// fixed, and varies ONLY the argument order of the self-call — `(f i b)` here
// against `(f b i)` in the witness. The `:Int` annotations are load-bearing and
// not decoration: without them `b` stays polymorphic once the permutation is
// removed, `f` never enters the analysed callable universe at all, and the
// control would pass for the wrong reason (the trap `qa` recorded against its
// own v18–v20 siblings). With them, `CRANELISP_OWNERSHIP_TRACE=1` shows `f`
// present in the universe and the cluster CONVERGED — `mk: result=MayAliasOf(1)`
// rather than the witness's `result=Fresh` — which is what makes this control
// discriminate the permutation rather than universe membership. (The same
// annotated source WITH the permutation restored reproduces the witness: 20/20
// runs wrong, ⊤ 5/5 — so the annotation is not the cure. Measured 2026-09-07;
// see the S121 test report.)
#[test]
fn non_permuting_self_call_control_yields_the_builder_sum() {
    let program = format!(
        "(import [primitives [*]])\n\
         (defn f [:Int i :Int b] (if (eq-i64 i 0) b (f i b)))\n\
         {S121_BUILDER_AND_CONSUMER}(defn main [] (Pure (sum (mk 0 []) 0 0)))\n"
    );
    assert_run_exit(
        "non_permuting_self_call.cl",
        &program,
        S121_BUILDER_SUM,
        "the control's self-call does not permute its parameters, its cluster \
         converges, and the builder's return protect is emitted",
    );
}

// =============================================================================
// S103 increment-II — the F2v single-ctor witness fixture (qa plan
// `tests/plan/s103-test-plan.md` §1.1, gate II-G1). F2v is the honest R5
// witness: one-word single-constructor `(Cell [:Int value])`, the shape R5's
// first landing (backend §7.1/§7.2) genuinely flattens. The *timing*/rc_inc
// gate itself is a perf lane (`ig_gates.py`, §2); the durable in-suite
// correctness guard is the same parallel≡serial invariant the F1–F4 rows carry
// — GREEN at draft (holds off-mechanism, because the code is pure) and
// LOAD-BEARING through R5: a flattening that corrupts the by-value copy path
// diverges the parallel and serial checksums here.
// =============================================================================

// spec: design/backend/lenient-eval.md §2.1 — the sparkability algorithm's
// speculative-parallel result MUST equal the serial result on the F2v
// single-ctor reshaped workload (parallel ≡ serial). GREEN at draft.
#[test]
fn s99_f2v_single_ctor_parallel_equals_serial() {
    assert_parallel_equals_serial("f2v.cl", include_str!("fixtures/s99/f2v_single_ctor.cl"));
}

// spec: design/backend/ring2-rc.md §5.5.2.6 — the capture-borrow parallel≡serial
// + no-corruption guard on F2v (the R5-witness shape). GREEN at draft;
// load-bearing when the borrow-elision + R5 flattening seams both run.
#[test]
fn s99_f2v_single_ctor_capture_borrow_parallel_equals_serial() {
    assert_borrow_parallel_equals_serial("f2v.cl", include_str!("fixtures/s99/f2v_single_ctor.cl"));
}

// =============================================================================
// S103 increment-II — L-B2(ii) byte-differential on the write-path fixtures
// (qa plan §1.2 / §4). `CRANELISP_NO_OWNERSHIP=1` is the permanent correctness
// oracle: R5 flattening is representation-internal + toggle-gated (toggle-off
// forces all-heap, byte-identical to pre-R5), so the OBSERVABLE output of F2v
// must be byte-identical with the toggle ON vs OFF regardless of which
// mechanism has landed. GREEN at draft (nothing flattens yet) and LOAD-BEARING
// when R5 lands — a flattening that changes an observable value fails here.
// Each session pins its polarity EXPLICITLY (env_remove for OFF) so the legs
// hold under the ambient-polarity L-B2(i) suite run.
// =============================================================================

/// Run a fixture under an explicit ownership-toggle polarity; return
/// (exit_code, stdout). Panics (fails) on a SIGNAL — a toggle-induced heap
/// corruption has no exit code.
fn run_ownership_polarity(name: &str, src: &str, no_ownership: bool) -> (i32, String) {
    let mut c = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .file(name, src);
    c = if no_ownership {
        c.env("CRANELISP_NO_OWNERSHIP", "1")
    } else {
        c.env_remove("CRANELISP_NO_OWNERSHIP")
    };
    let out = c.run(name).output();
    let code = out.status.code().unwrap_or_else(|| {
        panic!("{name} terminated by SIGNAL under ownership polarity no_ownership={no_ownership}; stderr:\n{}", out.stderr)
    });
    (code, out.stdout)
}

/// Assert a fixture's observable output (exit code + stdout) is byte-identical
/// under both ownership-toggle polarities — the L-B2(ii) differential oracle.
fn assert_ownership_toggle_byte_identical(name: &str, src: &str) {
    let (off_code, off_out) = run_ownership_polarity(name, src, false);
    let (on_code, on_out) = run_ownership_polarity(name, src, true);
    assert_eq!(
        off_code, on_code,
        "{name}: ownership-toggle changed the exit value (off {off_code} != on {on_code}) — \
         the CRANELISP_NO_OWNERSHIP oracle demands byte-identical observable output \
         (qa plan §4; s100-ownership-verification.md §0.1)"
    );
    assert_eq!(
        off_out, on_out,
        "{name}: ownership-toggle changed stdout — off:\n{off_out}\non:\n{on_out}"
    );
}

// spec: tests/plan/s100-ownership-verification.md §3.1 — L-B2(ii) byte-
// differential on F2v: toggle-on ≡ toggle-off observable output for the R5
// witness. GREEN at draft; discriminating once R5 lands.
#[test]
fn s99_f2v_output_byte_identical_under_ownership_toggle() {
    assert_ownership_toggle_byte_identical(
        "f2v.cl",
        include_str!("fixtures/s99/f2v_single_ctor.cl"),
    );
}

// spec: tests/plan/s100-ownership-verification.md §3.1 — L-B2(ii) byte-
// differential on F2 (the two-ctor nested-ADT witness) as the reuse-token
// oracle: reuse tokens are off-ABI/function-local, so toggle-off forces the
// conservative dealloc+alloc path — byte-identical to pre-reuse codegen.
// GREEN at draft; load-bearing when reuse tokens land.
#[test]
fn s99_f2_output_byte_identical_under_ownership_toggle() {
    assert_ownership_toggle_byte_identical("f2.cl", include_str!("fixtures/s99/f2_contention.cl"));
}
