//! Sprint 61 Slice 2 — exemplar solver correctness regression guards.
//!
//! Two regression guards, both originally authored FAILING per
//! `memory/feedback_failing_not_ignored.md` + Sprint 61 Wave 2 branch-(b)
//! handoff protocol. Both flipped green when /port's Layer 1 fix in
//! `exemplar/solver.cl::eliminate` + /backend's Layer 3 fix in
//! `crates/cranelisp-backend/src/compiler/mod.rs::is_last_use` landed
//! together in Wave 2. See `tests/plan/baseline.md §"Resolved this sprint"`.
//!
//! Sprint 61 Wave 5 / Slice 5 Item I migration (2026-04-22, user directive):
//! per `memory/feedback_repro_handoff.md`, minimal repros MUST live in
//! `tests/`, not in `exemplar/`. Both tests now construct their inputs
//! inline as string literals written to fresh `tempfile::TempDir` trees —
//! no dependency on `exemplar/repro-slice2.cl` or
//! `exemplar/test-eliminate-contract.cl` as external `.cl` fixtures.
//!
//! ## Migration rationale
//!
//! Before Wave 5 both tests subprocess-ran `.cl` files that had been
//! authored by /port (Layer 3 repro) and /qa (Layer 1 contract fixture).
//! Those files lived in `exemplar/` because Slice 2 landed under time
//! pressure — /port's scope violations and /qa's scope violations were
//! caught in /review but the mechanical migration was deferred to this
//! wave. The user directive 2026-04-22 makes the discipline explicit:
//! compiler regression guards MUST NOT depend on `exemplar/`, which is a
//! user-facing showcase subject to removal / relocation / replacement.
//!
//! /port is the follow-on agent — it deletes `exemplar/repro-slice2.cl` +
//! `exemplar/test-eliminate-contract.cl` and updates the FIXME block at
//! `exemplar/solver.cl:370+` to point at the test functions in this file
//! rather than the now-removed `.cl` sources.

use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

// ---------------------------------------------------------------------------
// Subprocess harness — both tests drive `./cranelisp --run <file>` on a
// fresh TempDir containing the inlined repro source. Each test is
// independent; no shared state, no checked-in fixtures.
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

/// Copy the subset of `exemplar/*.cl` modules that T-S2-1 imports into a
/// fresh TempDir, then write the inline repro source next to them so the
/// subprocess's `--run` resolves `[grid ...]` and `[solver ...]` imports
/// relative to the TempDir cwd.
///
/// The test only needs `grid.cl` + `solver.cl` because T-S2-1 imports
/// `(import [grid [Grid Cell Given Solved Candidates cell-at set-cell]])`
/// and `(import [solver [eliminate]])`.
fn tempdir_with_exemplar_modules(modules: &[&str]) -> (tempfile::TempDir, PathBuf) {
    let td = tempfile::tempdir().expect("TempDir creation");
    let exemplar = project_root().join("exemplar");
    for m in modules {
        let src = exemplar.join(m);
        let dst = td.path().join(m);
        std::fs::copy(&src, &dst)
            .unwrap_or_else(|e| panic!("copy {} into tempdir: {e}", src.display()));
    }
    let cwd = td.path().to_path_buf();
    (td, cwd)
}

/// Run `cranelisp --run <relative_cl>` in the given TempDir-rooted cwd.
fn run_cl(cwd: &std::path::Path, relative_cl: &str) -> Output {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} — run `cargo build` first"
    );
    Command::new(&binary)
        .args(["--run", relative_cl])
        .current_dir(cwd)
        .env("CRANELISP_LIB", stdlib_dir())
        .env("CRANELISP_PLATFORM_PATH", platform_dir())
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("failed to invoke cranelisp")
}

fn stdout_str(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}

fn stderr_str(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

// ===========================================================================
// T-S2-1 — Layer 1 contract: `eliminate` on a same-value Given/Solved cell
// MUST return None (a contradiction), not (Some g).
//
// The inline repro below builds a minimal grid with `(Given 5)` at cell 0
// and calls `(eliminate g 0 5)`. `main` returns:
//   0 — pass (eliminate returned None, per the Layer 1 contract)
//   1 — fail (eliminate returned (Some _); pre-fix buggy behaviour)
//   2 — setup failure (unexpected)
//
// This cargo-level assertion asserts exit == 0. Post-fix state: exit == 0.
// If this test ever starts returning exit 1, /backend's Layer 3 fix in
// `is_last_use` has regressed and the naive Layer 1 eliminate patch in
// solver.cl re-fails through the backtracking path.
// ===========================================================================

// spec: tests/plan/ring4.md §"Slice 2 branch-b outcome" T-S2-1;
//       exemplar/solver.cl:370+ FIXME block — Layer 1 eliminate contract;
//       memory/feedback_cross_skill_minimal_repro.md — minimal repro;
//       memory/feedback_repro_handoff.md — migration target for this file.
const ELIMINATE_CONTRACT_SOURCE: &str = r#";; T-S2-1 inline repro (migrated from exemplar/test-eliminate-contract.cl
;; into tests/ per memory/feedback_repro_handoff.md, Sprint 61 Slice 5 I).
;;
;; CONTRACT: eliminate on a cell already fixed at value v, asked to
;; eliminate digit d, MUST return None when v == d (contradiction —
;; eliminating the cell's own fixed value).
;;
;; Exit semantics: 0 = pass, 1 = contract violated, 2 = setup failure.

(platform stdio)
(import [primitives [*]])

(import [grid [Grid Cell Given Solved Candidates
               cell-at set-cell]])
(import [solver [eliminate]])

;; Build a grid where cell 0 is (Given 5) and the remaining 80 cells are
;; (Given 1). All cells are Given so no Candidates appear. Not a legal
;; Sudoku grid, but the test only exercises cell 0.
(defn build-grid-given-5-helper [v i]
  (if (eq-i64 i 81) v
    (if (eq-i64 i 0)
      (build-grid-given-5-helper (vec-push v (Given 5)) (add-i64 i 1))
      (build-grid-given-5-helper (vec-push v (Given 1)) (add-i64 i 1)))))

(defn make-given-5-grid []
  (Grid (build-grid-given-5-helper [] 0)))

(defn main []
  (let [g (make-given-5-grid)]
    ;; Setup sanity: cell 0 should be (Given 5).
    (match (cell-at g 0)
      [(Given v)
         (if (eq-i64 v 5)
           (match (eliminate g 0 5)
             [None 0
              (Some _) 1])
           2)
       _ 2])))
"#;

// spec: tests/plan/ring4.md §"Slice 2 branch-b outcome" T-S2-1
#[test]
fn eliminate_on_same_value_given_returns_none() {
    // T-S2-1 needs grid.cl (Grid, Cell, constructors, cell-at, set-cell)
    // and solver.cl (eliminate).
    let (td, cwd) = tempdir_with_exemplar_modules(&["grid.cl", "solver.cl"]);
    let entry = cwd.join("t_s2_1_repro.cl");
    std::fs::write(&entry, ELIMINATE_CONTRACT_SOURCE).expect("write repro");
    let o = run_cl(&cwd, "t_s2_1_repro.cl");
    let exit = o.status.code();

    assert_eq!(
        exit, Some(0),
        "`eliminate` on `(Given 5)` at cell 0 with digit 5 MUST return \
         None (contradiction — eliminating the cell's own fixed value). \
         Exit 0 = pass, 1 = eliminate returned (Some _), 2 = setup failure. \
         Got exit={exit:?}\nstdout: {}\nstderr: {}",
        stdout_str(&o),
        stderr_str(&o),
    );
    drop(td);
}

// ===========================================================================
// T-S2-2 — Layer 3 compiler bug: inline ADT constructor wrapping Vec,
// passed as a function argument, corrupts the inner Vec's length.
//
// The inline repro prints three lines:
//   direct-let: len=1   ; baseline — let-binding alone produces len=1
//   inline-arg: len=1   ; bug trigger — (consume (Box [0])) — SHOULD be len=1
//   let-arg:    len=1   ; workaround — (let [b (Box [0])] (consume b)) — len=1
//
// Pre-fix state (Sprint 61 Wave 2, SHA a9028c0): inline-arg printed len=0
// due to consuming-arg RC double-drop on inline ADT constructors wrapping
// a Vec. Post-fix (HEAD): all three print len=1.
//
// If this test ever regresses to `inline-arg: len=0`, /backend's
// `is_last_use` gate on `borrowed_vars` (ring2-rc.md §5.5) has regressed.
// ===========================================================================

// spec: tests/plan/ring4.md §"Slice 2 branch-b outcome" T-S2-2;
//       memory/feedback_repros_join_suite.md — committed failing repros;
//       design/backend/ring2-rc.md §5.5 — borrowed_vars rule
//       (regression history names this repro shape inline).
const INLINE_ADT_ARG_SOURCE: &str = r#";; T-S2-2 inline repro (migrated from exemplar/repro-slice2.cl into
;; tests/ per memory/feedback_repro_handoff.md, Sprint 61 Slice 5 I).
;;
;; ISOLATED COMPILER BUG (pre-fix): inline ADT constructor holding a Vec,
;; passed as a function argument, results in the Vec being corrupted
;; (zero-length) when the callee performs vec-set.
;;
;; Expected output (post-fix):
;;   direct-let: len=1
;;   inline-arg: len=1
;;   let-arg:    len=1

(platform stdio)
(import [primitives [*]])
(import [platform.stdio [print]])
(import [primitives [bind Pure]])

(deftype Box [cells])

(defn box-set [b idx x] (match b [(Box v) (Box (vec-set v idx x))]))
(defn box-len [b] (match b [(Box v) (vec-len v)]))

(defn consume [b] (box-set b 0 1))

(defn int-to-digit [n]
  (if (eq-i64 n 0) "0"
  (if (eq-i64 n 1) "1"
  (if (eq-i64 n 2) "2"
  (if (eq-i64 n 3) "3" "?")))))

(defn main []
  (let [b1 (Box [0])
        r1 (box-set b1 0 1)
        len1 (box-len r1)
        ;; Bug trigger: inline (Box [0]) passed directly to consume.
        r2 (consume (Box [0]))
        len2 (box-len r2)
        ;; Workaround: let-bind the Box first.
        b3 (Box [0])
        r3 (consume b3)
        len3 (box-len r3)]
    (bind (print (str-concat "direct-let: len=" (int-to-digit len1)))
      (fn [_]
        (bind (print (str-concat "inline-arg: len=" (int-to-digit len2)))
          (fn [_]
            (print (str-concat "let-arg:    len=" (int-to-digit len3)))))))))
"#;

// spec: tests/plan/ring4.md §"Slice 2 branch-b outcome" T-S2-2
#[test]
fn inline_adt_arg_wrapping_vec_preserves_len() {
    // T-S2-2 is self-contained — no exemplar module imports needed.
    let td = tempfile::tempdir().expect("tempdir");
    let entry = td.path().join("t_s2_2_repro.cl");
    std::fs::write(&entry, INLINE_ADT_ARG_SOURCE).expect("write repro");
    let o = run_cl(td.path(), "t_s2_2_repro.cl");

    assert!(
        o.status.success(),
        "T-S2-2 inline repro MUST exit cleanly (exit 0); non-zero exit \
         indicates a runtime failure separate from the length-corruption \
         bug. Got exit={:?}\nstdout: {}\nstderr: {}",
        o.status.code(),
        stdout_str(&o),
        stderr_str(&o),
    );

    let out = stdout_str(&o);

    // The direct-let and let-arg baselines must remain len=1.
    assert!(
        out.contains("direct-let: len=1"),
        "T-S2-2 baseline (direct-let) MUST print `direct-let: len=1`; \
         regression would invalidate the repro's framing. Got stdout:\n{out}"
    );
    assert!(
        out.contains("let-arg:    len=1"),
        "T-S2-2 workaround (let-arg) MUST print `let-arg:    len=1`. \
         Got stdout:\n{out}"
    );

    // The Layer 3 contract: inline-arg MUST also print `len=1`.
    assert!(
        out.contains("inline-arg: len=1"),
        "T-S2-2 Layer 3 contract VIOLATED — `(consume (Box [0]))` reads \
         the inner Vec's length as 0 instead of 1. Expected \
         `inline-arg: len=1`; got stdout:\n{out}\n\
         Regression surface for inline-ADT-arg-wrapping-Vec codegen bug \
         (design/backend/ring2-rc.md §5.5 borrowed_vars rule)."
    );
    drop(td);
}
