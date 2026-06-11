//! Sprint 64 Wave 6 batch 1 carry-forward — backend codegen regression guards.
//!
//! Defect repros — durable regression guards per
//! `memory/feedback_repros_join_suite.md`. This file holds self-contained
//! codegen regression tests that are NOT spec-conformance tests and NOT
//! example/exemplar correctness tests; they are guards against named
//! historical defects.
//!
//! (carry: legacy/exemplar_solver_correctness.rs::inline_adt_arg_wrapping_vec_preserves_len)

#[path = "helpers/e2e.rs"]
mod e2e;

use e2e::{Cranelisp, PreludeVariant};

// =============================================================================
// T-S2-2 — Layer-3 backend codegen: inline ADT constructor wrapping a Vec,
//          passed as a function argument, MUST NOT corrupt the inner Vec's
//          length.
// =============================================================================
//
// Per Sprint 61 Slice 2 history (and design/backend/ring2-rc.md §5.5
// borrowed_vars rule): pre-fix, `(consume (Box [0]))` read the inner
// Vec's length as 0 because the consuming-arg RC emission for inline
// ADT constructors wrapping a Vec dropped the inner Vec's length before
// the callee's match-unwrap. Post-fix, all three call shapes
// (direct-let, inline-arg, let-arg) read len=1.
//
// This test is self-contained — no exemplar/ source dependency — so it
// belongs in a defect-repro file rather than tests/exemplar.rs.

// spec: design/backend/ring2-rc.md §5.5 — Captured and Borrowed Variables
//       and Last-Use (regression history names this repro shape inline).
//       Cross-references the archived tests/plan/legacy/ring4.md
//       "Slice 2 branch-b outcome" T-S2-2 entry.
//
// FIXME(/spec): borrowed_vars is a backend implementation invariant, not
// a normatively-spec'd language behaviour. The user-observable surface
// is "ADT constructor wrapping Vec preserves length under all call
// shapes"; the design-doc citation is the closest normative anchor.
//
// (carry: legacy/exemplar_solver_correctness.rs::inline_adt_arg_wrapping_vec_preserves_len)
#[test]
fn t_s2_2_inline_adt_arg_wrapping_vec_preserves_len() {
    // Three call shapes are exercised. All three must print len=1.
    //   direct-let: baseline — let-binding alone produces len=1
    //   inline-arg: bug trigger — (consume (Box [0])) — must be len=1
    //   let-arg:    workaround — (let [b (Box [0])] (consume b))
    //
    // Pre-fix: `inline-arg` printed len=0 due to consuming-arg RC
    // double-drop on inline ADT constructors wrapping Vec.
    // Post-fix: all three print len=1.
    let source = r#"(platform stdio)
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

    let out = Cranelisp::new()
        .run("main.cl")
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .use_workspace_platforms()
        .file("main.cl", source)
        .output()
        .assert_ok();

    // The Layer-3 contract: all three lines must report len=1.
    out.assert_stdout_contains_all(&[
        "direct-let: len=1",
        "inline-arg: len=1",
        "let-arg:    len=1",
    ]);
}

// =============================================================================
// Sprint 59 Defects 4+5 reductions — `/run-tests` batched-dispatch crashes
// =============================================================================
//
// Carry-forward from `tests/legacy/sprint59_defects456_repro.rs` per Wave 6
// batch 3 audit (`tests/plan/wave-6-batch-3-audit.md`). Each test is a
// reduction rung — "this small shape passes; this slightly larger shape
// fails" — narrowing the historic Defects 4+5 surface (the
// `/run-tests <mod>` REPL command crashing with SIGSEGV/SIGTRAP when the
// dispatched test bodies exceed certain shapes).
//
// All tests assert "child process did NOT crash by signal" via
// `did_not_crash_by_signal` — exit None / exit 139 (SIGSEGV) / exit 133
// (SIGTRAP) all indicate the underlying defect reproduces.
//
// Pre-Sprint 63 inline `FIXME(/backend)` hypothesis comments are preserved
// verbatim from the legacy file — they document the discrimination
// calibration ("if this PASSES, the next axis is X; if this FAILS, the
// defect is in Y"). Per `tests/plan/wave-6-batch-3-audit.md` §"Tests
// flagged for /sprint judgment" §B, the inline FIXMEs migrate to
// numbered fixme files at FIXME 0145 close, not at carry-forward time.
// =============================================================================

use std::path::Path;

/// Assert the subprocess did NOT crash by signal. Exit None / 139
/// (SIGSEGV) / 133 (SIGTRAP) indicate the underlying defect reproduces.
fn assert_no_signal_crash(label: &str, out: &e2e::CrOutput) {
    let exit = out.status.code();
    let crashed = matches!(exit, Some(139) | Some(133)) || exit.is_none();
    if crashed {
        panic!(
            "{label}: child process crashed with exit={exit:?} \
             (139=SIGSEGV, 133=SIGTRAP, None=killed by signal). \
             This is the reduced reproduction of the underlying defect.\n\
             --- stdout ---\n{}\n--- stderr ---\n{}",
            out.stdout, out.stderr
        );
    }
}

/// Copy `exemplar/` into `<tmpdir>/exemplar/` for d6 + d45 tests that need
/// the real exemplar source. Used for the four open-Defect-6 ledger entries
/// (`d6_exemplar_*`) and the d45 real-exemplar reductions.
///
/// Per `tests/CLAUDE.md` §"Fresh Temp Directory per Test", reads from
/// `project_root().join("exemplar")` — this is read-only on a checked-in
/// path (`exemplar/` is not modified) so the // read-only annotation
/// applies.
fn copy_exemplar_into(tmpdir: &Path, dst_subdir: &str) {
    // read-only on project_root: copies exemplar/ tree into the per-test
    // tmpdir; never writes to exemplar/.
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("exemplar");
    let dst = tmpdir.join(dst_subdir);
    copy_dir_recursive(&src, &dst).expect("copy exemplar tree");
}

fn copy_dir_recursive(src: &Path, dst: &Path) -> std::io::Result<()> {
    std::fs::create_dir_all(dst)?;
    for entry in std::fs::read_dir(src)? {
        let entry = entry?;
        let name = entry.file_name();
        if let Some(s) = name.to_str()
            && s.starts_with('.')
        {
            // Skip dotfiles (`.cranelisp-cache/`, etc.) so test runs are
            // not contaminated by checked-in cache state.
            continue;
        }
        let from = entry.path();
        let to = dst.join(&name);
        let ft = entry.file_type()?;
        if ft.is_dir() {
            copy_dir_recursive(&from, &to)?;
        } else if ft.is_file() {
            std::fs::copy(&from, &to)?;
        }
    }
    Ok(())
}

// =============================================================================
// §A — d45: synthetic single-file modules under /run-tests
// =============================================================================

const TRIVIAL_MOD: &str = r#";; Trivial test module — sanity check that the subprocess harness works
;; for /run-tests at all. Should pass (no crash).
(import [primitives [*]])

(defn test-none-ok [] None)
"#;

// spec: repl/spec.md §16.3 — /run-tests
//
// FIXME(/backend) — If this test PASSES consistently, the crash is not a
// bare "/run-tests dispatches N tests" issue. Narrows attention to body
// shape. If this test FAILS (crashes), then the defect is in the batched
// dispatch loop itself, independent of body content.
//
// REGRESSION-GUARD: Sprint 59 Defects 4+5 — baseline rung.
//
// (carry: legacy/sprint59_defects456_repro::d45_baseline_trivial_run_tests_no_crash)
#[test]
fn d45_baseline_trivial_run_tests_no_crash() {
    let out = Cranelisp::new()
        .repl()
        .file("mymod.cl", TRIVIAL_MOD)
        .stdin("(import [mymod [test-none-ok]])\n/run-tests mymod\n")
        .output();
    assert_no_signal_crash("d45_baseline_trivial", &out);
    // Extra assertion: the test must actually run, not silently vanish
    // (prevents the test from becoming a vacuous pass if discovery breaks).
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("test-none-ok") && (combined.contains(" ok") || combined.contains("passed")),
        "baseline trivial test did not run — discovery broke.\n{combined}"
    );
}

const SIMPLE_CONTAINS_MOD: &str = r#";; One test body with a simple str-concat + contains? — no Grid, no ADT.
;; This is the smallest shape of html.cl's tests.
(import [primitives [*]])

(defn test-simple-contains []
  (if (contains? (str-concat "hello" "world") "world") None
    (Some "expected 'world' in concatenation")))
"#;

// spec: repl/spec.md §16.3 — /run-tests, single str-concat body
//
// FIXME(/backend) — Isolates whether a single str-concat+contains? test
// body through /run-tests is enough to crash. If PASS: need to widen to
// multiple tests or a deeper string. If FAIL: this one test shape is
// sufficient — the defect is in str-concat / contains? / run_test_by_name
// dispatch for Option-returning bodies.
//
// (carry: legacy/sprint59_defects456_repro::d45_single_str_concat_contains_run_tests_no_crash)
#[test]
fn d45_single_str_concat_contains_run_tests_no_crash() {
    let out = Cranelisp::new()
        .repl()
        .file("mymod.cl", SIMPLE_CONTAINS_MOD)
        .stdin("(import [mymod [test-simple-contains]])\n/run-tests mymod\n")
        .output();
    assert_no_signal_crash("d45_single_str_concat_contains", &out);
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("test-simple-contains"),
        "test did not run — discovery broke.\n{combined}"
    );
}

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

// spec: repl/spec.md §16.3 — /run-tests on 5-deep str-concat
//
// FIXME(/backend) — Copies html.cl test-wrap-tag verbatim minus the
// exemplar imports. If this test FAILS (crashes), the defect reproduces
// on a single 5-deep str-concat composition + str-eq.
//
// (carry: legacy/sprint59_defects456_repro::d45_wrap_tag_html_verbatim_run_tests_no_crash)
#[test]
fn d45_wrap_tag_html_verbatim_run_tests_no_crash() {
    let out = Cranelisp::new()
        .repl()
        .file("mymod.cl", WRAP_TAG_MOD)
        .stdin("(import [mymod [test-wrap-tag]])\n/run-tests mymod\n")
        .output();
    assert_no_signal_crash("d45_wrap_tag_html_verbatim", &out);
}

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

// spec: repl/spec.md §16.3 — multi-test batch dispatch
//
// FIXME(/backend) — If d45_single passes but this fails, the defect is
// the *second* run_test_by_name invocation in the batch leaking or
// double-free'ing the first test's return value.
//
// (carry: legacy/sprint59_defects456_repro::d45_multiple_tests_with_contains_run_tests_no_crash)
#[test]
fn d45_multiple_tests_with_contains_run_tests_no_crash() {
    let out = Cranelisp::new()
        .repl()
        .file("mymod.cl", MULTI_CONTAINS_MOD)
        .stdin("(import [mymod [test-a]])\n/run-tests mymod\n")
        .output();
    assert_no_signal_crash("d45_multiple_tests_with_contains", &out);
}

const FORM_LIKE_MOD: &str = r#";; form.cl-like test shape minimized: let + str-eq + Option.
(import [primitives [*]])

(defn test-url-decode-like []
  (if (str-eq (str-concat "hello" " world") "hello world") None
    (Some "str-concat should produce 'hello world'")))
"#;

// spec: repl/spec.md §16.3 — let + str-eq + Option body shape
//
// FIXME(/backend) — form.cl uses substring/split which are additional
// RC-sensitive primitives. Probes whether the Option(Some "...") form
// itself — heap-string argument to Some constructor — is the crash surface.
//
// (carry: legacy/sprint59_defects456_repro::d45_form_shaped_body_run_tests_no_crash)
#[test]
fn d45_form_shaped_body_run_tests_no_crash() {
    let out = Cranelisp::new()
        .repl()
        .file("mymod.cl", FORM_LIKE_MOD)
        .stdin("(import [mymod [test-url-decode-like]])\n/run-tests mymod\n")
        .output();
    assert_no_signal_crash("d45_form_shaped_body", &out);
}

const TWO_TRIVIAL_MOD: &str = r#"(import [primitives [*]])
(defn test-a [] None)
(defn test-b [] None)
"#;

// spec: repl/spec.md §16.3 — 2-test trivial batch
//
// REGRESSION-GUARD: proves batched /run-tests with two trivial test bodies
//   alone is OK. (If this crashes, the defect is in batched dispatch of
//   any 2+ tests.)
//
// (carry: legacy/sprint59_defects456_repro::d45_two_trivial_tests_run_tests_no_crash)
#[test]
fn d45_two_trivial_tests_run_tests_no_crash() {
    let out = Cranelisp::new()
        .repl()
        .file("mymod.cl", TWO_TRIVIAL_MOD)
        .stdin("(import [mymod [test-a]])\n/run-tests mymod\n")
        .output();
    assert_no_signal_crash("d45_two_trivial_tests", &out);
}

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

// spec: repl/spec.md §16.3 — 10-test str-concat batch
//
// FIXME(/backend) — If this passes but d45_real_exemplar_html fails,
// the defect is NOT batch-size driven: it specifically needs html.cl's
// imports (grid.cl) or one of its specific helpers.
//
// (carry: legacy/sprint59_defects456_repro::d45_ten_str_bodies_run_tests_no_crash)
#[test]
fn d45_ten_str_bodies_run_tests_no_crash() {
    let out = Cranelisp::new()
        .repl()
        .file("mymod.cl", TEN_STR_BODIES_MOD)
        .stdin("(import [mymod [test-01]])\n/run-tests mymod\n")
        .output();
    assert_no_signal_crash("d45_ten_str_bodies", &out);
}

// =============================================================================
// §B — d45: cross-module fixture probing (two-file synthetic)
// =============================================================================

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

// spec: repl/spec.md §16.3 + spec/08-modules.md §8.10.1 — cross-module ADT
//
// FIXME(/backend) — cross-module ADT constructor + match in a test body.
// If PASS: cross-module ADT alone is not enough; need Vec or Grid wrapper.
//
// (carry: legacy/sprint59_defects456_repro::d45_cross_module_adt_basic_no_crash)
#[test]
fn d45_cross_module_adt_basic_no_crash() {
    let out = Cranelisp::new()
        .repl()
        .file("lib.cl", LIB_SIMPLE_ADT)
        .file("mymod.cl", MYMOD_USES_CELL)
        .stdin("(import [mymod [test-cell-ctor]])\n/run-tests mymod\n")
        .output();
    assert_no_signal_crash("d45_cross_module_adt_basic", &out);
}

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

// spec: repl/spec.md §16.3 — cross-module import without use
//
// FIXME(/backend) — mymod imports Grid-ADT symbols but never builds one;
// tests are pure-string. If PASS: the IMPORT alone doesn't trigger.
//
// (carry: legacy/sprint59_defects456_repro::d45_cross_module_import_but_no_use_no_crash)
#[test]
fn d45_cross_module_import_but_no_use_no_crash() {
    let out = Cranelisp::new()
        .repl()
        .file("lib.cl", LIB_GRID_ADT)
        .file("mymod.cl", MYMOD_USES_GRID_NO_TESTS_THAT_BUILD)
        .stdin("(import [mymod [test-wrap-tag]])\n/run-tests mymod\n")
        .output();
    assert_no_signal_crash("d45_cross_module_import_but_no_use", &out);
}

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

// spec: repl/spec.md §16.3 — cross-module Grid-build in test body
//
// FIXME(/backend) — one test that builds (Grid (Vec Cell)) using a
// cross-module constructor.
//
// (carry: legacy/sprint59_defects456_repro::d45_cross_module_grid_build_in_test_no_crash)
#[test]
fn d45_cross_module_grid_build_in_test_no_crash() {
    let out = Cranelisp::new()
        .repl()
        .file("lib.cl", LIB_GRID_ADT)
        .file("mymod.cl", MYMOD_BUILDS_GRID_IN_TEST)
        .stdin("(import [mymod [test-grid-build]])\n/run-tests mymod\n")
        .output();
    assert_no_signal_crash("d45_cross_module_grid_build_in_test", &out);
}

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

// spec: repl/spec.md §16.3 — html-like 4-test mix
//
// FIXME(/backend) — 4 tests including Grid-build + cross-module match +
// deep str-concat nesting. Closely mirrors html.cl's test surface.
//
// (carry: legacy/sprint59_defects456_repro::d45_cross_module_html_like_batch_no_crash)
#[test]
fn d45_cross_module_html_like_batch_no_crash() {
    let out = Cranelisp::new()
        .repl()
        .file("lib.cl", LIB_GRID_ADT)
        .file("mymod.cl", MYMOD_HTML_LIKE)
        .stdin("(import [mymod [test-wrap-tag]])\n/run-tests mymod\n")
        .output();
    assert_no_signal_crash("d45_cross_module_html_like_batch", &out);
}

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

// spec: repl/spec.md §16.3 — full 10-test cross-module synthetic batch
//
// FIXME(/backend) — 10-test synthetic batch closely matching html.cl's shape.
// If FAIL: we've reduced to a synthetic 2-file pair. If PASS: something more
// specific to html.cl is load-bearing.
//
// (carry: legacy/sprint59_defects456_repro::d45_cross_module_html_full_10_tests_no_crash)
#[test]
fn d45_cross_module_html_full_10_tests_no_crash() {
    let out = Cranelisp::new()
        .repl()
        .file("lib.cl", LIB_GRID_ADT)
        .file("mymod.cl", MYMOD_HTML_FULL)
        .stdin("(import [mymod [test-wrap-tag]])\n/run-tests mymod\n")
        .output();
    assert_no_signal_crash("d45_cross_module_html_full_10_tests", &out);
}

// =============================================================================
// §C — d45: real exemplar source probing
// =============================================================================
//
// These tests copy `exemplar/` into the per-test TempDir to exercise the
// actual exemplar's html.cl + grid.cl. Per
// `tests/plan/wave-6-batch-3-audit.md` §"Tests flagged for /sprint judgment"
// §E, the copy-from-exemplar shape is preserved (not inlined) because the
// d6 ledger entries (4 of them) reproduce against the real exemplar source
// and inlining would change the semantic.

// spec: repl/spec.md §16.3 — real exemplar /run-tests html
//
// FIXME(/backend) — Runs /run-tests against the real exemplar/html.cl.
// Probes html.cl-specific surface: cross-module ADT chain (grid.cl),
// 15+ defns, build-all-ones-helper + Grid constructor in loops.
//
// (carry: legacy/sprint59_defects456_repro::d45_real_exemplar_html_run_tests_no_crash)
#[test]
fn d45_real_exemplar_html_run_tests_no_crash() {
    let cl = Cranelisp::new();
    copy_exemplar_into(&cl.tmpdir_path(), ".");
    // Empty user.cl prevents the binary from picking up checked-in user state.
    // Workspace stdlib + platforms required: the exemplar imports prelude
    // operators and `(platform stdio)`. Same shape as legacy `drive_repl`
    // which sets CRANELISP_LIB and CRANELISP_PLATFORM_PATH explicitly.
    let out = cl
        .repl()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .use_workspace_platforms()
        .file("user.cl", "")
        .stdin("(import [html [test-wrap-tag]])\n/run-tests html\n")
        .output();
    assert_no_signal_crash("d45_real_exemplar_html", &out);
}

// spec: design/arch/test-discovery.md §4.4 — single-test invocation
// (not the /run-tests batch loop).
//
// Isolation companion to the batched `/run-tests html` reductions below: if
// this single-invocation path is clean while the batched path crashes, the
// defect is in the dispatch loop, not the individual test call. The retired
// `run-test` special form (src/CLAUDE.md §"Test discovery"; test-discovery.md
// fourth convergence) is gone — running one test is now invoking its callable
// directly, bracketed by `catch-runtime-error`. This drives the single
// exemplar test `html/test-wrap-tag` through that combinator and asserts the
// child does not crash by signal. (The exemplar's stdlib `Result` shadows the
// seeded `primitives/Result`, so a *type* error may surface — that is fine;
// the load-bearing invariant here is "no SIGSEGV/SIGTRAP", per the Sprint 59
// Defect 4+5 origin.)
//
// (carry: legacy/sprint59_defects456_repro::d45_real_exemplar_html_single_run_test_no_crash)
#[test]
fn d45_real_exemplar_html_single_run_test_no_crash() {
    let cl = Cranelisp::new();
    copy_exemplar_into(&cl.tmpdir_path(), ".");
    let out = cl
        .repl()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .use_workspace_platforms()
        .file("user.cl", "")
        .stdin(
            "(import [html [test-wrap-tag]])\n\
             (import [primitives [catch-runtime-error]])\n\
             (catch-runtime-error (fn [] (test-wrap-tag)))\n",
        )
        .output();
    assert_no_signal_crash("d45_real_exemplar_html_single", &out);
}

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

// spec: repl/spec.md §16.3 — real html.cl with trimmed grid.cl
//
// FIXME(/backend) — real html.cl + trimmed grid.cl. Pinned the crash to
// html.cl + {Grid, Cell, Given, Solved, Candidates, cell-at, cell-value} alone.
//
// (carry: legacy/sprint59_defects456_repro::d45_real_html_with_trimmed_grid_no_crash)
#[test]
fn d45_real_html_with_trimmed_grid_no_crash() {
    // Read real html.cl from the workspace and pair with trimmed grid.
    // read-only on project_root: html.cl is sourced from exemplar/html.cl.
    let html_body = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("exemplar").join("html.cl"),
    )
    .expect("read exemplar/html.cl");
    let out = Cranelisp::new()
        .repl()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .use_workspace_platforms()
        .file("grid.cl", GRID_TRIMMED)
        .file("html.cl", &html_body)
        .stdin("(import [html [test-wrap-tag]])\n/run-tests html\n")
        .output();
    assert_no_signal_crash("d45_real_html_with_trimmed_grid", &out);
}

// =============================================================================
// §D — d45: html-source reduction ladder (8 rungs)
// =============================================================================
//
// Progressive html-source strip: no css, solution-only (3 tests), 1 test,
// 2 tests, 3 tests mixed, 2-arg solution, min v1 (9 cells), min v2 (1 cell).
// Each rung paired with trimmed grid.cl from §C.

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

// spec: repl/spec.md §16.3 — real html.cl minus css
//
// FIXME(/backend) — real html.cl minus the css function. If STILL crashes,
// css is not the culprit. If PASS, css's massive str-concat depth is the
// trigger.
//
// (carry: legacy/sprint59_defects456_repro::d45_html_no_css_no_crash)
#[test]
fn d45_html_no_css_no_crash() {
    let out = Cranelisp::new()
        .repl()
        .file("grid.cl", GRID_TRIMMED)
        .file("html.cl", HTML_NO_CSS)
        .stdin("(import [html [test-wrap-tag]])\n/run-tests html\n")
        .output();
    assert_no_signal_crash("d45_html_no_css", &out);
}

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

// spec: repl/spec.md §16.3 — only 3 Grid-touching tests
//
// FIXME(/backend) — only 3 Grid-touching tests. If crashes, we've pinned
// the axis to solution-page tests.
//
// (carry: legacy/sprint59_defects456_repro::d45_html_solution_tests_only_no_crash)
#[test]
fn d45_html_solution_tests_only_no_crash() {
    let out = Cranelisp::new()
        .repl()
        .file("grid.cl", GRID_TRIMMED)
        .file("html.cl", HTML_SOLUTION_TESTS_ONLY)
        .stdin("(import [html [test-solution-page-has-digits]])\n/run-tests html\n")
        .output();
    assert_no_signal_crash("d45_html_solution_tests_only", &out);
}

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

// spec: repl/spec.md §16.3 — 1 test, simplified solution-cell
//
// FIXME(/backend) — one test, one function that builds a nested string
// via cross-module match. Simplified solution-cell signature.
//
// (carry: legacy/sprint59_defects456_repro::d45_html_one_test_no_crash)
#[test]
fn d45_html_one_test_no_crash() {
    let out = Cranelisp::new()
        .repl()
        .file("grid.cl", GRID_TRIMMED)
        .file("html.cl", HTML_ONE_TEST)
        .stdin("(import [html [test-page]])\n/run-tests html\n")
        .output();
    assert_no_signal_crash("d45_html_one_test", &out);
}

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

// spec: repl/spec.md §16.3 — 2 tests sharing make-grid + page
//
// FIXME(/backend) — 2 tests doing same Grid-build + page. If crashes,
// the batched dispatch with shared make-grid trampoline reproduces.
//
// (carry: legacy/sprint59_defects456_repro::d45_html_two_tests_no_crash)
#[test]
fn d45_html_two_tests_no_crash() {
    let out = Cranelisp::new()
        .repl()
        .file("grid.cl", GRID_TRIMMED)
        .file("html.cl", HTML_TWO_TESTS)
        .stdin("(import [html [test-page-a]])\n/run-tests html\n")
        .output();
    assert_no_signal_crash("d45_html_two_tests", &out);
}

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

// spec: repl/spec.md §16.3 — 3 tests, 2 grid-build helpers
//
// FIXME(/backend) — 3 tests, third uses a SECOND grid-build function
// (build-mixed-helper). If crashes, two distinct Vec-of-ADT-building
// functions in same module is the trigger.
//
// (carry: legacy/sprint59_defects456_repro::d45_html_three_tests_mixed_no_crash)
#[test]
fn d45_html_three_tests_mixed_no_crash() {
    let out = Cranelisp::new()
        .repl()
        .file("grid.cl", GRID_TRIMMED)
        .file("html.cl", HTML_THREE_TESTS_MIXED)
        .stdin("(import [html [test-page-a]])\n/run-tests html\n")
        .output();
    assert_no_signal_crash("d45_html_three_tests_mixed", &out);
}

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

// spec: repl/spec.md §16.3 — 2-arg solution-cell, 2 cell-at calls
//
// FIXME(/backend) — 2 tests, solution-cell takes two grid params (2
// cell-at calls), wraps via td + wrap-tag.
//
// (carry: legacy/sprint59_defects456_repro::d45_html_two_arg_solution_no_crash)
#[test]
fn d45_html_two_arg_solution_no_crash() {
    let out = Cranelisp::new()
        .repl()
        .file("grid.cl", GRID_TRIMMED)
        .file("html.cl", HTML_TWO_ARG_SOLUTION)
        .stdin("(import [html [test-page-digits]])\n/run-tests html\n")
        .output();
    assert_no_signal_crash("d45_html_two_arg_solution", &out);
}

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

// spec: repl/spec.md §16.3 — 9-cell grid, flat str-concat
//
// FIXME(/backend) — 1 test, 9-cell grid, flat str-concat (no wrap-tag/td),
// but retained: two-grid-param solution-cell, 2 cell-at calls, match in
// tail of let.
//
// (carry: legacy/sprint59_defects456_repro::d45_html_min_v1_no_crash)
#[test]
fn d45_html_min_v1_no_crash() {
    let out = Cranelisp::new()
        .repl()
        .file("grid.cl", GRID_TRIMMED)
        .file("html.cl", HTML_MIN_V1)
        .stdin("(import [html [test-page]])\n/run-tests html\n")
        .output();
    assert_no_signal_crash("d45_html_min_v1", &out);
}

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

// spec: repl/spec.md §16.3 — 1-cell grid, single solution-cell call
//
// FIXME(/backend) — 1 test, single-cell Grid, no loop, one solution-cell
// call. If crashes, the iteration loop is not needed — just calling a
// cross-module let+2xcell-at+match helper crashes.
//
// (carry: legacy/sprint59_defects456_repro::d45_html_min_v2_no_crash)
#[test]
fn d45_html_min_v2_no_crash() {
    let out = Cranelisp::new()
        .repl()
        .file("grid.cl", GRID_TRIMMED)
        .file("html.cl", HTML_MIN_V2)
        .stdin("(import [html [test-one]])\n/run-tests html\n")
        .output();
    assert_no_signal_crash("d45_html_min_v2", &out);
}

// spec: spec/12-runtime.md §12.3 — consuming convention RC balance across
//       polymorphic dispatch with captured heap args.
//
// Smallest possible form of the d45 crash: a single direct call to
// `solution-cell g g 0` from the REPL. No /run-tests harness, no Option
// wrapper, no contains?, no str-eq — just the let+2xcell-at+match body
// that returns a String, called with the same Grid passed as both args.
// This is the construct that provokes the RC-ABI bug.
//
// REGRESSION-GUARD: minimal RC underflow shape. Two consecutive
//   invocations: the first produces the string cleanly, but the JIT
//   artefact left over after the first call (an over-inc on the string
//   return value plus an already-freed grid param whose RC has gone
//   negative) tips into SIGTRAP on the second.
//
// (carry: legacy/sprint59_defects456_repro::d45_solution_cell_single_call_no_rc_underflow)
#[test]
fn d45_solution_cell_single_call_no_rc_underflow() {
    let input = "\
(import [html [make-grid solution-cell]])
(let [g (make-grid)] (solution-cell g g 0))
(let [g (make-grid)] (solution-cell g g 0))
/quit
";
    let out = Cranelisp::new()
        .repl()
        .file("grid.cl", GRID_TRIMMED)
        .file("html.cl", HTML_MIN_V2)
        .stdin(input)
        .output();
    assert_no_signal_crash("d45_solution_cell_single_call", &out);
}

// =============================================================================
// §E — d6: synthetic Vec/ADT/Grid COW reductions (--run mode)
// =============================================================================

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

// spec: spec/12-runtime.md §12.3 — Vec COW with Int elements
//
// FIXME(/backend) — If this test PASSES (no segv), plain Vec COW with Int
// elements is not the defect. Next axis: move to Vec of ADT elements.
//
// (carry: legacy/sprint59_defects456_repro::d6_vec_cow_int_loop_does_not_segv)
#[test]
fn d6_vec_cow_int_loop_does_not_segv() {
    let out = Cranelisp::new()
        .run("repro.cl")
        .file("repro.cl", VEC_COW_LOOP_MOD)
        .output();
    assert_no_signal_crash("d6_vec_cow_int_loop", &out);
}

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

// spec: spec/12-runtime.md §12.3 — Vec COW with ADT (Cell) elements
//
// FIXME(/backend) — If d6_vec_cow_int passes but this fails, the defect
// is in COW + ADT cells.
//
// (carry: legacy/sprint59_defects456_repro::d6_vec_cow_adt_loop_does_not_segv)
#[test]
fn d6_vec_cow_adt_loop_does_not_segv() {
    let out = Cranelisp::new()
        .run("repro.cl")
        .file("repro.cl", VEC_ADT_COW_MOD)
        .output();
    assert_no_signal_crash("d6_vec_cow_adt_loop", &out);
}

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

// spec: spec/12-runtime.md §12.3 — Grid ADT wrapper + COW
//
// FIXME(/backend) — Grid ADT wrapper adds one level of boxing (and a
// match to unpack). If this fails but d6_vec_cow_adt passes, the defect
// is at the Grid level.
//
// (carry: legacy/sprint59_defects456_repro::d6_grid_wrapper_cow_does_not_segv)
#[test]
fn d6_grid_wrapper_cow_does_not_segv() {
    let out = Cranelisp::new()
        .run("repro.cl")
        .file("repro.cl", GRID_WRAPPER_MOD)
        .output();
    assert_no_signal_crash("d6_grid_wrapper_cow", &out);
}

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

// spec: spec/12-runtime.md §12.5 — recursive Grid-building with match nesting
//
// FIXME(/backend) — Recursive Grid-building with 30 levels of match
// nesting on SolveResult. If passes, increase depth or add peers-list
// (Vec of Int) handling.
//
// (carry: legacy/sprint59_defects456_repro::d6_solve_recursive_adt_does_not_segv)
#[test]
fn d6_solve_recursive_adt_does_not_segv() {
    let out = Cranelisp::new()
        .run("repro.cl")
        .file("repro.cl", SOLVE_RECURSIVE_MOD)
        .output();
    assert_no_signal_crash("d6_solve_recursive_adt", &out);
}

// =============================================================================
// §F — d6: real-exemplar reductions (4 currently FAILING — open Defect 6)
// =============================================================================
//
// Per `tests/plan/ledger.md §"Escaped carries — surfaced Sprint 61 Wave 3"`:
// these four tests fail at audit time (2026-05-05) because Defect 6 (deep
// recursion stack overflow in JIT'd `propagate`/`solve` on 81-cell
// Vec-copying ADT traversal) remains open. Per
// `memory/feedback_failing_not_ignored.md` they MUST land un-ignored as
// the durable record. The legacy ledger entries (lines 83–131 of
// `tests/plan/ledger.md`) name the legacy file's tests but cover the
// same regression surface — when /backend resolves Defect 6 these
// carry-forwards become passing regression guards.
//
// Disposition: `exemplar-gap (owner=/port, underlying-owner=/backend)`.

// spec: spec/12-runtime.md §12.5 — exemplar solver, no IO, real puzzle
//
// FIXME(/backend) — Runs solver against real exemplar source on a
// 17-clue puzzle, returning a determined-cell count. Sprint 61 Wave 3
// ledger entry (open Defect 6).
//
// REGRESSION-GUARD: Sprint 59 Defect 6 — open ledger.
// FAILING-NOT-IGNORED per memory/feedback_failing_not_ignored.md.
//
// (carry: legacy/sprint59_defects456_repro::d6_exemplar_solve_minimal_puzzle_no_io_does_not_segv)
#[test]
fn d6_exemplar_solve_minimal_puzzle_no_io_does_not_segv() {
    let cl = Cranelisp::new();
    copy_exemplar_into(&cl.tmpdir_path(), "exemplar");
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
    let out = cl
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .use_workspace_platforms()
        .run("exemplar/d6_repro_no_io.cl")
        .file("exemplar/d6_repro_no_io.cl", repro_source)
        .output();
    assert_no_signal_crash("d6_exemplar_solve_minimal_puzzle_no_io", &out);
}

// spec: spec/12-runtime.md §12.5 — single propagate call on real puzzle
//
// FIXME(/backend) — Runs propagate once (no fixpoint loop) on a real
// 17-clue puzzle. Sprint 61 Wave 3 ledger entry (open Defect 6).
//
// (carry: legacy/sprint59_defects456_repro::d6_exemplar_propagate_only_does_not_segv)
#[test]
fn d6_exemplar_propagate_only_does_not_segv() {
    let cl = Cranelisp::new();
    copy_exemplar_into(&cl.tmpdir_path(), "exemplar");
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
    let out = cl
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .use_workspace_platforms()
        .run("exemplar/d6_propagate_only.cl")
        .file("exemplar/d6_propagate_only.cl", repro_source)
        .output();
    assert_no_signal_crash("d6_exemplar_propagate_only", &out);
}

// spec: spec/12-runtime.md §12.5 — solve on all-dots empty puzzle
//
// FIXME(/backend) — Runs solve on a maximally empty puzzle. If the bug
// were puzzle-difficulty-dependent, an empty grid would converge fast.
// Sprint 61 Wave 3 ledger entry (open Defect 6).
//
// (carry: legacy/sprint59_defects456_repro::d6_exemplar_solve_all_dots_does_not_segv)
#[test]
fn d6_exemplar_solve_all_dots_does_not_segv() {
    let cl = Cranelisp::new();
    copy_exemplar_into(&cl.tmpdir_path(), "exemplar");
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
    let out = cl
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .use_workspace_platforms()
        .run("exemplar/d6_all_dots.cl")
        .file("exemplar/d6_all_dots.cl", repro_source)
        .output();
    assert_no_signal_crash("d6_exemplar_solve_all_dots", &out);
}

// spec: spec/12-runtime.md §12.5 — single propagate-pass-helper call
//
// FIXME(/backend) — Calls propagate-pass-helper directly (no fixpoint
// loop). Isolates the crash to the recursive structure inside one pass.
// Sprint 61 Wave 3 ledger entry (open Defect 6).
//
// (carry: legacy/sprint59_defects456_repro::d6_exemplar_propagate_single_pass_does_not_segv)
#[test]
fn d6_exemplar_propagate_single_pass_does_not_segv() {
    let cl = Cranelisp::new();
    copy_exemplar_into(&cl.tmpdir_path(), "exemplar");
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
    let out = cl
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .use_workspace_platforms()
        .run("exemplar/d6_one_pass.cl")
        .file("exemplar/d6_one_pass.cl", repro_source)
        .output();
    assert_no_signal_crash("d6_exemplar_propagate_single_pass", &out);
}

// =============================================================================
// §G — d6: real-exemplar reductions (currently passing)
// =============================================================================

// spec: spec/12-runtime.md §12.5 — single eliminate-from-peers call
//
// FIXME(/backend) — One eliminate-from-peers call on cell 0. Finest-grain
// reduction — if this still triggers, the bug reduces to a single
// eliminate-from-peers invocation. Per ledger §note 2026-04-22, this test
// passes consistently (verified at audit time 2026-05-05).
//
// (carry: legacy/sprint59_defects456_repro::d6_exemplar_eliminate_from_peers_does_not_segv)
#[test]
fn d6_exemplar_eliminate_from_peers_does_not_segv() {
    let cl = Cranelisp::new();
    copy_exemplar_into(&cl.tmpdir_path(), "exemplar");
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
    let out = cl
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .use_workspace_platforms()
        .run("exemplar/d6_elim_peers.cl")
        .file("exemplar/d6_elim_peers.cl", repro_source)
        .output();
    assert_no_signal_crash("d6_exemplar_eliminate_from_peers", &out);
}

// spec: spec/12-runtime.md §12.5 — make-grid only (pre-solver init)
//
// FIXME(/backend) — Construct a Grid via make-grid, return None/Some
// discriminant. If this crashes, the defect is in initial grid
// construction not the solver. Pre-solver-init rung.
//
// (carry: legacy/sprint59_defects456_repro::d6_exemplar_make_grid_only_does_not_segv)
#[test]
fn d6_exemplar_make_grid_only_does_not_segv() {
    let cl = Cranelisp::new();
    copy_exemplar_into(&cl.tmpdir_path(), "exemplar");
    let repro_source = r#";; D6 reduction — construct a Grid via make-grid, return None/Some discriminant.
(import [primitives [*]])
(import [grid [Grid make-grid]])

(defn main []
  (match (make-grid "003020600900305001001806400008102900700000008006708200002609500800203009005010300")
    [None 0
     (Some _) 1]))
"#;
    let out = cl
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .use_workspace_platforms()
        .run("exemplar/d6_make_grid.cl")
        .file("exemplar/d6_make_grid.cl", repro_source)
        .output();
    assert_no_signal_crash("d6_exemplar_make_grid_only", &out);
}

// =============================================================================
// Sprint 60 cache-reuse + drop-glue reductions
// =============================================================================
//
// Carry-forward from `tests/legacy/sprint60_reduction.rs` per Wave 6 batch 4
// audit (`tests/plan/wave-6-batch-4-audit.md`). Two reduction clusters:
//
//   §A cache-reuse SIGSEGV (steps 1 + 2.1–2.7 + 3 controls = 11 tests) —
//      first run populates `.cranelisp-cache`; second run cache-hit-loads
//      and historically segfaulted. Resolved by Sprint 60 Workstream A
//      (single-GOT fix). Reductions stay as regression guards.
//
//   §B drop-glue / auto-curry double-free (step 1 + 5 reductions = 6 tests) —
//      Grid-wrapped Vec + double `cell-at` call. Resolved post-Sprint-60
//      Wave 2 Round 2. Reductions stay as regression guards.
//
// All 17 sprint60_reduction tests PASS on the current binary at audit time
// (2026-05-05). Pre-Sprint 63 inline `FIXME(/backend)` hypothesis comments
// preserved verbatim — see `tests/plan/wave-6-batch-4-audit.md` §"Tests
// flagged for /sprint judgment" §C–§D for the migration discipline.
// =============================================================================

/// Run `cranelisp --run program.cl` from `cwd`, returning the raw `Output`.
/// Used by the drop-glue 10-trial cold-cache loop where the per-trial fresh
/// tempdir is the load-bearing setup. The standard `Cranelisp` builder
/// produces one TempDir per builder; the 10-trial pattern needs ten fresh
/// tempdirs, so we drop into bare `Command` for that loop.
fn run_program_at(cwd: &Path, entry: &str) -> std::process::Output {
    let binary = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("debug")
        .join("cranelisp");
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} -- run `cargo build` first"
    );
    let stdlib = Path::new(env!("CARGO_MANIFEST_DIR")).join("stdlib");
    let platform = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("debug");
    std::process::Command::new(&binary)
        .current_dir(cwd)
        .args(["--run", entry])
        .env("CRANELISP_LIB", stdlib)
        .env("CRANELISP_PLATFORM_PATH", platform)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .output()
        .expect("failed to invoke binary")
}

/// 10 trials, fresh tempdir per trial. Panic if any trial signal-crashes.
/// Used for the drop-glue cluster — under Rust-spawn cold-cache the crash
/// rate is ~90% when the bug is active, so 10 trials gives >99% confidence
/// that the reduction reproduces (or, post-fix, that it does not).
fn reduce_single_file_10_trials(source: &str, label: &str) {
    const TRIALS: usize = 10;
    let mut crashes: Vec<String> = Vec::new();
    for i in 0..TRIALS {
        let td = tempfile::tempdir().expect("tempdir for trial");
        std::fs::create_dir(td.path().join("subdir")).unwrap();
        std::fs::write(td.path().join("subdir").join("program.cl"), source).unwrap();
        let o = run_program_at(td.path(), "subdir/program.cl");
        let exit = o.status.code();
        let signal_crash = matches!(exit, Some(139) | Some(133) | Some(134)) || exit.is_none();
        if signal_crash {
            crashes.push(format!("trial {i}: exit={exit:?}"));
        }
    }
    if !crashes.is_empty() {
        panic!(
            "{label}: {}/{} cold-cache trials crashed with signal. \
             Reduced defect: drop-glue / auto-curry closure captures \
             ADT-wrapped Vec and double-frees its inner Vec. \
             trials that crashed: {}",
            crashes.len(),
            TRIALS,
            crashes.join(", "),
        );
    }
}

/// Run a two-file cache-reuse program: write `grid_body` + `program_body`
/// into a fresh tempdir, run `--run program.cl` twice in the same tempdir
/// (first populates the cache, second hits the cache), assert neither run
/// signal-crashed.
fn assert_two_file_cache_reuse_no_crash(grid_body: &str, program_body: &str, label: &str) {
    let first = Cranelisp::new()
        .run("program.cl")
        .file("grid.cl", grid_body)
        .file("program.cl", program_body)
        .output();
    assert_first_not_signal_crashed(label, &first);
    let second = first.run_again().run("program.cl").output();
    assert_no_signal_crash(label, &second);
}

/// Run a single-file cache-reuse program: write `program_body` into a fresh
/// tempdir, run twice in the same tempdir, assert neither run signal-crashed.
fn assert_single_file_cache_reuse_no_crash(program_body: &str, label: &str) {
    let first = Cranelisp::new()
        .run("program.cl")
        .file("program.cl", program_body)
        .output();
    assert_first_not_signal_crashed(label, &first);
    let second = first.run_again().run("program.cl").output();
    assert_no_signal_crash(label, &second);
}

/// First (fresh-cache) run must NOT signal-crash — we require the cache to
/// be populated. Non-zero exit codes are fine (they reflect main's Int
/// return), but a signal crash means the test is measuring the wrong thing.
fn assert_first_not_signal_crashed(label: &str, out: &e2e::CrOutput) {
    let exit = out.status.code();
    let crashed = matches!(exit, Some(139) | Some(133)) || exit.is_none();
    if crashed {
        panic!(
            "{label}: first (fresh-cache) run signal-crashed (exit={exit:?}). \
             Cannot measure cache-reuse behaviour if the fresh-build path itself crashes.\n\
             --- stdout ---\n{}\n--- stderr ---\n{}",
            out.stdout, out.stderr
        );
    }
}

// -----------------------------------------------------------------------------
// §A — cache-reuse cluster: step 1 baseline + 2.1–2.7 reductions + 3 controls
// -----------------------------------------------------------------------------

const S60_GRID_EXEMPLAR_SHAPED: &str = r#"(import [primitives [*]])

(deftype Cell
  (Given [:Int value])
  (Solved [:Int value])
  (Candidates [:Int bitmask]))

(deftype Grid [cells])

(defn build-helper [v i]
  (if (eq-i64 i 9) v
    (build-helper (vec-push v (Given 1)) (add-i64 i 1))))

(defn make-grid [] (Grid (build-helper [] 0)))
"#;

const S60_PROGRAM_CALLS_MAKE_GRID: &str = r#"(import [grid [make-grid]])
(defn main [] (let [g (make-grid)] 0))
"#;

// spec: design/backend/jit-object-convergence.md §1.1 — What MUST be identical.
//   Sprint 60 Workstream A's A.3b uncommitted finding: cache-reuse on the
//   exemplar-shaped baseline (Cell ADT + Grid wrapper + recursive
//   build-helper) crashes on cache-hit load with SIGSEGV.
//
// REGRESSION-GUARD: Sprint 60 Workstream A — exemplar-shaped baseline
//   reduction. Resolved by single-GOT fix.
//
// FIXME(/backend) — S60 Step 1: commits A.3b's uncommitted finding. First
// run compiles + caches. Second run originally crashed on cache-hit load
// with SIGSEGV. The exemplar-shaped baseline before reduction. When fixed:
// restored the JIT/object convergence invariant for the cache-hit pathway
// that populates `ModuleEntry::Def.code`.
//
// (carry: legacy/sprint60_reduction.rs::s60_cache_reuse_exemplar_shaped_no_crash)
#[test]
fn s60_cache_reuse_exemplar_shaped_no_crash() {
    assert_two_file_cache_reuse_no_crash(
        S60_GRID_EXEMPLAR_SHAPED,
        S60_PROGRAM_CALLS_MAKE_GRID,
        "s60_cache_reuse_exemplar_shaped",
    );
}

const S60_GRID_NO_CELL_ADT: &str = r#"(import [primitives [*]])

(deftype Grid [cells])

(defn build-helper [v i]
  (if (eq-i64 i 9) v
    (build-helper (vec-push v i) (add-i64 i 1))))

(defn make-grid [] (Grid (build-helper [] 0)))
"#;

// spec: (same anchor) — reduction 2.1 strips Cell ADT.
// REGRESSION-GUARD: Cell ADT not load-bearing.
// FIXME(/backend) — S60 reduction 2.1. Cell ADT not load-bearing.
//
// (carry: legacy/sprint60_reduction.rs::s60_cache_reuse_no_cell_adt_no_crash)
#[test]
fn s60_cache_reuse_no_cell_adt_no_crash() {
    assert_two_file_cache_reuse_no_crash(
        S60_GRID_NO_CELL_ADT,
        S60_PROGRAM_CALLS_MAKE_GRID,
        "s60_cache_reuse_no_cell_adt",
    );
}

const S60_GRID_NO_WRAPPER_ADT: &str = r#"(import [primitives [*]])

(defn build-helper [v i]
  (if (eq-i64 i 9) v
    (build-helper (vec-push v i) (add-i64 i 1))))

(defn make-grid [] (build-helper [] 0))
"#;

// spec: (same anchor) — reduction 2.2 strips Grid wrapper.
// REGRESSION-GUARD: Grid wrapper ADT not load-bearing.
// FIXME(/backend) — S60 reduction 2.2. Grid wrapper ADT not load-bearing.
//
// (carry: legacy/sprint60_reduction.rs::s60_cache_reuse_no_wrapper_adt_no_crash)
#[test]
fn s60_cache_reuse_no_wrapper_adt_no_crash() {
    assert_two_file_cache_reuse_no_crash(
        S60_GRID_NO_WRAPPER_ADT,
        S60_PROGRAM_CALLS_MAKE_GRID,
        "s60_cache_reuse_no_wrapper_adt",
    );
}

const S60_GRID_NON_RECURSIVE: &str = r#"(import [primitives [*]])

(defn build-helper [v i] (vec-push v i))

(defn make-grid [] (build-helper [] 0))
"#;

// spec: (same anchor) — reduction 2.3: helper not tail-recursive.
// REGRESSION-GUARD: self-recursion not load-bearing.
// FIXME(/backend) — S60 reduction 2.3. Self-recursion not load-bearing.
//
// (carry: legacy/sprint60_reduction.rs::s60_cache_reuse_non_recursive_helper_no_crash)
#[test]
fn s60_cache_reuse_non_recursive_helper_no_crash() {
    assert_two_file_cache_reuse_no_crash(
        S60_GRID_NON_RECURSIVE,
        S60_PROGRAM_CALLS_MAKE_GRID,
        "s60_cache_reuse_non_recursive_helper",
    );
}

const S60_GRID_NULLARY_VEC_HELPER: &str = r#"(import [primitives [*]])

(defn build-helper [] (vec-push [] 0))

(defn make-grid [] (build-helper))
"#;

// spec: (same anchor) — reduction 2.4: helper takes no args.
// REGRESSION-GUARD: helper arity not load-bearing.
// FIXME(/backend) — S60 reduction 2.4. Helper arity not load-bearing.
//
// (carry: legacy/sprint60_reduction.rs::s60_cache_reuse_nullary_helper_no_crash)
#[test]
fn s60_cache_reuse_nullary_helper_no_crash() {
    assert_two_file_cache_reuse_no_crash(
        S60_GRID_NULLARY_VEC_HELPER,
        S60_PROGRAM_CALLS_MAKE_GRID,
        "s60_cache_reuse_nullary_helper",
    );
}

const S60_GRID_EMPTY_VEC_HELPER: &str = r#"(import [primitives [*]])

(defn build-helper [] [])

(defn make-grid [] (build-helper))
"#;

// spec: (same anchor) — reduction 2.5: helper returns empty Vec.
// REGRESSION-GUARD: vec-push not load-bearing; any heap value suffices.
// FIXME(/backend) — S60 reduction 2.5. `vec-push` not load-bearing.
//
// (carry: legacy/sprint60_reduction.rs::s60_cache_reuse_empty_vec_helper_no_crash)
#[test]
fn s60_cache_reuse_empty_vec_helper_no_crash() {
    assert_two_file_cache_reuse_no_crash(
        S60_GRID_EMPTY_VEC_HELPER,
        S60_PROGRAM_CALLS_MAKE_GRID,
        "s60_cache_reuse_empty_vec_helper",
    );
}

const S60_GRID_INT_HELPER: &str = r#"(import [primitives [*]])

(defn build-helper [] 42)

(defn make-grid [] (build-helper))
"#;

// spec: (same anchor) — reduction 2.6: helper returns Int literal. NO HEAP.
// REGRESSION-GUARD: heap allocation NOT required; rules out RC entirely.
// FIXME(/backend) — S60 reduction 2.6. NO HEAP. This rules out RC/drop-glue
// entirely. The crash is purely about cache-hit handling of an imported
// wrapper that calls a same-module helper, regardless of value type.
//
// (carry: legacy/sprint60_reduction.rs::s60_cache_reuse_int_helper_no_heap_no_crash)
#[test]
fn s60_cache_reuse_int_helper_no_heap_no_crash() {
    assert_two_file_cache_reuse_no_crash(
        S60_GRID_INT_HELPER,
        S60_PROGRAM_CALLS_MAKE_GRID,
        "s60_cache_reuse_int_helper_no_heap",
    );
}

const S60_PROGRAM_NO_LET: &str = r#"(import [grid [make-grid]])
(defn main [] (make-grid))
"#;

// spec: (same anchor) — THE 5-LOC MINIMUM.
//   grid.cl: int helper + same-module wrapper.
//   program.cl: cross-module import + call from main.
// First run compiles both modules + caches; second run cache-loads and
// historically SIGSEGV'd deterministically.
//
// REGRESSION-GUARD: Sprint 60 Workstream A — minimum crashing shape.
// FIXME(/backend) — S60 MINIMAL — cache-hit path historically segfaulted on
// a two-file, no-heap, no-recursion, no-`let` program. The SOLE load-bearing
// shape: (1) module `grid` defines `build-helper` (no args, returns
// literal); (2) module `grid` defines `make-grid` calling `build-helper`;
// (3) module `program` imports `make-grid` and calls it from `main`;
// (4) cache-hit second run. Resolved by Sprint 60 Workstream A single-GOT
// fix; this test is the durable regression guard.
//
// Original hypothesis: on cache-hit, `make-grid`'s call to `build-helper`
// dispatched through a NULL/stale GOT slot. Root-cause was in
// `src/worker.rs::load_cached_module_via_linker` vicinity vs the
// convergence invariant breach at design/backend/jit-object-convergence.md
// §4 (`restore_cached_module`'s wholesale-swap of `symbol_tables[M].got`).
//
// (carry: legacy/sprint60_reduction.rs::s60_cache_reuse_minimal_5_loc_no_crash)
#[test]
fn s60_cache_reuse_minimal_5_loc_no_crash() {
    assert_two_file_cache_reuse_no_crash(
        S60_GRID_INT_HELPER,
        S60_PROGRAM_NO_LET,
        "s60_cache_reuse_minimal_5_loc",
    );
}

const S60_SINGLE_FILE_WITH_HELPER: &str = r#"(import [primitives [*]])
(defn build-helper [] 42)
(defn make-grid [] (build-helper))
(defn main [] (make-grid))
"#;

// REGRESSION-GUARD: control A — single-file. Pins cross-module-import as
// load-bearing for the original cache-hit defect.
//
// (carry: legacy/sprint60_reduction.rs::s60_control_single_file_no_crash)
#[test]
fn s60_control_single_file_no_crash() {
    assert_single_file_cache_reuse_no_crash(
        S60_SINGLE_FILE_WITH_HELPER,
        "s60_control_single_file",
    );
}

const S60_GRID_TRIVIAL_WRAPPER: &str = r#"(import [primitives [*]])
(defn make-grid [] 42)
"#;

// REGRESSION-GUARD: control B — no intra-module call in grid (`make-grid`
// returns a literal directly, no `build-helper`). Pins the intra-module
// call within `grid` as the load-bearing shape, not cross-module dispatch
// generally.
//
// (carry: legacy/sprint60_reduction.rs::s60_control_no_intra_module_call_no_crash)
#[test]
fn s60_control_no_intra_module_call_no_crash() {
    assert_two_file_cache_reuse_no_crash(
        S60_GRID_TRIVIAL_WRAPPER,
        S60_PROGRAM_NO_LET,
        "s60_control_no_intra_module_call",
    );
}

const S60_GRID_HELPER_ONLY: &str = r#"(import [primitives [*]])
(defn build-helper [] 42)
"#;

const S60_PROGRAM_CALLS_HELPER_DIRECTLY: &str = r#"(import [grid [build-helper]])
(defn main [] (build-helper))
"#;

// REGRESSION-GUARD: control C — direct call to helper, no wrapper layer in
// grid. Pins "imported wrapper that calls a same-module helper" as the
// load-bearing shape, not same-module calls in any imported module.
//
// (carry: legacy/sprint60_reduction.rs::s60_control_direct_helper_call_no_crash)
#[test]
fn s60_control_direct_helper_call_no_crash() {
    assert_two_file_cache_reuse_no_crash(
        S60_GRID_HELPER_ONLY,
        S60_PROGRAM_CALLS_HELPER_DIRECTLY,
        "s60_control_direct_helper_call",
    );
}

// -----------------------------------------------------------------------------
// §B — drop-glue / auto-curry double-free reductions (S60 Wave 2 Round 2)
// -----------------------------------------------------------------------------
//
// Cluster character: 14-LOC minimal source; ASLR-dependent / heap-layout-
// dependent flakiness. Each reduction trials 10× cold-cache to give >99%
// repro confidence under the documented ~90% Rust-spawn crash rate when
// the bug was active. Resolved post-S60 W2 R2; reductions stay as guards.

const S60_DROP_GLUE_MINIMAL: &str = r#"(import [primitives [*]])

(deftype Grid [cells])

(defn cell-at [g idx]
  (match g [(Grid cells) (vec-get cells idx)]))

(defn walk [g]
  (let [c1 (cell-at g 0)
        c2 (cell-at g 0)]
    0))

(defn main []
  (let [g (Grid (vec-push [] 0))]
    (walk g)))
"#;

// spec: spec/12-runtime.md §12.4 — RC inc/dec must balance; drop glue must
// not dec a captured value that the caller also dec's.
//
// REGRESSION-GUARD: Sprint 60 Wave 2 Round 2 — drop-glue / auto-curry
// closure captures the ADT `g` twice (once per `cell-at` call in `walk`);
// when both closures are RC-dec'd, the captured `g`'s RC reaches zero
// before `walk`'s scope cleanup, causing `heap_dealloc` to be invoked on
// `g`'s inner Vec twice. CLIF evidence: `walk`'s block1 allocates two
// 24-byte heap regions, stores two fn pointers + the captured `v1` (g),
// bumps g's RC twice, calls fn1(closure) then fn2(closure), then on return
// decrements each closure's RC to zero and runs drop glue.
//
// FIXME(/backend) — S60 Round 2 MINIMAL (14 LOC). Root cause was in either
// (a) `emit_consuming_caller_rc` for defn calls that get auto-curried
// despite both args present, or (b) closure env RC accounting for captures
// of ADT-wrapped Vec.
//
// (carry: legacy/sprint60_reduction.rs::s60_drop_glue_minimal_14_loc_no_crash)
#[test]
fn s60_drop_glue_minimal_14_loc_no_crash() {
    reduce_single_file_10_trials(S60_DROP_GLUE_MINIMAL, "s60_drop_glue_minimal_14_loc");
}

const S60_DROP_GLUE_ONE_CALL: &str = r#"(import [primitives [*]])

(deftype Grid [cells])

(defn cell-at [g idx]
  (match g [(Grid cells) (vec-get cells idx)]))

(defn walk [g]
  (let [c1 (cell-at g 0)]
    0))

(defn main []
  (let [g (Grid (vec-push [] 0))]
    (walk g)))
"#;

// REGRESSION-GUARD: control — single `cell-at` invocation does not crash.
// Pins the defect to the TWO-closure-same-capture interaction.
//
// (carry: legacy/sprint60_reduction.rs::s60_drop_glue_one_cellat_call_passes)
#[test]
fn s60_drop_glue_one_cellat_call_passes() {
    reduce_single_file_10_trials(S60_DROP_GLUE_ONE_CALL, "s60_drop_glue_one_cellat_call");
}

const S60_DROP_GLUE_INLINE_MATCH: &str = r#"(import [primitives [*]])

(deftype Grid [cells])

(defn walk [g]
  (let [c1 (match g [(Grid cs) (vec-get cs 0)])
        c2 (match g [(Grid cs) (vec-get cs 0)])]
    0))

(defn main []
  (let [g (Grid (vec-push [] 0))]
    (walk g)))
"#;

// REGRESSION-GUARD: control — inline-match twice on the same `g` does not
// crash. Pins the defect to the defn-call path (cell-at), NOT to
// match-semantics on Grid.
//
// (carry: legacy/sprint60_reduction.rs::s60_drop_glue_inline_match_passes)
#[test]
fn s60_drop_glue_inline_match_passes() {
    reduce_single_file_10_trials(S60_DROP_GLUE_INLINE_MATCH, "s60_drop_glue_inline_match");
}

const S60_DROP_GLUE_GRID_VEC_INT: &str = r#"(import [primitives [*]])

(deftype Grid [cells])

(defn cell-at [g idx]
  (match g [(Grid cells) (vec-get cells idx)]))

(defn walk [g]
  (let [c1 (cell-at g 0)
        c2 (cell-at g 0)]
    0))

(defn main []
  (let [g (Grid (vec-push [] 0))]
    (walk g)))
"#;

// FIXME(/backend) — S60 Round 2 variant. This is literally identical source
// to `s60_drop_glue_minimal_14_loc` — committed as a duplicate regression
// guard so that a well-intentioned "simplify" edit of the minimal test
// can't silently delete coverage. If one crashes, both do.
//
// REGRESSION-GUARD: deletion-resistance double for the minimal repro.
//
// (carry: legacy/sprint60_reduction.rs::s60_drop_glue_grid_vec_int_no_crash)
#[test]
fn s60_drop_glue_grid_vec_int_no_crash() {
    reduce_single_file_10_trials(S60_DROP_GLUE_GRID_VEC_INT, "s60_drop_glue_grid_vec_int");
}

const S60_DROP_GLUE_NO_WRAPPER: &str = r#"(import [primitives [*]])

(defn walk [v]
  (let [c1 (vec-get v 0)
        c2 (vec-get v 0)]
    0))

(defn main []
  (let [v (vec-push [] 0)]
    (walk v)))
"#;

// REGRESSION-GUARD: control — double `vec-get` on bare Vec, no ADT wrapper.
// Passes. Pins the defect to the Grid-wrapped-Vec shape specifically.
//
// (carry: legacy/sprint60_reduction.rs::s60_drop_glue_no_adt_wrapper_passes)
#[test]
fn s60_drop_glue_no_adt_wrapper_passes() {
    reduce_single_file_10_trials(S60_DROP_GLUE_NO_WRAPPER, "s60_drop_glue_no_adt_wrapper");
}

const S60_DROP_GLUE_NO_INTERMEDIATE: &str = r#"(import [primitives [*]])

(deftype Grid [cells])

(defn cell-at [g idx]
  (match g [(Grid cells) (vec-get cells idx)]))

(defn main []
  (let [g (Grid (vec-push [] 0))
        c1 (cell-at g 0)
        c2 (cell-at g 0)]
    0))
"#;

// REGRESSION-GUARD: control — double cell-at called directly from main (no
// walk fn). Passes. Pins the defect to the intermediate-fn parameter path.
//
// (carry: legacy/sprint60_reduction.rs::s60_drop_glue_no_intermediate_fn_passes)
#[test]
fn s60_drop_glue_no_intermediate_fn_passes() {
    reduce_single_file_10_trials(
        S60_DROP_GLUE_NO_INTERMEDIATE,
        "s60_drop_glue_no_intermediate_fn",
    );
}

// =============================================================================
// Sprint 60 Wave 2 Round 3 — `/run-tests` REPL-eval persistence-collapse
// =============================================================================
//
// Carry-forward from `tests/legacy/sprint60_run_tests_reduction.rs` per
// Wave 6 batch 4 audit. Cluster character: REPL-eval'd `(import [tiny ...])`
// against an empty entry `user.cl` produces a shutdown-path failure ("no
// parsed sexps for module 'user'") OR an active-path panic
// (`register_dep_for_eval MUST publish dep_sexps`) depending on the
// surfacing pathway. The four `_failing` reductions bound the defect
// shape; the fifth is a passing negative control proving the defect is
// REPL-eval-specific.
//
// CURRENT STATUS at audit time (2026-05-05):
//   #1, #2, #4: PASS (bug shape shifted since sprint authorship)
//   #3:        FAIL (open defect — failing-not-ignored per
//                    memory/feedback_failing_not_ignored.md)
//   #5:        PASS (negative control)
//
// Owning skill: /int (REPL session_v4 lifecycle wiring). FIXME 0146 is
// the harvest target.
//
// SPRINT 78 WAVE 4 (/qa) DECOUPLING: reductions #2–#5 exercise the
// REPL-eval'd import + scheduler lifecycle against a tiny `tiny.cl` fixture;
// their stdlib load was incidental. They now use the free-standing
// `run_repl_in_tmpdir_no_stdlib` helper (empty test-owned prelude, no
// `CRANELISP_LIB` → real stdlib) so they no longer red on the real-stdlib
// two-`Option` glob collision (FIXME 0312/0314). Reduction #1 genuinely runs
// the REAL exemplar `/run-tests html` and stays on the real-stdlib helper —
// see its body note: it is an exemplar/stdlib-conformance test, NOT a
// free-standing language test, and is left RED as an 0314-pending carry until
// /stdlib resolves the collision.
// =============================================================================

/// Drive the REPL binary from `cwd` (a fresh tempdir) with piped stdin.
fn run_repl_in_tmpdir(cwd: &Path, stdin_input: &str) -> std::process::Output {
    let binary = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("debug")
        .join("cranelisp");
    assert!(
        binary.exists(),
        "cranelisp binary not built at {binary:?} — run `cargo build` first"
    );
    let stdlib = Path::new(env!("CARGO_MANIFEST_DIR")).join("stdlib");
    let platform = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("debug");
    let mut child = std::process::Command::new(&binary)
        .current_dir(cwd)
        .env("CRANELISP_LIB", stdlib)
        .env("CRANELISP_PLATFORM_PATH", platform)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("failed to spawn cranelisp REPL");
    {
        use std::io::Write;
        if let Some(stdin) = child.stdin.as_mut() {
            let _ = stdin.write_all(stdin_input.as_bytes());
        }
    }
    child.wait_with_output().expect("failed to read REPL output")
}

/// Drive the REPL binary from `cwd` (a fresh tempdir) with piped stdin,
/// DECOUPLED from the real workspace `stdlib/`.
///
/// Sprint 78 Wave 4 (/qa): the sibling `run_repl_in_tmpdir` sets
/// `CRANELISP_LIB` to the real repo `stdlib/`, so the REPL loads
/// `stdlib/prelude.cl` at startup. After the `is_seeded` deletion the real
/// stdlib stops compiling (FIXME 0312/0314 — the two-`Option` glob collision),
/// which red-ed reductions 2–5 even though their SUBJECT (REPL-eval'd import
/// against an empty/absent entry `user.cl` + scheduler lifecycle) has nothing
/// to do with stdlib — the stdlib load was purely incidental.
///
/// This helper drops a test-owned EMPTY `prelude.cl` in the cwd (so the
/// binary's prelude auto-discovery finds a spec-clean, compiling prelude that
/// shadows stdlib per §8.8.2) and does NOT set `CRANELISP_LIB`. The reductions
/// thus exercise the same REPL-import + shutdown/eval lifecycle on a tiny
/// `tiny.cl` fixture, free-standing per root CLAUDE.md "Stdlib separation".
fn run_repl_in_tmpdir_no_stdlib(cwd: &Path, stdin_input: &str) -> std::process::Output {
    let binary = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("debug")
        .join("cranelisp");
    assert!(
        binary.exists(),
        "cranelisp binary not built at {binary:?} — run `cargo build` first"
    );
    // Empty test-owned prelude — shadows real stdlib (§8.8.2); spec-clean
    // (no `primitives` glob + separate Option footgun). Only dropped if the
    // test did not already place its own prelude/user content needing it.
    let prelude = cwd.join("prelude.cl");
    if !prelude.exists() {
        std::fs::write(&prelude, ";; empty test-owned prelude (no stdlib)\n").unwrap();
    }
    let mut child = std::process::Command::new(&binary)
        .current_dir(cwd)
        // NO CRANELISP_LIB — do not load the real workspace stdlib.
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("failed to spawn cranelisp REPL");
    {
        use std::io::Write;
        if let Some(stdin) = child.stdin.as_mut() {
            let _ = stdin.write_all(stdin_input.as_bytes());
        }
    }
    child.wait_with_output().expect("failed to read REPL output")
}

fn combined_out(o: &std::process::Output) -> String {
    format!(
        "{}{}",
        String::from_utf8_lossy(&o.stdout),
        String::from_utf8_lossy(&o.stderr),
    )
}

// spec: repl/spec.md §16.2.1 — `/run-tests [module]` MUST exit cleanly.
// REGRESSION-GUARD: Sprint 60 Wave 2 Round 3 — original cluster baseline
// (exemplar /run-tests html with empty user.cl).
//
// Status at audit: PASSES (the original "no parsed sexps" shutdown failure
// no longer fires for the exemplar batched shape).
//
// FIXME(/int) — REPL session_v4 lifecycle: REPL-eval'd imports against an
// empty entry user.cl historically left the user module Failed at
// shutdown. This shape now passes; the failure surface has shifted to
// the /quit variant (#3 below). Kept as a regression guard.
//
// (carry: legacy/sprint60_run_tests_reduction.rs::s60_run_tests_reduction_1_exemplar_batched_failing)
//
// **/stdlib-0314-PENDING CARRY (Sprint 78 Wave 4, /qa).** This reduction runs
// the REAL exemplar `/run-tests html` and therefore genuinely needs the real
// workspace stdlib + exemplar — it is an exemplar/stdlib-CONFORMANCE test, not
// a free-standing language test, so it CANNOT be decoupled (unlike its
// siblings #2–#5). It is currently RED because the `is_seeded` deletion (S78
// Wave 4) exposed a real two-`Option` glob collision in stdlib that stops the
// real stdlib compiling (FIXME 0312/0314). It stays failing-not-ignored as the
// durable record; closure is /stdlib's `fn.option` re-export fix (FIXME 0314),
// not a /qa decouple. Its purpose IS exemplar/stdlib conformance, so it belongs
// to that lane's get-to-green, not QA's free-standing suite.
#[test]
fn s60_run_tests_reduction_1_exemplar_batched_failing() {
    let exemplar_src = Path::new(env!("CARGO_MANIFEST_DIR")).join("exemplar");
    if !exemplar_src.exists() {
        eprintln!("exemplar/ missing — skipping this reduction");
        return;
    }
    let td = tempfile::tempdir().expect("tempdir for exemplar copy");
    copy_dir_recursive(&exemplar_src, td.path()).expect("copy exemplar tree");
    // Empty user.cl matches the original shape (wave6 test) — the defect
    // triggers only when user.cl is empty at session start.
    std::fs::write(td.path().join("user.cl"), "").unwrap();

    let input = "(import [html [test-wrap-tag]])\n/run-tests html\n";
    let out = run_repl_in_tmpdir(td.path(), input);
    let exit = out.status.code();
    let combined = combined_out(&out);

    let tests_all_ran = combined.contains("10 passed in");
    let load_err = combined.contains("no parsed sexps for module 'user'");
    let clean_exit = exit == Some(0);

    assert!(
        clean_exit && tests_all_ran && !load_err,
        "exemplar /run-tests html: exit={exit:?} (want 0). \
         tests_all_ran={tests_all_ran}. load_err_tail={load_err}. \
         --- combined ---\n{combined}"
    );
}

// spec: (same anchor) — MINIMAL REPRO of the shutdown-path defect.
// REGRESSION-GUARD: 19 LOC total (2-file tempdir). Any REPL session that
// imports from a local file-on-disk module while the current user.cl is
// absent/empty historically failed exit 1 at shutdown after EOF.
//
// Status at audit: PASSES (bug surface has shifted).
//
// FIXME(/int) — minimum REPL-import shape carries forward as a regression
// guard. If this ever fails again, the defect has regressed into the
// shutdown path.
//
// (carry: legacy/sprint60_run_tests_reduction.rs::s60_run_tests_reduction_2_repl_import_empty_user_failing)
#[test]
fn s60_run_tests_reduction_2_repl_import_empty_user_failing() {
    let td = tempfile::tempdir().expect("create tempdir");
    let cwd = td.path();
    std::fs::write(cwd.join("tiny.cl"), "(defn answer [] 42)\n").unwrap();
    // NO user.cl — the entry module sources to "" (empty sexps).

    let input = "(import [tiny [answer]])\n";
    let out = run_repl_in_tmpdir_no_stdlib(cwd, input);
    let exit = out.status.code();
    let combined = combined_out(&out);

    let load_err = combined.contains("no parsed sexps for module 'user'");
    let clean_exit = exit == Some(0);

    assert!(
        clean_exit && !load_err,
        "minimal REPL-import shape: exit={exit:?} (want 0). load_err={load_err}. \
         --- combined ---\n{combined}"
    );
}

// spec: (same anchor) — `/quit` variant.
//
// **OPEN DEFECT (failing-not-ignored)**: at audit time (2026-05-05) this
// test fails with exit 101 and a panic in `src/session_v4.rs:1572`:
// `register_dep_for_eval MUST publish dep_sexps before calling
// scheduler.register_module`. The original "no parsed sexps for module
// 'user'" shutdown-path symptom no longer fires; the bug surface has
// shifted into the active eval path. Same root-cause class
// (entry-module sexp-lifecycle inconsistency between REPL import and the
// persistent worker pool).
//
// Per `memory/feedback_failing_not_ignored.md`: lands un-ignored.
// FIXME(/int) — REPL session_v4 lifecycle: register_dep_for_eval ordering
// invariant violated when REPL evaluates an import against an empty entry
// user.cl + `/quit` shutdown. Migrate to numbered fixme at FIXME 0146
// close.
//
// (carry: legacy/sprint60_run_tests_reduction.rs::s60_run_tests_reduction_3_quit_variant_failing)
#[test]
fn s60_run_tests_reduction_3_quit_variant_failing() {
    let td = tempfile::tempdir().expect("create tempdir");
    let cwd = td.path();
    std::fs::write(cwd.join("tiny.cl"), "(defn answer [] 42)\n").unwrap();

    let input = "(import [tiny [answer]])\n/quit\n";
    let out = run_repl_in_tmpdir_no_stdlib(cwd, input);
    let exit = out.status.code();
    let combined = combined_out(&out);

    let load_err = combined.contains("no parsed sexps for module 'user'");
    let clean_exit = exit == Some(0);

    assert!(
        clean_exit && !load_err,
        "REPL with /quit after import should exit 0 and not emit load_err. \
         exit={exit:?} load_err={load_err}. \
         --- combined ---\n{combined}"
    );
}

// spec: (same anchor) — second-form variant: typing another expression
// after the import runs one extra iteration of the REPL loop, giving
// `poll_and_reload` a chance to observe the watcher event from
// `regenerate_backing_file`.
//
// Status at audit: PASSES (bug shape shifted; this surface no longer
// fires).
//
// FIXME(/int) — second-form variant carries forward as a regression guard.
// Original observation: even typing another expression after the import
// did not clear the scheduler state — the failure persisted through
// wait_object_complete. If this ever fails again, the defect has
// regressed into the second-form path.
//
// (carry: legacy/sprint60_run_tests_reduction.rs::s60_run_tests_reduction_4_second_form_variant_failing)
#[test]
fn s60_run_tests_reduction_4_second_form_variant_failing() {
    let td = tempfile::tempdir().expect("create tempdir");
    let cwd = td.path();
    std::fs::write(cwd.join("tiny.cl"), "(defn answer [] 42)\n").unwrap();

    // Import then a bare literal — the second iteration gives the watcher
    // a chance to observe the regenerate_backing_file write.
    let input = "(import [tiny [answer]])\n42\n";
    let out = run_repl_in_tmpdir_no_stdlib(cwd, input);
    let exit = out.status.code();
    let combined = combined_out(&out);

    let load_err = combined.contains("no parsed sexps for module 'user'");
    let clean_exit = exit == Some(0);

    assert!(
        clean_exit && !load_err,
        "REPL with second form after import should exit 0 and not emit load_err. \
         exit={exit:?} load_err={load_err}. \
         --- combined ---\n{combined}"
    );
}

// spec: (same anchor) — CONTROL: the same import form placed IN user.cl
// (as-a-file) rather than typed at the REPL prompt does NOT trigger the
// failure. Confirms the bug is specific to the REPL-eval path's
// interaction with the scheduler's user-module state — not a general
// local-import failure.
//
// REGRESSION-GUARD: passes today; if this ever fails, the defect has
// spread into the entry-module load path.
//
// (carry: legacy/sprint60_run_tests_reduction.rs::s60_run_tests_reduction_5_import_in_file_passes_control)
#[test]
fn s60_run_tests_reduction_5_import_in_file_passes_control() {
    let td = tempfile::tempdir().expect("create tempdir");
    let cwd = td.path();
    std::fs::write(cwd.join("tiny.cl"), "(defn answer [] 42)\n").unwrap();
    // user.cl HAS the import up-front.
    std::fs::write(cwd.join("user.cl"), "(import [tiny [answer]])\n").unwrap();

    // Empty stdin — entry module resolution alone drives the import.
    let out = run_repl_in_tmpdir_no_stdlib(cwd, "");
    let exit = out.status.code();
    let combined = combined_out(&out);

    assert_eq!(
        exit,
        Some(0),
        "REPL with import in user.cl (not typed at prompt) should exit 0. \
         exit={exit:?}. --- combined ---\n{combined}"
    );
}

// =============================================================================
// Sprint 64 Wave 6 batch 5 — Sprint 58 Wave 6 Defects 4+5 + Defect 6
// =============================================================================
//
// Carry-forward from `tests/legacy/wave6_demo_repros.rs` per Wave 6
// batch 5 audit. Two regression guards anchored to the original Sprint
// 58 Wave 6 user-proxy demo defects.
//
// Defect 4+5 collapsed to a single repro shape: discovering a list of
// tests under /run-tests and executing them in sequence MUST NOT
// segfault/trap, AND the discovery MUST find tests (positive
// completion). The d45 cluster above (§D) checks signal-crash; this
// adds the positive-completion angle (test-wrap-tag + ok/FAILED:).
//
// Defect 6 — exemplar solver `--run` entry stack-overflow on the real
// 81-cell puzzle. Distinct angle from the existing d6_exemplar_*
// cluster (synthetic single-form repros using exemplar source as a
// library, no IO): this exercises the **real solver entry**
// (`--run exemplar/solver.cl::main`) including the IO trampolines.
// Joins the four open-ledger d6_exemplar_* failing-not-ignored guards.
// =============================================================================

// spec: repl/spec.md §16.3 — `/run-tests <module>` MUST execute the
//       module's discovered test functions and report pass/fail without
//       crashing the process
//
// REGRESSION-GUARD: Sprint 58 Wave 6 Defects 4+5 — /run-tests html /
// /run-tests form on real exemplar previously produced exit 139 / 133
// (SIGSEGV / SIGTRAP) from the JIT'd test bodies. Combined fix landed;
// this guard adds the positive-completion assertion missing from
// d45_real_exemplar_html_run_tests_no_crash. Owning skill: /backend
// (RC / last-use accounting across consecutive run_test_by_name calls)
// or /int (run-tests dispatch loop).
//
// (carry: legacy/wave6_demo_repros.rs::run_tests_batched_invocation_no_crash)
//
// **/stdlib-0314-PENDING CARRY (Sprint 78 Wave 4, /qa).** Like
// `s60_run_tests_reduction_1`, this runs the REAL exemplar `/run-tests html`
// against the real workspace stdlib + platforms — an exemplar/stdlib
// CONFORMANCE test that CANNOT be made free-standing. Currently RED on the
// `is_seeded`-exposed two-`Option` stdlib collision (FIXME 0312/0314). Left
// failing-not-ignored; closure is /stdlib (FIXME 0314), not a /qa decouple.
#[test]
fn wave6_run_tests_batched_html_completes_without_crash() {
    use std::io::Write;
    use std::process::{Command, Stdio};

    // Copy exemplar tree into a fresh tempdir and zero out user.cl so the
    // checked-in user state is not in scope. Same shape as the d45 real-
    // exemplar tests above.
    let td = tempfile::tempdir().expect("tempdir for exemplar copy");
    copy_exemplar_into(td.path(), ".");
    std::fs::write(td.path().join("user.cl"), "").unwrap();
    let cwd = td.path();

    let binary = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("debug")
        .join("cranelisp");
    assert!(binary.exists(), "cranelisp binary not built");
    let stdlib = Path::new(env!("CARGO_MANIFEST_DIR")).join("stdlib");
    let platform = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("debug");

    let input = "(import [html [test-wrap-tag]])\n/run-tests html\n";
    let mut child = Command::new(&binary)
        .current_dir(cwd)
        .env("CRANELISP_LIB", stdlib)
        .env("CRANELISP_PLATFORM_PATH", platform)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn cranelisp REPL");
    {
        let stdin = child.stdin.as_mut().expect("stdin");
        let _ = stdin.write_all(input.as_bytes());
    }
    let out = child.wait_with_output().expect("wait subprocess");

    let exit = out.status.code();
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );
    // Failure mode 1: SIGSEGV / SIGTRAP from the JIT'd test bodies.
    let signal_crash = matches!(exit, Some(139) | Some(133)) || exit.is_none();
    // Failure mode 2: discovery race hides the test functions.
    let no_tests_found = combined.contains("No test-* functions found");
    // Failure mode 3: load fails outright before tests are discovered.
    let load_failed = combined.contains("no parsed sexps for module")
        || combined.contains("undefined variable: Nil");
    // Success: at least one test ran and reported pass/fail.
    let test_ran = combined.contains("test-wrap-tag")
        && (combined.contains(" ok") || combined.contains("FAILED:"));

    assert!(
        !signal_crash && !no_tests_found && !load_failed && test_ran,
        "/run-tests html did not complete cleanly. exit={exit:?}. \
         signal_crash={signal_crash} (Defect 4: html SIGSEGV; \
         Defect 5: form SIGTRAP). no_tests_found={no_tests_found}. \
         load_failed={load_failed}. test_ran={test_ran}. \
         Per repl/spec.md §16.3, /run-tests on a module with N test \
         functions must execute all N and report pass/fail without \
         crashing.\n--- combined ---\n{combined}"
    );
}

// spec: spec/12-runtime.md §12.5 — RC behaviour at depth: deep recursion
//       through Vec-copying ADT traversal must not segfault / overflow
//       the stack
//
// REGRESSION-GUARD: Sprint 58 Wave 6 Defect 6 (= Sprint 19 known issue) —
// exemplar solver `--run` entry stack-overflow on full 81-cell puzzle.
// Distinct angle from the d6_exemplar_* cluster above (synthetic single-
// form repros, no IO): this exercises the **real solver entry**
// (`--run exemplar/solver.cl::main`) including the IO trampolines that
// the synthetic repros elide. Differential observation: when /backend
// resolves the recursion depth issue, this guard becomes passing; if it
// still fails after the synthetic d6_exemplar_* guards pass, the
// remaining defect is in the IO-trampoline interaction.
//
// FAILING-NOT-IGNORED per `memory/feedback_failing_not_ignored.md`.
// Joins the four existing failing-not-ignored d6_exemplar_* tests in
// §F above. Owning skill /backend (deep recursion / Vec COW / stack
// frame size). Also FIXME(/port) — once Defect 6 is fixed, re-enable
// test-easy-puzzle, test-hard-puzzle, test-unsolvable in
// exemplar/solver.cl.
//
// (carry: legacy/wave6_demo_repros.rs::exemplar_solver_does_not_stack_overflow_on_small_puzzle)
#[test]
fn wave6_exemplar_solver_full_run_does_not_stack_overflow() {
    use std::process::{Command, Stdio};

    // Copy exemplar tree into a tempdir so the subprocess's cache + any
    // transient .cl mutations stay isolated.
    let td = tempfile::tempdir().expect("tempdir for exemplar copy");
    copy_exemplar_into(td.path(), "exemplar");
    let cwd = td.path();

    let binary = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("debug")
        .join("cranelisp");
    assert!(binary.exists(), "cranelisp binary not built");
    let stdlib = Path::new(env!("CARGO_MANIFEST_DIR")).join("stdlib");
    let platform = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("debug");

    // Use --run with the entry pointing to the real solver.cl. The
    // CRANELISP_LIB env var points to the workspace stdlib so prelude
    // resolves.
    let out = Command::new(&binary)
        .current_dir(cwd)
        .args(["--run", "exemplar/solver.cl"])
        .env("CRANELISP_LIB", stdlib)
        .env("CRANELISP_PLATFORM_PATH", platform)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("failed to invoke binary");

    let exit = out.status.code();
    // Stack overflow may surface as SIGABRT (None / SIGSEGV depending on
    // platform / runtime) — Rust's stack-overflow handler aborts the
    // process. Either way, exit success is required.
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

// =============================================================================
// FIXME 0177 + FIXME 0179 — cluster-mode check_forms cross-form state and
// staging+live read-union regressions.
//
// Authored Sprint 72 Wave 2 close-out as durable regression guards per
// `memory/feedback_repros_join_suite.md`. /review S72 W2 verified both
// FIXMEs were closed in source (see `crates/cranelisp-typecheck/src/form.rs`
// + `crates/cranelisp-typecheck/src/cluster.rs` for the resolved shape: a
// single `check_forms` frame threads `ModuleCheckAccumulator` across passes
// internally, and the unified `SymbolTableRead::Cluster { staging, live }`
// returns `View::union(staging, live)` for cluster-mode reads).
// =============================================================================

// regression-for: FIXME 0177 — check_forms cross-form state regression
// spec: design/arch/decisions/0044-cluster-atomic-typecheck-orchestrator-staging.md
//       §"`ClusterContext` (Approach B is canonical)"
//
// Pre-S66 the cross-form state hole manifested as stack-overflow when a
// later REPL input referenced a constrained-polymorphic defn registered
// by an earlier REPL input (Pass 4 monomorphisation re-entered the
// constrained-fn detection against a live-registered scheme without the
// per-call working state to terminate). Post-fix the single-frame
// `check_forms` rebuilds working state from live correctly and
// monomorphisation terminates with the correct `id$Int` specialisation.
#[test]
fn regression_0177_cross_form_state_no_bleed() {
    // Two separate REPL inputs: form 1 registers a constrained-polymorphic
    // `id`; form 2 (a wrapper defn `use1`) and a top-level call resolve `id`
    // at a concrete type. The second input's check_forms call rebuilds
    // per-call state from live and must monomorphise `id` cleanly.
    let cap = Cranelisp::repl_prims_capture(
        "(defn id [x] x)\n\
         (defn use1 [n] (id n))\n\
         (use1 7)\n",
    );
    // Successful eval prints `:primitives/Int 7` for the final call.
    assert!(
        cap.stdout.contains(":primitives/Int 7"),
        "expected ':primitives/Int 7' in stdout; stdout=\n{}\nstderr=\n{}",
        cap.stdout, cap.stderr,
    );
}

// regression-for: FIXME 0179 — cluster-mode union read staging + live
// spec: design/arch/decisions/0044-cluster-atomic-typecheck-orchestrator-staging.md
//       §"`ClusterContext` (Approach B is canonical)"
//
// Pre-S66 cluster-mode reads went only to live; an intra-cluster
// forward reference to a sibling defn staged in the same cluster but not
// yet committed read miss. Post-fix `SymbolTableRead::Cluster` returns
// `View::union(staging, live)` and Pass 2 body checks see staged Pass 1
// signatures of sibling forms.
#[test]
fn regression_0179_cluster_union_read_staging_and_live() {
    // Three-form cluster: deftype `Box` (form 1), defn `unwrap` matching
    // it (form 2), defn `roundtrip` calling `unwrap` (form 3). All three
    // are checked in one cluster — the body of `roundtrip` reads the
    // signature `unwrap` staged in Pass 1 (cluster-mode union read), and
    // the bodies of `unwrap` + `roundtrip` read `Box`'s `TypeDef` staged
    // in Pass 1.
    let cap = Cranelisp::repl_prims_capture(
        "(deftype Box [val])\n\
         (defn unwrap [b] (match b [(Box v) v]))\n\
         (defn roundtrip [n] (unwrap (Box n)))\n\
         (roundtrip 42)\n",
    );
    assert!(
        cap.stdout.contains(":primitives/Int 42"),
        "expected ':primitives/Int 42' in stdout; stdout=\n{}\nstderr=\n{}",
        cap.stdout, cap.stderr,
    );
}

// =============================================================================
// FIXME 0279 reduction — cross-module monomorphisation of a POLYMORPHIC
// imported function overflows the compiler (infinite `apply` recursion).
// =============================================================================
//
// Discovered as the `stdlib/io/monad.cl` compiler stack overflow (FIXME 0279,
// last blocker on the production prelude). Reduced from the full io.monad
// module to a 2-file, 3-line repro:
//
//   util.cl:  (defn f [x] x)            ; polymorphic identity :: (Fn [a] a)
//   main.cl:  (import [util [f]])
//             (defn main [] (f 9))      ; monomorphise f at Int
//
// Reduction findings (S76 W3 /qa):
//   - The `do`/`bind!`/`pure` macro+fn surface of io.monad is NOT the cause —
//     a recursive `do` macro DEFINED-but-unused does not overflow; a
//     non-recursive macro does not overflow.
//   - `pure` (the imported fn) IS the trigger, but NOT because of its name or
//     the `Pure` constructor: an imported `(defn lift [x] (Pure x))` overflows,
//     and so does an imported `(defn pure [x] x)`.
//   - The razor: an imported one-arg fn that returns a CONSTANT does NOT
//     overflow; an imported one-arg fn that returns its PARAMETER (i.e. is
//     POLYMORPHIC, `(Fn [a] a)`) DOES. A same-module polymorphic identity does
//     NOT overflow — the cross-module IMPORT is load-bearing.
//
// Root cause (lldb backtrace at the overflow): infinite recursion in
// `cranelisp_types::types::apply` (crates/cranelisp-types/src/types.rs:230) —
// `apply(subst, Var(id))` chases `id -> mapped` where the substitution maps a
// type var to a type containing itself (a cyclic/occurs-violating Subst). The
// cyclic subst is composed while instantiating the cross-module polymorphic
// scheme.
//
// Triage verdict: the defect is the CONSTRUCTION of the cyclic substitution
// when monomorphising a cross-module polymorphic scheme — a /typecheck
// responsibility (occurs-check / scheme instantiation / subst composition).
// `apply` in cranelisp-types is merely where the non-termination manifests.
//
// FIXME(/typecheck) — cross-module monomorphisation composes a self-referential
// Subst (occurs-check failure) for an imported `(Fn [a] a)`-shaped scheme.
// Lands FAILING (the compile stack-overflows and aborts; bounded by the
// harness 20s wall-clock so the abort surfaces as a non-success exit, not a
// suite hang). See FIXME 0279.
//
// spec: spec/08-modules.md §8.3 — imported function resolution + use; the
// polymorphic-scheme instantiation that §3 (types) requires must terminate.
#[test]
fn regression_0279_cross_module_polymorphic_import_monomorphisation() {
    use std::time::Duration;
    let result = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .file("util.cl", "(defn f [x] x)\n")
        .file("main.cl", "(import [util [f]])\n(defn main [] (f 9))\n")
        .run("main.cl")
        .timeout(Duration::from_secs(20))
        .try_output();
    match result {
        Ok(out) => {
            // The program is well-typed and must compile + run. Today it
            // stack-overflows (abort, no clean exit). A fix makes main exit
            // with the Int 9 (or 0 per §12.6 for a bare-Int main); the
            // assertion is simply that the compile did not abort.
            assert!(
                !out.stderr.contains("overflowed its stack")
                    && !out.stderr.contains("stack overflow"),
                "FIXME 0279: cross-module polymorphic import monomorphisation \
                 stack-overflowed in `cranelisp_types::types::apply` (cyclic \
                 Subst). Resolver /typecheck. stdout=\n{}\nstderr=\n{}",
                out.stdout,
                out.stderr
            );
        }
        Err(e2e::CrError::Timeout(_)) => {
            panic!("FIXME 0279: compile did not complete within 20s (worse than \
                    the expected overflow-abort); resolver /typecheck");
        }
        Err(e) => panic!("unexpected harness error: {e}"),
    }
}

// =============================================================================
// Sprint 78 — int-internal structural-target guard: SharedState field count
// =============================================================================
//
// RELOCATED in Sprint 78 Wave 1 (plan §3) FROM `tests/facade_pif_rows.rs`
// (`shared_state_field_count_matches_facade_after_pif`). Per FIXME 0298 this
// test introspects an int-INTERNAL struct (`SharedState`), not a boundary /
// public-API surface, so `facade_pif_rows.rs` (boundary-conformance only) was
// the wrong home. `regression.rs` is the canonical home for cross-cutting
// int-internal structural guards.
//
// This is the standing guard that the cross-thread in-progress parking maps
// (`module_sexps`, `suspend_states`) do not creep back onto `SharedState` after
// the Sprint 78 restructure deletes them. The restructure removes EXACTLY those
// 2 fields from 16 (the `register_dep_for_eval`/republish removal sheds methods,
// not fields). Wave 4 §2.7 then ADDS the one legitimate session-side field
// `prelude_fallback: cranelisp_typecheck::PreludeFallback` (the prelude-outer-
// scope companion map, parallel to `module_aliases`; session-side + unserialized
// — NOT creep). So the target is `== 15` (16 − module_sexps − suspend_states +
// prelude_fallback). `module_sexps`/`suspend_states` stay deleted.

// spec: design/int/s77-int-restructure.md §2.3 — SharedState drops 16 → 14
//       after module_sexps/suspend_states deletion; S78 Wave 4 §2.7 then adds
//       prelude_fallback → 15.
#[test]
fn shared_state_field_count_at_target_14() {
    // Count `pub` fields in `pub struct SharedState { … }` in session_v4.rs.
    //
    // Target is 15: 16 − module_sexps − suspend_states (S78 restructure) +
    // prelude_fallback (S78 Wave 4 §2.7 prelude-outer-scope companion). The
    // two cross-thread parking maps stay deleted; this guards that they do not
    // creep back while admitting the one legitimate Wave-4 field addition.
    let src = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/session_v4.rs");
    let text = std::fs::read_to_string(&src)
        .unwrap_or_else(|e| panic!("read {}: {e}", src.display()));
    let start = text
        .find("pub struct SharedState {")
        .expect("SharedState struct in src/session_v4.rs");
    let after = &text[start..];
    let end_offset = after
        .find("\n}\n")
        .expect("end of SharedState struct definition");
    let body = &after[..end_offset];
    // Count `pub ` field declarations — lines matching `\s+pub <ident>:`.
    let field_count = body
        .lines()
        .filter(|l| {
            let t = l.trim_start();
            t.starts_with("pub ") && t.contains(':') && !t.starts_with("pub fn")
        })
        .count();
    assert_eq!(
        field_count, 15,
        "SharedState has {field_count} pub fields; Sprint 78 target is exactly \
         15 (16 − module_sexps − suspend_states + prelude_fallback; \
         design/int/s77-int-restructure.md §2.3 + S78 Wave 4 §2.7). This is the \
         standing guard that the two cross-thread parking maps \
         (module_sexps/suspend_states) do not creep back, while admitting the \
         one legitimate Wave-4 session-side field `prelude_fallback`."
    );
}
