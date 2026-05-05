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

// spec: repl/spec.md §16.3 — single (run-test ...) call (not batch)
//
// FIXME(/backend) — If this test passes and
// d45_real_exemplar_html_run_tests fails, defect is in the /run-tests
// dispatch loop, not the individual run-test call.
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
        .stdin("(import [html [test-wrap-tag]])\n(run-test \"html/test-wrap-tag\")\n")
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
