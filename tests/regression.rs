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
