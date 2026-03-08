// Integration tests for the macro pipeline (Phase 5).
//
// Tests that defmacro works in both REPL and batch modes, macro expansion
// is wired correctly, begin splicing works, and error recovery is preserved.

mod helpers;

use helpers::{repl_eval, repl_eval_display, repl_session};

// ---------------------------------------------------------------------------
// REPL: defmacro compile + expand
// ---------------------------------------------------------------------------

// spec: 09-macros.md §9.2 — defmacro works at REPL (compile + register)
#[test]
fn repl_defmacro_identity() {
    let mut s = repl_session();
    let display = repl_eval_display(&mut s, "(defmacro id [x] x)");
    assert!(
        display.contains(":: macro"),
        "expected macro display, got: {display}"
    );
    // Use the macro.
    let val = repl_eval(&mut s, "(id 42)");
    assert_eq!(val, 42);
}

// spec: 09-macros.md §9.4.2 — quasiquote macro at REPL
#[test]
fn repl_defmacro_quasiquote() {
    let mut s = repl_session();
    repl_eval_display(&mut s, "(defmacro wrap [x] `(add-i64 1 ~x))");
    // (wrap 10) should expand to (add-i64 1 10) and evaluate.
    let val = repl_eval(&mut s, "(wrap 10)");
    assert_eq!(val, 11);
}

// spec: 09-macros.md §9.2.6 — multi-clause dispatch at REPL
#[test]
fn repl_defmacro_multi_clause() {
    let mut s = repl_session();
    let display = repl_eval_display(
        &mut s,
        "(defmacro pick ([x] x) ([x y] x))",
    );
    assert!(
        display.contains("2 clauses"),
        "expected '2 clauses' in display, got: {display}"
    );
    // Dispatch to 1-arg clause.
    let val1 = repl_eval(&mut s, "(pick 42)");
    assert_eq!(val1, 42);
    // Dispatch to 2-arg clause.
    let val2 = repl_eval(&mut s, "(pick 10 20)");
    assert_eq!(val2, 10);
}

// spec: 09-macros.md §9.13 — defmacro display format
#[test]
fn repl_defmacro_display_single_clause() {
    let mut s = repl_session();
    let display = repl_eval_display(&mut s, "(defmacro my-id [x] x)");
    assert!(
        display.contains("my-id :: macro"),
        "expected 'my-id :: macro', got: {display}"
    );
    assert!(
        !display.contains("clauses"),
        "single clause should not mention 'clauses', got: {display}"
    );
}

// spec: 09-macros.md §9.13 — defmacro display for multi-clause
#[test]
fn repl_defmacro_display_multi_clause() {
    let mut s = repl_session();
    let display = repl_eval_display(
        &mut s,
        "(defmacro mc ([x] x) ([x y] y) ([x y z] z))",
    );
    assert!(
        display.contains("3 clauses"),
        "expected '3 clauses' in display, got: {display}"
    );
}

// ---------------------------------------------------------------------------
// REPL: macro expansion into regular forms
// ---------------------------------------------------------------------------

// spec: 09-macros.md §9.2 — macro producing if form
#[test]
fn repl_macro_produces_if() {
    let mut s = repl_session();
    repl_eval_display(&mut s, "(defmacro my-if [c t e] `(if ~c ~t ~e))");
    let val = repl_eval(&mut s, "(my-if true 1 2)");
    assert_eq!(val, 1);
    let val2 = repl_eval(&mut s, "(my-if false 1 2)");
    assert_eq!(val2, 2);
}

// spec: 09-macros.md §9.2 — macro producing let form
#[test]
fn repl_macro_produces_let() {
    let mut s = repl_session();
    repl_eval_display(&mut s, "(defmacro my-let [n v body] `(let [~n ~v] ~body))");
    let val = repl_eval(&mut s, "(my-let x 10 (add-i64 x 5))");
    assert_eq!(val, 15);
}

// ---------------------------------------------------------------------------
// REPL: begin splicing (defmacro-in-results)
// ---------------------------------------------------------------------------

// spec: 09-macros.md §9.6 — macro expansion producing begin
#[test]
fn repl_macro_begin_splicing() {
    let mut s = repl_session();
    repl_eval_display(
        &mut s,
        "(defmacro define-and-call [name val] `(begin (defn ~name [] ~val) (~name)))",
    );
    let val = repl_eval(&mut s, "(define-and-call my-fn 99)");
    assert_eq!(val, 99);
}

// spec: 09-macros.md §9.6 — defmacro-in-results: macro expansion producing defmacro
#[test]
fn repl_defmacro_in_results() {
    let mut s = repl_session();
    repl_eval_display(
        &mut s,
        "(defmacro make-id-macro [name] `(begin (defmacro ~name [x] x)))",
    );
    repl_eval_display(&mut s, "(make-id-macro my-id)");
    let val = repl_eval(&mut s, "(my-id 42)");
    assert_eq!(val, 42);
}

// ---------------------------------------------------------------------------
// REPL: error recovery
// ---------------------------------------------------------------------------

// spec: 09-macros.md §9.14 — bad macro body doesn't corrupt session
#[test]
fn repl_error_recovery_bad_macro() {
    let mut s = repl_session();
    let result = s.eval("(defmacro bad [x] (+ 1 \"hello\"))");
    assert!(result.is_err(), "expected error for bad macro body");
    let val = repl_eval(&mut s, "42");
    assert_eq!(val, 42);
}

// spec: 09-macros.md §9.14 — failed macro doesn't leave partial registration
#[test]
fn repl_error_recovery_no_partial_macro() {
    let mut s = repl_session();
    let _ = s.eval("(defmacro bad-mac [x] (+ 1 \"hello\"))");
    // Verify the session is still functional after the failed defmacro.
    let val = repl_eval(&mut s, "(add-i64 1 2)");
    assert_eq!(val, 3);
}

// ---------------------------------------------------------------------------
// Batch: defmacro in batch mode
// ---------------------------------------------------------------------------

// spec: 09-macros.md §9.2 — defmacro in batch pipeline
#[test]
fn batch_defmacro_simple() {
    use cranelisp::pipeline;
    use cranelisp_types::CompileMode;

    let src = r#"
(defmacro double [x] `(add-i64 ~x ~x))
(defn main [] (double 21))
"#;
    let result = pipeline::compile_and_run(src, CompileMode::Batch).unwrap();
    assert_eq!(result.value, 42);
}

// spec: 09-macros.md §9.4.2 — quasiquote macro in batch
#[test]
fn batch_defmacro_quasiquote() {
    use cranelisp::pipeline;
    use cranelisp_types::CompileMode;

    let src = r#"
(defmacro inc [x] `(add-i64 ~x 1))
(defn main [] (inc 41))
"#;
    let result = pipeline::compile_and_run(src, CompileMode::Batch).unwrap();
    assert_eq!(result.value, 42);
}

// spec: 09-macros.md §9.2.6 — multi-clause macro in batch
#[test]
fn batch_defmacro_multi_clause() {
    use cranelisp::pipeline;
    use cranelisp_types::CompileMode;

    let src = r#"
(defmacro choose ([x] x) ([x y] `(add-i64 ~x ~y)))
(defn main [] (choose 20 22))
"#;
    let result = pipeline::compile_and_run(src, CompileMode::Batch).unwrap();
    assert_eq!(result.value, 42);
}

// spec: 09-macros.md §9.6 — begin splicing in batch
#[test]
fn batch_defmacro_begin_splicing() {
    use cranelisp::pipeline;
    use cranelisp_types::CompileMode;

    let src = r#"
(defmacro define-pair [name a b]
  `(begin
     (defn ~name [] (add-i64 ~a ~b))))
(define-pair add-them 20 22)
(defn main [] (add-them))
"#;
    let result = pipeline::compile_and_run(src, CompileMode::Batch).unwrap();
    assert_eq!(result.value, 42);
}

// spec: 09-macros.md §9.2 — macro using another macro in batch
#[test]
fn batch_macro_uses_earlier_macro() {
    use cranelisp::pipeline;
    use cranelisp_types::CompileMode;

    let src = r#"
(defmacro inc [x] `(add-i64 ~x 1))
(defmacro inc2 [x] `(inc (inc ~x)))
(defn main [] (inc2 40))
"#;
    let result = pipeline::compile_and_run(src, CompileMode::Batch).unwrap();
    assert_eq!(result.value, 42);
}

// spec: 09-macros.md §9.2 — identity macro (no quasiquote) in batch
#[test]
fn batch_defmacro_identity() {
    use cranelisp::pipeline;
    use cranelisp_types::CompileMode;

    let src = r#"
(defmacro id [x] x)
(defn main [] (id 42))
"#;
    let result = pipeline::compile_and_run(src, CompileMode::Batch).unwrap();
    assert_eq!(result.value, 42);
}

// ---------------------------------------------------------------------------
// REPL: macro registered in module symbol table
// ---------------------------------------------------------------------------

// spec: 09-macros.md §9.13 — macro visible in symbol table after defmacro
#[test]
fn repl_macro_in_symbol_table() {
    let mut s = repl_session();
    repl_eval_display(&mut s, "(defmacro my-mac [x] x)");
    let entry = s.tc.symbol_table().get("my-mac");
    assert!(
        matches!(entry, Some(cranelisp_types::ModuleEntry::Macro { .. })),
        "expected Macro entry in symbol table"
    );
}

// ---------------------------------------------------------------------------
// REPL: sequential macro definition and use
// ---------------------------------------------------------------------------

// spec: 09-macros.md §9.12 — macros available for subsequent inputs
#[test]
fn repl_macro_available_for_later_inputs() {
    let mut s = repl_session();
    repl_eval_display(&mut s, "(defmacro add-one [x] `(add-i64 ~x 1))");
    repl_eval_display(&mut s, "(defn inc [n] (add-one n))");
    let val = repl_eval(&mut s, "(inc 41)");
    assert_eq!(val, 42);
}

// spec: 09-macros.md §9.2 — multiple macros defined sequentially
#[test]
fn repl_multiple_macros_sequential() {
    let mut s = repl_session();
    repl_eval_display(&mut s, "(defmacro m1 [x] `(add-i64 ~x 1))");
    repl_eval_display(&mut s, "(defmacro m2 [x] `(m1 (m1 ~x)))");
    let val = repl_eval(&mut s, "(m2 40)");
    assert_eq!(val, 42);
}

// ---------------------------------------------------------------------------
// Batch: error cases
// ---------------------------------------------------------------------------

// spec: 09-macros.md §9.14 — malformed defmacro produces error
#[test]
fn batch_defmacro_parse_error() {
    use cranelisp::pipeline;
    use cranelisp_types::CompileMode;

    let result = pipeline::compile_and_run("(defmacro bad)", CompileMode::Batch);
    assert!(result.is_err());
}

// spec: 09-macros.md §9.14 — defmacro with non-symbol name
#[test]
fn batch_defmacro_name_error() {
    use cranelisp::pipeline;
    use cranelisp_types::CompileMode;

    let result = pipeline::compile_and_run("(defmacro 42 [x] x)", CompileMode::Batch);
    assert!(result.is_err());
}
