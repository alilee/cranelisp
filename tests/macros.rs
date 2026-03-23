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
        display.contains("; defmacro"),
        "expected '; defmacro' in display, got: {display}"
    );
    assert!(
        display.contains("user/id"),
        "expected 'user/id' in display, got: {display}"
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
    // New universal format: `:user/pick ; defmacro` + clause signature lines
    assert!(
        display.contains("; defmacro"),
        "expected '; defmacro' in display, got: {display}"
    );
    assert!(
        display.contains("; [x] -> Sexp") && display.contains("; [x y] -> Sexp"),
        "expected clause signature lines, got: {display}"
    );
    // Dispatch to 1-arg clause.
    let val1 = repl_eval(&mut s, "(pick 42)");
    assert_eq!(val1, 42);
    // Dispatch to 2-arg clause.
    let val2 = repl_eval(&mut s, "(pick 10 20)");
    assert_eq!(val2, 10);
}

// spec: repl/spec.md §4.1.6 — defmacro display universal format
#[test]
fn repl_defmacro_display_single_clause() {
    let mut s = repl_session();
    let display = repl_eval_display(&mut s, "(defmacro my-id [x] x)");
    // Universal format: `:user/my-id ; defmacro` + `; [x] -> Sexp`
    assert!(
        display.contains(":user/my-id ; defmacro"),
        "expected ':user/my-id ; defmacro', got: {display}"
    );
    assert!(
        display.contains("; [x] -> Sexp"),
        "expected clause signature '; [x] -> Sexp', got: {display}"
    );
}

// spec: repl/spec.md §4.1.6 — defmacro display for multi-clause
#[test]
fn repl_defmacro_display_multi_clause() {
    let mut s = repl_session();
    let display = repl_eval_display(
        &mut s,
        "(defmacro mc ([x] x) ([x y] y) ([x y z] z))",
    );
    // Universal format: 3 clause signature lines
    assert!(
        display.contains("; [x] -> Sexp"),
        "expected '; [x] -> Sexp' clause line, got: {display}"
    );
    assert!(
        display.contains("; [x y] -> Sexp"),
        "expected '; [x y] -> Sexp' clause line, got: {display}"
    );
    assert!(
        display.contains("; [x y z] -> Sexp"),
        "expected '; [x y z] -> Sexp' clause line, got: {display}"
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
(defmacro double [x] `(primitives/add-i64 ~x ~x))
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
(defmacro inc [x] `(primitives/add-i64 ~x 1))
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
(defmacro choose ([x] x) ([x y] `(primitives/add-i64 ~x ~y)))
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
     (defn ~name [] (primitives/add-i64 ~a ~b))))
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
(defmacro inc [x] `(primitives/add-i64 ~x 1))
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
    let entry = s.core.tc.symbol_table().get("my-mac");
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

// ---------------------------------------------------------------------------
// D3: Macro expansion error handling (Sprint 16)
// ---------------------------------------------------------------------------

// spec: 09-macros.md §9.2.3 — macro body returning non-Sexp type produces type error
// The macro body is compiled as a function (SList Sexp) -> Sexp. If the body
// returns Int instead of Sexp, the typechecker catches it during macro compilation.
#[test]
fn neg_macro_non_sexp_return_type_batch() {
    use cranelisp::pipeline;
    use cranelisp_types::CompileMode;

    // Macro body returns Int (42) instead of Sexp — should fail at typecheck.
    let src = r#"
(defmacro bad [x] 42)
(defn main [] (bad 1))
"#;
    let result = pipeline::compile_and_run(src, CompileMode::Batch);
    assert!(
        result.is_err(),
        "macro returning non-Sexp should produce a compile error"
    );
}

// spec: 09-macros.md §9.2.3 — macro body returning non-Sexp type in REPL
#[test]
fn neg_macro_non_sexp_return_type_repl() {
    let mut s = repl_session();
    // Macro body returns Int instead of Sexp.
    let result = s.eval("(defmacro bad [x] 42)");
    assert!(
        result.is_err(),
        "REPL: macro returning non-Sexp should produce a compile error"
    );
}

// spec: 09-macros.md §9.2.3 — macro body returning Bool (non-Sexp) errors
#[test]
fn neg_macro_non_sexp_return_bool_batch() {
    use cranelisp::pipeline;
    use cranelisp_types::CompileMode;

    // Macro body returns Bool — not Sexp.
    let src = r#"
(defmacro bad [x] true)
(defn main [] (bad 1))
"#;
    let result = pipeline::compile_and_run(src, CompileMode::Batch);
    assert!(
        result.is_err(),
        "macro returning Bool should produce a compile error"
    );
}

// spec: 12-runtime.md §12.7 — macro expansion depth limit exceeded
// When two macros expand to each other infinitely, the expander hits
// EXPANSION_DEPTH_LIMIT (100) and produces a MacroError.
#[test]
fn neg_macro_expansion_depth_limit_exceeded() {
    let mut s = repl_session();
    // Define two macros that expand to each other, creating infinite recursion.
    s.eval("(defmacro ping [x] `(pong ~x))").unwrap();
    s.eval("(defmacro pong [x] `(ping ~x))").unwrap();
    // Trying to expand this should hit the depth limit.
    let result = s.eval("(ping 42)");
    assert!(
        result.is_err(),
        "mutually recursive macros should hit expansion depth limit"
    );
    let msg = match result {
        Err(e) => e.message().to_string(),
        Ok(_) => unreachable!("already asserted is_err"),
    };
    assert!(
        msg.contains("depth") || msg.contains("limit") || msg.contains("expansion"),
        "error should mention depth/limit/expansion, got: {msg}"
    );
}

// spec: 09-macros.md §9.14 — macro arity mismatch produces clear error
#[test]
fn neg_macro_arity_mismatch() {
    let mut s = repl_session();
    s.eval("(defmacro one-arg [x] x)").unwrap();
    // Call with wrong number of arguments.
    let result = s.eval("(one-arg 1 2 3)");
    assert!(
        result.is_err(),
        "calling macro with wrong arity should error"
    );
    let msg = match result {
        Err(e) => e.message().to_string(),
        Ok(_) => unreachable!("already asserted is_err"),
    };
    assert!(
        msg.contains("no matching clause") || msg.contains("argument"),
        "error should mention clause matching or arguments, got: {msg}"
    );
}

// spec: 09-macros.md §9.14 — macro error does not corrupt REPL session
#[test]
fn neg_macro_error_no_session_corruption() {
    let mut s = repl_session();
    // Failed macro definition should not corrupt session.
    let _ = s.eval("(defmacro bad [x] 42)");
    // Session should still work.
    let val = repl_eval(&mut s, "(add-i64 1 2)");
    assert_eq!(val, 3);

    // Define a working macro.
    s.eval("(defmacro good [x] x)").unwrap();
    let val = repl_eval(&mut s, "(good 42)");
    assert_eq!(val, 42);
}
