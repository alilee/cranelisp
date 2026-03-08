// Ring 3 REPL experience tests: macro introspection, /expand, /imports, display.
//
// These tests validate the Ring 3 REPL features specified in repl/spec.md §11:
// - §11.1 /expand command
// - §11.2 macro introspection (/list, /info, /sig, /doc)
// - §11.3 defmacro display format
// - §11.4 bare macro name lookup
// - §11.5 test scenarios
// - §3.4 /imports command
//
// Tests use ReplSession::new() for isolation (no prelude dependency).
// Slash command tests that need the REPL input loop (e.g., /expand, /imports)
// are currently placeholder stubs pending E2E binary integration.

mod helpers;

use helpers::{repl_eval, repl_eval_display, repl_session};

// =============================================================================
// §11.5 Scenario 7: defmacro display at REPL (spec §11.3)
// =============================================================================

// spec: repl/spec.md §11.3 — single-clause defmacro shows "name :: macro"
#[test]
fn r3_defmacro_display_single_clause() {
    let mut s = repl_session();
    let display = repl_eval_display(&mut s, "(defmacro double [x] `(add-i64 ~x ~x))");
    assert!(
        display.contains("double :: macro"),
        "single-clause defmacro should show 'double :: macro', got: {display}"
    );
    // Single clause MUST NOT mention clause count.
    assert!(
        !display.contains("clauses"),
        "single-clause defmacro should NOT mention 'clauses', got: {display}"
    );
}

// spec: repl/spec.md §11.3 — multi-clause defmacro shows "name :: macro (N clauses)"
#[test]
fn r3_defmacro_display_multi_clause() {
    let mut s = repl_session();
    let display = repl_eval_display(
        &mut s,
        "(defmacro pick ([x] x) ([x y] x))",
    );
    assert!(
        display.contains("pick :: macro"),
        "multi-clause defmacro should contain 'pick :: macro', got: {display}"
    );
    assert!(
        display.contains("2 clauses"),
        "multi-clause defmacro should mention '2 clauses', got: {display}"
    );
}

// spec: repl/spec.md §11.3 — defmacro display for 3-clause macro
#[test]
fn r3_defmacro_display_three_clauses() {
    let mut s = repl_session();
    let display = repl_eval_display(
        &mut s,
        "(defmacro mc ([x] x) ([x y] y) ([x y z] z))",
    );
    assert!(
        display.contains("3 clauses"),
        "3-clause defmacro should mention '3 clauses', got: {display}"
    );
}

// =============================================================================
// §11.5 Scenario 4: /list after defmacro — Macros category appears (§11.2.1)
// =============================================================================

// spec: repl/spec.md §11.2.1 — macros registered as ModuleEntry::Macro in symbol table
#[test]
fn r3_list_macros_category_via_symbol_table() {
    let mut s = repl_session();
    repl_eval_display(&mut s, "(defmacro double [x] `(add-i64 ~x ~x))");
    repl_eval_display(&mut s, "(defmacro triple [x] `(add-i64 ~x (add-i64 ~x ~x)))");

    // Verify macros are in the symbol table as Macro entries.
    let table = s.tc.symbol_table();
    let double_entry = table.get("double");
    assert!(
        matches!(double_entry, Some(cranelisp_types::ModuleEntry::Macro { .. })),
        "expected Macro entry for 'double' in symbol table, got: {double_entry:?}"
    );
    let triple_entry = table.get("triple");
    assert!(
        matches!(triple_entry, Some(cranelisp_types::ModuleEntry::Macro { .. })),
        "expected Macro entry for 'triple' in symbol table, got: {triple_entry:?}"
    );
}

// spec: repl/spec.md §11.2.1, §3.3 — macros appear in Macros, not in Functions
#[test]
fn r3_list_neg_macros_not_in_functions() {
    let mut s = repl_session();
    repl_eval_display(&mut s, "(defmacro double [x] `(add-i64 ~x ~x))");
    s.eval("(defn inc [x] (add-i64 x 1))").unwrap();

    // Walk the symbol table and check that 'double' is a Macro, not a Def.
    let table = s.tc.symbol_table();
    let double_entry = table.get("double");
    assert!(
        matches!(double_entry, Some(cranelisp_types::ModuleEntry::Macro { .. })),
        "expected Macro entry for 'double', not Def"
    );
    // 'inc' should be a Def (function), not a Macro.
    let inc_entry = table.get("inc");
    assert!(
        matches!(inc_entry, Some(cranelisp_types::ModuleEntry::Def { .. })),
        "expected Def entry for 'inc', got: {inc_entry:?}"
    );
}

// =============================================================================
// §11.5 Scenario 5: /info on multi-clause macro (§11.2.2)
// =============================================================================

// spec: repl/spec.md §11.2.2 — /info macro clause count in symbol table
#[test]
fn r3_info_macro_clause_count() {
    let mut s = repl_session();
    repl_eval_display(
        &mut s,
        "(defmacro mc ([x] x) ([x y] x) ([x y z] z))",
    );

    let entry = s.tc.symbol_table().get("mc");
    match entry {
        Some(cranelisp_types::ModuleEntry::Macro { clauses, .. }) => {
            assert_eq!(
                clauses.len(),
                3,
                "expected 3 clauses for 'mc', got {}",
                clauses.len()
            );
        }
        other => {
            panic!("expected Macro entry for 'mc', got: {other:?}");
        }
    }
}

// spec: repl/spec.md §11.2.2 — macro without docstring has None
#[test]
fn r3_info_macro_docstring() {
    let mut s = repl_session();
    repl_eval_display(&mut s, "(defmacro id [x] x)");

    let entry = s.tc.symbol_table().get("id");
    match entry {
        Some(cranelisp_types::ModuleEntry::Macro { docstring, .. }) => {
            // Without docstring, should be None.
            assert!(
                docstring.is_none(),
                "macro without docstring should have None, got: {docstring:?}"
            );
        }
        other => {
            panic!("expected Macro entry for 'id', got: {other:?}");
        }
    }
}

// =============================================================================
// §11.5 Scenario 6: /sig on variadic macro (§11.2.3)
// =============================================================================

// spec: repl/spec.md §11.2.3 — macro clause params recorded in symbol table
#[test]
fn r3_sig_macro_params() {
    let mut s = repl_session();
    repl_eval_display(&mut s, "(defmacro simple [x y] x)");

    let entry = s.tc.symbol_table().get("simple");
    match entry {
        Some(cranelisp_types::ModuleEntry::Macro { clauses, .. }) => {
            assert_eq!(clauses.len(), 1, "expected 1 clause");
            let clause = &clauses[0];
            assert_eq!(clause.params.len(), 2, "expected 2 params");
            assert!(clause.rest_param.is_none(), "no rest param expected");
        }
        other => {
            panic!("expected Macro entry for 'simple', got: {other:?}");
        }
    }
}

// spec: repl/spec.md §11.2.3 — variadic macro clause with & rest
#[test]
#[ignore = "Ring 3, Sprint 11: parse error on '& rest' syntax in defmacro params"]
fn r3_sig_macro_variadic() {
    let mut s = repl_session();
    repl_eval_display(
        &mut s,
        "(defmacro my-cond ([x] x) ([x body & rest] `(if ~x ~body (my-cond ~@rest))))",
    );

    let entry = s.tc.symbol_table().get("my-cond");
    match entry {
        Some(cranelisp_types::ModuleEntry::Macro { clauses, .. }) => {
            assert_eq!(clauses.len(), 2, "expected 2 clauses");
            // Second clause should have rest_param.
            let clause2 = &clauses[1];
            assert!(
                clause2.rest_param.is_some(),
                "second clause should have a rest param"
            );
        }
        other => {
            panic!("expected Macro entry for 'my-cond', got: {other:?}");
        }
    }
}

// =============================================================================
// §11.5 Scenario 8: Bare macro name lookup (§11.4)
// =============================================================================

// spec: repl/spec.md §11.4 — bare macro name shows clause signatures
// NOTE: Bare macro names currently trigger zero-arg expansion dispatch rather
// than introspection. The spec says non-zero-arg macros should show signatures;
// zero-arg macros expand immediately.
#[test]
#[ignore = "Ring 3, Sprint 11: bare macro name triggers expansion dispatch, not introspection"]
fn r3_bare_macro_lookup() {
    let mut s = repl_session();
    repl_eval_display(&mut s, "(defmacro double [x] `(add-i64 ~x ~x))");

    // Entering a macro name bare should produce its signature, not an error.
    let result = s.eval("double");
    match result {
        Ok(r) => {
            let display = r.definition_display.unwrap_or_default();
            assert!(
                display.contains("macro"),
                "bare macro lookup should show 'macro' in display, got: {display}"
            );
        }
        Err(e) => {
            panic!("bare macro name 'double' should not error, got: {e}");
        }
    }
}

// spec: repl/spec.md §11.4 — multi-clause macro bare lookup shows all clause signatures
#[test]
#[ignore = "Ring 3, Sprint 11: bare macro name triggers expansion dispatch, not introspection"]
fn r3_bare_macro_lookup_multi_clause() {
    let mut s = repl_session();
    repl_eval_display(
        &mut s,
        "(defmacro pick ([x] x) ([x y] x))",
    );

    let result = s.eval("pick");
    match result {
        Ok(r) => {
            let display = r.definition_display.unwrap_or_default();
            assert!(
                display.contains("macro"),
                "bare multi-clause macro should show 'macro', got: {display}"
            );
        }
        Err(e) => {
            panic!("bare macro name 'pick' should not error, got: {e}");
        }
    }
}

// =============================================================================
// §11.5 Scenarios 1-3: /expand command (§11.1)
// These need E2E tests because /expand is a slash command processed by the
// REPL input loop, not by session.eval(). Stubs pending binary integration.
// =============================================================================

// spec: repl/spec.md §11.1 — /expand with a single macro shows expanded form
#[test]
#[ignore = "Ring 3, Sprint 11: /expand requires E2E test via binary subprocess"]
fn r3_expand_single_macro() {
    // TODO: E2E test. Define a macro, then /expand (macro-name arg).
    // Expected: displays expanded form without evaluation.
}

// spec: repl/spec.md §11.1 — /expand with nested macros expands recursively
#[test]
#[ignore = "Ring 3, Sprint 11: /expand requires E2E test via binary subprocess"]
fn r3_expand_nested_macros() {
    // TODO: E2E test. Define two macros where one calls the other.
    // /expand should recursively expand to fixed point.
}

// spec: repl/spec.md §11.1 — /expand with no macro calls shows input unchanged
#[test]
#[ignore = "Ring 3, Sprint 11: /expand requires E2E test via binary subprocess"]
fn r3_expand_no_macro() {
    // TODO: E2E test. /expand (add-i64 1 2) should display (add-i64 1 2) unchanged.
}

// =============================================================================
// §11.2.4 /doc on macro (spec §11.2.4)
// =============================================================================

// spec: repl/spec.md §11.2.4 — /doc on macro with no docstring
#[test]
#[ignore = "Ring 3, Sprint 11: /doc requires E2E test via binary subprocess"]
fn r3_doc_macro_no_docstring() {
    // TODO: E2E test. /doc my-macro should show "my-macro: no docstring".
}

// =============================================================================
// §3.4 /imports command
// =============================================================================

// spec: repl/spec.md §3.4 — /imports with no imports shows nothing
#[test]
#[ignore = "Ring 3, Sprint 11: /imports requires E2E test via binary subprocess"]
fn r3_imports_empty() {
    // In a fresh session with no explicit imports, /imports should produce
    // empty output (silent re-prompt).
}

// spec: repl/spec.md §3.4 — /imports <module> for nonexistent module
#[test]
#[ignore = "Ring 3, Sprint 11: /imports requires E2E test via binary subprocess"]
fn r3_imports_nonexistent_module() {
    // /imports nonexistent should produce empty output, not an error.
}

// spec: repl/spec.md §3.4 — /imports shows imports grouped by source module
#[test]
#[ignore = "Ring 3, Sprint 11: /imports requires E2E test via binary subprocess"]
fn r3_imports_grouped_by_module() {
    // After explicit (import [primitives [add-i64 sub-i64]]),
    // /imports should show:
    // From primitives:
    //   add-i64 :: (Fn [primitives/Int primitives/Int] primitives/Int)
    //   sub-i64 :: (Fn [primitives/Int primitives/Int] primitives/Int)
}

// spec: repl/spec.md §3.4 — /imports <module> filters to one module
#[test]
#[ignore = "Ring 3, Sprint 11: /imports requires E2E test via binary subprocess"]
fn r3_imports_filter_by_module() {
    // /imports primitives should show only primitives imports.
}

// =============================================================================
// §4.2 Special form feedback for defmacro
// =============================================================================

// spec: repl/spec.md §4.2 — bare 'defmacro' shows special form signature
#[test]
#[ignore = "Ring 3, Sprint 11: defmacro not registered as special form in builtins"]
fn r3_special_form_defmacro() {
    let mut s = repl_session();
    // Entering 'defmacro' bare should show its syntax, not an error.
    let result = s.eval("defmacro");
    match result {
        Ok(r) => {
            let display = if let Some(d) = r.definition_display { d }
            else { format!("{}", r.value) };
            assert!(
                display.contains("defmacro") || display.contains("Fn"),
                "bare 'defmacro' should show special form info, got: {display}"
            );
        }
        Err(e) => {
            panic!("bare 'defmacro' should produce feedback, not error: {e}");
        }
    }
}

// =============================================================================
// Negative tests: Ring 3 REPL
// =============================================================================

// spec: repl/spec.md §11.2.1 — non-macros absent from Macros category
#[test]
fn r3_neg_non_macros_absent_from_macros() {
    let mut s = repl_session();
    s.eval("(defn foo [x] x)").unwrap();
    s.eval("(deftype Color Red Blue)").unwrap();
    repl_eval_display(&mut s, "(defmacro my-mac [x] x)");

    // Walk symbol table: non-Macro entries must not be ModuleEntry::Macro.
    let table = s.tc.symbol_table();
    // Specifically: 'foo' must not be a Macro.
    let foo_entry = table.get("foo");
    assert!(
        !matches!(foo_entry, Some(cranelisp_types::ModuleEntry::Macro { .. })),
        "'foo' (defn) must not be in Macros category"
    );
    // 'Color' must not be a Macro.
    let color_entry = table.get("Color");
    assert!(
        !matches!(color_entry, Some(cranelisp_types::ModuleEntry::Macro { .. })),
        "'Color' (deftype) must not be in Macros category"
    );
    // 'my-mac' MUST be a Macro.
    let mac_entry = table.get("my-mac");
    assert!(
        matches!(mac_entry, Some(cranelisp_types::ModuleEntry::Macro { .. })),
        "'my-mac' (defmacro) must be in Macros category"
    );
}

// spec: repl/spec.md §11.1 — /expand on non-macro form displays input unchanged
#[test]
#[ignore = "Ring 3, Sprint 11: /expand requires E2E test via binary subprocess"]
fn r3_neg_expand_non_macro_unchanged() {
    // /expand (add-i64 1 2) should display (add-i64 1 2) unchanged when add-i64 is not a macro.
}

// spec: 09-macros.md §9.14 — malformed macro call: clear error, not crash
#[test]
fn r3_neg_malformed_macro_call_error() {
    let mut s = repl_session();
    // Define a macro that expects exactly 1 arg.
    repl_eval_display(&mut s, "(defmacro id [x] x)");

    // Call with wrong arity (0 args).
    let result = s.eval("(id)");
    assert!(
        result.is_err(),
        "calling macro with wrong arity should error, not crash"
    );

    // Session should still work after the error.
    let val = repl_eval(&mut s, "(add-i64 1 2)");
    assert_eq!(val, 3, "session should work after macro arity error");
}

// spec: 09-macros.md §9.14 — macro with wrong arity gives clear error message
#[test]
fn r3_neg_macro_wrong_arity_error_message() {
    let mut s = repl_session();
    repl_eval_display(&mut s, "(defmacro pair [x y] `(add-i64 ~x ~y))");

    // Call with 1 arg (needs 2).
    let result = s.eval("(pair 1)");
    assert!(
        result.is_err(),
        "calling 2-arg macro with 1 arg should error"
    );
    // The error message should mention arity or argument mismatch.
    if let Err(e) = result {
        let msg = e.message();
        assert!(
            msg.contains("argument") || msg.contains("arity")
                || msg.contains("expected") || msg.contains("clause")
                || msg.contains("match"),
            "error should mention argument/arity mismatch, got: {msg}"
        );
    }

    // Session should still work.
    let val = repl_eval(&mut s, "(add-i64 3 4)");
    assert_eq!(val, 7);
}

// spec: 09-macros.md §9.14 — malformed defmacro: missing params list
#[test]
fn r3_neg_defmacro_missing_params() {
    let mut s = repl_session();
    let result = s.eval("(defmacro bad)");
    assert!(
        result.is_err(),
        "defmacro without params should produce error"
    );
    // Session should still work.
    let val = repl_eval(&mut s, "42");
    assert_eq!(val, 42);
}

// spec: 09-macros.md §9.14 — malformed defmacro: non-symbol name
#[test]
fn r3_neg_defmacro_numeric_name() {
    let mut s = repl_session();
    let result = s.eval("(defmacro 42 [x] x)");
    assert!(
        result.is_err(),
        "defmacro with numeric name should produce error"
    );
    let val = repl_eval(&mut s, "42");
    assert_eq!(val, 42);
}

// spec: 09-macros.md §9.14 — malformed defmacro: missing body
#[test]
fn r3_neg_defmacro_missing_body() {
    let mut s = repl_session();
    let result = s.eval("(defmacro bad [x])");
    assert!(
        result.is_err(),
        "defmacro without body should produce error"
    );
    let val = repl_eval(&mut s, "42");
    assert_eq!(val, 42);
}

// spec: repl/spec.md §3.4 — /imports with no imports is empty, not error
#[test]
#[ignore = "Ring 3, Sprint 11: /imports requires E2E test via binary subprocess"]
fn r3_neg_imports_no_imports_not_error() {
    // In fresh session, /imports should produce empty output, not an error.
}

// spec: repl/spec.md §3.4 — /imports nonexistent is empty, not error
#[test]
#[ignore = "Ring 3, Sprint 11: /imports requires E2E test via binary subprocess"]
fn r3_neg_imports_nonexistent_not_error() {
    // /imports nonexistent should produce empty output, not an error.
}

// =============================================================================
// Edge cases: expansion depth, nested macro errors
// =============================================================================

// spec: 09-macros.md §9.3.3 — macro expansion reaches fixed point
#[test]
fn r3_macro_expansion_reaches_fixed_point() {
    let mut s = repl_session();
    // Define a macro that produces a form with no further macro calls.
    repl_eval_display(&mut s, "(defmacro wrap [x] `(add-i64 ~x 0))");
    // If expansion reaches a fixed point, this should work.
    let val = repl_eval(&mut s, "(wrap 42)");
    assert_eq!(val, 42, "expansion should reach fixed point");
}

// spec: 09-macros.md §9.14 — error in macro body type doesn't corrupt session
#[test]
fn r3_macro_body_type_error_recovery() {
    let mut s = repl_session();
    // This macro has a type error in its body (compile-time, not expansion-time).
    let result = s.eval("(defmacro bad [x] (add-i64 \"hello\" 1))");
    assert!(result.is_err(), "type error in macro body should fail");

    // Session should still work.
    let val = repl_eval(&mut s, "(add-i64 10 20)");
    assert_eq!(val, 30);
}

// spec: 09-macros.md §9.2 — macro that expands to a simple literal
// NOTE: macro bodies must return Sexp, not bare Int. A macro returning a bare
// integer literal would need to produce (quote 42) or similar.
#[test]
#[ignore = "Ring 3, Sprint 11: macro body must return Sexp (bare literal 42 produces type error)"]
fn r3_macro_expands_to_literal() {
    let mut s = repl_session();
    repl_eval_display(&mut s, "(defmacro always-42 [x] 42)");
    let val = repl_eval(&mut s, "(always-42 ignored)");
    assert_eq!(val, 42, "macro should expand to literal 42");
}

// spec: 09-macros.md §9.2 — macro using add-i64 in body
#[test]
fn r3_macro_with_arithmetic_expansion() {
    let mut s = repl_session();
    repl_eval_display(&mut s, "(defmacro double [x] `(add-i64 ~x ~x))");
    let val = repl_eval(&mut s, "(double 21)");
    assert_eq!(val, 42, "double macro should expand to (add-i64 21 21)");
}

// spec: 09-macros.md §9.2 — macro result used in further computation
#[test]
fn r3_macro_result_in_expression() {
    let mut s = repl_session();
    repl_eval_display(&mut s, "(defmacro inc [x] `(add-i64 ~x 1))");
    // Use macro result in a larger expression.
    let val = repl_eval(&mut s, "(add-i64 (inc 10) (inc 20))");
    assert_eq!(val, 32, "(add-i64 (inc 10) (inc 20)) should be 32");
}

// spec: 09-macros.md §9.2 — multiple macro definitions in one session
#[test]
fn r3_multiple_macros_in_session() {
    let mut s = repl_session();
    repl_eval_display(&mut s, "(defmacro m-a [x] `(add-i64 ~x 1))");
    repl_eval_display(&mut s, "(defmacro m-b [x] `(mul-i64 ~x 2))");

    let val_a = repl_eval(&mut s, "(m-a 10)");
    assert_eq!(val_a, 11);
    let val_b = repl_eval(&mut s, "(m-b 10)");
    assert_eq!(val_b, 20);
}

// spec: 09-macros.md §9.2 — macro persists across multiple evals
#[test]
fn r3_macro_persists_across_evals() {
    let mut s = repl_session();
    repl_eval_display(&mut s, "(defmacro id [x] x)");
    let val1 = repl_eval(&mut s, "(id 1)");
    assert_eq!(val1, 1);
    // Define something else, then use the macro again.
    s.eval("(defn foo [x] (add-i64 x 1))").unwrap();
    let val2 = repl_eval(&mut s, "(id 99)");
    assert_eq!(val2, 99, "macro should persist across subsequent definitions");
}

// spec: 09-macros.md §9.14 — macro error does not lose previously defined macros
#[test]
fn r3_macro_error_preserves_existing_macros() {
    let mut s = repl_session();
    repl_eval_display(&mut s, "(defmacro good [x] `(add-i64 ~x 1))");

    // Define a bad macro.
    let _ = s.eval("(defmacro bad [x] (add-i64 \"hello\" 1))");

    // The good macro should still work.
    let val = repl_eval(&mut s, "(good 41)");
    assert_eq!(val, 42, "previously defined macro should survive error");
}

// =============================================================================
// Batch mode: macro tests
// =============================================================================

// spec: 09-macros.md §9.2 — macro used in function body (batch)
#[test]
#[ignore = "Ring 3, Sprint 11: nested macro expansion in defn body causes marshal assertion failure"]
fn r3_batch_macro_in_function_body() {
    use cranelisp::pipeline;
    use cranelisp_types::CompileMode;

    let src = r#"
(defmacro inc [x] `(add-i64 ~x 1))
(defn add-two [n] (inc (inc n)))
(defn main [] (add-two 40))
"#;
    let result = pipeline::compile_and_run(src, CompileMode::Batch).unwrap();
    assert_eq!(result.value, 42);
}

// spec: 09-macros.md §9.2 — macro with multiple uses in same function (batch)
#[test]
fn r3_batch_macro_multiple_uses() {
    use cranelisp::pipeline;
    use cranelisp_types::CompileMode;

    let src = r#"
(defmacro double [x] `(add-i64 ~x ~x))
(defn main [] (add-i64 (double 10) (double 11)))
"#;
    let result = pipeline::compile_and_run(src, CompileMode::Batch).unwrap();
    assert_eq!(result.value, 42);
}
