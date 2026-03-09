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
fn r3_sig_macro_variadic() {
    let mut s = repl_session();
    let result = s.eval(
        "(defmacro my-cond ([x] x) ([x body & rest] `(if ~x ~body (my-cond ~@rest))))",
    );

    match result {
        Ok(_) => {
            let entry = s.tc.symbol_table().get("my-cond");
            match entry {
                Some(cranelisp_types::ModuleEntry::Macro { clauses, .. }) => {
                    assert_eq!(clauses.len(), 2, "expected 2 clauses");
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
        Err(e) => {
            panic!("variadic macro definition should succeed, got: {e}");
        }
    }
}

// =============================================================================
// §11.5 Scenario 8: Bare macro name lookup (§11.4)
// =============================================================================

// spec: repl/spec.md §11.4 — bare macro name shows clause signatures
// FIXME(/int): bare non-zero-arg macro names should show clause signatures, not dispatch
#[test]
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

// spec: repl/spec.md §4.2 — bare 'defmacro' shows special form signature
// FIXME(/typecheck): register 'defmacro' in special_forms list (builtins.rs:253)
#[test]
fn r3_special_form_defmacro() {
    let mut s = repl_session();
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
// §9.2.4 Macro docstrings
// =============================================================================

// spec: 09-macros.md §9.2.4 — macro with docstring stores it
#[test]
fn r3_macro_docstring_stored() {
    let mut s = repl_session();
    repl_eval_display(
        &mut s,
        "(defmacro my-inc \"Increment by one\" [x] `(add-i64 ~x 1))",
    );

    let entry = s.tc.symbol_table().get("my-inc");
    match entry {
        Some(cranelisp_types::ModuleEntry::Macro { docstring, .. }) => {
            assert_eq!(
                docstring.as_deref(),
                Some("Increment by one"),
                "macro docstring should be stored"
            );
        }
        other => {
            panic!("expected Macro entry for 'my-inc', got: {other:?}");
        }
    }
}

// spec: 09-macros.md §9.2.4 — macro without docstring has None
#[test]
fn r3_macro_no_docstring() {
    let mut s = repl_session();
    repl_eval_display(&mut s, "(defmacro simple [x] x)");

    let entry = s.tc.symbol_table().get("simple");
    match entry {
        Some(cranelisp_types::ModuleEntry::Macro { docstring, .. }) => {
            assert!(
                docstring.is_none(),
                "macro without docstring should have None, got: {docstring:?}"
            );
        }
        other => {
            panic!("expected Macro entry for 'simple', got: {other:?}");
        }
    }
}

// =============================================================================
// §9.3.4 Define-before-use
// =============================================================================

// spec: 09-macros.md §9.3.4 — macro defined before use works
#[test]
fn r3_define_before_use_works() {
    let mut s = repl_session();
    repl_eval_display(&mut s, "(defmacro inc [x] `(add-i64 ~x 1))");
    let val = repl_eval(&mut s, "(inc 41)");
    assert_eq!(val, 42, "macro defined before use should work");
}

// spec: 09-macros.md §9.3.4 — forward reference to undefined macro is not expanded
#[test]
fn r3_neg_forward_reference_not_expanded() {
    let mut s = repl_session();
    // Call a macro name before defining it — should be treated as a function call, not expansion.
    let result = s.eval("(not-yet-defined 42)");
    assert!(
        result.is_err(),
        "forward reference to undefined macro should error"
    );
}

// =============================================================================
// §9.8.1 Auto-gensym hygiene
// =============================================================================

// spec: 09-macros.md §9.8.1 — auto-gensym prevents variable capture
#[test]
fn r3_auto_gensym_prevents_capture() {
    let mut s = repl_session();
    // Define a macro that introduces a binding using gensym (x#).
    // The outer 'x' should not be captured.
    repl_eval_display(&mut s, "(defmacro my-let [v body] `(let [x# ~v] ~body))");
    let val = repl_eval(&mut s, "(let [x 100] (my-let 42 (add-i64 x 1)))");
    // x refers to outer binding (100), not the macro's x# (42).
    assert_eq!(val, 101, "auto-gensym should prevent capture: x should be 100, not 42");
}

// =============================================================================
// §9.9.4 Runtime error during expansion
// =============================================================================

// spec: 09-macros.md §9.9.4 — runtime error during expansion
// Moved to E2E test: e2e_s9_9_4_runtime_error_during_expansion
// Runtime errors (div-by-zero) cause SIGILL, so must test in subprocess.

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

// /expand neg coverage moved to E2E tests: e2e_s11_1_neg_expand_non_macro_unchanged

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

// /imports neg coverage moved to E2E tests: e2e_s3_4_imports_empty, e2e_s3_4_neg_imports_nonexistent_not_error

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

// spec: 09-macros.md §9.2 — macro body must return Sexp, not bare Int
// Negative test: a macro returning bare Int is a type error.
#[test]
fn r3_neg_macro_body_must_return_sexp() {
    let mut s = repl_session();
    let result = s.eval("(defmacro always-42 [x] 42)");
    assert!(
        result.is_err(),
        "macro body returning bare Int should be a type error"
    );
    if let Err(e) = result {
        let msg = e.message();
        assert!(
            msg.contains("Sexp") || msg.contains("type mismatch"),
            "error should mention Sexp type requirement, got: {msg}"
        );
    }
    // Session should still work after the error.
    let val = repl_eval(&mut s, "(add-i64 1 2)");
    assert_eq!(val, 3);
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
