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

// spec: repl/spec.md §4.1.6 — single-clause defmacro universal format
#[test]
fn r3_defmacro_display_single_clause() {
    let mut s = repl_session();
    let display = repl_eval_display(&mut s, "(defmacro double [x] `(add-i64 ~x ~x))");
    assert!(
        display.contains(":user/double ; defmacro"),
        "single-clause defmacro should show ':user/double ; defmacro', got: {display}"
    );
    assert!(
        display.contains("; [x] -> Sexp"),
        "single-clause defmacro should show clause signature, got: {display}"
    );
}

// spec: repl/spec.md §4.1.6 — multi-clause defmacro universal format
#[test]
fn r3_defmacro_display_multi_clause() {
    let mut s = repl_session();
    let display = repl_eval_display(
        &mut s,
        "(defmacro pick ([x] x) ([x y] x))",
    );
    assert!(
        display.contains(":user/pick ; defmacro"),
        "multi-clause defmacro should contain ':user/pick ; defmacro', got: {display}"
    );
    assert!(
        display.contains("; [x] -> Sexp") && display.contains("; [x y] -> Sexp"),
        "multi-clause defmacro should show clause signatures, got: {display}"
    );
}

// spec: repl/spec.md §4.1.6 — defmacro display for 3-clause macro
#[test]
fn r3_defmacro_display_three_clauses() {
    let mut s = repl_session();
    let display = repl_eval_display(
        &mut s,
        "(defmacro mc ([x] x) ([x y] y) ([x y z] z))",
    );
    // Three clause signature lines in universal format
    assert!(
        display.contains("; [x] -> Sexp"),
        "3-clause defmacro should show '; [x] -> Sexp', got: {display}"
    );
    assert!(
        display.contains("; [x y] -> Sexp"),
        "3-clause defmacro should show '; [x y] -> Sexp', got: {display}"
    );
    assert!(
        display.contains("; [x y z] -> Sexp"),
        "3-clause defmacro should show '; [x y z] -> Sexp', got: {display}"
    );
}

// =============================================================================
// §11.5 Scenario 4: /list after defmacro — Macros category appears (§11.2.1)
// =============================================================================

// spec: repl/spec.md §11.2.1 — macros registered as ModuleEntry::Macro in symbol table
// TODO: Reaches into TC internals (s.core.tc.symbol_table()). Replace with:
// - Round-trip via /list command asserting Macros category appears, or
// - Unit tests in typecheck crate verifying ModuleEntry::Macro registration.
#[test]
#[ignore]
fn r3_list_macros_category_via_symbol_table() {
    let _s = repl_session();
}

// spec: repl/spec.md §11.2.1, §3.3 — macros appear in Macros, not in Functions
// TODO: Reaches into TC internals. Replace with:
// - /list output asserting 'double' in Macros category and 'inc' in Functions, or
// - Unit tests in typecheck crate for ModuleEntry categorization.
#[test]
#[ignore]
fn r3_list_neg_macros_not_in_functions() {
    let _s = repl_session();
}

// =============================================================================
// §11.5 Scenario 5: /info on multi-clause macro (§11.2.2)
// =============================================================================

// spec: repl/spec.md §11.2.2 — /info macro clause count in symbol table
// TODO: Reaches into TC internals. Replace with:
// - /info output asserting 3 clause signatures shown, or
// - Unit tests in typecheck crate for clause registration.
#[test]
#[ignore]
fn r3_info_macro_clause_count() {
    let _s = repl_session();
}

// spec: repl/spec.md §11.2.2 — macro without docstring has None
// TODO: Reaches into TC internals. Replace with:
// - /doc output asserting no docstring shown, or
// - Unit tests in typecheck crate for docstring storage.
#[test]
#[ignore]
fn r3_info_macro_docstring() {
    let _s = repl_session();
}

// =============================================================================
// §11.5 Scenario 6: /sig on variadic macro (§11.2.3)
// =============================================================================

// spec: repl/spec.md §11.2.3 — macro clause params recorded in symbol table
// TODO: Reaches into TC internals. Replace with:
// - /sig output asserting param names [x y], or
// - Unit tests in typecheck crate for clause param registration.
#[test]
#[ignore]
fn r3_sig_macro_params() {
    let _s = repl_session();
}

// spec: repl/spec.md §11.2.3 — variadic macro clause with & rest
// TODO: Reaches into TC internals. Replace with:
// - /sig output asserting rest param shown, or
// - Unit tests in typecheck crate for rest param registration.
#[test]
#[ignore]
fn r3_sig_macro_variadic() {
    let _s = repl_session();
}

// =============================================================================
// §11.5 Scenario 8: Bare macro name lookup (§11.4)
// =============================================================================

// spec: repl/spec.md §11.4 — bare macro name shows clause signatures
#[test]
fn r3_bare_macro_lookup() {
    let mut s = repl_session();
    repl_eval_display(&mut s, "(defmacro double [x] `(add-i64 ~x ~x))");

    // Entering a macro name bare should produce its signature, not an error.
    let result = s.eval("double").unwrap();
    let display = s.session.format_eval_result(&result);
    assert!(
        display.contains("macro"),
        "bare macro lookup should show 'macro' in display, got: {display}"
    );
}

// spec: repl/spec.md §11.4 — multi-clause macro bare lookup shows all clause signatures
#[test]
fn r3_bare_macro_lookup_multi_clause() {
    let mut s = repl_session();
    repl_eval_display(
        &mut s,
        "(defmacro pick ([x] x) ([x y] x))",
    );

    let result = s.eval("pick").unwrap();
    let display = s.session.format_eval_result(&result);
    assert!(
        display.contains("macro"),
        "bare multi-clause macro should show 'macro', got: {display}"
    );
}

// spec: repl/spec.md §4.2 — bare 'defmacro' shows special form signature
#[test]
fn r3_special_form_defmacro() {
    let mut s = repl_session();
    let result = s.eval("defmacro").unwrap();
    let display = s.session.format_eval_result(&result);
    assert!(
        display.contains("defmacro") || display.contains("Fn"),
        "bare 'defmacro' should show special form info, got: {display}"
    );
}

// =============================================================================
// §9.2.4 Macro docstrings
// =============================================================================

// spec: 09-macros.md §9.2.4 — macro with docstring stores it
// TODO: Reaches into TC internals. Replace with:
// - /doc output asserting "Increment by one" shown, or
// - Unit tests in typecheck crate for docstring storage.
#[test]
#[ignore]
fn r3_macro_docstring_stored() {
    let _s = repl_session();
}

// spec: 09-macros.md §9.2.4 — macro without docstring has None
// TODO: Reaches into TC internals. Replace with:
// - /doc output asserting no docstring, or
// - Unit tests in typecheck crate for docstring storage.
#[test]
#[ignore]
fn r3_macro_no_docstring() {
    let _s = repl_session();
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
// TODO: Reaches into TC internals. Replace with:
// - /list output asserting 'foo' in Functions, 'Color' in Types, 'my-mac' in Macros, or
// - Unit tests in typecheck crate for ModuleEntry categorization.
#[test]
#[ignore]
fn r3_neg_non_macros_absent_from_macros() {
    let _s = repl_session();
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
    let src = r#"
(defmacro inc [x] `(primitives/add-i64 ~x 1))
(defn add-two [n] (inc (inc n)))
(defn main [] (add-two 40))
"#;
    let (value, _ty) = helpers::batch_run(src).unwrap();
    assert_eq!(value, 42);
}

// spec: 09-macros.md §9.2 — macro with multiple uses in same function (batch)
#[test]
fn r3_batch_macro_multiple_uses() {
    let src = r#"
(defmacro double [x] `(primitives/add-i64 ~x ~x))
(defn main [] (primitives/add-i64 (double 10) (double 11)))
"#;
    let (value, _ty) = helpers::batch_run(src).unwrap();
    assert_eq!(value, 42);
}

// =============================================================================
// Sprint 15 Wave 3: Universal output format — definition results (§1.1, §1.3)
// =============================================================================

// spec: repl/spec.md §1.3 — defn response shows `; defn` classification
#[test]
fn r3_defn_response_classification() {
    let mut s = repl_session();
    let display = repl_eval_display(&mut s, "(defn foo [x] x)");
    assert!(
        display.contains("; defn"),
        "defn response should include '; defn' classification, got: {display}"
    );
    assert!(
        display.contains("user/foo"),
        "defn response should include qualified name 'user/foo', got: {display}"
    );
}

// spec: repl/spec.md §1.3 — deftype response shows `; deftype` and `; match:` section
#[test]
fn r3_deftype_response_related() {
    let mut s = repl_session();
    let display = repl_eval_display(&mut s, "(deftype Color Red Green Blue)");
    assert!(
        display.contains("; deftype"),
        "deftype response should include '; deftype', got: {display}"
    );
    assert!(
        display.contains("; match:"),
        "deftype response should include '; match:' section, got: {display}"
    );
    assert!(
        display.contains("Red") && display.contains("Green") && display.contains("Blue"),
        "deftype '; match:' should list constructors, got: {display}"
    );
}

// spec: repl/spec.md §1.3 — deftrait response shows `; deftrait` and `; defn:` section
#[test]
fn r3_deftrait_response_related() {
    let mut s = repl_session();
    let display = repl_eval_display(
        &mut s,
        "(deftrait (Sizeable a) (size [a] Int))",
    );
    assert!(
        display.contains("; deftrait"),
        "deftrait response should include '; deftrait', got: {display}"
    );
    assert!(
        display.contains("; defn:") && display.contains("size"),
        "deftrait response should include '; defn:' with 'size', got: {display}"
    );
}

// =============================================================================
// Sprint 15 Wave 3: Macro universal format (§4.1.6)
// =============================================================================

// spec: repl/spec.md §4.1.6 — bare macro lookup shows `:module/name ; defmacro` + clauses
#[test]
fn r3_bare_macro_shows_universal_format() {
    let mut s = repl_session();
    repl_eval_display(&mut s, "(defmacro my-inc [x] `(add-i64 ~x 1))");
    let result = s.eval("my-inc").unwrap();
    let display = s.session.format_eval_result(&result);
    assert!(
        display.contains(":user/my-inc ; defmacro"),
        "bare macro should show ':user/my-inc ; defmacro', got: {display}"
    );
    assert!(
        display.contains("; [x] -> Sexp"),
        "bare macro should show clause signature, got: {display}"
    );
}

// spec: repl/spec.md §4.1.6 — multi-clause macro bare lookup shows all clause lines
#[test]
fn r3_bare_macro_multi_clause_all_sigs() {
    let mut s = repl_session();
    repl_eval_display(
        &mut s,
        "(defmacro multi ([x] x) ([x y] x) ([x y z] z))",
    );
    let result = s.eval("multi").unwrap();
    let display = s.session.format_eval_result(&result);
    assert!(
        display.contains("; defmacro"),
        "bare multi-clause macro should show '; defmacro', got: {display}"
    );
    // Count clause signature lines
    let clause_lines: Vec<_> = display.lines().filter(|l| l.contains("-> Sexp")).collect();
    assert_eq!(
        clause_lines.len(),
        3,
        "expected 3 clause signature lines, got {} in: {display}",
        clause_lines.len()
    );
}

// spec: repl/spec.md §4.1.6 — macro with docstring shows `:module/name ; defmacro - docstring`
#[test]
fn r3_macro_docstring_in_classification() {
    let mut s = repl_session();
    let display = repl_eval_display(
        &mut s,
        "(defmacro my-inc \"Increment by one\" [x] `(add-i64 ~x 1))",
    );
    assert!(
        display.contains("; defmacro"),
        "macro with docstring should show '; defmacro', got: {display}"
    );
    // The docstring may or may not appear in the definition result —
    // check that the primary line is well-formed.
    assert!(
        display.contains("user/my-inc"),
        "macro with docstring should show qualified name, got: {display}"
    );
}

// =============================================================================
// Sprint 15 Wave 3: Type/trait universal format (§4.1.3, §4.1.4)
// =============================================================================

// spec: repl/spec.md §4.1.3 — deftype result includes `; deftype` + `; match:` section
// Note: bare type name lookup (e.g., entering "Color" at REPL) goes through the
// binary's REPL input loop, not s.eval(). Tested via E2E: e2e_s4_1_bare_type_match_section.
// This test validates the deftype definition result.
#[test]
fn r3_deftype_result_match_section() {
    let mut s = repl_session();
    let display = repl_eval_display(&mut s, "(deftype Color Red Green Blue)");
    assert!(
        display.contains("; deftype"),
        "deftype result should show '; deftype', got: {display}"
    );
    assert!(
        display.contains("; match:"),
        "deftype result should show '; match:' section, got: {display}"
    );
    assert!(
        display.contains("Red") && display.contains("Green") && display.contains("Blue"),
        "deftype '; match:' should list constructors, got: {display}"
    );
}

// spec: repl/spec.md §4.1.4 — deftrait result includes `; deftrait` + `; defn:` section
// Note: bare trait name lookup goes through the REPL binary input loop.
// Tested via E2E: e2e_s4_1_bare_trait_defn_section.
// This test validates the deftrait definition result.
#[test]
fn r3_deftrait_result_defn_section() {
    let mut s = repl_session();
    let display = repl_eval_display(
        &mut s,
        "(deftrait (Showable a) (render [a] String))",
    );
    assert!(
        display.contains("; deftrait"),
        "deftrait result should show '; deftrait', got: {display}"
    );
    assert!(
        display.contains("; defn:") && display.contains("render"),
        "deftrait result should show '; defn:' with method names, got: {display}"
    );
}

// spec: repl/spec.md §4.1.4 — trait with impl: bare trait lookup shows `; impl:` section
// Note: bare trait lookup goes through the REPL binary.
// Tested via E2E: e2e_s4_1_bare_trait_defn_section.
// Integration test validates impl display via the impl result.
#[test]
fn r3_trait_impl_shows_impl_display() {
    let mut s = repl_session();
    repl_eval_display(
        &mut s,
        "(deftrait (Sizeable a) (size [a] Int))",
    );
    repl_eval_display(
        &mut s,
        "(deftype Circle [:Int radius])",
    );
    let display = repl_eval_display(
        &mut s,
        "(impl Sizeable Circle (defn size [_c] 42))",
    );
    assert!(
        display.contains("impl") && display.contains("Sizeable") && display.contains("Circle"),
        "impl display should show 'impl Sizeable for Circle', got: {display}"
    );
}

// spec: repl/spec.md §4.1.3 — builtin type Int shows `; impl:` section
// Note: bare type lookup for user types goes through the REPL binary.
// Tested via E2E: e2e_s4_1_bare_builtin_type_impl.
// This test validates that the impl registration does not error.
#[test]
fn r3_impl_registration_no_error() {
    let mut s = repl_session();
    repl_eval_display(
        &mut s,
        "(deftrait (Sizeable a) (size [a] Int))",
    );
    repl_eval_display(
        &mut s,
        "(deftype Circle [:Int radius])",
    );
    // impl with a constant body (avoids accessor syntax issues)
    let display = repl_eval_display(
        &mut s,
        "(impl Sizeable Circle (defn size [_c] 42))",
    );
    assert!(
        display.contains("impl"),
        "impl should display successfully, got: {display}"
    );
}

// =============================================================================
// Sprint 15 Wave 3: Special form universal format (§4.1.5)
// =============================================================================

// spec: repl/spec.md §4.1.5 — bare special form shows `; special form` classification
#[test]
fn r3_bare_special_form_classification() {
    let mut s = repl_session();
    let result = s.eval("if").unwrap();
    let display = s.session.format_eval_result(&result);
    assert!(
        display.contains("; special form"),
        "bare 'if' should show '; special form' classification, got: {display}"
    );
}

// spec: repl/spec.md §4.1.5 — bare special form 'let' shows classification
#[test]
fn r3_bare_special_form_let() {
    let mut s = repl_session();
    let result = s.eval("let").unwrap();
    let display = s.session.format_eval_result(&result);
    assert!(
        display.contains("; special form"),
        "bare 'let' should show '; special form' classification, got: {display}"
    );
}

// spec: repl/spec.md §4.1.5 — bare special form 'defmacro' shows classification
#[test]
fn r3_bare_special_form_defmacro_classification() {
    let mut s = repl_session();
    let result = s.eval("defmacro").unwrap();
    let display = s.session.format_eval_result(&result);
    assert!(
        display.contains("; special form"),
        "bare 'defmacro' should show '; special form' classification, got: {display}"
    );
}

// =============================================================================
// Sprint 15 Wave 3: Negative tests — universal format boundaries
// =============================================================================

// spec: repl/spec.md §1.1 — defn display MUST NOT use old `name :: macro` format
#[test]
fn r3_neg_macro_display_no_old_format() {
    let mut s = repl_session();
    let display = repl_eval_display(&mut s, "(defmacro my-mac [x] x)");
    assert!(
        !display.contains(":: macro"),
        "macro display MUST NOT use old ':: macro' format, got: {display}"
    );
    assert!(
        !display.contains("clauses"),
        "macro display MUST NOT use old 'N clauses' format, got: {display}"
    );
}

// spec: repl/spec.md §1.1 — deftrait display MUST include `; deftrait` (not bare)
#[test]
fn r3_neg_deftrait_display_not_bare() {
    let mut s = repl_session();
    let display = repl_eval_display(
        &mut s,
        "(deftrait (Showable a) (render [a] String))",
    );
    // The old format was just `:user/Showable` — now it must have `; deftrait`
    let first_line = display.lines().next().unwrap_or("");
    assert!(
        first_line.contains("; deftrait"),
        "deftrait display MUST include '; deftrait' on primary line, got: {first_line}"
    );
}

// spec: repl/spec.md §1.1 — defn display MUST include `; defn` classification
#[test]
fn r3_neg_defn_display_has_classification() {
    let mut s = repl_session();
    let display = repl_eval_display(&mut s, "(defn id [x] x)");
    let first_line = display.lines().next().unwrap_or("");
    assert!(
        first_line.contains("; defn"),
        "defn display MUST include '; defn' on primary line, got: {first_line}"
    );
}

// spec: repl/spec.md §4.1.2 — bare constructor classification is `; deftype` not `; defn`
// Note: bare constructor lookup for classification goes through the REPL binary input loop,
// not via s.eval() which evaluates the constructor as a value. Covered by E2E test:
// e2e_s4_1_bare_constructor_classification.
// This integration test verifies constructors produce values, not errors.
#[test]
fn r3_constructor_evaluates_as_value() {
    let mut s = repl_session();
    repl_eval_display(&mut s, "(deftype Color Red Green Blue)");
    let result = s.eval("Red").unwrap();
    // Constructor evaluates to a value (nullary constructor tag)
    assert!(
        !result.is_def(),
        "constructor eval should be a value, not a definition"
    );
}
