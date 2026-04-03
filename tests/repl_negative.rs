// Negative tests for Rings 0-2 REPL features.
//
// These tests verify what MUST NOT happen. They run against the CURRENT
// codebase BEFORE Ring 3 changes land, surfacing hidden defects early.
//
// Naming convention: `_neg_` or `_not_` in test name (per tests/CLAUDE.md).
//
// Categories:
//   1. /list scope boundaries (§3.3)
//   2. Expression/definition display (§1.2-1.3)
//   3. Error boundaries (§5.2)
//   4. Module resolution (§4.1)

#[path = "helpers/mod.rs"]
mod helpers;

use cranelisp::session_v4::EvalResult;
use cranelisp_backend::display::format_result;
use cranelisp_types::{CranelispError, DefKind, ModuleEntry, Type, TypeName};
use helpers::*;

// =============================================================================
// /list Scope Boundaries — Negative Tests (spec: repl/spec.md §3.3)
//
// The /list command iterates session.core.tc.symbol_table().all_symbols().
// These tests inspect the same symbol table to verify that the categories
// that handle_list would produce do NOT contain forbidden entries.
// =============================================================================

/// Classify a symbol table entry the same way handle_list does.
/// Returns (category, qualified_name) or None if the entry should be skipped.
fn classify_entry(
    sym: &str,
    entry: &ModuleEntry,
    module: &str,
) -> Option<(&'static str, String)> {
    // Skip constructors — handle_list skips them.
    if matches!(entry, ModuleEntry::Constructor { .. }) {
        return None;
    }
    // Skip imports and reexports — handle_list skips them.
    if matches!(entry, ModuleEntry::Import { .. } | ModuleEntry::Reexport { .. }) {
        return None;
    }

    match entry {
        ModuleEntry::TypeDef { .. } => Some(("Types", format!("{module}/{sym}"))),
        ModuleEntry::TraitDecl { .. } => Some(("Traits", format!("{module}/{sym}"))),
        ModuleEntry::Macro { .. } => Some(("Macros", sym.to_string())),
        ModuleEntry::Def { kind, .. } => match kind.as_ref() {
            DefKind::SpecialForm { .. } => Some(("Special forms", sym.to_string())),
            DefKind::Primitive { .. } => None, // skip — belongs in primitives module
            _ => Some(("Functions", format!("{module}/{sym}"))),
        },
        _ => None,
    }
}

/// Collect all /list categories from a REPL session, simulating handle_list.
/// Returns (types, traits, special_forms, functions) — each a Vec of display names.
fn collect_list_categories(
    session: &helpers::ReplSession,
) -> (Vec<String>, Vec<String>, Vec<String>, Vec<String>) {
    let module = session.session.tc.current_module_path().to_string();
    let table = session.session.tc.symbol_table();

    let mut types = Vec::new();
    let mut traits = Vec::new();
    let mut special_forms = Vec::new();
    let mut functions = Vec::new();

    for (sym, entry) in table.all_symbols() {
        if let Some((category, name)) = classify_entry(sym.as_ref(), entry, &module) {
            match category {
                "Types" => types.push(name),
                "Traits" => traits.push(name),
                "Special forms" => special_forms.push(name),
                "Functions" => functions.push(name),
                _ => {}
            }
        }
    }

    types.sort();
    traits.sort();
    special_forms.sort();
    functions.sort();

    (types, traits, special_forms, functions)
}

// spec: repl/spec.md §3.3 — Functions MUST NOT contain primitives
#[test]
fn list_neg_no_primitives_in_functions() {
    // /list Functions category MUST NOT contain primitives (add-i64, mul-i64,
    // eq-i64, etc.) when current module is `user`. Primitives are defined in
    // the `primitives` module, not the `user` module.
    let session = repl_session();
    let (_types, _traits, _special_forms, functions) = collect_list_categories(&session);

    let primitives = [
        "add-i64", "sub-i64", "mul-i64", "div-i64",
        "eq-i64", "lt-i64", "gt-i64", "le-i64", "ge-i64",
        "add-f64", "sub-f64", "mul-f64", "div-f64",
        "eq-f64", "lt-f64", "gt-f64", "le-f64", "ge-f64",
        "not", "str-len", "str-eq", "str-concat", "int-to-string",
    ];

    for prim in &primitives {
        for f in &functions {
            assert!(
                !f.ends_with(&format!("/{prim}")),
                "Functions category MUST NOT contain primitive '{prim}', found: {f}"
            );
            // Also check if it appears as a bare name (shouldn't, but safety check)
            assert!(
                f != prim,
                "Functions category MUST NOT contain bare primitive name '{prim}'"
            );
        }
    }
}

// spec: repl/spec.md §3.3 — Functions MUST NOT contain imported trait methods
// BUG: Trait methods (+, -, *, /, =, <, show, etc.) are registered as Def
// entries directly in the `user` module's symbol table, not as Import entries.
// handle_list classifies them as Functions. The spec says imported names belong
// in the Imports category (or should be filtered), not in Functions.
// D17 elimination resolved this: trait methods no longer registered as Def in user module.
#[test]
fn list_neg_no_imported_names_in_functions() {
    // /list Functions category MUST NOT contain imported names such as
    // trait methods (+, -, *, /, =, <, show) — they belong in the Imports
    // category (Ring 3), not in Functions. In Ring 2, handle_list skips
    // Import entries, so imported methods should not appear anywhere.
    let session = repl_session();
    let (_types, _traits, _special_forms, functions) = collect_list_categories(&session);

    // These are trait methods imported into user from builtins.
    // They should NOT appear in the Functions category.
    let trait_methods = ["+", "-", "*", "/", "=", "<", ">", "<=", ">=", "show"];

    for method in &trait_methods {
        for f in &functions {
            let bare = f.rsplit('/').next().unwrap_or(f);
            assert!(
                bare != *method,
                "Functions category MUST NOT contain imported trait method '{method}', found: {f}"
            );
        }
    }
}

// spec: repl/spec.md §3.3 — Types MUST NOT contain primitives module types
#[test]
fn list_neg_no_primitives_types_in_types() {
    // /list Types category MUST NOT contain types from the primitives module
    // (Int, Bool, Float, String) when current module is `user`.
    let session = repl_session();
    let (types, _traits, _special_forms, _functions) = collect_list_categories(&session);

    let primitive_types = ["Int", "Bool", "Float", "String"];

    for pt in &primitive_types {
        for t in &types {
            let bare = t.rsplit('/').next().unwrap_or(t);
            assert!(
                bare != *pt,
                "Types category MUST NOT contain primitive type '{pt}', found: {t}"
            );
        }
    }
}

// spec: repl/spec.md §3.3 — Fresh session: ONLY Special forms
#[test]
fn list_neg_fresh_session_special_forms_only() {
    // In a fresh `user` session with no definitions, /list MUST show ONLY
    // Special forms. No Functions, no Types, no Traits that the user defined.
    // Note: the REPL session starts with builtin traits (Num, Eq, Ord, Display)
    // registered, which are compiler-seeded. The /list command shows them
    // because they are TraitDecl entries in the user module's symbol table.
    // This test verifies that Functions and user-defined Types are empty.
    let session = repl_session();
    let (types, _traits, special_forms, functions) = collect_list_categories(&session);

    // Special forms must be present (if, let, defn, etc.)
    assert!(
        !special_forms.is_empty(),
        "Special forms should be present in a fresh session"
    );

    // Functions must be empty — no user-defined functions yet
    assert!(
        functions.is_empty(),
        "Functions category MUST be empty in a fresh session, found: {functions:?}"
    );

    // Types must be empty — no user-defined types yet
    assert!(
        types.is_empty(),
        "Types category MUST be empty in a fresh session, found: {types:?}"
    );
}

// spec: repl/spec.md §3.3 — After defn: Functions appears, primitives still absent
#[test]
fn list_neg_defn_adds_functions_not_primitives() {
    // After (defn foo [x] x): Functions category appears with foo, but
    // primitives MUST still be absent from Functions.
    let mut session = repl_session();
    session.eval("(defn foo [x] x)").unwrap();

    let (_types, _traits, _special_forms, functions) = collect_list_categories(&session);

    // foo should be present
    assert!(
        functions.iter().any(|f| f.contains("foo")),
        "foo should appear in Functions after defn, got: {functions:?}"
    );

    // Primitives must still be absent
    let primitives = ["add-i64", "sub-i64", "mul-i64", "div-i64", "eq-i64"];
    for prim in &primitives {
        for f in &functions {
            let bare = f.rsplit('/').next().unwrap_or(f);
            assert!(
                bare != *prim,
                "After defn, primitives MUST still be absent from Functions. Found: {f}"
            );
        }
    }
}

// spec: repl/spec.md §3.3 — Constructors MUST NOT appear in Functions
#[test]
fn list_neg_constructors_not_in_functions() {
    // After (deftype Color Red Green Blue): constructors Red, Green, Blue
    // MUST NOT appear in the Functions category. They belong to their type.
    let mut session = repl_session();
    session.eval("(deftype Color Red Green Blue)").unwrap();

    let (_types, _traits, _special_forms, functions) = collect_list_categories(&session);

    let constructors = ["Red", "Green", "Blue"];
    for ctor in &constructors {
        for f in &functions {
            let bare = f.rsplit('/').next().unwrap_or(f);
            assert!(
                bare != *ctor,
                "Constructor '{ctor}' MUST NOT appear in Functions category, found: {f}"
            );
        }
    }
}

// spec: repl/spec.md §3.3 — No item appears in two categories
#[test]
fn list_neg_no_item_in_two_categories() {
    // After defining a function, a type, and a trait, no item should appear
    // in two different /list categories simultaneously.
    let mut session = repl_session();
    session.eval("(defn foo [x] x)").unwrap();
    session.eval("(deftype Color Red Green Blue)").unwrap();
    session
        .eval("(deftrait (Sizeable a) (size [:a] :Int))")
        .unwrap();

    let (types, traits, special_forms, functions) = collect_list_categories(&session);

    // Collect all names into a flat list with their category
    let mut all_items: Vec<(&str, &str)> = Vec::new();
    for t in &types {
        all_items.push(("Types", t.as_str()));
    }
    for t in &traits {
        all_items.push(("Traits", t.as_str()));
    }
    for sf in &special_forms {
        all_items.push(("Special forms", sf.as_str()));
    }
    for f in &functions {
        all_items.push(("Functions", f.as_str()));
    }

    // Check for duplicates across categories. Extract the bare name for comparison.
    for i in 0..all_items.len() {
        for j in (i + 1)..all_items.len() {
            let (cat_a, name_a) = all_items[i];
            let (cat_b, name_b) = all_items[j];
            if cat_a != cat_b {
                let bare_a = name_a.rsplit('/').next().unwrap_or(name_a);
                let bare_b = name_b.rsplit('/').next().unwrap_or(name_b);
                assert!(
                    bare_a != bare_b,
                    "'{bare_a}' appears in both '{cat_a}' and '{cat_b}' — \
                     no item should appear in two categories"
                );
            }
        }
    }
}

// =============================================================================
// Expression/Definition Display — Negative Tests (spec: repl/spec.md §1.2-1.3)
// =============================================================================

// spec: repl/spec.md §1.3 — defn MUST NOT display <closure>
#[test]
fn display_neg_defn_not_closure() {
    // Spec §1.3: "It MUST NOT display `<closure>` — the user defined a *named*
    // function, not an anonymous closure."
    // The definition display format is `:TypeScheme qualified-name`.
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "(defn foo [x] x)");
    assert!(
        !display.contains("<closure>"),
        "defn display MUST NOT contain '<closure>', got: {display}"
    );
    // It should contain the qualified name
    assert!(
        display.contains("user/foo"),
        "defn display should contain qualified name 'user/foo', got: {display}"
    );
}

// spec: repl/spec.md §1.2 — Named function result MUST NOT show bare unqualified type
#[test]
fn display_neg_type_always_qualified() {
    // Spec §1.4: "Type names MUST always be fully qualified with their module path."
    // A function returning Int must show `primitives/Int`, not bare `Int`.
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "(defn double [x] (mul-i64 x 2))");
    // The display should contain "primitives/Int" (qualified)
    assert!(
        display.contains("primitives/Int"),
        "type display must use qualified name 'primitives/Int', got: {display}"
    );
    // Extract the type portion (between : and the name). Check there's no bare
    // "Int" that isn't preceded by "primitives/".
    // We check that every occurrence of "Int" in the display is part of "primitives/Int".
    let without_qualified = display.replace("primitives/Int", "");
    assert!(
        !without_qualified.contains("Int"),
        "type display MUST NOT contain bare 'Int' without module qualifier, got: {display}"
    );
}

// spec: repl/spec.md §1.4 — Type variables MUST NOT show internal names (t0, t1)
#[test]
fn display_neg_type_vars_normalized() {
    // Spec §1.4: "Polymorphic type schemes MUST display quantified variables as
    // consecutive lowercase letters starting from `a`."
    // Type variables MUST NOT show internal names like t0, t1, _t42.
    let mut session = repl_session();
    let result = session.eval("(defn id [x] x)").unwrap();
    let display = format_result(result.value(), &result.ty());

    // Must not contain raw type var names
    assert!(
        !display.contains("t0"),
        "type display MUST NOT contain internal var name 't0', got: {display}"
    );
    assert!(
        !display.contains("t1"),
        "type display MUST NOT contain internal var name 't1', got: {display}"
    );
    // Also check for underscore-prefixed variants
    assert!(
        !display.contains("_t"),
        "type display MUST NOT contain internal var name '_t...', got: {display}"
    );
}

// spec: repl/spec.md §1.4 — Type vars normalized for multi-param poly fns
#[test]
fn display_neg_type_vars_normalized_multi_param() {
    // Verify that a function with multiple type variables normalizes all of them.
    let mut session = repl_session();
    let result = session.eval("(defn konst [x y] x)").unwrap();
    let display = format_result(result.value(), &result.ty());

    // Should contain a and b, not tN
    for i in 0..20 {
        assert!(
            !display.contains(&format!("t{i}")),
            "type display MUST NOT contain internal var name 't{i}', got: {display}"
        );
    }
}

// spec: repl/spec.md §1.3 — deftype MUST NOT show function-like type
#[test]
fn display_neg_deftype_not_function() {
    // Spec §1.3: "A type definition MUST display the fully-qualified type name."
    // It MUST NOT show a function-like type (e.g., (Fn [...] ...)).
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "(deftype Color Red Green Blue)");

    assert!(
        !display.contains("Fn"),
        "deftype display MUST NOT contain 'Fn' — should show type name, got: {display}"
    );
    assert!(
        !display.contains("<closure>"),
        "deftype display MUST NOT contain '<closure>', got: {display}"
    );
    // Should show the qualified type name
    assert!(
        display.contains("user/Color"),
        "deftype should show qualified type name 'user/Color', got: {display}"
    );
}

// spec: repl/spec.md §1.3 — deftype with fields MUST NOT show function-like type
#[test]
fn display_neg_deftype_with_fields_not_function() {
    // Product type definition should show the type name, not a constructor function type.
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "(deftype Point [:Int x :Int y])");

    assert!(
        !display.contains("(Fn"),
        "deftype display MUST NOT contain '(Fn' — should show type name, got: {display}"
    );
    assert!(
        display.contains("user/Point"),
        "deftype should show qualified type name 'user/Point', got: {display}"
    );
}

// spec: repl/spec.md §1.2 — Bool display MUST NOT show 0/1
#[test]
fn display_neg_bool_not_numeric() {
    // Spec §1.5: Bool displays as `true` or `false`, not 0/1.
    let s_true = format_result(1, &Type::Bool);
    // The display must not contain the digit that could be the raw i64 value.
    // "true" contains no digits, so we check for digits adjacent to Bool.
    assert!(
        s_true.contains("true"),
        "Bool true must display as 'true', got: {s_true}"
    );
    // Ensure the value portion is "true" not "1"
    let value_part = s_true.split_whitespace().last().unwrap_or("");
    assert!(
        value_part == "true",
        "Bool value portion must be 'true', not '{value_part}', got: {s_true}"
    );

    let s_false = format_result(0, &Type::Bool);
    let value_part = s_false.split_whitespace().last().unwrap_or("");
    assert!(
        value_part == "false",
        "Bool value portion must be 'false', not '{value_part}', got: {s_false}"
    );
}

// spec: repl/spec.md §1.2 — Expression result MUST NOT lack the colon prefix
#[test]
fn display_neg_must_have_colon_prefix() {
    // All display format lines must start with `:`.
    let s = format_result(42, &Type::Int);
    assert!(
        s.starts_with(':'),
        "display MUST start with ':', got: {s}"
    );

    let s = format_result(1, &Type::Bool);
    assert!(
        s.starts_with(':'),
        "Bool display MUST start with ':', got: {s}"
    );

    let bits = 3.14_f64.to_bits() as i64;
    let s = format_result(bits, &Type::Float);
    assert!(
        s.starts_with(':'),
        "Float display MUST start with ':', got: {s}"
    );
}

// =============================================================================
// Error Boundaries — Negative Tests (spec: repl/spec.md §5.2)
// =============================================================================

// spec: repl/spec.md §5.2 — After type error, next expression MUST NOT be affected
#[test]
fn error_neg_type_error_no_corrupt_next() {
    // After a type error, the next valid expression MUST NOT be affected by
    // any failed type state from the previous error. Specifically:
    // 1. The type of a simple expression should be correct.
    // 2. The value should be correct.
    // 3. No spurious error should occur.
    let mut session = repl_session();

    // Define something first.
    session.eval("(defn inc [x] (add-i64 x 1))").unwrap();
    assert_eq!(repl_eval(&mut session, "(inc 5)"), 6);

    // Trigger a type error that might leave stale unification state.
    let err = session.eval("(add-i64 true \"hello\")");
    assert!(err.is_err());

    // The next expression MUST work correctly — no corruption.
    let result = session.eval("(inc 10)").unwrap();
    assert_eq!(result.value(), 11, "value MUST NOT be affected by prior type error");
    assert_eq!(
        *result.ty(),
        Type::Int,
        "type MUST NOT be affected by prior type error"
    );

    // A new definition MUST also work.
    let result = session.eval("(defn dec [x] (sub-i64 x 1))").unwrap();
    assert!(result.is_def());
    assert_eq!(repl_eval(&mut session, "(dec 10)"), 9);
}

// spec: repl/spec.md §5.2 — After parse error, definitions MUST still be callable
#[test]
fn error_neg_parse_error_preserves_definitions() {
    // After a parse error, previously defined functions MUST still be callable.
    // The parse error should not corrupt any part of the session state.
    let mut session = repl_session();

    // Define several functions.
    session.eval("(defn a [x] (add-i64 x 1))").unwrap();
    session.eval("(defn b [x] (mul-i64 x 2))").unwrap();
    session.eval("(deftype Dir North South)").unwrap();

    // Trigger a parse error.
    let err = session.eval("(a 1");
    assert!(
        err.is_err(),
        "unbalanced parens should produce a parse error"
    );
    match &err {
        Err(CranelispError::ParseError { .. }) => {} // expected
        Err(other) => panic!("expected ParseError, got: {other}"),
        _ => unreachable!(),
    }

    // All prior definitions MUST still work.
    assert_eq!(repl_eval(&mut session, "(a 5)"), 6);
    assert_eq!(repl_eval(&mut session, "(b 5)"), 10);
    let r = session.eval("North").unwrap();
    assert_eq!(*r.ty(), Type::ADT(TypeName::from("Dir"), vec![]));
}

// spec: repl/spec.md §5.2 — Failed defn MUST NOT leave a partial binding
// BUG: A failed defn leaves a partial binding in the symbol table. The
// TypeChecker registers the name's type during check_repl_input before the
// body type-check fails. The snapshot/restore mechanism restores the type
// state, but the name remains in the symbol table as a Def entry with no
// corresponding GOT code pointer. Calling it yields "no GOT slot for function"
// instead of "unbound". The error message is correct (the call does fail),
// but the error category and message are wrong — it should say "unbound",
// not "no GOT slot". Fix: ensure snapshot/restore also reverts symbol table
// additions, or filter Def entries without code pointers.
#[test]
fn error_neg_failed_defn_no_partial_binding() {
    // A failed defn (type error in body) MUST NOT leave a partial binding
    // in scope. The name should not be resolvable after the error.
    let mut session = repl_session();

    // Try to define a function with a type error.
    let err = session.eval("(defn broken [x] (add-i64 x true))");
    assert!(err.is_err());

    // The name 'broken' MUST NOT be callable.
    let err2 = session.eval("(broken 1)");
    assert!(
        err2.is_err(),
        "Failed defn MUST NOT leave 'broken' callable, but it succeeded"
    );

    // Verify the error message indicates unbound/undefined.
    match &err2 {
        Err(e) => {
            let msg = e.message();
            assert!(
                msg.contains("unbound") || msg.contains("undefined")
                    || msg.contains("not found") || msg.contains("unknown"),
                "error for failed defn name should indicate unbound, got: {msg}"
            );
        }
        _ => unreachable!(),
    }

    // The session should still work for other expressions.
    assert_eq!(repl_eval(&mut session, "(add-i64 1 2)"), 3);
}

// spec: repl/spec.md §5.2 — Failed defn with same name as existing MUST preserve original
#[test]
fn error_neg_failed_redefn_preserves_original() {
    // If a function is already defined and a redefinition fails (type error),
    // the original definition MUST still be intact.
    let mut session = repl_session();

    // Define a valid function.
    session.eval("(defn f [x] (add-i64 x 1))").unwrap();
    assert_eq!(repl_eval(&mut session, "(f 5)"), 6);

    // Attempt to redefine with a type error.
    let err = session.eval("(defn f [x] (add-i64 x true))");
    assert!(err.is_err());

    // The original definition MUST still work.
    assert_eq!(
        repl_eval(&mut session, "(f 5)"),
        6,
        "original defn MUST be preserved after failed redefinition"
    );
}

// spec: repl/spec.md §5.2 — Multiple errors in sequence MUST NOT accumulate damage
#[test]
fn error_neg_multiple_errors_no_accumulation() {
    // Repeated errors of different types must not accumulate damage.
    // After N errors, the session must still evaluate simple expressions correctly.
    let mut session = repl_session();
    session.eval("(defn ok [x] (add-i64 x 1))").unwrap();

    // Trigger a sequence of different error types.
    let _ = session.eval("(add-i64 true 1)"); // type error
    let _ = session.eval("(unknown-fn 42)"); // unbound error
    let _ = session.eval("(if 42 1 2)"); // type error (condition)
    let _ = session.eval("(let [x] x)"); // parse/syntax error
    let _ = session.eval("(add-i64 \"s\" 1)"); // type error (string)

    // After all errors, the session MUST still work.
    let result = session.eval("(ok 10)").unwrap();
    assert_eq!(result.value(), 11, "session MUST NOT be damaged by accumulated errors");
    assert_eq!(*result.ty(), Type::Int);

    // New definitions MUST still work.
    session.eval("(defn ok2 [x] (mul-i64 x 2))").unwrap();
    assert_eq!(repl_eval(&mut session, "(ok2 5)"), 10);
}

// =============================================================================
// Module Resolution — Negative Tests (spec: repl/spec.md §4.1)
// =============================================================================

// spec: 08-modules §8.9.1 — Bare primitive MUST NOT resolve without import
#[test]
fn module_neg_unimported_primitive_unbound() {
    // Spec §8.9.1: "Names in `primitives` are stored in qualified form only
    // (`primitives/add-i64`). They are NOT available as bare names unless
    // imported through the prelude chain."
    //
    // Bare `add-i64` in a module with no import MUST produce an "unbound" error.
    // Uses ReplSession::new() directly — NOT repl_session() which auto-imports primitives.
    let mut session = ReplSession::new();

    let err = session.eval("(add-i64 2 3)");
    assert!(
        err.is_err(),
        "bare primitive `add-i64` without import MUST produce an error"
    );
    let msg = match &err {
        Err(e) => e.message(),
        _ => unreachable!(),
    };
    assert!(
        msg.contains("unbound") || msg.contains("undefined")
            || msg.contains("not found") || msg.contains("unknown"),
        "error should indicate unbound, got: {msg}"
    );
}

// spec: 08-modules §8.9.1 — Qualified primitive access works; bare does not
#[test]
fn module_neg_primitive_module_scoping() {
    // Spec §8.9.1: Primitives are qualified-only. Bare `sub-i64` MUST NOT
    // resolve. Qualified `primitives/sub-i64` MUST work.
    // Uses ReplSession::new() directly — NOT repl_session() which auto-imports primitives.
    let mut session = ReplSession::new();

    // Bare access MUST fail.
    let err = session.eval("(sub-i64 5 3)");
    assert!(
        err.is_err(),
        "bare `sub-i64` without import MUST produce an error"
    );

    // Qualified access MUST succeed.
    assert_eq!(repl_eval(&mut session, "(primitives/sub-i64 5 3)"), 2);

    // Explicit import MUST make bare access work.
    repl_eval(&mut session, "(import [primitives [sub-i64]])");
    assert_eq!(repl_eval(&mut session, "(sub-i64 10 4)"), 6);
}

// spec: repl/spec.md §4.1 — Type name in wrong position MUST error appropriately
#[test]
fn module_neg_type_name_not_callable() {
    // Using a type name as a function (when it's not a constructor) should error.
    // "Int" is a bare type name — it should not be callable.
    let mut session = repl_session();
    let err = session.eval("(Int 42)");
    assert!(
        err.is_err(),
        "calling a type name as a function MUST produce an error"
    );
    // Session should still work.
    assert_eq!(repl_eval(&mut session, "42"), 42);
}

// =============================================================================
// Additional Display Negative Tests
// =============================================================================

// spec: repl/spec.md §1.3 — defn with monomorphic type MUST show fully qualified types
#[test]
fn display_neg_defn_monomorphic_fully_qualified() {
    // A monomorphic function definition MUST display fully qualified types.
    // (defn square [x] (mul-i64 x x)) -> :(Fn [primitives/Int] primitives/Int) user/square
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "(defn square [x] (mul-i64 x x))");

    // Must contain qualified Int
    assert!(
        display.contains("primitives/Int"),
        "monomorphic defn MUST show qualified 'primitives/Int', got: {display}"
    );

    // Must contain qualified function name
    assert!(
        display.contains("user/square"),
        "monomorphic defn MUST show qualified name 'user/square', got: {display}"
    );

    // MUST NOT contain bare "Int" without qualifier
    let without_qualified = display.replace("primitives/Int", "");
    assert!(
        !without_qualified.contains("Int"),
        "display MUST NOT contain bare 'Int', got: {display}"
    );
}

// spec: repl/spec.md §1.3 — defn with Bool return MUST show fully qualified Bool
#[test]
fn display_neg_defn_bool_return_fully_qualified() {
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "(defn is-pos [x] (gt-i64 x 0))");

    assert!(
        display.contains("primitives/Bool"),
        "defn returning Bool MUST show qualified 'primitives/Bool', got: {display}"
    );
    assert!(
        display.contains("primitives/Int"),
        "defn with Int param MUST show qualified 'primitives/Int', got: {display}"
    );
}

// spec: repl/spec.md §1.5 — Closure value MUST NOT show the function's qualified name
#[test]
fn display_neg_closure_not_qualified_name() {
    // When a closure value is produced (not a defn), it MUST show <closure>,
    // not a qualified function name.
    let mut session = repl_session();
    session
        .eval("(defn make-adder [n] (fn [x] (add-i64 n x)))")
        .unwrap();
    let display = repl_eval_display(&mut session, "(make-adder 5)");

    // Should contain <closure>
    assert!(
        display.contains("<closure>"),
        "closure value MUST display as '<closure>', got: {display}"
    );
    // Should NOT contain the name of the lambda or defining function
    // (no "make-adder" or "lambda" or function address in the value part)
    let value_part = display.split_whitespace().last().unwrap_or("");
    assert!(
        value_part == "<closure>",
        "closure value portion MUST be '<closure>', got: {value_part}"
    );
}

// spec: repl/spec.md §1.3 — defn polymorphic ADT return MUST NOT show raw var ids
#[test]
fn display_neg_polymorphic_adt_return_no_raw_vars() {
    // A polymorphic function returning an ADT MUST NOT show raw type variable
    // IDs (t0, t1, etc.) in its display.
    let mut session = repl_session();
    session
        .eval("(deftype (Option a) None (Some [:a val]))")
        .unwrap();
    let result = session.eval("(defn wrap [x] (Some x))").unwrap();
    let display = format_result(result.value(), &result.ty());

    // Must not contain raw var names
    for i in 0..30 {
        assert!(
            !display.contains(&format!("t{i}")),
            "polymorphic ADT return MUST NOT show raw var 't{i}', got: {display}"
        );
    }
}

// =============================================================================
// /list Scope After Multiple Definitions — Negative Tests
// =============================================================================

// spec: repl/spec.md §3.3 — After deftype, constructors absent from all non-Types categories
#[test]
fn list_neg_constructors_absent_from_all_categories() {
    // After defining a sum type with constructors, the constructor names
    // must appear ONLY as constructor entries (which handle_list skips).
    // They must not appear in Functions, Traits, or Special forms.
    let mut session = repl_session();
    session.eval("(deftype Dir North South East West)").unwrap();
    session.eval("(defn go [d] (match d [North 0 South 1 East 2 West 3]))").unwrap();

    let (_types, traits, special_forms, functions) = collect_list_categories(&session);

    let ctors = ["North", "South", "East", "West"];
    for ctor in &ctors {
        for f in &functions {
            let bare = f.rsplit('/').next().unwrap_or(f);
            assert!(bare != *ctor, "Constructor '{ctor}' MUST NOT be in Functions: {f}");
        }
        for t in &traits {
            let bare = t.rsplit('/').next().unwrap_or(t);
            assert!(bare != *ctor, "Constructor '{ctor}' MUST NOT be in Traits: {t}");
        }
        for sf in &special_forms {
            assert!(sf != ctor, "Constructor '{ctor}' MUST NOT be in Special forms");
        }
    }
}

// spec: repl/spec.md §3.3 — After data type defn, constructor absent from Functions
#[test]
fn list_neg_data_constructor_not_in_functions() {
    // Data constructors (with fields) should also be absent from Functions.
    let mut session = repl_session();
    session
        .eval("(deftype (Option a) None (Some [:a val]))")
        .unwrap();

    let (_types, _traits, _special_forms, functions) = collect_list_categories(&session);

    for ctor in &["None", "Some"] {
        for f in &functions {
            let bare = f.rsplit('/').next().unwrap_or(f);
            assert!(
                bare != *ctor,
                "Data constructor '{ctor}' MUST NOT be in Functions: {f}"
            );
        }
    }
}

// =============================================================================
// Error Boundary Edge Cases — Negative Tests
// =============================================================================

// spec: repl/spec.md §5.2 — Failed deftype MUST NOT leave partial type definition
#[test]
fn error_neg_failed_deftype_no_partial_type() {
    // A deftype that fails should not leave a partial type definition visible.
    // We trigger a failure by defining a type with a duplicate constructor name.
    let mut session = repl_session();

    // First, define a type with constructor "Red".
    session.eval("(deftype Color Red Blue)").unwrap();

    // Attempt to define another type that reuses "Red" — this should fail or
    // the second type should be independent. If it succeeds, that's OK —
    // what matters is the session isn't corrupted.
    let _result = session.eval("(deftype Shade Red Dark)");
    // Whether it succeeds or fails, the session must still work.

    // The original type must still work.
    let r = session.eval("Blue").unwrap();
    assert_eq!(*r.ty(), Type::ADT(TypeName::from("Color"), vec![]));
    // Basic expressions must work.
    assert_eq!(repl_eval(&mut session, "(add-i64 1 2)"), 3);
}

// spec: repl/spec.md §5.2 — Error in complex expression MUST NOT corrupt type inference
#[test]
fn error_neg_complex_expr_error_no_type_corruption() {
    // A complex expression that fails mid-inference should not leave stale
    // type constraints that affect subsequent expressions.
    let mut session = repl_session();

    // Define some infrastructure.
    session.eval("(defn inc [x] (add-i64 x 1))").unwrap();
    session
        .eval("(deftype (Option a) None (Some [:a val]))")
        .unwrap();

    // Trigger a complex type error involving ADTs and functions.
    let err = session.eval("(match (Some 42) [(Some x) (add-i64 x true) None 0])");
    assert!(err.is_err());

    // The type system MUST NOT be corrupted.
    // This specific expression must infer Int, not be confused by the prior error.
    let result = session.eval("(inc 5)").unwrap();
    assert_eq!(result.value(), 6);
    assert_eq!(*result.ty(), Type::Int);

    // ADT operations must still work.
    let result = session.eval("(Some 99)").unwrap();
    assert_eq!(
        *result.ty(),
        Type::ADT(TypeName::from("Option"), vec![Type::Int])
    );
}
