//! Per-submodule tests for `program/support.rs` — the `self`-less toolbox:
//! child enumeration, subst walkers, AST-annotation writers, name manglers and
//! the macro-clause predicates. Split from the pooled `program/tests.rs`
//! (FIXME 0722).

use super::*;



#[test]
fn macro_clause_defn_name_is_recognised() {
    assert!(is_macro_clause_defn_name("__macro_m_clause_0"));
    assert!(is_macro_clause_defn_name("__macro_make-def-name_clause_3"));
    // Not a macro-clause shape: ordinary user defns, REPL exprs, trait impls.
    assert!(!is_macro_clause_defn_name("helper"));
    assert!(!is_macro_clause_defn_name("__expr"));
    assert!(!is_macro_clause_defn_name("Double.double$Int"));
    assert!(!is_macro_clause_defn_name("clause_only"));
}

#[test]
fn undefined_var_in_macro_clause_gets_dependency_diagnostic() {
    // §0.8: a same-module non-macro reference inside a macro clause body
    // must surface a clear diagnostic naming the symbol AND the
    // dependency-module rule — not the bare "undefined variable".
    let err = CranelispError::TypeError {
        message: "undefined variable: helper".to_string(),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    };
    let enriched = enrich_macro_clause_resolution_error("__macro_m_clause_0", err);
    let CranelispError::TypeError { message, .. } = enriched else {
        panic!("expected TypeError");
    };
    // Offending symbol name is preserved (callers substring-match on it).
    assert!(message.contains("helper"), "message: {message}");
    // The §0.8 dependency-module direction is present.
    assert!(
        message.contains("same-module") || message.contains("dependency"),
        "message: {message}"
    );
}

#[test]
fn undefined_var_outside_macro_clause_is_unchanged() {
    // A plain user defn keeps the generic message — no false enrichment.
    let original = "undefined variable: helper".to_string();
    let err = CranelispError::TypeError {
        message: original.clone(),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    };
    let passed = enrich_macro_clause_resolution_error("f", err);
    let CranelispError::TypeError { message, .. } = passed else {
        panic!("expected TypeError");
    };
    assert_eq!(message, original);
}

#[test]
fn non_undefined_var_error_in_macro_clause_is_unchanged() {
    // Only "undefined variable" errors are rewritten; other type errors
    // (e.g. unification mismatch) pass through untouched even inside a
    // macro-clause defn.
    let original = "type mismatch: Int vs String".to_string();
    let err = CranelispError::TypeError {
        message: original.clone(),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    };
    let passed = enrich_macro_clause_resolution_error("__macro_m_clause_0", err);
    let CranelispError::TypeError { message, .. } = passed else {
        panic!("expected TypeError");
    };
    assert_eq!(message, original);
}

// =========================================================================
// ModuleEntry::Def AST-annotation shape + CheckResult slim shape
// (harvested from tests/legacy/wave2_g6.rs per FIXME 0117, typecheck half).
//
// wave2_g6 was a Layer-3 integration file observing the Sprint 57 Wave 2
// (G6) write paths via the Rust API. Two of its observations are
// typecheck-internal contracts and are harvested here; the backend half
// (the `Code { ptr }` write onto `ModuleEntry::Def.code` via the
// `CodeFinalizer` trait, and the `/clif`/`/source` introspection +
// cross-module-call read-path guards) stays for the W-C backend sweep.
//
// 1. Phase-1 AST annotation: after `check`, a user `(defn ...)` is
//    registered as `ModuleEntry::Def` carrying `ast: Some(_)` (the
//    annotated `Defn`). This is the typecheck-owned half of the legacy
//    `g6_code_on_entry_after_compile` assertion — the `code.is_some()`
//    half is the backend write path (W-C).
// 2. `CheckResult` slim shape: the boundary type carries exactly
//    `{ warnings, display }` after Wave 2's slim-down — the legacy
//    `g6_check_result_slim_shape` structural guard.
// =========================================================================
