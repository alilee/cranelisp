//! Per-submodule test module for `registry.rs` — the write-side: a parsed
//! `TraitDecl` becomes symbol-table state (`ActiveConstraints` + per-method
//! `Def`s). Relocated verbatim from the pooled `traits/tests.rs` (S102 FIXME
//! 0497 de-pool), now a sibling of the code it exercises so attribution is
//! structural, per METHOD §2.2 / Principle 23.

use cranelisp_types::{ModuleEntry, Symbol, TraitName, TypeName};

use super::*;
use crate::traits::test_helpers::*;

// spec: 07-traits §7.1 — no traits registered at startup
#[test]
fn test_no_traits_at_startup() {
    let tc = tf();
    // No traits should be discoverable via lookup
    assert!(tc.lookup_trait_decl(&TraitName::from("TestTrait")).is_none());
}

// spec: 07-traits §7.3 — no impls registered at startup
#[test]
fn test_no_impls_at_startup() {
    let tc = tf();
    // No impls should be discoverable via has_impl
    assert!(!tc.has_impl(&TraitName::from("Num"), &TypeName::from("Int")));
}

// spec: 03-types §3.6.1 — constraint detection: add and get trait constraints
#[test]
fn test_active_constraints_add_and_get() {
    let mut ac = ActiveConstraints::default();
    ac.add(0, test_fqtn_trait("Num"));
    assert_eq!(ac.get(0).map(|v| v.len()), Some(1));
    assert!(ac.get(1).is_none());
}

// spec: 03-types §3.6.2 — constraint propagation: duplicate adds are idempotent
#[test]
fn test_active_constraints_add_is_idempotent() {
    let mut ac = ActiveConstraints::default();
    ac.add(0, test_fqtn_trait("Num"));
    ac.add(0, test_fqtn_trait("Num"));
    ac.add(0, test_fqtn_trait("Eq"));
    ac.add(0, test_fqtn_trait("Eq"));
    let traits = ac.get(0).unwrap();
    assert_eq!(traits.len(), 2, "duplicate adds should be ignored");
    assert_eq!(traits[0].name.as_ref(), "Num");
    assert_eq!(traits[1].name.as_ref(), "Eq");
}

// spec: 03-types §3.6.2 — collect constraints for specific type variable set
#[test]
fn test_active_constraints_collect_for_vars() {
    let mut ac = ActiveConstraints::default();
    ac.add(0, test_fqtn_trait("Num"));
    ac.add(1, test_fqtn_trait("Eq"));

    let collected = ac.collect_for_vars(&[0, 2]);
    assert!(collected.contains_key(&0));
    assert!(!collected.contains_key(&1));
    assert!(!collected.contains_key(&2));
}

// spec: 03-types §3.6.2 — constraint state can be cleared
#[test]
fn test_active_constraints_clear() {
    let mut ac = ActiveConstraints::default();
    ac.add(0, test_fqtn_trait("Num"));
    ac.clear();
    assert!(ac.constraints.is_empty());
}

// spec: 07-traits §7.1 — deftrait registers trait and methods in symbol table
#[test]
fn test_register_trait_decl() {
    let mut tc = tf_prims();
    let decl = make_test_trait_decl();
    tc.register_trait_decl_self(&decl).unwrap();

    // Trait should be discoverable via SymbolTable lookup
    assert!(tc.lookup_trait_decl(&TraitName::from("TestTrait")).is_some());
    // Method should be reverse-mapped via trait_origin on ModuleEntry::Def
    assert_eq!(
        tc.method_to_trait(&Symbol::from("test-op")),
        Some(TraitName::from("TestTrait"))
    );
    // Trait should be in symbol table
    assert!(matches!(
        tc.symbol_table().get("TestTrait"),
        Some(ModuleEntry::TraitDecl { .. })
    ));
}

// spec: 07-traits §7.1 — a genuinely-DIFFERENT redeclaration of the same
// trait name is an error. The conflicting decl shares the name `TestTrait`
// but declares a different method (`other-op` instead of `test-op`), so it
// is NOT the idempotent retry re-submission accommodated below — it must be
// rejected.
#[test]
fn test_register_conflicting_duplicate_trait_fails() {
    let mut tc = tf_prims();
    let decl = make_test_trait_decl();
    tc.register_trait_decl_self(&decl).unwrap();

    // Same name, DIFFERENT method set — a real conflict.
    let mut conflicting = make_test_trait_decl();
    conflicting.methods[0].name = Symbol::from("other-op");
    let err = tc.register_trait_decl_self(&conflicting).unwrap_err();
    assert!(err.message().contains("already defined"));
}

// spec: spec/08-modules.md §8.2 — S86 D3. Re-registering the IDENTICAL trait
// declaration is idempotent (a no-op), NOT an "already defined" error. The
// cluster orchestration retries a module's typecheck from the top with no
// saved resume index when a declared `(mod child)` submodule must load, so a
// trait-defining module's `(deftrait …)` is re-submitted unchanged on the
// retry pass; the registration must absorb the re-submission the same way
// `register_type_def` upserts. Before the D3 fix this errored
// `trait TestTrait already defined`.
#[test]
fn test_register_identical_trait_twice_is_idempotent() {
    let mut tc = tf_prims();
    let decl = make_test_trait_decl();
    tc.register_trait_decl_self(&decl).unwrap();
    // Identical re-submission (the retry-from-top shape) must succeed.
    tc.register_trait_decl_self(&decl)
        .expect("identical re-registration must be idempotent (S86 D3)");
    // The trait is still registered exactly once and resolvable.
    assert!(tc.lookup_trait_decl(&TraitName::from("TestTrait")).is_some());
}

// spec: 03-types §3.4.1 — trait method scheme carries trait constraint
#[test]
fn test_trait_method_has_constrained_scheme() {
    let mut tc = tf_prims();
    let decl = make_test_trait_decl();
    tc.register_trait_decl_self(&decl).unwrap();

    if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("test-op") {
        assert_eq!(scheme.type_vars.len(), 1, "test-op should have 1 quantified var");
        assert!(
            !scheme.constraints.is_empty(),
            "test-op should have TestTrait constraint"
        );
        let var_id = scheme.type_vars[0];
        let traits = scheme.constraints.get(&var_id).unwrap();
        assert_eq!(traits.len(), 1);
        assert_eq!(traits[0].name.as_ref(), "TestTrait");
    } else {
        panic!("test-op should be registered");
    }
}

// spec: pipeline-orchestration §5 — no core traits at startup (Decision 17 eliminated)
#[test]
fn test_no_core_traits_at_startup() {
    let tc = tf();
    // Traits come from prelude .cl files, NOT compiler builtins.
    // No traits should be discoverable via SymbolTable lookup.
    assert!(tc.lookup_trait_decl(&TraitName::from("Num")).is_none(),
        "no traits should be registered at startup");
    assert!(!tc.has_impl(&TraitName::from("Num"), &TypeName::from("Int")),
        "no impls should be registered at startup");
}

// spec: pipeline-orchestration §5 — operator symbols NOT in symbol table at startup
#[test]
fn test_no_operators_at_startup() {
    let tc = tf();
    let ops = ["+", "-", "*", "/", "=", "!=", "<", ">", "<=", ">="];
    for op in ops {
        assert!(
            tc.symbol_table().get(op).is_none(),
            "operator {op} should NOT be in symbol table at startup"
        );
    }
}
