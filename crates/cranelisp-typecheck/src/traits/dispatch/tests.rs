//! Per-submodule test module for `dispatch.rs` (S102 FIXME 0497 de-pool —
//! relocated verbatim from the pooled `traits/primitive_dispatch_tests.rs`,
//! content-unchanged, now a sibling of the code it exercises so attribution is
//! structural, per METHOD §2.2 / Principle 23).

use cranelisp_types::{Symbol, TraitName, TypeName};

use super::*;

// FIXME 0185 — verify the primitive-trait-method dispatch table mirrors
// the pre-D43 backend `primitive_for_trait_method` mapping.
#[test]
fn num_plus_int_maps_to_add_i64() {
    let result = primitive_for_trait_method(
        &TraitName::from("Num"),
        &Symbol::from("+"),
        &TypeName::from("Int"),
    );
    assert_eq!(result, Some("add-i64"));
}

#[test]
fn num_plus_float_maps_to_add_f64() {
    let result = primitive_for_trait_method(
        &TraitName::from("Num"),
        &Symbol::from("+"),
        &TypeName::from("Float"),
    );
    assert_eq!(result, Some("add-f64"));
}

#[test]
fn eq_eq_int_maps_to_eq_i64() {
    let result = primitive_for_trait_method(
        &TraitName::from("Eq"),
        &Symbol::from("="),
        &TypeName::from("Int"),
    );
    assert_eq!(result, Some("eq-i64"));
}

#[test]
fn eq_neq_string_maps_to_neq_string() {
    let result = primitive_for_trait_method(
        &TraitName::from("Eq"),
        &Symbol::from("!="),
        &TypeName::from("String"),
    );
    assert_eq!(result, Some("neq-string"));
}

#[test]
fn ord_lt_int_maps_to_lt_i64() {
    let result = primitive_for_trait_method(
        &TraitName::from("Ord"),
        &Symbol::from("<"),
        &TypeName::from("Int"),
    );
    assert_eq!(result, Some("lt-i64"));
}

#[test]
fn display_show_int_maps_to_int_to_string() {
    let result = primitive_for_trait_method(
        &TraitName::from("Display"),
        &Symbol::from("show"),
        &TypeName::from("Int"),
    );
    assert_eq!(result, Some("int-to-string"));
}

#[test]
fn unknown_combination_returns_none() {
    let result = primitive_for_trait_method(
        &TraitName::from("Display"),
        &Symbol::from("show"),
        &TypeName::from("Option"),
    );
    assert_eq!(result, None);
}

#[test]
fn user_trait_returns_none() {
    let result = primitive_for_trait_method(
        &TraitName::from("MyTrait"),
        &Symbol::from("foo"),
        &TypeName::from("Int"),
    );
    assert_eq!(result, None);
}
