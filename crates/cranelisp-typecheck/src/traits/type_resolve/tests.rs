//! Per-submodule test module for `type_resolve.rs` — the `TypeExpr -> Type`
//! resolution free functions (`resolve_trait_type_expr`) and default-method
//! body construction (`build_default_body`). Relocated verbatim from the
//! pooled `traits/tests.rs` (S102 FIXME 0497 de-pool), now a sibling of the
//! code it exercises, per METHOD §2.2 / Principle 23.

use std::collections::HashMap;

use cranelisp_types::{Span, Symbol, Type, TypeExpr, TypeId};

use super::*;
use crate::traits::test_helpers::*;

// -----------------------------------------------------------------------
// resolve_trait_type_expr
// -----------------------------------------------------------------------

// spec: 07-traits §7.1.1 — self type resolves to implementing type
#[test]
fn test_resolve_trait_type_expr_self() {
    let mut var_map = HashMap::new();
    let mut next_id: TypeId = 100;
    let result = resolve_trait_type_expr(
        &TypeExpr::SelfType,
        &Type::Int,
        Span::SYNTHETIC,
        &mut var_map,
        &mut next_id,
        &|_| None,
    )
    .unwrap();
    assert_eq!(result, Type::Int);
}

// spec: 07-traits §7.1.4 — named type in trait signature resolves to concrete type
#[test]
fn test_resolve_trait_type_expr_named() {
    let mut var_map = HashMap::new();
    let mut next_id: TypeId = 100;
    let result = resolve_trait_type_expr(
        &TypeExpr::Named(cranelisp_types::TypeRef::new(None, cranelisp_types::TypeName::from("Bool"))),
        &Type::Int,
        Span::SYNTHETIC,
        &mut var_map,
        &mut next_id,
        &|_| None,
    )
    .unwrap();
    assert_eq!(result, Type::Bool);
}

// spec: 07-traits §7.1.4 — type variable in trait sig gets fresh var
#[test]
fn test_resolve_trait_type_expr_type_var_gets_fresh_var() {
    let mut var_map = HashMap::new();
    let mut next_id: TypeId = 100;
    let result = resolve_trait_type_expr(
        &TypeExpr::TypeVar(Symbol::from("b")),
        &Type::Float,
        Span::SYNTHETIC,
        &mut var_map,
        &mut next_id,
        &|_| None,
    )
    .unwrap();
    assert!(matches!(result, Type::Var(_)));
    assert_ne!(result, Type::Float);
}

// spec: 07-traits §7.1.4 — pre-seeded type var reuses existing mapping
#[test]
fn test_resolve_trait_type_expr_type_var_preseeded() {
    let mut var_map = HashMap::new();
    var_map.insert(Symbol::from("a"), Type::Int);
    let mut next_id: TypeId = 100;
    let result = resolve_trait_type_expr(
        &TypeExpr::TypeVar(Symbol::from("a")),
        &Type::Float,
        Span::SYNTHETIC,
        &mut var_map,
        &mut next_id,
        &|_| None,
    )
    .unwrap();
    assert_eq!(result, Type::Int);
}

// spec: 07-traits §7.1.4 — same type variable name reuses same var across calls
#[test]
fn test_resolve_trait_type_expr_same_var_reused() {
    let mut var_map = HashMap::new();
    let mut next_id: TypeId = 100;
    let r1 = resolve_trait_type_expr(
        &TypeExpr::TypeVar(Symbol::from("b")),
        &Type::Int,
        Span::SYNTHETIC,
        &mut var_map,
        &mut next_id,
        &|_| None,
    )
    .unwrap();
    let r2 = resolve_trait_type_expr(
        &TypeExpr::TypeVar(Symbol::from("b")),
        &Type::Int,
        Span::SYNTHETIC,
        &mut var_map,
        &mut next_id,
        &|_| None,
    )
    .unwrap();
    assert_eq!(r1, r2);
}

// -----------------------------------------------------------------------
// build_default_body (default method-body generation)
// -----------------------------------------------------------------------

// spec: 07-traits §7.1.5 — default method body: != is (not (= x y))
#[test]
fn test_build_default_body_neq() {
    // != → (not (= x y))
    let body = build_default_body(
        "Eq", "!=",
        &[Symbol::from("x"), Symbol::from("y")],
        Span::SYNTHETIC,
    ).unwrap();

    assert_apply_callee(&body, "not");
    let not_args = apply_args(&body);
    assert_eq!(not_args.len(), 1);
    assert_apply_callee(&not_args[0], "=");
    let eq_args = apply_args(&not_args[0]);
    assert_eq!(eq_args.len(), 2);
    assert_var(&eq_args[0], "x");
    assert_var(&eq_args[1], "y");
}

// spec: 07-traits §7.1.5 — default method body: > is (< y x)
#[test]
fn test_build_default_body_gt() {
    // > → (< y x)
    let body = build_default_body(
        "Ord", ">",
        &[Symbol::from("x"), Symbol::from("y")],
        Span::SYNTHETIC,
    ).unwrap();

    assert_apply_callee(&body, "<");
    let args = apply_args(&body);
    assert_eq!(args.len(), 2);
    assert_var(&args[0], "y");
    assert_var(&args[1], "x");
}

// spec: 07-traits §7.1.5 — default method body: <= is (not (< y x))
#[test]
fn test_build_default_body_le() {
    // <= → (not (< y x))
    let body = build_default_body(
        "Ord", "<=",
        &[Symbol::from("x"), Symbol::from("y")],
        Span::SYNTHETIC,
    ).unwrap();

    assert_apply_callee(&body, "not");
    let not_args = apply_args(&body);
    assert_eq!(not_args.len(), 1);
    assert_apply_callee(&not_args[0], "<");
    let lt_args = apply_args(&not_args[0]);
    assert_eq!(lt_args.len(), 2);
    assert_var(&lt_args[0], "y");
    assert_var(&lt_args[1], "x");
}

// spec: 07-traits §7.1.5 — default method body: >= is (not (< x y))
#[test]
fn test_build_default_body_ge() {
    // >= → (not (< x y))
    let body = build_default_body(
        "Ord", ">=",
        &[Symbol::from("x"), Symbol::from("y")],
        Span::SYNTHETIC,
    ).unwrap();

    assert_apply_callee(&body, "not");
    let not_args = apply_args(&body);
    assert_eq!(not_args.len(), 1);
    assert_apply_callee(&not_args[0], "<");
    let lt_args = apply_args(&not_args[0]);
    assert_eq!(lt_args.len(), 2);
    assert_var(&lt_args[0], "x");
    assert_var(&lt_args[1], "y");
}

// spec: 07-traits §7.1.5 — unknown trait/method has no default body
#[test]
fn test_build_default_body_unknown_method_errors() {
    let result = build_default_body(
        "Unknown", "foo",
        &[Symbol::from("x"), Symbol::from("y")],
        Span::SYNTHETIC,
    );
    assert!(result.is_err());
}

// spec: 07-traits §7.1.5 — default body with wrong param count errors
#[test]
fn test_build_default_body_wrong_param_count_errors() {
    let result = build_default_body(
        "Eq", "!=",
        &[Symbol::from("x")],
        Span::SYNTHETIC,
    );
    assert!(result.is_err());
}
