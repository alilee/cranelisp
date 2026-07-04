//! Per-submodule test module for `dispatch.rs` (S102 FIXME 0497 de-pool —
//! relocated verbatim from the pooled `traits/primitive_dispatch_tests.rs`,
//! content-unchanged, now a sibling of the code it exercises so attribution is
//! structural, per METHOD §2.2 / Principle 23).

use cranelisp_types::{
    CranelispError, Defn, DefnVariant, Expr, ResolvedCall, Span, Symbol, TraitDecl,
    TraitImpl, TraitMethodSig, TraitName, Type, TypeExpr, TypeName, Visibility,
};

use super::*;
use crate::traits::test_helpers::*;

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

// -----------------------------------------------------------------------
// Method resolution (`try_resolve_trait_method`) — relocated from the pooled
// `traits/tests.rs` (S102 FIXME 0497 de-pool); these exercise the read-side
// dispatch seam that lives in `dispatch.rs`.
// -----------------------------------------------------------------------

// spec: 07-traits §7.4.1 — resolve trait method to concrete impl mangled name
#[test]
fn test_try_resolve_trait_method_success() {
    let mut tc = tc_with_prims();
    let decl = make_test_trait_decl();
    tc.register_trait_decl_self(&decl).unwrap();

    let impl_ = TraitImpl {
        trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("TestTrait")),
        target: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int"))),
        type_constraints: vec![],
        methods: vec![Defn {
            name: Symbol::from("test-op"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("lhs"), None), (Symbol::from("rhs"), None)],
                body: cranelisp_types::Expr::Apply {
                    callee: Box::new(cranelisp_types::Expr::var(Symbol::from("add-i64"), Span::SYNTHETIC)),
                    args: vec![
                        cranelisp_types::Expr::var(Symbol::from("lhs"), Span::SYNTHETIC),
                        cranelisp_types::Expr::var(Symbol::from("rhs"), Span::SYNTHETIC),
                    ],
                    span: Span::SYNTHETIC,
                    resolved_call: None,
                    inferred_type: None,
                },
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        }],
        span: Span::SYNTHETIC,
    };
    tc.register_trait_impl_self(&impl_).unwrap();

    let result = tc.try_resolve_trait_method_self(
        &Symbol::from("test-op"),
        &[Type::Int, Type::Int],
        Span::SYNTHETIC,
    );
    let result = result.expect("should not error");
    assert!(result.is_some());
    if let Some(ResolvedCall::TraitMethod {
        trait_name,
        method_name,
        impl_type,
        mangled_name,
    }) = result
    {
        assert_eq!(trait_name.name.as_ref(), "TestTrait");
        assert_eq!(method_name.as_ref(), "test-op");
        assert_eq!(impl_type.name.as_ref(), "Int");
        assert_eq!(mangled_name.as_ref(), "TestTrait.test-op$Int");
    }
}

// spec: 07-traits §7.4.3 — no matching impl returns TypeError
#[test]
fn test_try_resolve_trait_method_no_impl() {
    let mut tc = tf_prims();
    let decl = make_test_trait_decl();
    tc.register_trait_decl_self(&decl).unwrap();
    // No impl registered for Bool under TestTrait

    let result = tc.try_resolve_trait_method_self(
        &Symbol::from("test-op"),
        &[Type::Bool, Type::Bool],
        Span::SYNTHETIC,
    );
    assert!(result.is_err());
    let err = result.unwrap_err();
    match err {
        CranelispError::TypeError { message, .. } => {
            assert!(message.contains("no impl of trait TestTrait for type Bool"), "{message}");
        }
        other => panic!("expected TypeError, got {other:?}"),
    }
}

// spec: 07-traits §7.4 — a nullary, return-type-polymorphic trait method
// (`self` in return position, no parameter to dispatch on) dispatches on the
// call's RETURN type once the call context fixes it. This is the typecheck
// seam of defect D-default: without the return-type fallback the resolver
// returned `Ok(None)` (no dispatch arg), leaving `resolved_call: None` so
// codegen emitted "undefined function: z". With the call return type fixed
// to Int the resolver must select the Int impl.
#[test]
fn nullary_return_poly_method_dispatches_on_return_type() {
    let mut tc = tc_with_prims();
    register_nullary_rp_int_impl(&mut tc);

    // Simulate the post-inference recorded call return type: `(z)` fixed to
    // Int by its call context. `try_resolve_trait_method` reads this from
    // `expr_types` at the call span when there is no dispatch argument.
    let call_span = Span::new(10, 13);
    tc.seed_expr_type(call_span, Type::Int);

    let result = tc
        .try_resolve_trait_method_self(&Symbol::from("z"), &[], call_span)
        .expect("should not error");
    let resolved = result.expect("nullary return-poly method must resolve to the Int impl");
    match resolved {
        ResolvedCall::TraitMethod { method_name, impl_type, mangled_name, .. } => {
            assert_eq!(method_name.as_ref(), "z");
            assert_eq!(impl_type.name.as_ref(), "Int");
            assert_eq!(mangled_name.as_ref(), "NullaryRP.z$Int");
        }
        other => panic!("expected TraitMethod resolution, got {other:?}"),
    }
}

// spec: 07-traits §7.4 — NEGATIVE: when the call return type is NOT yet
// fixed (no `expr_types` entry / still a var), a nullary return-poly method
// must DEFER (`Ok(None)`), not guess an impl. The later deferred pass
// resolves it once the context pins the type.
#[test]
fn nullary_return_poly_method_defers_when_return_type_unfixed() {
    let mut tc = tc_with_prims();
    register_nullary_rp_int_impl(&mut tc);

    // No expr_types entry seeded at the span → return type is unknown.
    let result = tc.try_resolve_trait_method_self(
        &Symbol::from("z"),
        &[],
        Span::new(20, 23),
    );
    assert!(
        matches!(result, Ok(None)),
        "must defer when the return type is not yet fixed, got {result:?}"
    );
}

// spec: 07-traits §7.4.1 — non-trait-method name returns None
#[test]
fn test_try_resolve_non_trait_method() {
    let mut tc = tf_prims();
    let result = tc.try_resolve_trait_method_self(
        &Symbol::from("add-i64"),
        &[Type::Int, Type::Int],
        Span::SYNTHETIC,
    );
    assert!(matches!(result, Ok(None)));
}

// spec: 07-traits §7.1 — is_trait_method distinguishes trait methods from plain fns
#[test]
fn test_is_trait_method() {
    let mut tc = tf_prims();
    let decl = make_test_trait_decl();
    tc.register_trait_decl_self(&decl).unwrap();

    assert!(tc.is_trait_method(&Symbol::from("test-op")));
    assert!(!tc.is_trait_method(&Symbol::from("add-i64")));
}

// spec: 07-traits §7.4.2 — trait method resolution works with inline trait definitions
#[test]
fn test_try_resolve_with_inline_trait() {
    let mut tc = tc_with_prims();
    // Register Num trait inline (as prelude would)
    let num_decl = TraitDecl {
        name: TraitName::from("Num"),
        docstring: None,
        type_params: vec![Symbol::from("a")],
        methods: vec![TraitMethodSig {
            name: Symbol::from("+"),
            docstring: None,
            params: vec![
                (Symbol::from("lhs"), TypeExpr::TypeVar(Symbol::from("a"))),
                (Symbol::from("rhs"), TypeExpr::TypeVar(Symbol::from("a"))),
            ],
            ret_type: TypeExpr::TypeVar(Symbol::from("a")),
            span: Span::SYNTHETIC,
            hkt_param_index: None,
            default_body: None,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };
    tc.register_trait_decl_self(&num_decl).unwrap();

    // Register impl Num for Int
    let impl_ = TraitImpl {
        trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Num")),
        target: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int"))),
        type_constraints: vec![],
        methods: vec![Defn {
            name: Symbol::from("+"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("add-i64"), Span::SYNTHETIC)),
                    args: vec![
                        Expr::var(Symbol::from("x"), Span::SYNTHETIC),
                        Expr::var(Symbol::from("y"), Span::SYNTHETIC),
                    ],
                    span: Span::SYNTHETIC,
                    resolved_call: None,
                    inferred_type: None,
                },
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        }],
        span: Span::SYNTHETIC,
    };
    tc.register_trait_impl_self(&impl_).unwrap();
    tc.clear_transient_state();

    let result = tc.try_resolve_trait_method_self(
        &Symbol::from("+"),
        &[Type::Int, Type::Int],
        Span::SYNTHETIC,
    ).expect("should not error");
    assert!(result.is_some());
    if let Some(ResolvedCall::TraitMethod { mangled_name, .. }) = result {
        assert_eq!(mangled_name.as_ref(), "Num.+$Int");
    }
}
