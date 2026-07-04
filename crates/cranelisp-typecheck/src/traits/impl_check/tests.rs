//! Per-submodule test module for `impl_check.rs` — impl recording +
//! method-body type-checking + default-method synthesis. Relocated verbatim
//! from the pooled `traits/tests.rs` (S102 FIXME 0497 de-pool), now a sibling
//! of the code it exercises, per METHOD §2.2 / Principle 23.

use cranelisp_types::{
    Defn, DefnVariant, Expr, Span, TraitDecl, TraitImpl, TraitMethodSig, TypeExpr,
    TypeName, Visibility, Symbol, TraitName,
};

use crate::traits::test_helpers::*;

// spec: 07-traits §7.3.1 — register concrete trait implementation
#[test]
fn test_register_trait_impl() {
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

    assert!(tc.has_impl(&TraitName::from("TestTrait"), &TypeName::from("Int")));
    assert!(!tc.has_impl(&TraitName::from("TestTrait"), &TypeName::from("Bool")));
}

// spec: 07-traits §7.4.3 — has_impl tracks trait-type pairs via SymbolTable
#[test]
fn test_has_impl_via_symbol_table() {
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

    assert!(tc.has_impl(&TraitName::from("TestTrait"), &TypeName::from("Int")));
    assert!(!tc.has_impl(&TraitName::from("TestTrait"), &TypeName::from("Bool")));
}

// spec: 07-traits §7.1.5 — generate_default_methods synthesizes missing impl methods
#[test]
fn test_generate_default_methods_produces_real_bodies() {
    // Register Eq trait inline and create an impl with only "=" provided.
    // The "!=" default should be generated with a real body.
    let mut tc = tf_prims();

    // Register Eq trait inline (as prelude would)
    let eq_decl = TraitDecl {
        name: TraitName::from("Eq"),
        docstring: None,
        type_params: vec![Symbol::from("a")],
        methods: vec![
            TraitMethodSig {
                name: Symbol::from("="),
                docstring: None,
                params: vec![
                    (Symbol::from("x"), TypeExpr::TypeVar(Symbol::from("a"))),
                    (Symbol::from("y"), TypeExpr::TypeVar(Symbol::from("a"))),
                ],
                ret_type: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Bool"))),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_body: None,
            },
            TraitMethodSig {
                name: Symbol::from("!="),
                docstring: None,
                params: vec![
                    (Symbol::from("x"), TypeExpr::TypeVar(Symbol::from("a"))),
                    (Symbol::from("y"), TypeExpr::TypeVar(Symbol::from("a"))),
                ],
                ret_type: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Bool"))),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                // Default body: (not (= x y)) — parsed Expr per S69 Submission 26
                // (default_body is now Option<Expr>, was Option<Sexp>).
                default_body: Some(Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("not"), Span::SYNTHETIC)),
                    args: vec![Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("="), Span::SYNTHETIC)),
                        args: vec![
                            Expr::var(Symbol::from("x"), Span::SYNTHETIC),
                            Expr::var(Symbol::from("y"), Span::SYNTHETIC),
                        ],
                        span: Span::SYNTHETIC,
                        resolved_call: None,
                        inferred_type: None,
                    }],
                    span: Span::SYNTHETIC,
                    resolved_call: None,
                    inferred_type: None,
                }),
            },
        ],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };
    tc.register_trait_decl_self(&eq_decl).unwrap();

    let impl_ = TraitImpl {
        trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Eq")),
        target: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int"))),
        type_constraints: vec![],
        methods: vec![Defn {
            name: Symbol::from("="),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("lhs"), None), (Symbol::from("rhs"), None)],
                body: Expr::BoolLit { value: true, span: Span::SYNTHETIC, inferred_type: None, },
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        }],
        span: Span::SYNTHETIC,
    };

    let decl = tc.lookup_trait_decl(&TraitName::from("Eq"))
        .expect("Eq trait should be registered");
    let defaults = tc.generate_default_methods(&tc.state, &decl, &impl_).unwrap();

    assert_eq!(defaults.len(), 1, "should generate 1 default method (!=)");
    let neq = &defaults[0];
    assert_eq!(neq.name.as_ref(), "Eq.!=$Int");
    assert_eq!(neq.params().len(), 2);

    // Body should be (not (= x y)), not IntLit 0
    assert_apply_callee(neq.body(), "not");
}
