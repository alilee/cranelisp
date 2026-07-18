//! Per-submodule test module for `impl_check.rs` — impl recording +
//! method-body type-checking + default-method synthesis. Relocated verbatim
//! from the pooled `traits/tests.rs` (S102 FIXME 0497 de-pool), now a sibling
//! of the code it exercises, per METHOD §2.2 / Principle 23.

use cranelisp_types::{
    Defn, DefnVariant, Expr, ModuleFullPath, Span, TraitDecl, TraitImpl, TraitMethodSig, TypeExpr,
    TypeName, Visibility, Symbol, TraitName,
};

use crate::traits::test_helpers::*;

/// Build a unary `(deftrait <name> (<method> [lhs rhs] a))` decl (type param
/// `a`, both params + return `a`).
fn unary_trait_decl(name: &str, method: &str) -> TraitDecl {
    TraitDecl {
        name: TraitName::from(name),
        docstring: None,
        type_params: vec![Symbol::from("a")],
        methods: vec![TraitMethodSig {
            name: Symbol::from(method),
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
    }
}

/// Build `(impl <trait> Int (defn <method> [lhs rhs] (add-i64 lhs rhs)))`.
fn int_op_impl(trait_name: &str, method: &str) -> TraitImpl {
    TraitImpl {
        head_con_var: None,
        trait_name: cranelisp_types::TraitRef::new(None, TraitName::from(trait_name)),
        target: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int"))),
        type_constraints: vec![],
        methods: vec![Defn {
            name: Symbol::from(method),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("lhs"), None), (Symbol::from("rhs"), None)],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("add-i64"), Span::SYNTHETIC)),
                    args: vec![
                        Expr::var(Symbol::from("lhs"), Span::SYNTHETIC),
                        Expr::var(Symbol::from("rhs"), Span::SYNTHETIC),
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
    }
}

// spec: 07-traits §7.3 + 08-modules §8.6.2 — an `(impl <trait> <type> …)` form
// resolves its bare `trait_name` in module scope WITH the implicit-prelude
// fallback hop: a PRELUDE-GLOBBED trait (reachable only via the implicit
// prelude glob, no `Import` edge) must be resolvable, exactly as a bare-name
// lookup already reaches prelude-provided names (S78 §2). This is the seam pin
// for E9 (S108) — the CHECK-path face of the E3/E8/0558 prelude-fallback-hop
// class; the e2e guard is
// `tests/repl_introspection.rs::impl_of_prelude_globbed_trait_resolves_trait_name`.
//
// It pins THREE facets in one fixture: (1) the prelude-globbed trait resolves +
// its impl registers via the hop; (2) the non-fallback current-module probe
// still MISSES it — a same-module identity/idempotency check ("is this trait
// already re-registered in THIS module?"), module-local by design and DISTINCT
// from the §8.6.4 name-freedom question (see facet-2 assertion below); (3) a
// locally-defined trait impl AND a genuinely-unknown trait behave exactly as
// before (unchanged / still `unknown trait`). Fails on revert of the hop.
//
// defect: class=prelude-scope-miss locus=crates/cranelisp-typecheck/src/traits/impl_check.rs::register_trait_impl found=S108 owner=/dev
#[test]
fn impl_of_prelude_globbed_trait_resolves_via_outer_scope_hop() {
    let mut tc = tf_prims();

    let prelude = ModuleFullPath::from("prelude");
    let user = ModuleFullPath::from("user");

    // 1. Prelude declares trait `Display` (method `show`). Glob primitives into
    //    prelude so the impl body (`add-i64`) and the bare type name `Int`
    //    resolve there (and, from `user`, via the prelude fallback).
    tc.set_current_module(prelude.clone());
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    tc.register_trait_decl_self(&unary_trait_decl("Display", "show"))
        .unwrap();

    // 2. Switch to `user`. It does NOT import `Display`; the only path to the
    //    trait is the implicit-prelude fallback. With the bit OFF, prove the
    //    pre-fallback state: the impl-form lookup misses (the E9 bug).
    tc.set_current_module(user.clone());
    assert!(
        tc.resolve_trait_decl(&TraitName::from("Display")).is_none(),
        "bit OFF: a prelude-globbed trait must be invisible without the fallback"
    );

    // 3. Turn the prelude-fallback bit ON for `user` (what
    //    `inject_prelude_if_needed` does for an ordinary entry module).
    tc.prelude_fallback.insert(user.clone(), true);

    // Facet 1: the impl-form trait-name lookup now hops to the prelude
    // fallback and finds `Display` — and the whole `(impl Display Int …)`
    // registers without `unknown trait`.
    assert!(
        tc.resolve_trait_decl(&TraitName::from("Display")).is_some(),
        "bit ON: the prelude-globbed trait `Display` must resolve via the prelude-fallback hop"
    );
    tc.register_trait_impl_self(&int_op_impl("Display", "show"))
        .expect("`(impl Display Int …)` of a prelude-globbed trait must register via the hop");
    // Proof the impl actually landed (in the trait's home, prelude — Decision 45
    // Pattern B), discoverable through the same fallback dispatch uses.
    assert!(
        tc.has_impl(&TraitName::from("Display"), &TypeName::from("Int")),
        "the registered `impl Display Int` must be discoverable via the prelude fallback"
    );

    // Facet 2 (same-module identity/idempotency, NOT name-freedom): the
    // NON-fallback current-module probe — the `deftrait` re-registration check,
    // "is this exact trait already registered in THIS module?" — must STILL miss
    // the prelude decl. It is module-local BY DESIGN and does NOT consult the
    // prelude; that is the correct answer to the identity question. Whether a
    // user `(deftrait Display …)` may be defined AT ALL is the SEPARATE
    // name-freedom question, answered by the prelude-consulting
    // `reject_def_over_binding` seam — which REJECTS a def over a prelude-provided
    // name as a §8.6.4 compile-time conflict (NOT a shadow). This assertion pins
    // the identity probe only; it says nothing about name-freedom.
    assert!(
        tc.lookup_trait_decl(&TraitName::from("Display")).is_none(),
        "the non-fallback current-module lookup must NOT see the prelude decl \
         (same-module identity/idempotency probe, module-local by design; \
          name-freedom is the separate §8.6.4 reject_def_over_binding question)"
    );

    // Facet 3a (unchanged, unknown): a genuinely-unknown trait still misses both
    // scopes and the impl form still raises `unknown trait`.
    let unknown_err = tc
        .register_trait_impl_self(&int_op_impl("Nonexistent", "show"))
        .expect_err("an impl of a genuinely-unknown trait must still be rejected");
    let msg = format!("{unknown_err}");
    assert!(
        msg.contains("unknown trait"),
        "unknown-trait rejection must be intact; got: {msg}"
    );

    // Facet 3b (unchanged, local): a LOCALLY-defined trait impl still resolves
    // through the current module, exactly as before.
    tc.register_trait_decl_self(&unary_trait_decl("LocalTr", "lop"))
        .unwrap();
    tc.register_trait_impl_self(&int_op_impl("LocalTr", "lop"))
        .expect("a locally-defined trait impl must register unchanged");
    assert!(
        tc.has_impl(&TraitName::from("LocalTr"), &TypeName::from("Int")),
        "the locally-defined trait impl must be discoverable"
    );
}

// spec: 07-traits §7.3.1 — register concrete trait implementation
#[test]
fn test_register_trait_impl() {
    let mut tc = tc_with_prims();
    let decl = make_test_trait_decl();
    tc.register_trait_decl_self(&decl).unwrap();

    let impl_ = TraitImpl {
        head_con_var: None,
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
        head_con_var: None,
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
        head_con_var: None,
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
    // S102 4th lossy-head cure: the default-method `$Type` suffix is now the FQ
    // home-qualified type head (`primitives/Int`), lock-step with the dispatch
    // mangle, so two same-bare-named types from different modules don't collide.
    let fq_int = cranelisp_types::FQTypeName::new(
        cranelisp_types::ModuleFullPath::from("primitives"),
        TypeName::from("Int"),
    );
    let defaults = tc.generate_default_methods(&tc.state, &decl, &impl_, &fq_int).unwrap();

    assert_eq!(defaults.len(), 1, "should generate 1 default method (!=)");
    let neq = &defaults[0];
    assert_eq!(neq.name.as_ref(), "Eq.!=$primitives/Int");
    assert_eq!(neq.params().len(), 2);

    // Body should be (not (= x y)), not IntLit 0
    assert_apply_callee(neq.body(), "not");
}
