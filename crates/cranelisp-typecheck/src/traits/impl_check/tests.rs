//! Per-submodule test module for `impl_check.rs` — impl recording +
//! method-body type-checking + default-method synthesis. Relocated verbatim
//! from the pooled `traits/tests.rs` (S102 FIXME 0497 de-pool), now a sibling
//! of the code it exercises, per METHOD §2.2 / Principle 23.

use cranelisp_types::{
    Defn, DefnVariant, Expr, ModuleEntry, ModuleFullPath, Span, Symbol, TraitDecl,
    TraitImpl, TraitName, Type, TypeExpr, TypeName, Visibility,
};

use crate::traits::test_helpers::*;

/// Build a conventional `(deftrait <name> (<method> [lhs rhs] self))` decl —
/// bare head, empty `type_params`, both params + return `self` (S112 settled
/// kind-`*` model).
fn unary_trait_decl(name: &str, method: &str) -> TraitDecl {
    parse_trait_decl(&format!("(deftrait {name} ({method} [lhs rhs] self))"))
}

/// Build `(impl <trait> Int (defn <method> [lhs rhs] (add-i64 lhs rhs)))`.
fn int_op_impl(trait_name: &str, method: &str) -> TraitImpl {
    TraitImpl {
        head_con_var: None,
        trait_name: cranelisp_types::TraitRef::new(None, TraitName::from(trait_name)),
        target: TypeExpr::Named(cranelisp_types::TypeRef::new(
            Some(ModuleFullPath::from("primitives")),
            TypeName::from("Int"),
        )),
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

// spec: 07-traits §7.3 — impl methods must match the declaration's arity.
#[test]
fn impl_method_too_few_parameters_rejected_before_enrollment() {
    let mut tc = tf_prims();
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    tc.register_trait_decl_self(&unary_trait_decl("ArityLow", "op"))
        .unwrap();
    let mut impl_ = int_op_impl("ArityLow", "op");
    impl_.methods[0].variants[0].params.pop();

    let err = tc.register_trait_impl_self(&impl_).unwrap_err();
    assert!(err.message().contains("has 1 parameter"), "{err:?}");
    assert!(!tc.has_impl(&TraitName::from("ArityLow"), &TypeName::from("Int")));
}

// spec: 07-traits §7.3 — extra binders are never silently dropped.
#[test]
fn impl_method_too_many_parameters_rejected_before_enrollment() {
    let mut tc = tf_prims();
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    tc.register_trait_decl_self(&unary_trait_decl("ArityHigh", "op"))
        .unwrap();
    let mut impl_ = int_op_impl("ArityHigh", "op");
    impl_.methods[0].variants[0]
        .params
        .push((Symbol::from("extra"), None));

    let err = tc.register_trait_impl_self(&impl_).unwrap_err();
    assert!(err.message().contains("has 3 parameters"), "{err:?}");
    assert!(!tc.has_impl(&TraitName::from("ArityHigh"), &TypeName::from("Int")));
}

// spec: 07-traits §7.3 — a bad later sibling publishes neither the impl nor
// an earlier method definition; re-impl uses the same replacement transaction.
#[test]
fn multi_method_failure_rolls_back_earlier_method_write() {
    let mut tc = tf_prims();
    let decl = parse_trait_decl(
        "(deftrait AtomicPair (first [a b] self) (second [a b] self))",
    );
    tc.register_trait_decl_self(&decl).unwrap();

    let mut impl_ = int_op_impl("AtomicPair", "first");
    let mut second = impl_.methods[0].clone();
    second.name = Symbol::from("second");
    second.variants[0].params.pop();
    impl_.methods.push(second);

    tc.register_trait_impl_self(&impl_).unwrap_err();
    assert!(!tc.has_impl(&TraitName::from("AtomicPair"), &TypeName::from("Int")));
    assert!(
        tc.symbol_table()
            .get("AtomicPair.first$primitives/Int")
            .is_none(),
        "the earlier sibling method must be rolled back"
    );
}

// spec: 07-traits §7.3 — failed re-impl preserves the prior settled methods.
#[test]
fn failed_reimpl_restores_prior_method_definition() {
    let mut tc = tf_prims();
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    let decl = parse_trait_decl(
        "(deftrait AtomicReplace (first [a b] self) (second [a b] self))",
    );
    tc.register_trait_decl_self(&decl).unwrap();

    let mut initial = int_op_impl("AtomicReplace", "first");
    let mut initial_second = initial.methods[0].clone();
    initial_second.name = Symbol::from("second");
    initial.methods.push(initial_second);
    tc.register_trait_impl_self(&initial).unwrap();

    let mut replacement = initial.clone();
    replacement.methods[0].variants[0].body = Expr::IntLit {
        value: 99,
        span: Span::SYNTHETIC,
        inferred_type: None,
    };
    replacement.methods[1].variants[0].params.pop();
    tc.register_trait_impl_self(&replacement).unwrap_err();

    let table = tc.symbol_table();
    let entry = table
        .get("AtomicReplace.first$primitives/Int")
        .expect("the prior method remains enrolled");
    let cranelisp_types::ModuleEntry::Def { ast: Some(defn), .. } = entry else {
        panic!("expected prior checked method definition, got {entry:?}");
    };
    assert!(
        matches!(defn.body, Expr::Apply { .. }),
        "failed replacement must restore the prior body"
    );
}

// spec: 07-traits §7.1.5 — an omitted unannotated default infers per impl.
#[test]
fn omitted_inferred_default_is_checked_for_concrete_self() {
    let mut tc = tf_prims();
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    tc.register_trait_decl_self(&parse_trait_decl(
        "(deftrait IdentityDefault (identity [x] x))",
    ))
    .unwrap();
    let impl_ = TraitImpl {
        head_con_var: None,
        trait_name: cranelisp_types::TraitRef::new(
            None,
            TraitName::from("IdentityDefault"),
        ),
        target: TypeExpr::Named(cranelisp_types::TypeRef::new(
            Some(ModuleFullPath::from("primitives")),
            TypeName::from("Int"),
        )),
        type_constraints: vec![],
        methods: vec![],
        span: Span::SYNTHETIC,
    };

    tc.register_trait_impl_self(&impl_).unwrap();
    assert!(tc.has_impl(
        &TraitName::from("IdentityDefault"),
        &TypeName::from("Int")
    ));
}

// spec: 07-traits §7.1.5 — an omitted default may dispatch through a required
// sibling while the impl is being enrolled; conformance checking must see the
// candidate impl without publishing it if a later check fails.
#[test]
fn omitted_default_can_dispatch_through_candidate_impl_sibling() {
    let mut tc = tf_prims();
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    tc.register_trait_decl_self(&parse_trait_decl(
        "(deftrait Sized (size [x] Int) (bump [x] (add-i64 (size x) 1)))",
    ))
    .unwrap();

    let impl_ = TraitImpl {
        head_con_var: None,
        trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Sized")),
        target: TypeExpr::Named(cranelisp_types::TypeRef::new(
            Some(ModuleFullPath::from("primitives")),
            TypeName::from("Int"),
        )),
        type_constraints: vec![],
        methods: vec![Defn {
            name: Symbol::from("size"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None)],
                body: Expr::var(Symbol::from("x"), Span::SYNTHETIC),
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        }],
        span: Span::SYNTHETIC,
    };

    tc.register_trait_impl_self(&impl_)
        .expect("the candidate impl must be visible while checking its default sibling call");
    assert!(tc.has_impl(&TraitName::from("Sized"), &TypeName::from("Int")));
    let table = tc.symbol_table();
    let Some(ModuleEntry::Def { scheme, .. }) = table.get("Sized.bump$primitives/Int") else {
        panic!("the checked default method must be written under its concrete mangle");
    };
    assert_eq!(
        scheme.ty,
        Type::Fn(vec![Type::Int], Box::new(Type::Int)),
        "the inferred default result must be substitution-resolved before publication"
    );
    drop(table);

    let mut call = Expr::Apply {
        callee: Box::new(Expr::var(Symbol::from("bump"), Span::SYNTHETIC)),
        args: vec![Expr::IntLit {
            value: 6,
            span: Span::SYNTHETIC,
            inferred_type: None,
        }],
        span: Span::SYNTHETIC,
        resolved_call: None,
        inferred_type: None,
    };
    assert_eq!(
        tc.infer_expr_for_test(&mut call).unwrap(),
        Type::Int,
        "dispatch must use the selected concrete method's inferred result"
    );
}

// spec: 07-traits §7.1.5 — a body annotation constrains the inferred result.
#[test]
fn annotated_default_result_mismatch_rejects_without_enrollment() {
    let mut tc = tf_prims();
    tc.register_trait_decl_self(&parse_trait_decl(
        "(deftrait ConstrainedDefault (flag [x] :Bool 1))",
    ))
    .unwrap();
    let impl_ = TraitImpl {
        head_con_var: None,
        trait_name: cranelisp_types::TraitRef::new(
            None,
            TraitName::from("ConstrainedDefault"),
        ),
        target: TypeExpr::Named(cranelisp_types::TypeRef::new(
            Some(ModuleFullPath::from("primitives")),
            TypeName::from("Int"),
        )),
        type_constraints: vec![],
        methods: vec![],
        span: Span::SYNTHETIC,
    };

    tc.register_trait_impl_self(&impl_).unwrap_err();
    assert!(!tc.has_impl(
        &TraitName::from("ConstrainedDefault"),
        &TypeName::from("Int")
    ));
}

// spec: 05-definitions §5.4 — impl conformance diagnostics identify the
// declaration as expected and the method body as supplied.
#[test]
fn impl_return_mismatch_reports_trait_method_and_declared_direction() {
    let mut tc = tf_prims();
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    tc.register_trait_decl_self(&parse_trait_decl("(deftrait D2 (dsc [self] String))"))
        .unwrap();
    let impl_ = TraitImpl {
        head_con_var: None,
        trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("D2")),
        target: TypeExpr::Named(cranelisp_types::TypeRef::new(
            Some(ModuleFullPath::from("primitives")),
            TypeName::from("Int"),
        )),
        type_constraints: vec![],
        methods: vec![Defn {
            name: Symbol::from("dsc"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("self"), None)],
                body: Expr::IntLit {
                    value: 42,
                    span: Span::SYNTHETIC,
                    inferred_type: None,
                },
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        }],
        span: Span::SYNTHETIC,
    };

    let err = tc.register_trait_impl_self(&impl_).unwrap_err();
    let message = err.message();
    assert!(
        message.contains("impl of trait `D2` for `primitives/Int`"),
        "{err:?}"
    );
    assert!(message.contains("method `dsc` does not conform"), "{err:?}");
    assert!(
        message.contains("expected primitives/String, got primitives/Int"),
        "{err:?}"
    );
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
                    callee: Box::new(cranelisp_types::Expr::var(
                        Symbol::from("add-i64"),
                        Span::SYNTHETIC,
                    )),
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
                    callee: Box::new(cranelisp_types::Expr::var(
                        Symbol::from("add-i64"),
                        Span::SYNTHETIC,
                    )),
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
    let eq_decl = parse_trait_decl(
        "(deftrait Eq (= [x y] Bool) (!= [x y] (not (= x y))))",
    );
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
                body: Expr::BoolLit {
                    value: true,
                    span: Span::SYNTHETIC,
                    inferred_type: None,
                },
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        }],
        span: Span::SYNTHETIC,
    };

    let decl = tc
        .lookup_trait_decl(&TraitName::from("Eq"))
        .expect("Eq trait should be registered");
    // S102 4th lossy-head cure: the default-method `$Type` suffix is now the FQ
    // home-qualified type head (`primitives/Int`), lock-step with the dispatch
    // mangle, so two same-bare-named types from different modules don't collide.
    let fq_int = cranelisp_types::FQTypeName::new(
        cranelisp_types::ModuleFullPath::from("primitives"),
        TypeName::from("Int"),
    );
    let defaults = tc
        .generate_default_methods(&tc.state, &decl, &impl_, &fq_int)
        .unwrap();

    assert_eq!(defaults.len(), 1, "should generate 1 default method (!=)");
    let neq = &defaults[0];
    assert_eq!(neq.name.as_ref(), "Eq.!=$primitives/Int");
    assert_eq!(neq.params().len(), 2);

    // Body should be (not (= x y)), not IntLit 0
    assert_apply_callee(neq.body(), "not");
}

// ===========================================================================
// S112 §7.3.5 Case-3 kind-check seam — slot-1 echo (shape + con_var spelling)
// and slot-2 kind interpretation (`design/typecheck/hkt.md` §5.4). One
// deterministic path; the trait's DECLARATION is authoritative on its kind.
// ===========================================================================

use cranelisp_types::TraitRef;

/// `(deftrait (Functor f) (fmap [:(Fn [a] b) func :(f a) x] (f b)))`.
fn functor_decl() -> TraitDecl {
    parse_trait_decl("(deftrait (Functor f) (fmap [:(Fn [a] b) func :(f a) x] (f b)))")
}

/// Register `(deftype (Option a) None (Some [:a val]))` in the fixture's module.
fn register_option(tc: &mut crate::checker::TestFixture) {
    tc.register_type_def_self(
        &TypeName::from("Option"),
        &None,
        &[Symbol::from("a")],
        &[
            cranelisp_types::ConstructorDef {
                name: Symbol::from("None"),
                docstring: None,
                fields: vec![],
                span: Span::SYNTHETIC,
            },
            cranelisp_types::ConstructorDef {
                name: Symbol::from("Some"),
                docstring: None,
                fields: vec![cranelisp_types::FieldDef {
                    name: Symbol::from("val"),
                    type_expr: TypeExpr::TypeVar(Symbol::from("a")),
                    span: Span::SYNTHETIC,
                }],
                span: Span::SYNTHETIC,
            },
        ],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();
}

/// Register `(deftype (Pair a b) MkPair)` — an arity-2 constructor.
fn register_pair(tc: &mut crate::checker::TestFixture) {
    tc.register_type_def_self(
        &TypeName::from("Pair"),
        &None,
        &[Symbol::from("a"), Symbol::from("b")],
        &[cranelisp_types::ConstructorDef {
            name: Symbol::from("MkPair"),
            docstring: None,
            fields: vec![],
            span: Span::SYNTHETIC,
        }],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();
}

/// Build a `Functor` impl: `(impl (<head_con_var>?) <target> (defn fmap [func x] <body>))`.
fn functor_impl(head_con_var: Option<&str>, target: TypeExpr, body: Expr) -> TraitImpl {
    TraitImpl {
        head_con_var: head_con_var.map(Symbol::from),
        trait_name: TraitRef::new(None, TraitName::from("Functor")),
        target,
        type_constraints: vec![],
        methods: vec![Defn {
            name: Symbol::from("fmap"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("func"), None), (Symbol::from("x"), None)],
                body,
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        }],
        span: Span::SYNTHETIC,
    }
}

/// `(Trait Constructor)` pairing target — slot 2 of a higher-kinded impl.
fn pairing(trait_name: &str, con: &str) -> TypeExpr {
    TypeExpr::Applied(
        cranelisp_types::TypeRef::new(None, TypeName::from(trait_name)),
        vec![TypeExpr::Named(cranelisp_types::TypeRef::new(
            None,
            TypeName::from(con),
        ))],
    )
}

// spec: 07-traits §7.3.4/§7.3.5 Case 2 — POSITIVE. The correctly-echoed head
// `(Functor f)` + a well-kinded pairing `(Functor Option)` registers. The seam
// passes shape + spelling and the constructor's arity (1) matches `f`.
#[test]
fn hkt_impl_correct_echo_and_pairing_accepts() {
    let mut tc = tf_prims();
    register_option(&mut tc);
    tc.register_trait_decl_self(&functor_decl()).unwrap();

    // fmap body: `None` — has type `(Option b)`, satisfying the `(f b)` return.
    let impl_ = functor_impl(
        Some("f"),
        pairing("Functor", "Option"),
        Expr::var(Symbol::from("None"), Span::SYNTHETIC),
    );
    tc.register_trait_impl_self(&impl_)
        .expect("correct echo `(Functor f)` + well-kinded `(Functor Option)` must register");
    assert!(tc.has_impl(&TraitName::from("Functor"), &TypeName::from("Option")));
}

// spec: 07-traits §7.3 "Slot 1 is fixed" (hkt.md §5.4 step 3, spelling bit) —
// NEGATIVE. A parenthesized head with the WRONG con_var spelling `(Functor g)`
// passes the shape bit (`Some(_)`) but its spelling `g` ≠ the declared `f`, so
// it is rejected with a diagnostic naming BOTH spellings and the expected form.
#[test]
fn hkt_impl_wrong_con_var_spelling_rejected() {
    let mut tc = tf_prims();
    register_option(&mut tc);
    tc.register_trait_decl_self(&functor_decl()).unwrap();

    let impl_ = functor_impl(
        Some("g"), // wrong spelling
        pairing("Functor", "Option"),
        Expr::var(Symbol::from("None"), Span::SYNTHETIC),
    );
    let err = tc
        .register_trait_impl_self(&impl_)
        .expect_err("`(Functor g)` does not echo declared `(Functor f)`");
    let msg = err.message();
    assert!(msg.contains('g'), "names the written spelling: {msg}");
    assert!(msg.contains('f'), "names the declared spelling: {msg}");
    assert!(msg.contains("Functor"), "names the trait: {msg}");
    assert!(!tc.has_impl(&TraitName::from("Functor"), &TypeName::from("Option")));
}

// spec: 07-traits §7.3 "Slot 1 is fixed" (hkt.md §5.4 step 3, shape bit) —
// NEGATIVE. A bare-head impl of a higher-kinded trait is rejected: slot 1 must
// echo `(Functor f)`.
#[test]
fn hkt_impl_bare_head_rejected() {
    let mut tc = tf_prims();
    register_option(&mut tc);
    tc.register_trait_decl_self(&functor_decl()).unwrap();

    let impl_ = functor_impl(
        None, // bare head — shape mismatch
        pairing("Functor", "Option"),
        Expr::var(Symbol::from("None"), Span::SYNTHETIC),
    );
    let err = tc
        .register_trait_impl_self(&impl_)
        .expect_err("a bare-head impl of an HK trait is rejected");
    let msg = err.message();
    assert!(
        msg.contains("higher-kinded"),
        "names the kind mismatch: {msg}"
    );
    assert!(
        msg.contains("echo"),
        "directs to echo the declared head: {msg}"
    );
}

// spec: 07-traits §7.3 "Slot 1 is fixed" (hkt.md §5.4 step 3, shape bit) —
// NEGATIVE. A parenthesized (echoed) head on a CONVENTIONAL (kind-`*`) trait is
// rejected: its impl head is the bare trait name.
#[test]
fn conventional_impl_parenthesized_head_rejected() {
    let mut tc = tf_prims();
    tc.register_trait_decl_self(&unary_trait_decl("Display", "show"))
        .unwrap();

    let impl_ = TraitImpl {
        head_con_var: Some(Symbol::from("f")), // parenthesized head on a conventional trait
        trait_name: TraitRef::new(None, TraitName::from("Display")),
        target: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int"))),
        type_constraints: vec![],
        methods: vec![Defn {
            name: Symbol::from("show"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("lhs"), None), (Symbol::from("rhs"), None)],
                body: Expr::var(Symbol::from("lhs"), Span::SYNTHETIC),
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        }],
        span: Span::SYNTHETIC,
    };
    let err = tc
        .register_trait_impl_self(&impl_)
        .expect_err("a parenthesized head on a conventional trait is rejected");
    let msg = err.message();
    assert!(msg.contains("conventional"), "names the kind: {msg}");
    assert!(
        msg.contains("bare name"),
        "directs to the bare name form: {msg}"
    );
}

// spec: 07-traits §7.2.3 / §7.3.5 Case 2 — NEGATIVE (the 0628 root). An HK trait
// impl'd on a PRIMITIVE is rejected "not a type constructor" — the clean §7.2
// diagnostic, NOT a backend `undefined function` leak.
#[test]
fn hkt_impl_on_primitive_rejected() {
    let mut tc = tf_prims();
    tc.register_trait_decl_self(&functor_decl()).unwrap();

    let impl_ = functor_impl(
        Some("f"),
        pairing("Functor", "Int"),
        Expr::var(Symbol::from("None"), Span::SYNTHETIC),
    );
    let err = tc
        .register_trait_impl_self(&impl_)
        .expect_err("`(Functor Int)` — a primitive is not a type constructor");
    let msg = err.message();
    assert!(
        msg.contains("not a type constructor"),
        "clean §7.2 diagnostic: {msg}"
    );
    assert!(msg.contains("Int"), "names the offending type: {msg}");
}

// spec: 07-traits §7.3.5 Case 2 — NEGATIVE. A fully-applied type inside the
// pairing `(Functor (Option Int))` is a kind-mismatch: slot 2 names the BARE
// constructor, not an applied type.
#[test]
fn hkt_impl_applied_type_in_pairing_rejected() {
    let mut tc = tf_prims();
    register_option(&mut tc);
    tc.register_trait_decl_self(&functor_decl()).unwrap();

    // target = (Functor (Option Int))
    let target = TypeExpr::Applied(
        cranelisp_types::TypeRef::new(None, TypeName::from("Functor")),
        vec![TypeExpr::Applied(
            cranelisp_types::TypeRef::new(None, TypeName::from("Option")),
            vec![TypeExpr::Named(cranelisp_types::TypeRef::new(
                None,
                TypeName::from("Int"),
            ))],
        )],
    );
    let impl_ = functor_impl(
        Some("f"),
        target,
        Expr::var(Symbol::from("None"), Span::SYNTHETIC),
    );
    let err = tc
        .register_trait_impl_self(&impl_)
        .expect_err("`(Functor (Option Int))` — an applied type is not a bare constructor");
    let msg = err.message();
    assert!(
        msg.contains("kind-mismatch"),
        "names the kind-mismatch: {msg}"
    );
    assert!(
        msg.contains("bare constructor"),
        "directs to the bare constructor: {msg}"
    );
}

// spec: 07-traits §7.2.3 / §7.3.5 Case 2 — NEGATIVE. A wrong-arity constructor
// in the pairing `(Functor Pair)` (Pair : * -> * -> *) is rejected: the trait
// expects a constructor of arity 1.
#[test]
fn hkt_impl_wrong_arity_constructor_rejected() {
    let mut tc = tf_prims();
    register_pair(&mut tc);
    tc.register_trait_decl_self(&functor_decl()).unwrap();

    let impl_ = functor_impl(
        Some("f"),
        pairing("Functor", "Pair"),
        Expr::var(Symbol::from("MkPair"), Span::SYNTHETIC),
    );
    let err = tc
        .register_trait_impl_self(&impl_)
        .expect_err("`(Functor Pair)` — Pair has arity 2, Functor expects 1");
    let msg = err.message();
    assert!(msg.contains("Pair"), "names the constructor: {msg}");
    assert!(msg.contains('2'), "names Pair's arity: {msg}");
    assert!(msg.contains("Functor"), "names the trait: {msg}");
}

// spec: 07-traits §7.3.5 Case 1 — NEGATIVE. A conventional-trait target that is
// a bare / under-applied constructor `(impl Display Option)` is the sole Case-1
// rejection: `Option` is a constructor, not a type — apply it.
#[test]
fn conventional_impl_under_applied_constructor_rejected() {
    let mut tc = tf_prims();
    register_option(&mut tc);
    tc.register_trait_decl_self(&unary_trait_decl("Display", "show"))
        .unwrap();

    let impl_ = TraitImpl {
        head_con_var: None,
        trait_name: TraitRef::new(None, TraitName::from("Display")),
        target: TypeExpr::Named(cranelisp_types::TypeRef::new(
            None,
            TypeName::from("Option"),
        )),
        type_constraints: vec![],
        methods: vec![Defn {
            name: Symbol::from("show"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("lhs"), None), (Symbol::from("rhs"), None)],
                body: Expr::var(Symbol::from("lhs"), Span::SYNTHETIC),
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        }],
        span: Span::SYNTHETIC,
    };
    let err = tc
        .register_trait_impl_self(&impl_)
        .expect_err("`(impl Display Option)` — Option is under-applied");
    let msg = err.message();
    assert!(msg.contains("Option"), "names the constructor: {msg}");
    assert!(
        msg.contains("constructor, not a type"),
        "the §7.3.5 Case 1 diagnostic: {msg}"
    );
    // M2: the fix suggestion is arity-aware — one fresh var per declared param.
    // `Option : * -> *` → `(Option a)`.
    assert!(
        msg.contains("(Option a)"),
        "arity-aware fix suggestion (M2): {msg}"
    );
}

// ===========================================================================
// W5.1 remediation — B1 pairing-head mismatch (§7.3.5 Case-2 4th rejection)
// + I1 conventional over-applied (§7.3.5 Case 1) + M2 arity-aware suggestion.
// Unit twins of the e2e rows in `tests/spec_07_traits.rs`.
// ===========================================================================

/// Build a conventional `(deftrait <name> (shw [self] Int))` decl — bare head,
/// empty `type_params`; a kind-`*` trait whose impl target is a plain type.
fn disp_decl(name: &str) -> TraitDecl {
    parse_trait_decl(&format!("(deftrait {name} (shw [self] Int))"))
}

/// Build a conventional-trait impl `(impl <trait> <target> (defn shw [w] 5))`.
fn disp_impl(trait_name: &str, target: TypeExpr) -> TraitImpl {
    TraitImpl {
        head_con_var: None,
        trait_name: TraitRef::new(None, TraitName::from(trait_name)),
        target,
        type_constraints: vec![],
        methods: vec![Defn {
            name: Symbol::from("shw"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("w"), None)],
                body: Expr::IntLit {
                    value: 5,
                    span: Span::SYNTHETIC,
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

// spec: 07-traits §7.3.5 Case 2 — B1 NEGATIVE. A pairing head naming a
// NONEXISTENT trait `(NotFunctor Option)` is rejected FIRST (before the
// constructor kind-check): the head resolves to no trait, so its FQ ≠ slot-1's
// `Functor` FQ. The diagnostic names BOTH the written `(NotFunctor Option)` and
// the expected `(Functor Option)`; the impl MUST NOT register.
#[test]
fn hkt_impl_pairing_head_nonexistent_trait_rejected() {
    let mut tc = tf_prims();
    register_option(&mut tc);
    tc.register_trait_decl_self(&functor_decl()).unwrap();

    let impl_ = functor_impl(
        Some("f"),
        pairing("NotFunctor", "Option"),
        Expr::var(Symbol::from("None"), Span::SYNTHETIC),
    );
    let err = tc
        .register_trait_impl_self(&impl_)
        .expect_err("`(NotFunctor Option)` — the pairing head names no trait");
    let msg = err.message();
    assert!(
        msg.contains("(NotFunctor Option)"),
        "names the written pairing: {msg}"
    );
    assert!(
        msg.contains("(Functor Option)"),
        "names the expected pairing: {msg}"
    );
    assert!(!tc.has_impl(&TraitName::from("Functor"), &TypeName::from("Option")));
}

// spec: 07-traits §7.3.5 Case 2 — B1 NEGATIVE, the DIFFERENT-real-trait variant.
// A pairing head naming a second GENUINE trait `(Mappy Option)` is rejected: it
// resolves to a trait, but its FQ ≠ slot-1's `Functor` FQ (resolved-identity
// compare, not spelling). Names both pairings; MUST NOT register under Functor.
#[test]
fn hkt_impl_pairing_head_different_real_trait_rejected() {
    let mut tc = tf_prims();
    register_option(&mut tc);
    tc.register_trait_decl_self(&functor_decl()).unwrap();
    // A second genuine HK trait, whose name is the wrong pairing head.
    let mut mappy = functor_decl();
    mappy.name = TraitName::from("Mappy");
    mappy.methods[0].name = Symbol::from("mapp");
    tc.register_trait_decl_self(&mappy).unwrap();

    let impl_ = functor_impl(
        Some("f"),
        pairing("Mappy", "Option"),
        Expr::var(Symbol::from("None"), Span::SYNTHETIC),
    );
    let err = tc
        .register_trait_impl_self(&impl_)
        .expect_err("`(Mappy Option)` — a different real trait as the pairing head");
    let msg = err.message();
    assert!(
        msg.contains("(Mappy Option)"),
        "names the written pairing: {msg}"
    );
    assert!(
        msg.contains("(Functor Option)"),
        "names the expected pairing: {msg}"
    );
    assert!(!tc.has_impl(&TraitName::from("Functor"), &TypeName::from("Option")));
}

// spec: 07-traits §7.3.5 Case 2 — B1 POSITIVE. The matching pairing head
// `(Functor Option)` on a correctly-echoed `(Functor f)` head registers — the
// FQ-identity compare passes (this is the twin the two rejections flank).
// (Same as `hkt_impl_correct_echo_and_pairing_accepts`; kept as the explicit
// B1-axis positive.)
#[test]
fn hkt_impl_pairing_head_matches_slot1_accepts() {
    let mut tc = tf_prims();
    register_option(&mut tc);
    tc.register_trait_decl_self(&functor_decl()).unwrap();

    let impl_ = functor_impl(
        Some("f"),
        pairing("Functor", "Option"),
        Expr::var(Symbol::from("None"), Span::SYNTHETIC),
    );
    tc.register_trait_impl_self(&impl_)
        .expect("matching pairing head `(Functor Option)` must register");
    assert!(tc.has_impl(&TraitName::from("Functor"), &TypeName::from("Option")));
}

// ===========================================================================
// S112 R-1 (TB-25) — the pairing head's WRITTEN QUALIFIER participates in the
// resolve. `(Trait Constructor)`'s head is a §8.5 trait reference; the B1
// FQ-identity compare is against the head resolved WITH its `pairing_head.module`,
// never the bare name. Resolved identity, not spelling, governs (§7.3.5
// *Pairing-head identity*, spec scribed 2026-07-18). Three cells:
//   (a) qualified head with a BAD module   → unresolvable → reject;
//   (b) qualified head resolving to slot-1's trait (differing spelling) → ACCEPT;
//   (c) qualified head to a DIFFERENT same-named trait in another module → reject.
// ===========================================================================

/// `(module/Trait Constructor)` — a QUALIFIED pairing head (slot 2 of an HK
/// impl), carrying `pairing_head.module = Some(module)`.
fn pairing_qualified(module: &str, trait_name: &str, con: &str) -> TypeExpr {
    TypeExpr::Applied(
        cranelisp_types::TypeRef::new(
            Some(ModuleFullPath::from(module)),
            TypeName::from(trait_name),
        ),
        vec![TypeExpr::Named(cranelisp_types::TypeRef::new(
            None,
            TypeName::from(con),
        ))],
    )
}

// spec: 07-traits §7.3.5 Case 2 / *Pairing-head identity* — R-1 NEGATIVE (a).
// A qualified pairing head naming a NONEXISTENT module `(nosuchmod/Functor
// Option)` resolves — with its written qualifier — to no trait: FQ ≠ slot-1's
// `Functor` FQ. Pre-R-1 the qualifier was DROPPED and bare `Functor` resolved,
// silently ACCEPTING. Now it is a clean located reject naming the written
// qualified spelling and the expected pairing; the impl MUST NOT register.
#[test]
fn hkt_impl_pairing_head_qualified_bad_module_rejected() {
    let mut tc = tf_prims();
    register_option(&mut tc);
    tc.register_trait_decl_self(&functor_decl()).unwrap();

    let impl_ = functor_impl(
        Some("f"),
        pairing_qualified("nosuchmod", "Functor", "Option"),
        Expr::var(Symbol::from("None"), Span::SYNTHETIC),
    );
    let err = tc
        .register_trait_impl_self(&impl_)
        .expect_err("`(nosuchmod/Functor Option)` — the qualified head resolves to no trait");
    let msg = err.message();
    assert!(
        msg.contains("(nosuchmod/Functor Option)"),
        "names the written QUALIFIED pairing (qualifier participates): {msg}"
    );
    assert!(
        msg.contains("(Functor Option)"),
        "names the expected pairing: {msg}"
    );
    assert!(!tc.has_impl(&TraitName::from("Functor"), &TypeName::from("Option")));
}

// spec: 07-traits §7.3.5 *Pairing-head identity* — R-1 POSITIVE (b). Slot 1 is
// bare `Functor` IMPORTED from module `fmt`; the pairing head is the QUALIFIED
// `fmt/Functor`. The two spellings differ but resolve to the SAME trait
// (`fmt/Functor`), so the resolved-identity compare ACCEPTS (TB-25 — valid
// references to the same thing are the same thing, whatever the syntax). This is
// the cell the qualifier-drop bug would still pass (bare `Functor` also resolves
// to `fmt/Functor` via the import) — kept as the explicit qualified-spelling
// positive so the resolve honours `Some(module)` rather than ignoring it.
#[test]
fn hkt_impl_pairing_head_qualified_resolves_to_slot1_accepts() {
    let mut tc = tf_prims();
    let fmt = ModuleFullPath::from("fmt");
    let user = ModuleFullPath::from("user");

    // `Functor` lives in `fmt`; `user` (the writer) imports it bare.
    tc.set_current_module(fmt.clone());
    tc.register_trait_decl_self(&functor_decl()).unwrap();
    tc.set_current_module(user.clone());
    seed_glob_import(&mut tc, &fmt);
    register_option(&mut tc);

    // Slot 1 bare `Functor` (→ fmt/Functor via import); pairing head qualified
    // `fmt/Functor` (module: Some("fmt")). Both resolve to fmt/Functor.
    let impl_ = functor_impl(
        Some("f"),
        pairing_qualified("fmt", "Functor", "Option"),
        Expr::var(Symbol::from("None"), Span::SYNTHETIC),
    );
    tc.register_trait_impl_self(&impl_)
        .expect("qualified `fmt/Functor` resolves to slot-1's imported `Functor` — must register");
    assert!(tc.has_impl(&TraitName::from("Functor"), &TypeName::from("Option")));
}

// spec: 07-traits §7.3.5 *Pairing-head identity* — R-1 NEGATIVE (c), the cell
// the qualifier fix is LOAD-BEARING for. Slot 1 resolves to `user/Functor`; a
// SECOND, same-named `Functor` trait lives in module `other`. The pairing head
// is qualified `other/Functor`. Same bare spelling as slot 1, but the qualifier
// routes to `other/Functor` — a DIFFERENT FQ. Pre-R-1 the qualifier was dropped,
// bare `Functor` resolved to `user/Functor`, and the impl silently ACCEPTED
// under the wrong trait; now the qualified resolve makes FQ ≠ slot-1's: reject.
#[test]
fn hkt_impl_pairing_head_qualified_different_module_trait_rejected() {
    let mut tc = tf_prims();
    let other = ModuleFullPath::from("other");
    let user = ModuleFullPath::from("user");

    register_option(&mut tc);
    tc.register_trait_decl_self(&functor_decl()).unwrap(); // user/Functor (slot 1)

    // A DIFFERENT, same-named `Functor` in `other`.
    tc.set_current_module(other.clone());
    tc.register_trait_decl_self(&functor_decl()).unwrap(); // other/Functor
    tc.set_current_module(user.clone());

    let impl_ = functor_impl(
        Some("f"),
        pairing_qualified("other", "Functor", "Option"),
        Expr::var(Symbol::from("None"), Span::SYNTHETIC),
    );
    let err = tc
        .register_trait_impl_self(&impl_)
        .expect_err("`(other/Functor Option)` — a different-module same-named trait");
    let msg = err.message();
    assert!(
        msg.contains("(other/Functor Option)"),
        "names the written QUALIFIED pairing (qualifier routes to `other`): {msg}"
    );
    assert!(
        msg.contains("(Functor Option)"),
        "names the expected pairing: {msg}"
    );
    assert!(!tc.has_impl(&TraitName::from("Functor"), &TypeName::from("Option")));
}

// spec: 07-traits §7.3.5 Case 1 — I1 NEGATIVE. An OVER-applied conventional
// target `(Disp (Option Int Int))` applies `Option` (arity 1) to 2 args. The
// `!=` arity guard rejects with "takes 1 type parameter but is applied to 2";
// the fix suggestion is arity-aware (M2, `(Option a)`). MUST NOT register.
#[test]
fn conventional_impl_over_applied_target_rejected() {
    let mut tc = tf_prims();
    register_option(&mut tc);
    tc.register_trait_decl_self(&disp_decl("Disp")).unwrap();

    let target = TypeExpr::Applied(
        cranelisp_types::TypeRef::new(None, TypeName::from("Option")),
        vec![
            TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int"))),
            TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int"))),
        ],
    );
    let err = tc
        .register_trait_impl_self(&disp_impl("Disp", target))
        .expect_err("`(Option Int Int)` over-applies Option (arity 1)");
    let msg = err.message();
    assert!(
        msg.contains("1 type parameter"),
        "names the declared arity: {msg}"
    );
    assert!(
        msg.contains("applied to 2"),
        "names the arity surplus: {msg}"
    );
    assert!(
        msg.contains("(Option a)"),
        "arity-aware fix suggestion (M2): {msg}"
    );
    assert!(!tc.has_impl(&TraitName::from("Disp"), &TypeName::from("Option")));
}

// spec: 07-traits §7.3.5 Case 1 — I1 POSITIVE (the exactly-arity fence). A
// target applied to EXACTLY its arity `(Disp (Option Int))` registers and stays
// green when `>` generalises to `!=` (`provided == arity == 1`, so `!=` never
// fires) — the guard-generalisation hazard fence.
#[test]
fn conventional_impl_exactly_arity_target_accepts() {
    let mut tc = tf_prims();
    // This impl ACCEPTS and proceeds to method-body checking, whose return type
    // is `Int` — glob primitives into the current module so `Int` (and the
    // target arg `Int`) resolve.
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    register_option(&mut tc);
    tc.register_trait_decl_self(&disp_decl("Disp")).unwrap();

    let target = TypeExpr::Applied(
        cranelisp_types::TypeRef::new(None, TypeName::from("Option")),
        vec![TypeExpr::Named(cranelisp_types::TypeRef::new(
            None,
            TypeName::from("Int"),
        ))],
    );
    tc.register_trait_impl_self(&disp_impl("Disp", target))
        .expect("`(Option Int)` applies Option to exactly its arity — must register");
    assert!(tc.has_impl(&TraitName::from("Disp"), &TypeName::from("Option")));
}

// spec: hkt.md §5.4 M2 — the arity-aware fix-suggestion template. One fresh
// type-var per declared parameter, in `a, b, c, …` order.
#[test]
fn arity_var_suggestion_is_arity_aware() {
    use super::arity_var_suggestion;
    assert_eq!(arity_var_suggestion("Option", 1), "(Option a)");
    assert_eq!(arity_var_suggestion("Pair", 2), "(Pair a b)");
    assert_eq!(arity_var_suggestion("Tri", 3), "(Tri a b c)");
}
