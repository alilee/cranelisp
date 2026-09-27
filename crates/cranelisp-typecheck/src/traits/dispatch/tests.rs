//! Per-submodule test module for `dispatch.rs` (S102 FIXME 0497 de-pool —
//! relocated verbatim from the pooled `traits/primitive_dispatch_tests.rs`,
//! content-unchanged, now a sibling of the code it exercises so attribution is
//! structural, per METHOD §2.2 / Principle 23).

use cranelisp_types::{
    CranelispError, Defn, DefnVariant, Expr, ResolvedCall, Span, Symbol, TraitImpl, TraitName,
    Type, TypeExpr, TypeName, Visibility,
};

use super::*;
use crate::checker::TestFixture;
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
        impl_module,
    }) = result
    {
        assert_eq!(trait_name.name.as_ref(), "TestTrait");
        assert_eq!(method_name.as_ref(), "test-op");
        assert_eq!(impl_type.name.as_ref(), "Int");
        // S102 4th lossy-head cure: the `$Type` suffix carries FQ nominal
        // identity (`primitives/Int`), lock-step with the definition side.
        assert_eq!(mangled_name.as_ref(), "TestTrait.test-op$primitives/Int");
        // S110 W0.1b (§1.1.1): the carrier's storage module is the impl-writer's
        // module, read off the `TraitImpl` shell. `tc_with_prims` sets the
        // fixture's current module to `test`, where both trait + impl are
        // written, so the same-module storage is `test`.
        assert_eq!(impl_module.as_ref(), "test");
    }
}

// spec: design/arch/backend-keyed-consumer.md §1.1.1 — a CROSS-module trait
// method call records the impl-WRITER's module (read off the `TraitImpl`
// shell), NOT the caller's `current_module`. The pin inserts a shell whose
// `impl_module` is a third module ("writermod") distinct from both the trait's
// home ("test") and the resolving `current_module` ("test"); a correct read
// yields "writermod", the pre-W0.1b bug yielded "test".
#[test]
fn resolved_target_cross_module_trait_method_records_impl_writer_module() {
    let mut tc = tc_with_prims();
    let decl = make_test_trait_decl();
    tc.register_trait_decl_self(&decl).unwrap();

    // Insert the discovery shell into the trait's home ("test") with an
    // `impl_module` pointing at a distinct writer module, keyed by the
    // receiver's identity `primitives/Int`. (The writer module carries the
    // mangled method Defs in production.)
    let record = cranelisp_types::WrittenTraitImpl::new(
        cranelisp_types::FQTraitName::new(
            cranelisp_types::ModuleFullPath::from("test"),
            TraitName::from("TestTrait"),
        ),
        cranelisp_types::FQTypeName::new(
            cranelisp_types::ModuleFullPath::from("primitives"),
            TypeName::from("Int"),
        ),
        cranelisp_types::ModuleFullPath::from("writermod"),
        vec![Symbol::from("test-op")],
        Visibility::Public,
    );
    tc.symbol_table_mut()
        .stage_trait_impl_shell(&record)
        .unwrap()
        .commit();

    let result = tc
        .try_resolve_trait_method_self(
            &Symbol::from("test-op"),
            &[Type::Int, Type::Int],
            Span::SYNTHETIC,
        )
        .expect("should not error");
    match result {
        Some(ResolvedCall::TraitMethod {
            impl_module,
            mangled_name,
            ..
        }) => {
            assert_eq!(
                impl_module.as_ref(),
                "writermod",
                "carrier must name the impl-writer's module, not current_module"
            );
            assert_eq!(mangled_name.as_ref(), "TestTrait.test-op$primitives/Int");
        }
        other => panic!("expected a TraitMethod resolution, got {other:?}"),
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
            // S87-1: the trait renders fully-qualified (`user/TestTrait`); the
            // bare primitive `Bool` is not a resolvable type-def in this bare
            // fixture, so the type half best-effort-falls-back to the bare name.
            assert!(
                message.contains("no impl of trait user/TestTrait for type Bool"),
                "{message}"
            );
        }
        other => panic!("expected TypeError, got {other:?}"),
    }
}

// spec: 07-traits §7.4.3 — S87-1: the "no impl" diagnostic renders the impl
// TYPE fully-qualified so a missing impl under two same-named ADTs from
// different modules is disambiguable (`user/Widget` vs a would-be
// `other/Widget`), not an undifferentiated bare `Widget`.
#[test]
fn no_impl_diagnostic_renders_type_fully_qualified() {
    use cranelisp_types::{ConstructorDef, FQTypeName, ModuleFullPath};

    let mut tc = tf_prims();
    tc.register_trait_decl_self(&make_test_trait_decl())
        .unwrap();
    // Register a `Widget` ADT in the current (`user`) module so the type name
    // resolves to its FQ identity `user/Widget`.
    tc.register_type_def_self(
        &TypeName::from("Widget"),
        &None,
        &[],
        &[ConstructorDef {
            name: Symbol::from("Widget"),
            docstring: None,
            fields: vec![],
            span: Span::SYNTHETIC,
        }],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();

    let widget = Type::ADT(
        FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Widget")),
        vec![],
    );
    // No impl of TestTrait for Widget is registered.
    let err = tc
        .try_resolve_trait_method_self(
            &Symbol::from("test-op"),
            &[widget.clone(), widget],
            Span::SYNTHETIC,
        )
        .expect_err("missing impl must be a type error");
    match err {
        CranelispError::TypeError { message, .. } => {
            assert!(
                message.contains("user/Widget"),
                "type half must be module-qualified for same-named-ADT disambiguation: {message}"
            );
            assert!(
                message.contains("user/TestTrait"),
                "trait half must be module-qualified: {message}"
            );
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
        ResolvedCall::TraitMethod {
            method_name,
            impl_type,
            mangled_name,
            ..
        } => {
            assert_eq!(method_name.as_ref(), "z");
            assert_eq!(impl_type.name.as_ref(), "Int");
            assert_eq!(mangled_name.as_ref(), "NullaryRP.z$primitives/Int");
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
    let result = tc.try_resolve_trait_method_self(&Symbol::from("z"), &[], Span::new(20, 23));
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
    let num_decl = parse_trait_decl("(deftrait Num (+ [lhs rhs] self))");
    tc.register_trait_decl_self(&num_decl).unwrap();

    // Register impl Num for Int
    let impl_ = TraitImpl {
        head_con_var: None,
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

    let result = tc
        .try_resolve_trait_method_self(&Symbol::from("+"), &[Type::Int, Type::Int], Span::SYNTHETIC)
        .expect("should not error");
    assert!(result.is_some());
    // NOTE: `Num.+`/Int hits the primitive short-circuit → `BuiltinFn`, so this
    // arm is not taken; kept FQ-consistent for the day the path changes.
    if let Some(ResolvedCall::TraitMethod { mangled_name, .. }) = result {
        assert_eq!(mangled_name.as_ref(), "Num.+$primitives/Int");
    }
}

// ===========================================================================
// S102 — trait-method FQ-key mangle (4th lossy-head cure). Strategy-matrix
// unit cells for `mangle_trait_method` (the shared mint used by BOTH the
// dispatch site here and the definition/writeback site in `impl_check`) and
// the receiver identity it mangles with (`receiver_identity`). The collision
// + lock-step cells are written FAILING-FIRST against the pre-cure bare-head
// grammar (they would collide/diverge under `$Widget`).
//
// spec: spec/07-traits.md §7.4 (mangled `Trait.method$Type`) respecting
// spec/03-types.md §3.8.4 (nominal, fully-qualified type identity).
// ===========================================================================

fn fqtn(module: &str, name: &str) -> cranelisp_types::FQTypeName {
    cranelisp_types::FQTypeName::new(
        cranelisp_types::ModuleFullPath::from(module),
        TypeName::from(name),
    )
}

// (a) FQ-qualified + (d) ordinary single-home regression pin: the `$Type`
// suffix is the home-qualified head `module/Type`, stable for the common case.
// spec: spec/07-traits.md §7.4 — mangled name carries the impl type identity.
#[test]
fn mangle_trait_method_carries_fq_home_qualified_head() {
    let m = crate::traits::mangle_trait_method("Show", "show", &fqtn("primitives", "Int"));
    assert_eq!(m, "Show.show$primitives/Int");
    // A user single-home ADT stays stable and unambiguous too.
    let u = crate::traits::mangle_trait_method("Describe", "describe", &fqtn("user", "Point"));
    assert_eq!(u, "Describe.describe$user/Point");
}

// (c) COLLISION cell — the crux, FAILING-FIRST on the bare-head grammar. Two
// DISTINCT nominal types with the SAME bare name from DIFFERENT modules
// (`a/Widget` ≠ `b/Widget`, §3.8.4) MUST mint DISTINCT dispatch/definition
// symbols. Pre-cure both collapsed to `Describe.describe$Widget` (equal →
// silent wrong dispatch).
// spec: spec/03-types.md §3.8.4 — same bare name, different module ⇒ distinct.
#[test]
fn mangle_trait_method_distinct_for_same_bare_name_different_home() {
    let a = crate::traits::mangle_trait_method("Describe", "describe", &fqtn("a", "Widget"));
    let b = crate::traits::mangle_trait_method("Describe", "describe", &fqtn("b", "Widget"));
    assert_eq!(a, "Describe.describe$a/Widget");
    assert_eq!(b, "Describe.describe$b/Widget");
    assert_ne!(
        a, b,
        "same-bare-name-different-home types must not collide (§3.8.4)"
    );
}

// (b-support) The receiver identity of an ADT is its OWN `FQTypeName`; no
// caller-scope or trait-home re-resolution of the bare head participates, so
// a caller-local or home-local same-named type cannot capture the dispatch.
// spec: spec/03-types.md §3.8.4 — receiver identity is authoritative.
#[test]
fn receiver_identity_of_adt_is_its_own_home() {
    let got = receiver_identity(&Type::ADT(fqtn("a", "Widget"), vec![]));
    assert_eq!(got, Some(fqtn("a", "Widget")));
}

// (b-support, scalar) A built-in scalar's identity is its canonical
// `primitives` home, where bootstrap installs it (spec §8.9.1); a non-nominal
// head has none.
// spec: spec/07-traits.md §7.4 — intrinsic impl-type dispatch.
#[test]
fn receiver_identity_of_scalar_is_primitives_and_non_nominal_has_none() {
    assert_eq!(
        receiver_identity(&Type::Int),
        Some(fqtn("primitives", "Int"))
    );
    assert_eq!(
        receiver_identity(&Type::Bool),
        Some(fqtn("primitives", "Bool"))
    );
    assert_eq!(receiver_identity(&Type::Var(0)), None);
    assert_eq!(
        receiver_identity(&Type::Fn(vec![Type::Int], Box::new(Type::Int))),
        None
    );
}

// (e) ADT-arg trait-method GRAIN determination: the receiver HEAD is sufficient
// and correct for lock-step. The identity drops the ADT type-args (`Vec Int`
// and `Vec String` both yield the head `primitives/Vec`), MATCHING the
// definition side which names by the impl target head — so the two agree. This
// pins that arg-recursion is NOT applied at this grain (it would break
// lock-step unless impl registration also recursed; out of scope).
// spec: spec/07-traits.md §7.4 — dispatch keyed on the impl (receiver) type.
#[test]
fn receiver_identity_head_grain_drops_type_args() {
    let a =
        receiver_identity(&Type::ADT(fqtn("primitives", "Vec"), vec![Type::Int])).expect("nominal");
    let b = receiver_identity(&Type::ADT(fqtn("primitives", "Vec"), vec![Type::String]))
        .expect("nominal");
    assert_eq!(
        a,
        fqtn("primitives", "Vec"),
        "receiver head only — args dropped"
    );
    assert_eq!(
        a, b,
        "both Vec instantiations share the head key (grain = receiver head)"
    );
    let m = crate::traits::mangle_trait_method("Sizeable", "size", &a);
    assert_eq!(m, "Sizeable.size$primitives/Vec");
}

// (b) LOCK-STEP end-to-end: the dispatch site's minted `mangled_name` MUST equal
// the symbol-table key the DEFINITION side (`register_trait_impl` →
// `finalize_impl_method_writeback`) wrote for the impl method. If the two
// diverged, dispatch would resolve to a symbol with no definition. Non-primitive
// trait (`TestTrait`) so the real mangle path (not the `BuiltinFn`
// short-circuit) is exercised.
// spec: spec/07-traits.md §7.4 — name-path == definition-path invariant.
#[test]
fn dispatch_mangle_equals_definition_writeback_key_lockstep() {
    let mut tc = tc_with_prims();
    let decl = make_test_trait_decl();
    tc.register_trait_decl_self(&decl).unwrap();
    tc.register_trait_impl_self(&test_trait_int_impl()).unwrap();

    let result = tc
        .try_resolve_trait_method_self(
            &Symbol::from("test-op"),
            &[Type::Int, Type::Int],
            Span::SYNTHETIC,
        )
        .expect("should not error");
    let dispatch_key = match result {
        Some(ResolvedCall::TraitMethod { mangled_name, .. }) => mangled_name.as_ref().to_string(),
        other => panic!("expected TraitMethod, got {other:?}"),
    };
    assert_eq!(dispatch_key, "TestTrait.test-op$primitives/Int");
    // The definition side must have written a Def entry under the SAME key.
    // Probe the symbol table directly by exact key: bare-name `lookup` would
    // mis-split the `/` in the FQ suffix as a module separator (the documented
    // `/`-split gotcha), so it is not a valid probe for a mangled key.
    assert!(
        tc.symbol_table().get(dispatch_key.as_str()).is_some(),
        "definition-side writeback must exist under the dispatch key `{dispatch_key}` \
         (lock-step: name-path == definition-path)",
    );
}

/// `(impl TestTrait Int (defn test-op [lhs rhs] (add-i64 lhs rhs)))`.
fn test_trait_int_impl() -> TraitImpl {
    TraitImpl {
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
    }
}

// ===========================================================================
// BN-1 — impl existence is keyed by the receiver's identity
// (`design/typecheck/typecheck.md` §9.1.1). Each twin stages impl shells in
// the trait's home (`test`) and judges receivers that share a bare name but
// not an identity.
//
// spec: spec/07-traits.md §7.3 (an impl is for one type); spec/08-modules.md
// §8.1 and spec/03-types.md §3.8.4 (a type's identity includes its module).
// ===========================================================================

fn test_trait_fq() -> cranelisp_types::FQTraitName {
    cranelisp_types::FQTraitName::new(
        cranelisp_types::ModuleFullPath::from("test"),
        TraitName::from("TestTrait"),
    )
}

/// `TestTrait` declared in `test`, with one impl shell per receiver, each
/// written by `writermod`.
fn trait_home_with_shells(receivers: &[cranelisp_types::FQTypeName]) -> TestFixture {
    let mut tc = tc_with_prims();
    tc.register_trait_decl_self(&make_test_trait_decl())
        .unwrap();
    for receiver in receivers {
        let record = cranelisp_types::WrittenTraitImpl::new(
            test_trait_fq(),
            receiver.clone(),
            cranelisp_types::ModuleFullPath::from("writermod"),
            vec![Symbol::from("test-op")],
            Visibility::Public,
        );
        tc.symbol_table_mut()
            .stage_trait_impl_shell(&record)
            .unwrap()
            .commit();
    }
    tc
}

fn adt(module: &str, name: &str) -> Type {
    Type::ADT(fqtn(module, name), vec![])
}

// spec: spec/07-traits.md §7.3; spec/08-modules.md §8.1 — `a/U`'s impl
// satisfies `a/U` only; same-named `b/U` has none.
#[test]
fn impl_for_same_named_type_in_another_module_does_not_satisfy_trait() {
    let tc = trait_home_with_shells(&[fqtn("a", "U")]);
    let env = tc.env();
    assert_eq!(
        env.trait_satisfaction(&test_trait_fq(), &adt("a", "U")),
        TraitSatisfaction::Satisfied
    );
    assert_eq!(
        env.trait_satisfaction(&test_trait_fq(), &adt("b", "U")),
        TraitSatisfaction::Unsatisfied,
        "`a/U`'s impl must not satisfy `b/U`"
    );
}

// spec: spec/07-traits.md §7.3; spec/08-modules.md §8.9.1 — an impl for an
// ADT named `Int` is not an impl for the scalar `Int`.
#[test]
fn impl_for_adt_named_int_does_not_satisfy_scalar_int() {
    let tc = trait_home_with_shells(&[fqtn("test", "Int")]);
    let env = tc.env();
    assert_eq!(
        env.trait_satisfaction(&test_trait_fq(), &adt("test", "Int")),
        TraitSatisfaction::Satisfied
    );
    assert_eq!(
        env.trait_satisfaction(&test_trait_fq(), &Type::Int),
        TraitSatisfaction::Unsatisfied,
        "`test/Int`'s impl must not satisfy `primitives/Int`"
    );
}

// spec: spec/07-traits.md §7.3; spec/08-modules.md §8.9.1 — an impl for the
// scalar `Int` is not an impl for an ADT named `Int`.
#[test]
fn impl_for_scalar_int_does_not_satisfy_adt_named_int() {
    let tc = trait_home_with_shells(&[fqtn("primitives", "Int")]);
    let env = tc.env();
    assert_eq!(
        env.trait_satisfaction(&test_trait_fq(), &Type::Int),
        TraitSatisfaction::Satisfied
    );
    assert_eq!(
        env.trait_satisfaction(&test_trait_fq(), &adt("test", "Int")),
        TraitSatisfaction::Unsatisfied,
        "`primitives/Int`'s impl must not satisfy `test/Int`"
    );
}

// spec: spec/07-traits.md §7.3, §7.4.3 — dispatch at `b/U` is the located
// no-impl error, not a resolution through `a/U`'s shell; dispatch at `a/U`
// resolves to its own writer.
#[test]
fn dispatch_at_same_named_type_without_impl_is_no_impl_error() {
    let mut tc = trait_home_with_shells(&[fqtn("a", "U")]);
    let located = Span::new(40, 52);
    let err = tc
        .try_resolve_trait_method_self(
            &Symbol::from("test-op"),
            &[adt("b", "U"), adt("b", "U")],
            located,
        )
        .expect_err("`b/U` has no impl of `TestTrait`");
    let CranelispError::TypeError { message, location } = err else {
        panic!("expected a no-impl TypeError, got {err:?}");
    };
    assert!(
        message.contains("no impl of trait test/TestTrait for type"),
        "{message}"
    );
    assert_eq!(location.span, located);

    let resolved = tc
        .try_resolve_trait_method_self(
            &Symbol::from("test-op"),
            &[adt("a", "U"), adt("a", "U")],
            Span::SYNTHETIC,
        )
        .expect("`a/U` has an impl");
    match resolved {
        Some(ResolvedCall::TraitMethod {
            mangled_name,
            impl_module,
            ..
        }) => {
            assert_eq!(mangled_name.as_ref(), "TestTrait.test-op$a/U");
            assert_eq!(impl_module.as_ref(), "writermod");
        }
        other => panic!("expected a TraitMethod resolution, got {other:?}"),
    }
}

// spec: spec/07-traits.md §7.4; spec/08-modules.md §8.9.1 — the trait's home
// declares its own unimplemented ADT named `Int`. Dispatch on the scalar still
// mints the scalar impl's `primitives/Int` symbol, in lock-step with the
// definition-side writeback.
#[test]
fn dispatch_of_scalar_beside_home_local_int_adt_mints_primitives_key_lockstep() {
    let mut tc = tc_with_prims();
    tc.register_trait_decl_self(&make_test_trait_decl())
        .unwrap();
    tc.register_trait_impl_self(&test_trait_int_impl()).unwrap();
    tc.register_type_def_self(
        &TypeName::from("Int"),
        &None,
        &[],
        &[cranelisp_types::ConstructorDef {
            name: Symbol::from("LocalInt"),
            docstring: None,
            fields: vec![],
            span: Span::SYNTHETIC,
        }],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .expect("a home-local ADT may share the spelling `Int`");
    tc.clear_transient_state();

    let result = tc
        .try_resolve_trait_method_self(
            &Symbol::from("test-op"),
            &[Type::Int, Type::Int],
            Span::SYNTHETIC,
        )
        .expect("the scalar impl exists");
    let (mangled_name, impl_type) = match result {
        Some(ResolvedCall::TraitMethod {
            mangled_name,
            impl_type,
            ..
        }) => (mangled_name.as_ref().to_string(), impl_type),
        other => panic!("expected a TraitMethod resolution, got {other:?}"),
    };
    assert_eq!(mangled_name, "TestTrait.test-op$primitives/Int");
    assert_eq!(impl_type, fqtn("primitives", "Int"));
    assert!(
        tc.symbol_table().get(mangled_name.as_str()).is_some(),
        "the definition side wrote `{mangled_name}`"
    );
}
