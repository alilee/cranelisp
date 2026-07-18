//! Shared `#[cfg(test)]` fixture + assertion helpers for the `traits/`
//! per-submodule test modules (S102 FIXME 0497 de-pool). These were the
//! module-level helpers of the former pooled `traits/tests.rs`; they are
//! relocated verbatim (content-unchanged, only `pub(crate)`-exposed) so the
//! per-seam sibling test modules (`registry/tests.rs`, `impl_check/tests.rs`,
//! `dispatch/tests.rs`, `monomorphise/tests.rs`, `type_resolve/tests.rs`) can
//! each reach them without duplicating fixtures — per METHOD §2.2 / Principle 23.

use crate::builtins::FixtureBuilder;
use crate::checker::TestFixture;
use cranelisp_types::{
    Defn, DefnVariant, Expr, FQSymbol, FQTraitName, FQTypeName, ModuleEntry,
    ModuleFullPath, Span, Symbol, TraitDecl, TraitImpl, TraitMethodSig, TraitName,
    TypeExpr, TypeName, Visibility,
};

/// Empty fixture (FIXME 0243 narrowing). For the startup-negative tests
/// that assert NOTHING is registered (no traits / no impls / no operators)
/// — the empty builder is the most honest starting position for "nothing
/// seeded" and also the minimal one.
pub(crate) fn tf() -> TestFixture {
    TestFixture::with_content(FixtureBuilder::new())
}

/// Fixture seeding builtin type names + the Ring 0/1/3 primitive `Def`s
/// (FIXME 0243 narrowing). The trait-decl / trait-impl / resolution tests
/// register impls whose `target` is `Int` (needs the builtin type name in
/// scope) and whose method bodies call `add-i64` (needs the primitive
/// `Def`). This is the minimal preset those tests consume — `full()`'s
/// special forms, `macros` module, and IO ADT are not touched. `with_io()`
/// is omitted; `with_primitives()` requires `with_builtin_type_names()`
/// first (bootstrap order).
pub(crate) fn tf_prims() -> TestFixture {
    TestFixture::with_content(
        FixtureBuilder::new().with_builtin_type_names().with_primitives(),
    )
}

/// Seed glob-import edges from `source` into the fixture's CURRENT module,
/// mirroring `(import [source [*]])`. Import registration is no longer a
/// typecheck concern (facade `typecheck.md`); tests seed the edges
/// directly. Inserts an `Import` for every public symbol of `source`.
pub(crate) fn seed_glob_import(tc: &mut TestFixture, source: &ModuleFullPath) {
    let names: Vec<Symbol> = {
        let src = tc.modules.get(source).expect("source module exists");
        src.all_symbols()
            .filter(|(_, e)| e.is_public())
            .map(|(n, _)| n.clone())
            .collect()
    };
    for name in names {
        tc.symbol_table_mut().insert(
            name.clone(),
            ModuleEntry::Import {
                source: FQSymbol { module: source.clone(), symbol: name },
                visibility: Visibility::Public,
            },
        );
    }
}

/// Test helper: create an FQTraitName in the "test" module.
pub(crate) fn test_fqtn_trait(name: &str) -> FQTraitName {
    FQTraitName::new(ModuleFullPath::from("test"), TraitName::from(name))
}

/// Test helper: create an FQTypeName in the "test" module.
pub(crate) fn test_fqtn(name: &str) -> FQTypeName {
    FQTypeName::new(ModuleFullPath::from("test"), TypeName::from(name))
}

/// Create a TypeChecker with primitives imported into a "test" module.
/// Narrowed (FIXME 0243) from `TestFixture::new()` (= `full()`) to the
/// builtin-type-names + primitives content the dependent tests consume.
pub(crate) fn tc_with_prims() -> TestFixture {
    let mut tc = tf_prims();
    tc.set_current_module(ModuleFullPath::from("test"));
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    tc
}

/// Make a test-only trait decl (not conflicting with builtins).
pub(crate) fn make_test_trait_decl() -> TraitDecl {
    TraitDecl {
        name: TraitName::from("TestTrait"),
        docstring: None,
        type_params: vec![Symbol::from("a")],
        methods: vec![
            TraitMethodSig {
                name: Symbol::from("test-op"),
                docstring: None,
                params: vec![
                    (Symbol::from("lhs"), TypeExpr::TypeVar(Symbol::from("a"))),
                    (Symbol::from("rhs"), TypeExpr::TypeVar(Symbol::from("a"))),
                ],
                ret_type: TypeExpr::TypeVar(Symbol::from("a")),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_body: None,
            },
        ],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    }
}

/// Nullary trait decl whose only method `z` takes no params and returns
/// `Self` — the return-type-polymorphic shape (`(deftrait T (z [] self))`,
/// `(default)`, `(zero)`, `(empty)`). There is no argument to dispatch on.
pub(crate) fn make_nullary_return_poly_trait_decl() -> TraitDecl {
    TraitDecl {
        name: TraitName::from("NullaryRP"),
        docstring: None,
        type_params: vec![],
        methods: vec![TraitMethodSig {
            name: Symbol::from("z"),
            docstring: None,
            params: vec![],
            ret_type: TypeExpr::SelfType,
            span: Span::SYNTHETIC,
            hkt_param_index: None,
            default_body: None,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    }
}

/// Register the nullary `NullaryRP` trait + an `Int` impl `(defn z [] 0)`.
pub(crate) fn register_nullary_rp_int_impl(tc: &mut TestFixture) {
    tc.register_trait_decl_self(&make_nullary_return_poly_trait_decl())
        .unwrap();
    let impl_ = TraitImpl {
        head_con_var: None,
        trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("NullaryRP")),
        target: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int"))),
        type_constraints: vec![],
        methods: vec![Defn {
            name: Symbol::from("z"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: cranelisp_types::Expr::IntLit {
                    value: 0,
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
    tc.register_trait_impl_self(&impl_).unwrap();
}

/// Helper: check that an expr is `Apply { callee: Var(name), .. }`
pub(crate) fn assert_apply_callee(expr: &Expr, expected_name: &str) {
    if let Expr::Apply { callee, .. } = expr {
        if let Expr::Var { name, .. } = callee.as_ref() {
            assert_eq!(name.as_ref(), expected_name);
            return;
        }
    }
    panic!("expected Apply with callee Var({expected_name}), got {expr:?}");
}

/// Helper: extract Apply args
pub(crate) fn apply_args(expr: &Expr) -> &[Expr] {
    if let Expr::Apply { args, .. } = expr {
        args.as_slice()
    } else {
        panic!("expected Apply, got {expr:?}");
    }
}

/// Helper: assert Var with given name
pub(crate) fn assert_var(expr: &Expr, expected: &str) {
    if let Expr::Var { name, .. } = expr {
        assert_eq!(name.as_ref(), expected);
    } else {
        panic!("expected Var({expected}), got {expr:?}");
    }
}

/// Register a minimal `Num` trait with `+` and an impl for Int
/// (identical in intent to `program::tests::register_num_trait_inline`, but
/// kept local to the traits test module so we don't cross test-module boundaries).
pub(crate) fn register_num_for_int(tc: &mut TestFixture) {
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
                body: cranelisp_types::Expr::Apply {
                    callee: Box::new(cranelisp_types::Expr::var(Symbol::from("add-i64"), Span::SYNTHETIC)),
                    args: vec![
                        cranelisp_types::Expr::var(Symbol::from("x"), Span::SYNTHETIC),
                        cranelisp_types::Expr::var(Symbol::from("y"), Span::SYNTHETIC),
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
}

/// Register an `impl Num for Float` (`(defn + [x y] (add-f64 x y))`) on a
/// fixture that already carries the `Num` decl (via [`register_num_for_int`]).
/// Used by the ≥2-instantiations mono-mint matrix cell (0497 step ii) so a
/// `(add 1.5 2.5)` call site can resolve `+` to the Float impl and mint a
/// second, distinct mono instance alongside `add$Int+Int`.
pub(crate) fn register_num_impl_for_float(tc: &mut TestFixture) {
    let impl_ = TraitImpl {
        head_con_var: None,
        trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Num")),
        target: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Float"))),
        type_constraints: vec![],
        methods: vec![Defn {
            name: Symbol::from("+"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                body: cranelisp_types::Expr::Apply {
                    callee: Box::new(cranelisp_types::Expr::var(Symbol::from("add-f64"), Span::SYNTHETIC)),
                    args: vec![
                        cranelisp_types::Expr::var(Symbol::from("x"), Span::SYNTHETIC),
                        cranelisp_types::Expr::var(Symbol::from("y"), Span::SYNTHETIC),
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
}

/// Walk an Expr tree and visit every inferred_type, asserting it is concrete.
pub(crate) fn assert_types_concrete(expr: &cranelisp_types::Expr) {
    if let Some(ty) = expr.inferred_type() {
        assert!(
            !ty.contains_var(),
            "inferred_type should be concrete, got Var at span {:?}: {:?}",
            expr.span(),
            ty
        );
    }
    use cranelisp_types::Expr as E;
    match expr {
        E::Apply { callee, args, .. } => {
            assert_types_concrete(callee);
            for a in args {
                assert_types_concrete(a);
            }
        }
        E::Let { bindings, body, .. } | E::ParBind { bindings, body, .. } => {
            for (_, b) in bindings {
                assert_types_concrete(b);
            }
            assert_types_concrete(body);
        }
        E::If { cond, then_branch, else_branch, .. } => {
            assert_types_concrete(cond);
            assert_types_concrete(then_branch);
            assert_types_concrete(else_branch);
        }
        E::Lambda { body, .. }
        | E::Annotate { expr: body, .. }
        | E::Trace { body, .. } => {
            assert_types_concrete(body);
        }
        E::Match { scrutinee, arms, .. } => {
            assert_types_concrete(scrutinee);
            for arm in arms {
                assert_types_concrete(&arm.body);
            }
        }
        E::VecLit { elements, .. } => {
            for e in elements {
                assert_types_concrete(e);
            }
        }
        _ => {}
    }
}
