use super::*;
use crate::builtins::FixtureBuilder;
use crate::checker::TestFixture;
use cranelisp_types::{
    ApplyRef, Binding, Callable, CallableOrigin, ConstructorDef, Life, ModuleFullPath, TraitName,
    VarRef,
};

/// Minimal fixture for the ADT-registration tests (FIXME 0243 narrowing).
///
/// These tests register their OWN ADTs via `register_type_def_self` and,
/// where a constructor field is a builtin scalar (`:Int`/`:Bool`/…), seed
/// the corresponding `primitives` import edge into the user module inline
/// (see `test_register_product_type_with_fields`). None of them consult the
/// heavy `full()` world (special forms, seeded primitives, the `macros`
/// module, the IO ADT). An empty builder is the minimal starting position;
/// `user` is the current module exactly as under `TestFixture::new()`.
fn tf() -> TestFixture {
    TestFixture::with_content(FixtureBuilder::new())
}

/// Minimal fixture for the internal-constructor tests (FIXME 0243
/// narrowing). These consult the seeded `IO` ADT in `primitives` (whose
/// `Bind` constructor carries `internal: true`); `with_io()` seeds it and
/// requires `with_builtin_type_names()` first (bootstrap order — IO's field
/// types reference builtin scalars). Nothing heavier (special forms, the
/// Ring 0/1/3 primitive `Def`s, the `macros` module) is consulted.
fn tf_io() -> TestFixture {
    TestFixture::with_content(FixtureBuilder::new().with_builtin_type_names().with_io())
}

/// Test helper: create an FQTypeName in the "user" module (default current
/// module for both `TestFixture::new()` and the narrowed `tf()`).
fn user_fqtn(name: &str) -> FQTypeName {
    FQTypeName::new(ModuleFullPath::from("user"), TypeName::from(name))
}

fn make_ctor(name: &str) -> ConstructorDef {
    ConstructorDef {
        name: Symbol::from(name),
        docstring: None,
        fields: vec![],
        span: Span::SYNTHETIC,
    }
}

/// Test helper: resolve a constructor by its BARE name to its terminal
/// binding, following a sole same-module name candidate one hop. A sum ctor's
/// binding is keyed `Type.Ctor` (`member_key`) with the bare name exposed as a
/// candidate; a product ctor keeps its bare type-name key directly.
/// Type-agnostic — follows the candidate without knowing the type.
fn ctor_entry<'t>(table: &'t cranelisp_types::SymbolTable, name: &str) -> Option<&'t Binding> {
    if let Some(entry) = table.get(name) {
        return Some(entry);
    }
    let candidates = table.name_candidates(&Symbol::from(name));
    let candidate = candidates.as_slice().first()?;
    (candidates.len() == 1 && candidate.source.module == table.path)
        .then(|| table.get(candidate.source.symbol.as_ref()))
        .flatten()
}

fn ctor_callable<'t>(table: &'t cranelisp_types::SymbolTable, name: &str) -> Option<&'t Callable> {
    let callable = ctor_entry(table, name)?.callable()?;
    matches!(callable.origin, CallableOrigin::Ctor { .. }).then_some(callable)
}

fn is_candidate(table: &cranelisp_types::SymbolTable, name: &str) -> bool {
    table.get(name).is_none() && table.name_candidates(&Symbol::from(name)).len() == 1
}

fn is_ambiguous(table: &cranelisp_types::SymbolTable, name: &str) -> bool {
    table.name_candidates(&Symbol::from(name)).len() > 1
}

fn is_concrete_callable(binding: Option<&Binding>) -> bool {
    matches!(
        binding.and_then(Binding::callable).map(|c| &c.arm.life),
        Some(Life::Concrete { .. })
    )
}

// spec: 05-definitions §5.2.3 — enum type registers constructors in symbol table
#[test]
fn test_register_enum_type() {
    let mut tc = tf();
    tc.register_type_def_self(
        &TypeName::from("Color"),
        &None,
        &[],
        &[make_ctor("Red"), make_ctor("Green"), make_ctor("Blue")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();

    // Type should be registered in symbol table
    assert!(tc.lookup_type_def(&TypeName::from("Color")).is_some());

    // Constructors should be in symbol table
    assert!(ctor_entry(&tc.symbol_table(), "Red").is_some());
    assert!(ctor_entry(&tc.symbol_table(), "Green").is_some());
    assert!(ctor_entry(&tc.symbol_table(), "Blue").is_some());

    // Constructor type lookup
    assert_eq!(
        tc.lookup_constructor_type("Red"),
        Some(TypeName::from("Color"))
    );
}

// spec: 05-definitions §5.2.7 — nullary constructor scheme is ADT type
#[test]
fn test_constructor_scheme_is_adt_type() {
    let mut tc = tf();
    tc.register_type_def_self(
        &TypeName::from("Bool2"),
        &None,
        &[],
        &[make_ctor("True2"), make_ctor("False2")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();

    if let Some(callable) = ctor_callable(&tc.symbol_table(), "True2") {
        let scheme = &callable.arm.scheme;
        assert_eq!(scheme.ty, Type::ADT(user_fqtn("Bool2"), vec![]));
    } else {
        panic!("True2 should be a Constructor entry");
    }
}

// spec: 05-definitions §5.2.2 — polymorphic sum type: None and Some constructors
#[test]
fn test_register_polymorphic_option() {
    let mut tc = tf();
    tc.register_type_def_self(
        &TypeName::from("Option"),
        &None,
        &[Symbol::from("a")],
        &[
            make_ctor("None"),
            ConstructorDef {
                name: Symbol::from("Some"),
                docstring: None,
                fields: vec![cranelisp_types::FieldDef {
                    name: Symbol::from("val"),
                    type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("a")),
                    span: Span::SYNTHETIC,
                }],
                span: Span::SYNTHETIC,
            },
        ],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();

    // None should be polymorphic: forall [a]. (Option a)
    if let Some(callable) = ctor_callable(&tc.symbol_table(), "None") {
        let scheme = &callable.arm.scheme;
        assert_eq!(
            scheme.type_vars.len(),
            1,
            "None should have 1 quantified var"
        );
        match &scheme.ty {
            Type::ADT(name, args) => {
                assert_eq!(name.name.as_ref(), "Option");
                assert_eq!(args.len(), 1);
                assert!(matches!(args[0], Type::Var(_)));
            }
            _ => panic!("None should have ADT type, got {:?}", scheme.ty),
        }
    } else {
        panic!("None should be a Constructor entry");
    }

    // Some should be polymorphic: forall [a]. (Fn [a] (Option a))
    if let Some(callable) = ctor_callable(&tc.symbol_table(), "Some") {
        let scheme = &callable.arm.scheme;
        assert_eq!(
            scheme.type_vars.len(),
            1,
            "Some should have 1 quantified var"
        );
        match &scheme.ty {
            Type::Fn(params, ret) => {
                assert_eq!(params.len(), 1);
                assert!(matches!(params[0], Type::Var(_)));
                match ret.as_ref() {
                    Type::ADT(name, args) => {
                        assert_eq!(name.name.as_ref(), "Option");
                        assert_eq!(args.len(), 1);
                        // The type var in Fn param should match the one in ADT args
                        assert_eq!(params[0], args[0]);
                    }
                    _ => panic!("Some return should be ADT"),
                }
            }
            _ => panic!("Some should have Fn type, got {:?}", scheme.ty),
        }
    } else {
        panic!("Some should be a Constructor entry");
    }

    // spec: 05-definitions §5.2.6 — `val` is payload metadata on the
    // `Some` sum arm. It must not mint either a canonical accessor or a bare
    // resolution candidate; payload extraction is positional `match`.
    let table = tc.symbol_table();
    assert!(
        table.get("Option.val").is_none(),
        "sum payload labels must not mint canonical accessors"
    );
    assert!(
        table.name_candidates(&Symbol::from("val")).is_empty(),
        "sum payload labels must not mint bare candidates"
    );
}

// spec: 05-definitions §5.2.1 — product type constructor is function from fields to ADT
#[test]
fn test_register_product_type_with_fields() {
    // This test's product ctor has `:Int`/`:Bool` fields and seeds the
    // matching `primitives` Import edges inline, so the `Int`/`Bool`
    // IntrinsicType entries must exist in the `primitives` module —
    // `with_builtin_type_names()` seeds them (FIXME 0243: the one adt.rs
    // test that genuinely needs builtin scalar field types in scope).
    let mut tc = TestFixture::with_content(FixtureBuilder::new().with_builtin_type_names());
    // Phase B Part 2b: bare `Int`/`Bool` references in field types
    // require explicit import per Principle 17 (no Tier 2 universe walk).
    // Import registration is no longer a typecheck concern (facade
    // `typecheck.md` §"Import/export registration is not a typecheck
    // concern"); seed the needed `Int`/`Bool` import edges directly into
    // the user module's symbol table, mirroring what the orchestrator's
    // import installer would land.
    {
        let mut user = tc.symbol_table_mut();
        for ty in ["Int", "Bool"] {
            user.expose_candidate(
                Symbol::from(ty),
                cranelisp_types::FQSymbol {
                    module: cranelisp_types::ModuleFullPath::from("primitives"),
                    symbol: Symbol::from(ty),
                },
                Visibility::Public,
            )
            .unwrap();
        }
    }
    tc.register_type_def_self(
        &TypeName::from("Pair"),
        &None,
        &[],
        &[ConstructorDef {
            name: Symbol::from("MkPair"),
            docstring: None,
            fields: vec![
                cranelisp_types::FieldDef {
                    name: Symbol::from("x"),
                    type_expr: cranelisp_types::TypeExpr::Named(cranelisp_types::TypeRef::new(
                        None,
                        TypeName::from("Int"),
                    )),
                    span: Span::SYNTHETIC,
                },
                cranelisp_types::FieldDef {
                    name: Symbol::from("y"),
                    type_expr: cranelisp_types::TypeExpr::Named(cranelisp_types::TypeRef::new(
                        None,
                        TypeName::from("Bool"),
                    )),
                    span: Span::SYNTHETIC,
                },
            ],
            span: Span::SYNTHETIC,
        }],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();

    // MkPair :: (Fn [Int Bool] Pair)
    if let Some(callable) = ctor_callable(&tc.symbol_table(), "MkPair") {
        let scheme = &callable.arm.scheme;
        assert!(scheme.type_vars.is_empty(), "MkPair should be monomorphic");
        assert_eq!(
            scheme.ty,
            Type::Fn(
                vec![Type::Int, Type::Bool],
                Box::new(Type::ADT(user_fqtn("Pair"), vec![]))
            )
        );
    } else {
        panic!("MkPair should be a Constructor entry");
    }

    // Per S70: TypeDefInfo.constructors is Vec<Symbol>; per-ctor metadata
    // (param_names, field types from scheme.ty) lives on the ctor's Def.
    let info = tc.lookup_type_def(&TypeName::from("Pair")).unwrap();
    assert_eq!(info.constructors.len(), 1);
    assert_eq!(info.constructors[0].as_ref(), "MkPair");
    if let Some(callable) = ctor_callable(&tc.symbol_table(), "MkPair") {
        let CallableOrigin::Ctor { field_count, .. } = &callable.origin else {
            unreachable!()
        };
        assert_eq!(*field_count, 2);
        let scheme = &callable.arm.scheme;
        let param_names = &callable.arm.param_names;
        assert_eq!(param_names.len(), 2);
        assert_eq!(param_names[0].as_ref(), "x");
        assert_eq!(param_names[1].as_ref(), "y");
        let field_types = match &scheme.ty {
            Type::Fn(p, _) => p.clone(),
            _ => panic!("MkPair scheme should be Fn"),
        };
        assert_eq!(field_types[0], Type::Int);
        assert_eq!(field_types[1], Type::Bool);
    } else {
        panic!("MkPair should be a Def in symbol table");
    }
}

/// Seed `Int`/`Bool` import edges into the user module so bare scalar field
/// types resolve (mirrors `test_register_product_type_with_fields`).
fn tf_with_scalar_imports() -> TestFixture {
    let tc = TestFixture::with_content(FixtureBuilder::new().with_builtin_type_names());
    {
        let mut user = tc.symbol_table_mut();
        for ty in ["Int", "Bool"] {
            user.expose_candidate(
                Symbol::from(ty),
                cranelisp_types::FQSymbol {
                    module: cranelisp_types::ModuleFullPath::from("primitives"),
                    symbol: Symbol::from(ty),
                },
                Visibility::Public,
            )
            .unwrap();
        }
    }
    tc
}

fn product_int_field(type_name: &str, field: &str) -> ConstructorDef {
    ConstructorDef {
        name: Symbol::from(type_name),
        docstring: None,
        fields: vec![cranelisp_types::FieldDef {
            name: Symbol::from(field),
            type_expr: cranelisp_types::TypeExpr::Named(cranelisp_types::TypeRef::new(
                None,
                TypeName::from("Int"),
            )),
            span: Span::SYNTHETIC,
        }],
        span: Span::SYNTHETIC,
    }
}

// spec: 05-definitions §5.2.6 — Generated Accessors
// (`fixme-0365-field-accessor-dotted.md` §1.6.1). A product field synthesises
// an accessor typed `(Fn [ProductType] FieldType)`, installed concrete under
// the canonical key `Type.field` (`Box.v`); bare `field` is a name candidate
// onto it.
#[test]
fn product_field_synthesises_concrete_accessor() {
    let mut tc = tf_with_scalar_imports();
    tc.register_type_def_self(
        &TypeName::from("Box"),
        &None,
        &[],
        &[product_int_field("Box", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();

    // Canonical `Box.v` is a concrete accessor callable; bare `v` exposes it
    // as its sole candidate.
    assert!(
        is_candidate(&tc.symbol_table(), "v"),
        "bare `v` must expose Box.v as its sole candidate"
    );
    match tc.symbol_table().get("Box.v").and_then(Binding::callable) {
        Some(callable) => {
            assert!(
                matches!(callable.arm.life, Life::Concrete { .. }),
                "accessor `v` must be a concrete UserFn"
            );
            assert!(
                tc.symbol_table()
                    .get("Box.v")
                    .unwrap()
                    .callable_got_slot()
                    .is_some(),
                "accessor needs a GOT slot"
            );
            assert!(
                matches!(callable.arm.life, Life::Concrete { ast: Some(_), .. }),
                "accessor carries a synthesised match body"
            );
            assert_eq!(
                callable.arm.param_names.len(),
                1,
                "accessor takes one parameter"
            );
            let scheme = &callable.arm.scheme;
            // Scheme: (Fn [Box] Int).
            match &scheme.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params.len(), 1);
                    assert_eq!(params[0], Type::ADT(user_fqtn("Box"), vec![]));
                    assert_eq!(ret.as_ref(), &Type::Int);
                }
                other => panic!("accessor scheme must be Fn, got {other:?}"),
            }
        }
        other => panic!("canonical Box.v must be a Def, got {other:?}"),
    }
}

// spec: 05-definitions §5.2.6 — accessor synthesis over an existing
// NON-accessor binding is retained alongside the accessor candidate. The
// canonical accessor remains independently addressable as `Box.v`.
#[test]
fn accessor_candidate_coexists_with_nonaccessor_binding() {
    let mut tc = tf_with_scalar_imports();
    // Seed a user binding `v` (a NotDetermined UserFn) BEFORE the deftype.
    tc.symbol_table_mut()
        .declare(
            Symbol::from("v"),
            Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Int,
            },
            vec![],
            None,
            0,
            CallableOrigin::Plain,
            Visibility::Public,
        )
        .unwrap();
    tc.register_type_def_self(
        &TypeName::from("Box"),
        &None,
        &[],
        &[product_int_field("Box", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();

    // The existing local binding is unchanged and the accessor is retained as
    // another candidate under the bare spelling.
    match tc.symbol_table().get("v").and_then(Binding::callable) {
        Some(callable) => assert!(
            matches!(callable.arm.life, Life::Declared { .. }),
            "existing non-accessor `v` must be preserved, not overwritten"
        ),
        other => panic!("`v` must still be the user binding, got {other:?}"),
    }
    let candidates = tc.symbol_table().name_candidates(&Symbol::from("v"));
    assert_eq!(candidates.len(), 2, "local v plus canonical Box.v");
    assert!(
        candidates
            .iter()
            .any(|candidate| candidate.source.symbol.as_ref() == "Box.v")
    );
}

// spec: 05-definitions §5.2.6 "Duplicate field names in the same scope" +
// 08-modules §8.6.5 — two product types with the same field name leave the
// bare spelling with two candidates, NOT a silently-picked winner; a use
// that context does not settle is ambiguous. The second deftype is not
// rejected as a duplicate definition, and both canonical accessors stay
// reachable. The owning types are recorded as the qualified alternatives the
// ambiguity error lists.
#[test]
fn cross_type_duplicate_field_poisons_bare_accessor() {
    let mut tc = tf_with_scalar_imports();
    tc.register_type_def_self(
        &TypeName::from("Box"),
        &None,
        &[],
        &[product_int_field("Box", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();

    // Before the collision, bare `v` exposes the canonical `Box.v` as its sole
    // candidate; `Box.v` is the real concrete accessor.
    assert!(
        is_candidate(&tc.symbol_table(), "v"),
        "single-type bare `v` exposes only Box.v before any collision"
    );
    assert!(
        matches!(
            tc.symbol_table()
                .get("Box.v")
                .and_then(Binding::callable)
                .map(|c| &c.arm.life),
            Some(Life::Concrete { .. })
        ),
        "canonical Box.v is the concrete UserFn accessor"
    );

    // The SECOND deftype with the same field name MUST NOT be rejected as a
    // duplicate definition — registration succeeds.
    tc.register_type_def_self(
        &TypeName::from("Cup"),
        &None,
        &[],
        &[product_int_field("Cup", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();

    // `v` now retains both canonical candidates rather than selecting a winner.
    assert!(is_ambiguous(&tc.symbol_table(), "v"));
    // It is NOT folded into the overload mechanism: no `Overloaded` base, no
    // mangled `v$Box`/`v$Cup` variants exist.
    assert!(
        tc.symbol_table().get("v$Box").is_none() && tc.symbol_table().get("v$Cup").is_none(),
        "duplicate-field accessors MUST NOT be folded into mangled overload \
             variants (no v$Box / v$Cup)"
    );

    // Both owning types are recorded as the qualified alternatives the
    // ambiguity error lists (`Box.v` and `Cup.v`).
    let alts = tc
        .state
        .accessor_owning_types
        .get(&Symbol::from("v"))
        .expect("poisoned accessor must record its owning-type alternatives");
    assert_eq!(alts.len(), 2, "Box + Cup are the alternatives");
    let names: Vec<&str> = alts.iter().map(|t| t.name.as_ref()).collect();
    assert!(names.contains(&"Box"));
    assert!(names.contains(&"Cup"));

    // The field stays reachable via `match` to each colliding type: a
    // single-arm match binding the product's field type-checks for both
    // Box and Cup (an e2e asserts the runtime values; here we assert the
    // typechecker accepts the destructuring path the spec promises).
    for ty in ["Box", "Cup"] {
        use cranelisp_types::{MatchArm, Pattern, SymbolRef};
        let scrutinee = Expr::ConstrADT {
            type_name: user_fqtn(ty),
            tag: 0,
            fields: vec![Expr::IntLit {
                value: 5,
                span: Span::SYNTHETIC,
                inferred_type: None,
            }],
            span: Span::SYNTHETIC,
            inferred_type: None,
        };
        let mut match_expr = Expr::Match {
            scrutinee: Box::new(scrutinee),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: SymbolRef::new(None, Symbol::from(ty)),
                    bindings: vec![Symbol::from("v")],
                    span: Span::SYNTHETIC,
                },
                body: Expr::var(Symbol::from("v"), Span::SYNTHETIC),
                span: Span::SYNTHETIC,
            }],
            span: Span::SYNTHETIC,
            compiler_generated: false,
            inferred_type: None,
        };
        let ty_result = tc.infer_expr_for_test(&mut match_expr);
        assert!(
            ty_result.is_ok(),
            "`(match ({ty} 5) [({ty} v) v])` must type-check despite the \
                 poisoned bare accessor — match access is always available \
                 (§5.2.6); got {ty_result:?}"
        );
    }
}

/// Simulate the REPL's per-input cluster boundary: each input line is a
/// SEPARATE cluster with a FRESH per-`CheckState` accessor-tracking state,
/// while the live symbol table (committed entries) persists. Clearing the
/// two per-cluster sets reproduces exactly the condition FIXME 0366 closes —
/// the second deftype's accessor synthesis cannot see the first accessor in
/// same-check ephemeral state, only in the committed live table.
fn new_cluster(tc: &mut TestFixture) {
    tc.state.accessor_owning_types.clear();
}

// spec: 05-definitions §5.2.6 + 08-modules §8.6.5 (FIXME 0366) — at the REPL
// each input is its own cluster, so a duplicate field-name accessor defined
// in a LATER cluster must still leave the bare name with both candidates,
// re-deriving the earlier owner from the COMMITTED live accessor entry — NOT
// silently first-wins. This pins the typecheck seam the e2e
// `repl_cross_cluster_duplicate_field_accessor_is_ambiguous` exercises.
#[test]
fn cross_cluster_duplicate_field_poisons_bare_accessor() {
    let mut tc = tf_with_scalar_imports();
    // Cluster 1: `Box` — `v` is a normal concrete accessor.
    tc.register_type_def_self(
        &TypeName::from("Box"),
        &None,
        &[],
        &[product_int_field("Box", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();
    // Bare `v` is a name candidate; canonical `Box.v` is the concrete
    // accessor binding.
    assert!(
        is_candidate(&tc.symbol_table(), "v"),
        "single-type bare `v` exposes one candidate after cluster 1"
    );
    assert!(
        is_concrete_callable(tc.symbol_table().get("Box.v")),
        "canonical Box.v is the concrete UserFn accessor after cluster 1"
    );

    // Cluster boundary: fresh per-`CheckState` accessor tracking; the live
    // `Box.v` canonical accessor + `v` candidate from cluster 1 stay committed.
    new_cluster(&mut tc);

    // Cluster 2: `Cup` with the SAME field name `v`. The earlier accessor is
    // visible only in the committed live table, not in this cluster's state.
    tc.register_type_def_self(
        &TypeName::from("Cup"),
        &None,
        &[],
        &[product_int_field("Cup", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();

    // `v` keeps both candidates, exactly as in the single-cluster
    // (`--run`/`--link`) path — neither owner wins by order.
    assert!(
        is_ambiguous(&tc.symbol_table(), "v"),
        "cross-cluster duplicate-field accessor `v` must retain both candidates"
    );
    // The cross-cluster ambiguity hint lists BOTH owning types even though
    // `Box` was recorded in the now-discarded cluster-1 state — the prior
    // owner is re-seeded from the committed accessor.
    let alts = tc
        .state
        .accessor_owning_types
        .get(&Symbol::from("v"))
        .expect("poisoned accessor must record its owning-type alternatives");
    let names: Vec<&str> = alts.iter().map(|t| t.name.as_ref()).collect();
    assert!(
        names.contains(&"Box"),
        "Box must be an alternative, got {names:?}"
    );
    assert!(
        names.contains(&"Cup"),
        "Cup must be an alternative, got {names:?}"
    );
}

// spec: 05-definitions §5.2.6 (S91 Phase 6) — the bare-field-name ambiguity
// ERROR MESSAGE must list the canonical alternatives (`Box.v`, `Cup.v`) in
// EVERY mode, REPL included (no exemption). At the REPL the BARE USE turn
// (`(v …)`) is its OWN cluster with a FRESH `CheckState`, so the per-cluster
// `accessor_owning_types` map that `--run` carries is EMPTY by the time the
// bare use is checked — the message must re-derive the alternatives from the
// durable symbol table. This is the cross-cluster seam the e2e
// `bare_field_ambiguity_message_lists_both_alternatives` exercises.
#[test]
fn cross_cluster_bare_field_ambiguity_message_lists_canonical_alternatives() {
    let mut tc = tf_with_scalar_imports();
    // Cluster 1: `Box` with field `v`.
    tc.register_type_def_self(
        &TypeName::from("Box"),
        &None,
        &[],
        &[product_int_field("Box", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();
    // Cluster 2: `Cup` with the SAME field `v` → bare `v` has two candidates.
    new_cluster(&mut tc);
    tc.register_type_def_self(
        &TypeName::from("Cup"),
        &None,
        &[],
        &[product_int_field("Cup", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();
    assert!(
        is_ambiguous(&tc.symbol_table(), "v"),
        "duplicate field `v` must be poisoned after cluster 2"
    );

    // Cluster 3 (the BARE USE turn): fresh `CheckState` — the per-cluster
    // owner-tracking map is empty. This is the exact REPL condition where the
    // pre-fix message truncated to `ambiguous bare name 'v'` with NO
    // alternatives.
    new_cluster(&mut tc);
    assert!(
        tc.state
            .accessor_owning_types
            .get(&Symbol::from("v"))
            .is_none(),
        "the bare-use cluster starts with no per-cluster owner record \
             (the truncation condition)"
    );

    let mut bare = Expr::var(Symbol::from("v"), Span::SYNTHETIC);
    let err = tc
        .infer_expr_for_test(&mut bare)
        .expect_err("bare use of the poisoned field `v` must be a resolution error");
    let message = match err {
        CranelispError::TypeError { message, .. } => message,
        other => panic!("expected a TypeError for the ambiguous bare name, got {other:?}"),
    };
    assert!(
        message.contains("ambiguous bare name 'v'"),
        "diagnostic must frame the failure as an ambiguity, got: {message}"
    );
    // The REGRESSION GUARD: BOTH canonical alternatives must appear even
    // though the per-cluster owner map was empty (re-derived from the table).
    assert!(
        message.contains("Box.v") && message.contains("Cup.v"),
        "the ambiguity message must list BOTH canonical alternatives \
             `Box.v` and `Cup.v` (no REPL exemption, §5.2.6), got: {message}"
    );
}

// spec: 05-definitions §5.2.6 (S91 Phase 6) — unit-level reconstruction seam:
// `reconstruct_accessor_alternatives` re-derives the owning types of a
// multi-candidate bare field name from the durable symbol table when the per-cluster
// `accessor_owning_types` map is empty (the cross-cluster REPL case).
#[test]
fn reconstruct_accessor_alternatives_reads_owners_from_table() {
    let mut tc = tf_with_scalar_imports();
    tc.register_type_def_self(
        &TypeName::from("Box"),
        &None,
        &[],
        &[product_int_field("Box", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();
    new_cluster(&mut tc);
    tc.register_type_def_self(
        &TypeName::from("Cup"),
        &None,
        &[],
        &[product_int_field("Cup", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();
    new_cluster(&mut tc); // empty per-cluster map — force the table re-derivation

    let owners = tc.env().reconstruct_accessor_alternatives(&tc.state, "v");
    let names: Vec<&str> = owners.iter().map(|t| t.name.as_ref()).collect();
    assert!(
        names.contains(&"Box") && names.contains(&"Cup"),
        "reconstruction must read both owning types from the table, got {names:?}"
    );
    // A non-colliding / unknown field name yields no alternatives (the caller
    // then emits the bare message with no qualified-accessor hint).
    assert!(
        tc.env()
            .reconstruct_accessor_alternatives(&tc.state, "no_such_field")
            .is_empty(),
        "a field name with no synthesised accessor must reconstruct to no alternatives"
    );
}

// spec: 05-definitions §5.2.6 (FIXME 0366) — NEGATIVE: a SINGLE product
// type's accessor synthesised in its own cluster, with no duplicate field
// name across types, must remain a normal concrete accessor across cluster
// boundaries (the legitimate case must not gain a spurious candidate).
#[test]
fn cross_cluster_single_type_accessor_not_poisoned() {
    let mut tc = tf_with_scalar_imports();
    tc.register_type_def_self(
        &TypeName::from("Box"),
        &None,
        &[],
        &[product_int_field("Box", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();
    // A LATER cluster with an UNRELATED type/field — no collision on `v`.
    new_cluster(&mut tc);
    tc.register_type_def_self(
        &TypeName::from("Cup"),
        &None,
        &[],
        &[product_int_field("Cup", "w")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();
    // Distinct bare fields `v`/`w` each keep a single candidate onto their
    // canonical concrete accessors `Box.v` / `Cup.w`.
    for (bare, canonical) in [("v", "Box.v"), ("w", "Cup.w")] {
        assert!(
            is_candidate(&tc.symbol_table(), bare),
            "distinct-field bare `{bare}` must remain a single candidate \
                 across clusters (no spurious poison), got {:?}",
            tc.symbol_table().name_candidates(&Symbol::from(bare))
        );
        assert!(
            is_concrete_callable(tc.symbol_table().get(canonical)),
            "canonical `{canonical}` must be the concrete UserFn accessor, got {:?}",
            tc.symbol_table().get(canonical)
        );
    }
}

// spec: 05-definitions §5.2.6 (FIXME 0366) — NEGATIVE: re-running the SAME
// deftype in a later cluster (a redefinition, NOT two distinct types sharing
// a field name) must NOT add a second candidate — re-exposing the same
// canonical source deduplicates, and the accessor is re-synthesised in place.
#[test]
fn cross_cluster_same_type_redefinition_not_poisoned() {
    let mut tc = tf_with_scalar_imports();
    tc.register_type_def_self(
        &TypeName::from("Box"),
        &None,
        &[],
        &[product_int_field("Box", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();
    // Cluster boundary, then RE-DEFINE the same `Box` type.
    new_cluster(&mut tc);
    tc.register_type_def_self(
        &TypeName::from("Box"),
        &None,
        &[],
        &[product_int_field("Box", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();
    // A same-type redefinition is not a cross-type duplicate field: the
    // canonical `Box.v` is re-synthesised and bare `v` keeps its single
    // candidate.
    assert!(
        is_candidate(&tc.symbol_table(), "v"),
        "`v` after a same-type Box redefinition must stay a single candidate"
    );
    assert!(
        is_concrete_callable(tc.symbol_table().get("Box.v")),
        "canonical Box.v stays the concrete UserFn accessor after redefinition"
    );
}

// =====================================================================
// FIXME 0365 Item 1 — `Type.member` dotted field-accessor typing
// (spec §8.5.2 / §5.2.6). The dotted form `Box.v` resolves the field
// accessor `v` of `Box` directly and is typed by ordinary value-position
// scheme instantiation off the accessor's `(Fn [Type] FieldType)` scheme.
// =====================================================================

/// Register a polymorphic single-field product `(Box a) [:a v]`.
fn register_poly_box(tc: &mut TestFixture) {
    tc.register_type_def_self(
        &TypeName::from("Box"),
        &None,
        &[Symbol::from("a")],
        &[ConstructorDef {
            name: Symbol::from("Box"),
            docstring: None,
            fields: vec![cranelisp_types::FieldDef {
                name: Symbol::from("v"),
                type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("a")),
                span: Span::SYNTHETIC,
            }],
            span: Span::SYNTHETIC,
        }],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();
}

// spec: 08-modules §8.5.2 — `Box.v` types as `(Fn [Box] Int)` for a
// monomorphic product. Each per-type dotted accessor has a distinct
// denotation even when the bare `v` has several candidates.
#[test]
fn dotted_accessor_types_fn_of_type_monomorphic() {
    let mut tc = tf_with_scalar_imports();
    tc.register_type_def_self(
        &TypeName::from("Box"),
        &None,
        &[],
        &[product_int_field("Box", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();

    let mut expr = Expr::var(Symbol::from("Box.v"), Span::SYNTHETIC);
    let ty = tc
        .infer_expr_for_test(&mut expr)
        .expect("Box.v must type as the field accessor");
    match ty {
        Type::Fn(params, ret) => {
            assert_eq!(params.len(), 1);
            assert_eq!(params[0], Type::ADT(user_fqtn("Box"), vec![]));
            assert_eq!(ret.as_ref(), &Type::Int);
        }
        other => panic!("Box.v must type as (Fn [Box] Int), got {other:?}"),
    }
}

// spec: 08-modules §8.5.2 (`fixme-0365-field-accessor-dotted.md` §1.6.2) —
// when two types share a field name, bare `v` has two candidates and an
// unsettled use is an error, while the canonical `Box.v` / `Cup.v` accessors
// resolve unchanged.
#[test]
fn dotted_accessor_disambiguates_poisoned_bare_field() {
    let mut tc = tf_with_scalar_imports();
    // Add a Bool-field type to give Cup.v a different return type.
    tc.register_type_def_self(
        &TypeName::from("Box"),
        &None,
        &[],
        &[product_int_field("Box", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();
    tc.register_type_def_self(
        &TypeName::from("Cup"),
        &None,
        &[],
        &[ConstructorDef {
            name: Symbol::from("Cup"),
            docstring: None,
            fields: vec![cranelisp_types::FieldDef {
                name: Symbol::from("v"),
                type_expr: cranelisp_types::TypeExpr::Named(cranelisp_types::TypeRef::new(
                    None,
                    TypeName::from("Bool"),
                )),
                span: Span::SYNTHETIC,
            }],
            span: Span::SYNTHETIC,
        }],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();

    // Bare `v` has two candidates.
    assert!(is_ambiguous(&tc.symbol_table(), "v"));
    // A bare use with no settling context is an ambiguity error.
    let mut bare = Expr::var(Symbol::from("v"), Span::SYNTHETIC);
    assert!(
        tc.infer_expr_for_test(&mut bare).is_err(),
        "contested bare `v` must be a resolution error (ambiguous alias)"
    );

    // The canonical Box.v : (Fn [Box] Int), Cup.v : (Fn [Cup] Bool) both
    // still resolve.
    let mut box_v = Expr::var(Symbol::from("Box.v"), Span::SYNTHETIC);
    match tc.infer_expr_for_test(&mut box_v).unwrap() {
        Type::Fn(p, r) => {
            assert_eq!(p[0], Type::ADT(user_fqtn("Box"), vec![]));
            assert_eq!(r.as_ref(), &Type::Int);
        }
        other => panic!("Box.v must be (Fn [Box] Int), got {other:?}"),
    }
    let mut cup_v = Expr::var(Symbol::from("Cup.v"), Span::SYNTHETIC);
    match tc.infer_expr_for_test(&mut cup_v).unwrap() {
        Type::Fn(p, r) => {
            assert_eq!(p[0], Type::ADT(user_fqtn("Cup"), vec![]));
            assert_eq!(r.as_ref(), &Type::Bool);
        }
        other => panic!("Cup.v must be (Fn [Cup] Bool), got {other:?}"),
    }
}

// spec: 03-types §3.5.3 + 08-modules §8.6.5 — ordinary argument
// constraints select one canonical accessor before ambiguity is decided.
#[test]
fn contested_bare_accessor_selects_by_argument_and_records_canonical_identity() {
    let mut tc = tf_with_scalar_imports();
    tc.register_type_def_self(
        &TypeName::from("Box"),
        &None,
        &[],
        &[product_int_field("Box", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();
    tc.register_type_def_self(
        &TypeName::from("Cup"),
        &None,
        &[],
        &[ConstructorDef {
            name: Symbol::from("Cup"),
            docstring: None,
            fields: vec![cranelisp_types::FieldDef {
                name: Symbol::from("v"),
                type_expr: cranelisp_types::TypeExpr::Named(cranelisp_types::TypeRef::new(
                    None,
                    TypeName::from("Bool"),
                )),
                span: Span::SYNTHETIC,
            }],
            span: Span::SYNTHETIC,
        }],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();

    let callee_span = Span::new(10, 11);
    let call_span = Span::new(10, 20);
    let mut call = Expr::Apply {
        callee: Box::new(Expr::var(Symbol::from("v"), callee_span)),
        args: vec![Expr::ConstrADT {
            type_name: user_fqtn("Box"),
            tag: 0,
            fields: vec![Expr::IntLit {
                value: 7,
                span: Span::new(16, 17),
                inferred_type: None,
            }],
            span: Span::new(12, 18),
            inferred_type: None,
        }],
        span: call_span,
        resolved_call: None,
        inferred_type: None,
    };

    let next_id_before = tc.next_id.load(std::sync::atomic::Ordering::Relaxed);
    let constraints_before = tc.state.active_constraints.constraints.clone();
    let warnings_before = tc.state.warnings.len();
    assert_eq!(tc.infer_expr_for_test(&mut call).unwrap(), Type::Int);
    assert_eq!(
        tc.next_id.load(std::sync::atomic::Ordering::Relaxed) - next_id_before,
        2,
        "only the real pending anchor and call result may consume IDs; isolated trials consume none"
    );
    assert_eq!(tc.state.active_constraints.constraints, constraints_before);
    assert_eq!(tc.state.warnings.len(), warnings_before);
    assert_eq!(
        tc.state.method_resolutions.var_refs.get(&callee_span),
        Some(&VarRef::Global(FQSymbol {
            module: ModuleFullPath::from("user"),
            symbol: Symbol::from("Box.v"),
        }))
    );
    assert_eq!(
        tc.state.method_resolutions.apply_refs.get(&call_span),
        Some(&ApplyRef::ViaCallee)
    );
}

// spec: 08-modules §8.6.5 — zero type-compatible candidates is distinct
// from an unknown spelling and reports every considered canonical identity.
#[test]
fn contested_bare_accessor_no_match_is_not_undefined() {
    let mut tc = tf_with_scalar_imports();
    for ty in ["Box", "Cup"] {
        tc.register_type_def_self(
            &TypeName::from(ty),
            &None,
            &[],
            &[product_int_field(ty, "v")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();
    }
    let mut call = Expr::Apply {
        callee: Box::new(Expr::var(Symbol::from("v"), Span::new(30, 31))),
        args: vec![Expr::IntLit {
            value: 7,
            span: Span::new(32, 33),
            inferred_type: None,
        }],
        span: Span::new(30, 34),
        resolved_call: None,
        inferred_type: None,
    };
    let error = tc.infer_expr_for_test(&mut call).unwrap_err();
    let message = error.message();
    assert!(message.contains("no matching declaration"), "{message}");
    assert!(!message.contains("undefined variable"), "{message}");
    assert!(message.contains("user/Box.v"), "{message}");
    assert!(message.contains("user/Cup.v"), "{message}");
}

// design use-site-candidate-selection §§3.5, 3.9 — diagnostics are canonical,
// complete, deduplicated, and independent of exposure insertion order.
#[test]
fn contested_candidate_diagnostic_is_insertion_order_independent() {
    let diagnose = |owners: [&str; 2]| {
        let mut tc = tf_with_scalar_imports();
        for owner in owners {
            tc.register_type_def_self(
                &TypeName::from(owner),
                &None,
                &[],
                &[product_int_field(owner, "v")],
                Visibility::Public,
                Span::SYNTHETIC,
            )
            .unwrap();
        }
        let mut call = Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("v"), Span::new(135, 136))),
            args: vec![Expr::BoolLit {
                value: true,
                span: Span::new(137, 138),
                inferred_type: None,
            }],
            span: Span::new(135, 139),
            resolved_call: None,
            inferred_type: None,
        };
        tc.infer_expr_for_test(&mut call)
            .unwrap_err()
            .message()
            .to_string()
    };
    let forward = diagnose(["Box", "Cup"]);
    let reverse = diagnose(["Cup", "Box"]);
    assert_eq!(forward, reverse);
    assert_eq!(forward.matches("user/Box.v").count(), 1, "{forward}");
    assert_eq!(forward.matches("user/Cup.v").count(), 1, "{forward}");
}

// spec: 03-types §3.5.3 + 08-modules §8.6.5 — a monomorphic local alias
// preserves the pending source-use anchor and selects the same declaration as
// the direct-call twin.
#[test]
fn contested_bare_accessor_selects_through_local_alias() {
    let mut tc = tf_with_scalar_imports();
    for ty in ["Box", "Cup"] {
        tc.register_type_def_self(
            &TypeName::from(ty),
            &None,
            &[],
            &[product_int_field(ty, "v")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();
    }
    let source_span = Span::new(40, 41);
    let call_span = Span::new(50, 60);
    let mut expression = Expr::Let {
        bindings: vec![(
            Symbol::from("project"),
            Expr::var(Symbol::from("v"), source_span),
        )],
        body: Box::new(Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("project"), Span::new(50, 57))),
            args: vec![Expr::ConstrADT {
                type_name: user_fqtn("Box"),
                tag: 0,
                fields: vec![Expr::IntLit {
                    value: 9,
                    span: Span::new(58, 59),
                    inferred_type: None,
                }],
                span: Span::new(57, 60),
                inferred_type: None,
            }],
            span: call_span,
            resolved_call: None,
            inferred_type: None,
        }),
        span: Span::new(35, 61),
        inferred_type: None,
    };
    assert_eq!(tc.infer_expr_for_test(&mut expression).unwrap(), Type::Int);
    assert_eq!(
        tc.state.method_resolutions.var_refs.get(&source_span),
        Some(&VarRef::Global(FQSymbol {
            module: ModuleFullPath::from("user"),
            symbol: Symbol::from("Box.v"),
        }))
    );
    assert_eq!(
        tc.state.method_resolutions.apply_refs.get(&call_span),
        Some(&ApplyRef::ViaCallee)
    );
}

// spec: 08-modules §8.5.2 — a polymorphic product's dotted accessor reads
// the quantified scheme: `(Box a).v` instantiates to `(Fn [(Box a)] a)`
// with the param ADT arg and the return type the SAME fresh var.
#[test]
fn dotted_accessor_types_polymorphic_scheme() {
    let mut tc = tf_with_scalar_imports();
    register_poly_box(&mut tc);

    let mut expr = Expr::var(Symbol::from("Box.v"), Span::SYNTHETIC);
    let ty = tc.infer_expr_for_test(&mut expr).unwrap();
    match ty {
        Type::Fn(params, ret) => {
            assert_eq!(params.len(), 1);
            match &params[0] {
                Type::ADT(fqtn, args) => {
                    assert_eq!(fqtn, &user_fqtn("Box"));
                    assert_eq!(args.len(), 1);
                    // The accessor return type IS the product's type arg
                    // (the field type `a`).
                    assert_eq!(&args[0], ret.as_ref());
                    assert!(matches!(ret.as_ref(), Type::Var(_)));
                }
                other => panic!("expected (Box a) param, got {other:?}"),
            }
        }
        other => panic!("Box.v must be (Fn [(Box a)] a), got {other:?}"),
    }
}

// spec: 08-modules §8.5.2 — the dotted accessor is first-class: applying it
// to a `(Box 7)` yields the field type (Int), exactly as a bound callable.
#[test]
fn dotted_accessor_is_first_class_applied() {
    let mut tc = tf_with_scalar_imports();
    tc.register_type_def_self(
        &TypeName::from("Box"),
        &None,
        &[],
        &[product_int_field("Box", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();

    // (Box.v (Box 7)) : Int.
    let construct = Expr::ConstrADT {
        type_name: user_fqtn("Box"),
        tag: 0,
        fields: vec![Expr::IntLit {
            value: 7,
            span: Span::SYNTHETIC,
            inferred_type: None,
        }],
        span: Span::SYNTHETIC,
        inferred_type: None,
    };
    let mut apply = Expr::Apply {
        callee: Box::new(Expr::var(Symbol::from("Box.v"), Span::SYNTHETIC)),
        args: vec![construct],
        span: Span::SYNTHETIC,
        resolved_call: None,
        inferred_type: None,
    };
    let ty = tc.infer_expr_for_test(&mut apply).unwrap();
    assert_eq!(ty, Type::Int, "(Box.v (Box 7)) must type as Int");
}

// spec: 08-modules §8.5.2 (`fixme-0365-field-accessor-dotted.md` §1.6.1,
// §1.6.5) — the canonical `Box.v` is the Public compiled accessor; bare `v` is
// a name candidate onto it. Exactly one compiled function per (type, field) —
// the bare candidate adds NO codegen target and no second GOT slot.
#[test]
fn canonical_dotted_is_the_def_bare_is_the_alias() {
    let mut tc = tf_with_scalar_imports();
    let before = tc.symbol_table().codegen_targets().count();
    tc.register_type_def_self(
        &TypeName::from("Box"),
        &None,
        &[],
        &[product_int_field("Box", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();
    let after = tc.symbol_table().codegen_targets().count();

    // Canonical `Box.v` is the concrete, Public accessor callable.
    match tc.symbol_table().get("Box.v") {
        Some(entry) if is_concrete_callable(Some(entry)) => {
            assert!(
                entry
                    .callable()
                    .is_some_and(|c| matches!(c.origin, CallableOrigin::Accessor { .. })),
                "canonical Box.v must be a concrete UserFn Def"
            );
            assert!(
                entry.is_public(),
                "canonical Box.v must be uniformly Public"
            );
            assert!(
                entry.callable_got_slot().is_some(),
                "canonical Box.v carries its own GOT slot"
            );
        }
        other => panic!("Box.v must be the canonical accessor Def, got {other:?}"),
    }
    // Bare `v` is a name candidate onto the canonical key, not a binding.
    assert!(
        is_candidate(&tc.symbol_table(), "v"),
        "bare `v` MUST expose only Box.v (not be a compiled Def), \
             got {:?}",
        tc.symbol_table().name_candidates(&Symbol::from("v"))
    );
    // The deftype adds the product ctor `Box` + the canonical accessor
    // `Box.v` as codegen targets — delta 2. The bare `v` candidate adds ZERO
    // — exactly one compiled function per (type, field).
    assert_eq!(
        after - before,
        2,
        "non-contested deftype must add only the ctor + canonical accessor \
             as codegen targets — the bare `v` alias must NOT be a \
             defined_symbols() entry (before={before}, after={after})"
    );
}

// spec: 08-modules §8.5.2 (`fixme-0365-field-accessor-dotted.md` §1.6.2) —
// bare `v` resolves through its sole candidate to the canonical `Box.v` when
// exactly one type owns the field.
#[test]
fn bare_alias_resolves_to_canonical_when_unique() {
    let mut tc = tf_with_scalar_imports();
    tc.register_type_def_self(
        &TypeName::from("Box"),
        &None,
        &[],
        &[product_int_field("Box", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();
    let mut bare = Expr::var(Symbol::from("v"), Span::SYNTHETIC);
    match tc
        .infer_expr_for_test(&mut bare)
        .expect("bare v resolves via alias")
    {
        Type::Fn(p, r) => {
            assert_eq!(p[0], Type::ADT(user_fqtn("Box"), vec![]));
            assert_eq!(r.as_ref(), &Type::Int);
        }
        other => panic!("bare v must type as (Fn [Box] Int) via the alias, got {other:?}"),
    }
}

// spec: 08-modules §8.5.2 — NEGATIVE: a `Type.member` whose member is not a
// field accessor of the type does NOT resolve as a dotted accessor (it is
// an undefined variable — the resolver returns None, no spurious type).
#[test]
fn dotted_accessor_nonfield_member_is_undefined() {
    let mut tc = tf_with_scalar_imports();
    tc.register_type_def_self(
        &TypeName::from("Box"),
        &None,
        &[],
        &[product_int_field("Box", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();

    let mut expr = Expr::var(Symbol::from("Box.nonfield"), Span::SYNTHETIC);
    let result = tc.infer_expr_for_test(&mut expr);
    assert!(
        result.is_err(),
        "Box.nonfield must NOT resolve as a field accessor"
    );
}

// =====================================================================
// Impl-time field-accessor collision gate, AS BUILT. A trait `impl` whose
// method name equals a field-accessor name of the target type is rejected
// before the impl enters the symbol table. Spec §7.3.1 now permits the
// overlap; these cases assert the superseded rejection and are replaced
// after ACT-0983 intake (`fixme-0365-field-accessor-dotted.md` §2.1).
// =====================================================================

fn collide_trait_decl(method: &str) -> cranelisp_types::TraitDecl {
    crate::traits::test_helpers::parse_trait_decl(&format!("(deftrait HasV ({method} [x] Int))"))
}

fn collide_impl(target: &str, method: &str) -> cranelisp_types::TraitImpl {
    use cranelisp_types::{Defn, DefnVariant, TraitImpl, TraitRef, TypeExpr, TypeRef};
    TraitImpl {
        head_con_var: None,
        trait_name: TraitRef::new(None, TraitName::from("HasV")),
        target: TypeExpr::Named(TypeRef::new(None, TypeName::from(target))),
        type_constraints: vec![],
        methods: vec![Defn {
            name: Symbol::from(method),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None)],
                body: Expr::IntLit {
                    value: 99,
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

// spec: 07-traits §7.3.1 — NEGATIVE (the load-bearing _neg): an impl method
// `v` colliding with `Box`'s field accessor `v` is rejected at impl time,
// with a diagnostic naming the collision, and produces NO symbol-table side
// effect (no TraitImpl entry, no mangled method Def).
#[test]
fn impl_method_colliding_with_field_accessor_rejected() {
    let mut tc = tf_with_scalar_imports();
    tc.register_type_def_self(
        &TypeName::from("Box"),
        &None,
        &[],
        &[product_int_field("Box", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();
    tc.register_trait_decl_self(&collide_trait_decl("v"))
        .unwrap();

    let err = tc
        .register_trait_impl_self(&collide_impl("Box", "v"))
        .expect_err("a colliding impl method `v` must be rejected");
    let msg = format!("{err}");
    assert!(
        msg.contains("collides with the field accessor") && msg.contains("v"),
        "the diagnostic must name the collision and the colliding name; got {msg}"
    );

    // Structural rejection (Principle 18): no TraitImpl entry, no mangled
    // method Def landed for the rejected impl.
    assert!(
        !tc.has_impl(&TraitName::from("HasV"), &TypeName::from("Box")),
        "the rejected impl MUST NOT register a TraitImpl entry"
    );
    // The rejected impl leaves both declaration candidates intact: the
    // product accessor and the trait method. Packet B deliberately makes a
    // bare collision a candidate set rather than preserving the former
    // first-wins alias shape.
    let mut candidates: Vec<String> = tc
        .symbol_table()
        .name_candidates(&Symbol::from("v"))
        .into_iter()
        .map(|candidate| candidate.source.to_string())
        .collect();
    candidates.sort();
    assert_eq!(candidates, ["user/Box.v", "user/HasV.v"]);
    let mut contested = Expr::var(Symbol::from("v"), Span::new(70, 71));
    let message = tc
        .infer_expr_for_test(&mut contested)
        .expect_err("an unconstrained mixed declaration use remains ambiguous")
        .message()
        .to_string();
    assert!(message.contains("user/Box.v"), "{message}");
    assert!(message.contains("user/HasV.v"), "{message}");
    assert!(
        tc.symbol_table()
            .get("Box.v")
            .and_then(Binding::callable)
            .is_some()
    );
}

// spec: 07-traits §7.4.1; design use-site-candidate-selection §§3.2, 3.8 —
// argument HM facts can select a trait method over a same-spelling accessor,
// and dispatch consumes the selected canonical declaration without re-resolving
// the contested bare spelling.
#[test]
fn contested_accessor_and_trait_method_selects_trait_and_records_dispatch() {
    let mut tc = tf_with_scalar_imports();
    tc.register_type_def_self(
        &TypeName::from("Box"),
        &None,
        &[],
        &[product_int_field("Box", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();
    tc.register_trait_decl_self(&collide_trait_decl("v"))
        .unwrap();
    tc.register_trait_impl_self(&collide_impl("Int", "v"))
        .unwrap();

    let callee_span = Span::new(80, 81);
    let call_span = Span::new(80, 85);
    let mut expression = Expr::Apply {
        callee: Box::new(Expr::var(Symbol::from("v"), callee_span)),
        args: vec![Expr::IntLit {
            value: 1,
            span: Span::new(82, 83),
            inferred_type: None,
        }],
        span: call_span,
        resolved_call: None,
        inferred_type: None,
    };
    assert_eq!(tc.infer_expr_for_test(&mut expression).unwrap(), Type::Int);
    assert_eq!(
        tc.state.method_resolutions.var_refs.get(&callee_span),
        Some(&VarRef::Global(FQSymbol {
            module: ModuleFullPath::from("user"),
            symbol: Symbol::from("HasV.v"),
        }))
    );
    assert!(matches!(
        tc.state.method_resolutions.apply_refs.get(&call_span),
        Some(ApplyRef::Dispatch(_))
    ));
    assert!(matches!(
        tc.state.method_resolutions.resolved_calls.get(&call_span),
        Some(cranelisp_types::ResolvedCall::TraitMethod { .. })
    ));
}

// spec: 06-pattern-matching §§6.2.1, 6.4.1; design
// use-site-candidate-selection §§3.4, 3.7 — arm-body HM facts flow through a
// provisional binder and select the one compatible constructor before
// exhaustiveness reads the canonical pattern identity.
#[test]
fn contested_constructor_selects_from_binder_use_and_records_canonical_identity() {
    let mut tc = tf_with_scalar_imports();
    for (owner, field_type) in [("IntHit", "Int"), ("BoolHit", "Bool")] {
        tc.register_type_def_self(
            &TypeName::from(owner),
            &None,
            &[],
            &[ConstructorDef {
                name: Symbol::from("Hit"),
                docstring: None,
                fields: vec![cranelisp_types::FieldDef {
                    name: Symbol::from("value"),
                    type_expr: cranelisp_types::TypeExpr::Named(cranelisp_types::TypeRef::new(
                        None,
                        TypeName::from(field_type),
                    )),
                    span: Span::SYNTHETIC,
                }],
                span: Span::SYNTHETIC,
            }],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();
    }

    use cranelisp_types::{MatchArm, Pattern, SymbolRef};
    let pattern_span = Span::new(110, 120);
    let mut expression = Expr::Lambda {
        params: vec![(Symbol::from("subject"), None)],
        body: Box::new(Expr::Match {
            scrutinee: Box::new(Expr::var(Symbol::from("subject"), Span::new(101, 108))),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: SymbolRef::new(None, Symbol::from("Hit")),
                    bindings: vec![Symbol::from("value")],
                    span: pattern_span,
                },
                body: Expr::If {
                    cond: Box::new(Expr::var(Symbol::from("value"), Span::new(121, 126))),
                    then_branch: Box::new(Expr::IntLit {
                        value: 1,
                        span: Span::new(127, 128),
                        inferred_type: None,
                    }),
                    else_branch: Box::new(Expr::IntLit {
                        value: 0,
                        span: Span::new(129, 130),
                        inferred_type: None,
                    }),
                    span: Span::new(121, 130),
                    inferred_type: None,
                },
                span: Span::new(110, 130),
            }],
            span: Span::new(101, 131),
            compiler_generated: false,
            inferred_type: None,
        }),
        span: Span::new(100, 132),
        inferred_type: None,
    };
    assert_eq!(
        tc.infer_expr_for_test(&mut expression).unwrap(),
        Type::Fn(
            vec![Type::ADT(user_fqtn("BoolHit"), vec![])],
            Box::new(Type::Int),
        )
    );
    assert_eq!(
        tc.state.method_resolutions.pattern_ctors.get(&pattern_span),
        Some(&FQSymbol {
            module: ModuleFullPath::from("user"),
            symbol: Symbol::from("BoolHit.Hit"),
        })
    );
}

// spec: 07-traits §7.3.1 — POSITIVE: a non-colliding impl method (`show`
// != field `v`) registers normally.
#[test]
fn impl_method_not_colliding_registers() {
    let mut tc = tf_with_scalar_imports();
    tc.register_type_def_self(
        &TypeName::from("Box"),
        &None,
        &[],
        &[product_int_field("Box", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();
    tc.register_trait_decl_self(&collide_trait_decl("show"))
        .unwrap();

    tc.register_trait_impl_self(&collide_impl("Box", "show"))
        .expect("a non-colliding impl method must register");
    assert!(tc.has_impl(&TraitName::from("HasV"), &TypeName::from("Box")));
}

// spec: 07-traits §7.3.1 — POSITIVE (primitive target): `Int` has no field
// accessors, so the collision set is empty and the impl registers.
#[test]
fn impl_on_primitive_target_unaffected_by_collision_check() {
    let mut tc = tc_with_prims_for_collision();
    tc.register_trait_decl_self(&collide_trait_decl("v"))
        .unwrap();

    tc.register_trait_impl_self(&collide_impl("Int", "v"))
        .expect("Int has no field accessors — `v` impl method must register");
    assert!(tc.has_impl(&TraitName::from("HasV"), &TypeName::from("Int")));
}

/// Fixture for the primitive-target collision test: scalar imports plus the
/// Ring 0 primitives the impl body (`99`) and trait decl need. `Int`/`Bool`
/// type names are in scope via `tf_with_scalar_imports`.
fn tc_with_prims_for_collision() -> TestFixture {
    tf_with_scalar_imports()
}

// spec: 07-traits §7.3.1 — NEGATIVE (parameterized target): the collision
// check resolves a polymorphic `(Box a)` target's FQTypeName the same way,
// so an impl method `v` on `Box` is rejected for the poly product too.
#[test]
fn impl_method_colliding_on_polymorphic_target_rejected() {
    use cranelisp_types::{Defn, DefnVariant, TraitImpl, TraitRef, TypeExpr, TypeRef};
    let mut tc = tf_with_scalar_imports();
    register_poly_box(&mut tc);
    tc.register_trait_decl_self(&collide_trait_decl("v"))
        .unwrap();

    // Settled model (§7.3.5 Case 1): a conventional-trait target must be
    // kind `*`, so a polymorphic product is applied — `(Box a)`, not the
    // bare (under-applied) `Box` — before the accessor-collision check runs.
    let poly_impl = TraitImpl {
        head_con_var: None,
        trait_name: TraitRef::new(None, TraitName::from("HasV")),
        target: TypeExpr::Applied(
            TypeRef::new(None, TypeName::from("Box")),
            vec![TypeExpr::TypeVar(Symbol::from("a"))],
        ),
        type_constraints: vec![],
        methods: vec![Defn {
            name: Symbol::from("v"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None)],
                body: Expr::IntLit {
                    value: 99,
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
    let err = tc
        .register_trait_impl_self(&poly_impl)
        .expect_err("a colliding impl method `v` on (Box a) must be rejected");
    assert!(format!("{err}").contains("collides with the field accessor"));
    assert!(!tc.has_impl(&TraitName::from("HasV"), &TypeName::from("Box")));
}

// spec: 07-traits §7.3.1 (FIXME 0366 cross-cluster) — NEGATIVE: a field `v`
// deftype'd in one cluster and a colliding impl in a LATER cluster is still
// rejected, because `field_accessor_names_of` reads the committed-live union
// view (the qualified `Box.v` accessor survives the cluster boundary).
#[test]
fn impl_method_colliding_cross_cluster_rejected() {
    let mut tc = tf_with_scalar_imports();
    // Cluster 1: deftype Box (registers accessor `v` + `Box.v`).
    tc.register_type_def_self(
        &TypeName::from("Box"),
        &None,
        &[],
        &[product_int_field("Box", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();
    // Cluster boundary: fresh per-CheckState accessor tracking. The live
    // accessor entries persist.
    new_cluster(&mut tc);
    tc.register_trait_decl_self(&collide_trait_decl("v"))
        .unwrap();
    // Cluster 2: the colliding impl — rejected via the committed-live view.
    let err = tc
        .register_trait_impl_self(&collide_impl("Box", "v"))
        .expect_err("cross-cluster colliding impl `v` must be rejected");
    assert!(format!("{err}").contains("collides with the field accessor"));
    assert!(!tc.has_impl(&TraitName::from("HasV"), &TypeName::from("Box")));
}

// spec: 07-traits §7.3.1 — NEGATIVE (as built; superseded by §7.3.1, intake
// ACT-0983): when bare `v` has candidates from a cross-type duplicate field
// (`Box`/`Cup`), the field name `v`
// is still recognised as a field accessor of `Box`, so an impl method `v`
// for `Box` is rejected (the qualified `Box.v` accessor + the owner map both
// contribute the bare name).
#[test]
fn impl_method_colliding_with_poisoned_accessor_rejected() {
    let mut tc = tf_with_scalar_imports();
    tc.register_type_def_self(
        &TypeName::from("Box"),
        &None,
        &[],
        &[product_int_field("Box", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();
    tc.register_type_def_self(
        &TypeName::from("Cup"),
        &None,
        &[],
        &[product_int_field("Cup", "v")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();
    // Bare `v` has two candidates now.
    assert!(is_ambiguous(&tc.symbol_table(), "v"));
    tc.register_trait_decl_self(&collide_trait_decl("v"))
        .unwrap();
    let err = tc
        .register_trait_impl_self(&collide_impl("Box", "v"))
        .expect_err("impl `v` colliding with a poisoned accessor must be rejected");
    assert!(format!("{err}").contains("collides with the field accessor"));
    assert!(!tc.has_impl(&TraitName::from("HasV"), &TypeName::from("Box")));
}

// spec: 06-pattern-matching §6.5.1 — all constructors covered passes exhaustiveness
#[test]
fn test_exhaustiveness_all_covered() {
    let mut tc = tf();
    tc.register_type_def_self(
        &TypeName::from("Color"),
        &None,
        &[],
        &[make_ctor("Red"), make_ctor("Green"), make_ctor("Blue")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();

    let covered = vec![
        Symbol::from("Red"),
        Symbol::from("Green"),
        Symbol::from("Blue"),
    ];
    assert!(
        tc.check_exhaustiveness(&TypeName::from("Color"), &covered, false, Span::SYNTHETIC)
            .is_ok()
    );
}

// spec: 06-pattern-matching §6.5.1 — missing constructor fails exhaustiveness check
#[test]
fn test_exhaustiveness_missing_constructor() {
    let mut tc = tf();
    tc.register_type_def_self(
        &TypeName::from("Color"),
        &None,
        &[],
        &[make_ctor("Red"), make_ctor("Green"), make_ctor("Blue")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();

    let covered = vec![Symbol::from("Red"), Symbol::from("Green")];
    let err = tc
        .check_exhaustiveness(&TypeName::from("Color"), &covered, false, Span::SYNTHETIC)
        .unwrap_err();
    assert!(err.message().contains("Blue"));
}

// spec: 06-pattern-matching §6.5.1 — wildcard pattern covers all constructors
#[test]
fn test_exhaustiveness_wildcard_covers_all() {
    let mut tc = tf();
    tc.register_type_def_self(
        &TypeName::from("Color"),
        &None,
        &[],
        &[make_ctor("Red"), make_ctor("Green"), make_ctor("Blue")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();

    // Empty covered but has wildcard -- ok
    assert!(
        tc.check_exhaustiveness(&TypeName::from("Color"), &[], true, Span::SYNTHETIC)
            .is_ok()
    );
}

// spec: 05-definitions §5.2.7 — constructors receive sequential integer tags
#[test]
fn test_constructor_tags() {
    let mut tc = tf();
    tc.register_type_def_self(
        &TypeName::from("Dir"),
        &None,
        &[],
        &[
            make_ctor("North"),
            make_ctor("South"),
            make_ctor("East"),
            make_ctor("West"),
        ],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();

    let info = tc.lookup_type_def(&TypeName::from("Dir")).unwrap();
    // Per S70: info.constructors is Vec<Symbol>; tag lives on the ctor's
    // ModuleEntry::Def's DefKind::Constructor.
    let table = tc.symbol_table();
    for (i, name) in ["North", "South", "East", "West"].iter().enumerate() {
        assert_eq!(info.constructors[i].as_ref(), *name);
        if let Some(callable) = ctor_callable(&table, *name) {
            if let CallableOrigin::Ctor { tag, .. } = &callable.origin {
                assert_eq!(*tag, i, "{name} should have tag {i}");
            } else {
                panic!("{name} should be DefKind::Constructor");
            }
        } else {
            panic!("{name} should be a Def in symbol table");
        }
    }
}

// --- Ring 1: Polymorphic ADT tests ---

/// Helper: register (Option a) with None and Some[:a val].
fn register_option(tc: &mut TestFixture) {
    tc.register_type_def_self(
        &TypeName::from("Option"),
        &None,
        &[Symbol::from("a")],
        &[
            make_ctor("None"),
            ConstructorDef {
                name: Symbol::from("Some"),
                docstring: None,
                fields: vec![cranelisp_types::FieldDef {
                    name: Symbol::from("val"),
                    type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("a")),
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

// spec: 05-definitions §5.2.2 — polymorphic type parameters recorded in TypeDefInfo
#[test]
fn test_polymorphic_type_params_recorded() {
    let mut tc = tf();
    register_option(&mut tc);

    let info = tc.lookup_type_def(&TypeName::from("Option")).unwrap();
    assert_eq!(info.type_params.len(), 1);
    assert_eq!(info.type_params[0].as_ref(), "a");
}

// spec: 05-definitions §5.2.7 — polymorphic ADT constructors receive sequential tags
#[test]
fn test_polymorphic_constructor_tags() {
    let mut tc = tf();
    register_option(&mut tc);

    let info = tc.lookup_type_def(&TypeName::from("Option")).unwrap();
    // Per S70: info.constructors is Vec<Symbol>; tags live on the per-ctor
    // ModuleEntry::Def's DefKind::Constructor.
    assert_eq!(info.constructors[0].as_ref(), "None");
    assert_eq!(info.constructors[1].as_ref(), "Some");
    let table = tc.symbol_table();
    for (i, name) in ["None", "Some"].iter().enumerate() {
        if let Some(callable) = ctor_callable(&table, *name)
            && let CallableOrigin::Ctor { tag, .. } = &callable.origin
        {
            assert_eq!(*tag, i, "{name} should have tag {i}");
        } else {
            panic!("{name} should be Def(Constructor)");
        }
    }
}

// spec: 04-adt §4.2 + design/typecheck/non-concrete-producer-obligations.md
// §2.1 — a polymorphic constructor is a slot-less synthesis template. Its
// concrete instances, rather than the residual template, are callable values.
#[test]
fn polymorphic_constructors_are_slotless_templates() {
    let mut tc = tf();
    register_option(&mut tc);

    let table = tc.symbol_table();
    let assert_template = |name: &str| match ctor_entry(&table, name) {
        Some(entry) if ctor_callable(&table, name).is_some() => {
            assert!(
                matches!(
                    entry.callable().map(|callable| &callable.arm.life),
                    Some(Life::Template {
                        body: TemplateBody::Synth(_),
                        ..
                    })
                ),
                "{name} must be a synthesized template"
            );
            assert_eq!(entry.callable_got_slot(), None);
        }
        _ => panic!("{name} should be a Def(Constructor) entry"),
    };

    assert_template("Some");
    assert_template("None");
}

// spec: 03-types §3.3 — polymorphic field type resolves to type variable
#[test]
fn test_polymorphic_field_has_var_type() {
    let mut tc = tf();
    register_option(&mut tc);

    let info = tc.lookup_type_def(&TypeName::from("Option")).unwrap();
    // Per S70: info.constructors[i] is Symbol; field metadata lives on the
    // ctor's Def — param_names + scheme.ty's Fn signature.
    assert_eq!(info.constructors[1].as_ref(), "Some");
    if let Some(callable) = ctor_callable(&tc.symbol_table(), "Some") {
        if let CallableOrigin::Ctor { field_count, .. } = &callable.origin {
            assert_eq!(*field_count, 1);
        } else {
            panic!("Some should be DefKind::Constructor");
        }
        assert_eq!(callable.arm.param_names.len(), 1);
        assert_eq!(callable.arm.param_names[0].as_ref(), "val");
        let scheme = &callable.arm.scheme;
        // Field type should be a type variable (the allocated ID)
        match &scheme.ty {
            Type::Fn(params, _) => {
                assert_eq!(params.len(), 1);
                assert!(matches!(params[0], Type::Var(_)));
            }
            _ => panic!("Some scheme should be Fn"),
        }
    } else {
        panic!("Some should be a Def in symbol table");
    }
}

// spec: 06-pattern-matching §6.5.1 — exhaustiveness with mixed nullary and data constructors
#[test]
fn test_exhaustiveness_with_mixed_constructors() {
    let mut tc = tf();
    register_option(&mut tc);

    // Missing None
    let covered = vec![Symbol::from("Some")];
    let err = tc
        .check_exhaustiveness(&TypeName::from("Option"), &covered, false, Span::SYNTHETIC)
        .unwrap_err();
    assert!(err.message().contains("None"));

    // Missing Some
    let covered = vec![Symbol::from("None")];
    let err = tc
        .check_exhaustiveness(&TypeName::from("Option"), &covered, false, Span::SYNTHETIC)
        .unwrap_err();
    assert!(err.message().contains("Some"));

    // Both covered
    let covered = vec![Symbol::from("None"), Symbol::from("Some")];
    assert!(
        tc.check_exhaustiveness(&TypeName::from("Option"), &covered, false, Span::SYNTHETIC,)
            .is_ok()
    );
}

// spec: 05-definitions §5.2.4 — explicit product parameters and field types
#[test]
fn test_explicitly_parameterised_product_type() {
    // (deftype (Pair a b) [:a first :b second])
    let mut tc = tf();
    tc.register_type_def_self(
        &TypeName::from("Pair"),
        &None,
        &[Symbol::from("a"), Symbol::from("b")],
        &[ConstructorDef {
            name: Symbol::from("MkPair"),
            docstring: None,
            fields: vec![
                cranelisp_types::FieldDef {
                    name: Symbol::from("first"),
                    type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("a")),
                    span: Span::SYNTHETIC,
                },
                cranelisp_types::FieldDef {
                    name: Symbol::from("second"),
                    type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("b")),
                    span: Span::SYNTHETIC,
                },
            ],
            span: Span::SYNTHETIC,
        }],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();

    // MkPair :: forall [a, b]. (Fn [a b] (Pair a b))
    if let Some(callable) = ctor_callable(&tc.symbol_table(), "MkPair") {
        let scheme = &callable.arm.scheme;
        assert_eq!(
            scheme.type_vars.len(),
            2,
            "MkPair should have 2 quantified vars"
        );
        match &scheme.ty {
            Type::Fn(params, ret) => {
                assert_eq!(params.len(), 2);
                match ret.as_ref() {
                    Type::ADT(fqtn, args) => {
                        assert_eq!(fqtn.name.as_ref(), "Pair");
                        assert_eq!(args.len(), 2);
                        // param vars should match the ADT arg vars
                        assert_eq!(params[0], args[0]);
                        assert_eq!(params[1], args[1]);
                    }
                    _ => panic!("MkPair return should be ADT"),
                }
            }
            _ => panic!("MkPair should have Fn type"),
        }
    } else {
        panic!("MkPair should be a Constructor entry");
    }
}

// spec: 05-definitions §5.2.2 — multi-parameter polymorphic ADT registration
#[test]
fn test_register_multi_param_type() {
    // (deftype (Either a b) (Left [:a val]) (Right [:b val]))
    let mut tc = tf();
    tc.register_type_def_self(
        &TypeName::from("Either"),
        &None,
        &[Symbol::from("a"), Symbol::from("b")],
        &[
            ConstructorDef {
                name: Symbol::from("Left"),
                docstring: None,
                fields: vec![cranelisp_types::FieldDef {
                    name: Symbol::from("val"),
                    type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("a")),
                    span: Span::SYNTHETIC,
                }],
                span: Span::SYNTHETIC,
            },
            ConstructorDef {
                name: Symbol::from("Right"),
                docstring: None,
                fields: vec![cranelisp_types::FieldDef {
                    name: Symbol::from("val"),
                    type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("b")),
                    span: Span::SYNTHETIC,
                }],
                span: Span::SYNTHETIC,
            },
        ],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();

    let info = tc.lookup_type_def(&TypeName::from("Either")).unwrap();
    assert_eq!(info.type_params.len(), 2);
    assert_eq!(info.constructors.len(), 2);

    // Both constructors should have 2 quantified vars
    if let Some(callable) = ctor_callable(&tc.symbol_table(), "Left") {
        let scheme = &callable.arm.scheme;
        assert_eq!(scheme.type_vars.len(), 2);
    } else {
        panic!("Left should be a Constructor entry");
    }
}

// spec: 03-types §3.2.2 — type-expr resolution validates ADT arity against
// the registered TypeDef's type-parameter count.
#[test]
fn test_resolution_validates_registered_arity() {
    use cranelisp_types::{TypeExpr, TypeRef};

    let mut tc = tf();
    register_option(&mut tc);
    tc.register_type_def_self(
        &TypeName::from("Color"),
        &None,
        &[],
        &[make_ctor("Red")],
        Visibility::Public,
        Span::SYNTHETIC,
    )
    .unwrap();

    // `Option` has arity 1: `(Option Color)` resolves; applying it with
    // zero args is rejected. (`Color` is registered in `user`; `Int` lives
    // in `primitives` and is not import-reachable from `user` here.)
    let opt_color = TypeExpr::Applied(
        TypeRef::new(None, TypeName::from("Option")),
        vec![TypeExpr::Named(TypeRef::new(None, TypeName::from("Color")))],
    );
    assert!(tc.resolve_type_expr_in_user(&opt_color).is_ok());

    let opt_zero = TypeExpr::Applied(TypeRef::new(None, TypeName::from("Option")), vec![]);
    assert!(tc.resolve_type_expr_in_user(&opt_zero).is_err());

    // `Color` has arity 0: bare `Color` resolves to its ADT type.
    let color = TypeExpr::Named(TypeRef::new(None, TypeName::from("Color")));
    assert!(tc.resolve_type_expr_in_user(&color).is_ok());

    // Unknown type name errors.
    let bogus = TypeExpr::Named(TypeRef::new(None, TypeName::from("Nope")));
    assert!(tc.resolve_type_expr_in_user(&bogus).is_err());
}

// spec: 05-definitions §5.2.7 — nullary monomorphic constructor scheme is bare ADT type
#[test]
fn test_build_constructor_scheme_nullary_mono() {
    let ctor = CtorBuild {
        name: Symbol::from("Red"),
        fields: vec![],
        docstring: None,
        internal: false,
    };
    let adt_type = Type::ADT(user_fqtn("Color"), vec![]);
    let scheme = build_constructor_scheme(&ctor, &adt_type, &[]);

    assert!(scheme.type_vars.is_empty());
    assert_eq!(scheme.ty, Type::ADT(user_fqtn("Color"), vec![]));
}

// spec: 05-definitions §5.2.1 — data constructor scheme is Fn from fields to ADT
#[test]
fn test_build_constructor_scheme_data_mono() {
    let ctor = CtorBuild {
        name: Symbol::from("Point"),
        fields: vec![
            FieldInfo {
                name: Symbol::from("x"),
                ty: Type::Int,
            },
            FieldInfo {
                name: Symbol::from("y"),
                ty: Type::Int,
            },
        ],
        docstring: None,
        internal: false,
    };
    let adt_type = Type::ADT(user_fqtn("Point"), vec![]);
    let scheme = build_constructor_scheme(&ctor, &adt_type, &[]);

    assert!(scheme.type_vars.is_empty());
    assert_eq!(
        scheme.ty,
        Type::Fn(
            vec![Type::Int, Type::Int],
            Box::new(Type::ADT(user_fqtn("Point"), vec![]))
        )
    );
}

// spec: 05-definitions §5.2.2 — polymorphic constructor scheme quantifies over type params
#[test]
fn test_build_constructor_scheme_polymorphic() {
    let ctor = CtorBuild {
        name: Symbol::from("Some"),
        fields: vec![FieldInfo {
            name: Symbol::from("val"),
            ty: Type::Var(42),
        }],
        docstring: None,
        internal: false,
    };
    let adt_type = Type::ADT(user_fqtn("Option"), vec![Type::Var(42)]);
    let scheme = build_constructor_scheme(&ctor, &adt_type, &[42]);

    assert_eq!(scheme.type_vars, vec![42]);
    assert_eq!(
        scheme.ty,
        Type::Fn(
            vec![Type::Var(42)],
            Box::new(Type::ADT(user_fqtn("Option"), vec![Type::Var(42)]))
        )
    );
}

// spec: 10-io §10.1 — is_internal_constructor returns true for internal ctors
#[test]
fn test_is_internal_constructor() {
    let tc = tf_io();
    let primitives_path = ModuleFullPath::from("primitives");
    let env = tc.env();
    // Bind carries `internal: true` on its `DefKind::Constructor`. Rooted
    // at its home module (primitives), the check resolves the Constructor
    // Def and reads the discriminator.
    assert!(
        env.is_internal_constructor_check_in_module(&primitives_path, "Bind"),
        "Bind must be reported internal"
    );
    // Non-internal IO constructors return false.
    assert!(!env.is_internal_constructor_check_in_module(&primitives_path, "Pure"));
    assert!(!env.is_internal_constructor_check_in_module(&primitives_path, "Effect"));
    // Unknown constructors return false.
    assert!(!env.is_internal_constructor_check_in_module(&primitives_path, "NoSuchCtor"));
}

// spec: 10-io §10.1 — internal-ctor check chain-follows Import entries.
//
// Regression for the Wave-4c enforcement defect: when `Bind` is reachable
// from a module via a glob import (the realistic shape — `user`/`test`
// imports `primitives`), the `internal` discriminator must still be read
// through the Import entry. A direct probe returned the Import (not the
// Constructor Def) and silently reported `false`, so `(Bind …)` resolved
// and compiled in user code.
#[test]
fn test_is_internal_constructor_through_import() {
    use cranelisp_types::{FQSymbol, Symbol, Visibility};
    let tc = tf_io();
    let user_path = ModuleFullPath::from("user");
    // Seed user-module Imports of `Bind` and its parent `IO` type from
    // primitives — what a glob import of primitives materialises (both the
    // constructor name and the type name land as Import entries).
    {
        let mut user_tbl = tc.modules.get_mut(&user_path).unwrap();
        for (name, source) in [("Bind", "IO.Bind"), ("IO", "IO")] {
            user_tbl
                .expose_candidate(
                    Symbol::from(name),
                    FQSymbol {
                        module: ModuleFullPath::from("primitives"),
                        symbol: Symbol::from(source),
                    },
                    Visibility::Public,
                )
                .unwrap();
        }
    }
    let env = tc.env();
    assert!(
        env.is_internal_constructor_check_in_module(&user_path, "Bind"),
        "Bind imported into user must still be reported internal \
             (chain-follow the Import to the primitives Constructor Def)"
    );
}

// spec: 10-io §10.1 — exhaustiveness excludes internal constructors
#[test]
fn test_exhaustiveness_excludes_internal_constructors() {
    let tc = tf_io();
    let primitives_path = ModuleFullPath::from("primitives");
    // IO has Pure (tag=0), Effect (tag=1), Bind (tag=2, internal).
    // Exhaustiveness should only require Pure and Effect.
    let covered = vec![Symbol::from("Pure"), Symbol::from("Effect")];
    assert!(
        tc.check_exhaustiveness_in_module(
            &primitives_path,
            &TypeName::from("IO"),
            &covered,
            false,
            Span::SYNTHETIC,
        )
        .is_ok(),
        "matching Pure + Effect should be exhaustive (Bind is internal)"
    );

    // Missing Effect should fail.
    let covered = vec![Symbol::from("Pure")];
    let err = tc
        .check_exhaustiveness_in_module(
            &primitives_path,
            &TypeName::from("IO"),
            &covered,
            false,
            Span::SYNTHETIC,
        )
        .unwrap_err();
    assert!(
        err.message().contains("Effect"),
        "should report missing Effect, got: {}",
        err.message()
    );
    // Should NOT mention Bind.
    assert!(
        !err.message().contains("Bind"),
        "should not mention internal Bind"
    );
}
