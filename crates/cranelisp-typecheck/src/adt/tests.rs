    use super::*;
    use crate::builtins::FixtureBuilder;
    use crate::checker::TestFixture;
    use cranelisp_types::{ConstructorDef, ModuleFullPath};

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
        TestFixture::with_content(
            FixtureBuilder::new().with_builtin_type_names().with_io(),
        )
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
        assert!(tc.symbol_table().get("Red").is_some());
        assert!(tc.symbol_table().get("Green").is_some());
        assert!(tc.symbol_table().get("Blue").is_some());

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

        if let Some(ModuleEntry::Def { kind, scheme, .. }) = tc.symbol_table().get("True2")
            && matches!(kind.as_ref(), DefKind::Constructor { .. })
        {
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
        if let Some(ModuleEntry::Def { kind, scheme, .. }) = tc.symbol_table().get("None")
            && matches!(kind.as_ref(), DefKind::Constructor { .. })
        {
            assert_eq!(scheme.type_vars.len(), 1, "None should have 1 quantified var");
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
        if let Some(ModuleEntry::Def { kind, scheme, .. }) = tc.symbol_table().get("Some")
            && matches!(kind.as_ref(), DefKind::Constructor { .. })
        {
            assert_eq!(scheme.type_vars.len(), 1, "Some should have 1 quantified var");
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
                user.insert(
                    Symbol::from(ty),
                    cranelisp_types::ModuleEntry::Import {
                        source: cranelisp_types::FQSymbol {
                            module: cranelisp_types::ModuleFullPath::from("primitives"),
                            symbol: Symbol::from(ty),
                        },
                        visibility: Visibility::Public,
                    },
                );
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
                        type_expr: cranelisp_types::TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int"))),
                        span: Span::SYNTHETIC,
                    },
                    cranelisp_types::FieldDef {
                        name: Symbol::from("y"),
                        type_expr: cranelisp_types::TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Bool"))),
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
        if let Some(ModuleEntry::Def { kind, scheme, .. }) = tc.symbol_table().get("MkPair")
            && matches!(kind.as_ref(), DefKind::Constructor { .. })
        {
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
        if let Some(ModuleEntry::Def { kind, scheme, param_names, .. }) =
            tc.symbol_table().get("MkPair")
        {
            if let DefKind::Constructor { field_count, .. } = kind.as_ref() {
                assert_eq!(*field_count, 2);
            } else {
                panic!("MkPair should be DefKind::Constructor");
            }
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
                user.insert(
                    Symbol::from(ty),
                    cranelisp_types::ModuleEntry::Import {
                        source: cranelisp_types::FQSymbol {
                            module: cranelisp_types::ModuleFullPath::from("primitives"),
                            symbol: Symbol::from(ty),
                        },
                        visibility: Visibility::Public,
                    },
                );
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

    // spec: 05-definitions §5.2.6 — Generated Accessors. A product field
    // synthesises a free accessor fn `field :: (Fn [ProductType] FieldType)`,
    // born concrete (UserFn with a GOT slot), registered under the field name.
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

        // `v` is a concrete UserFn accessor with a GOT slot.
        match tc.symbol_table().get("v") {
            Some(entry @ ModuleEntry::Def { kind, scheme, ast, param_names, .. }) => {
                assert!(
                    matches!(
                        kind.as_ref(),
                        DefKind::UserFn {
                            fn_state: cranelisp_types::UserFnState::Concrete { .. }
                        }
                    ),
                    "accessor `v` must be a concrete UserFn"
                );
                assert!(entry.callable_got_slot().is_some(), "accessor needs a GOT slot");
                assert!(ast.is_some(), "accessor carries a synthesised match body");
                assert_eq!(param_names.len(), 1, "accessor takes one parameter");
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
            other => panic!("accessor `v` must be a Def, got {other:?}"),
        }
    }

    // spec: 05-definitions §5.2.6 — accessor synthesis over an existing
    // NON-accessor binding is refused (safe disposition): the existing binding
    // is kept, the collision is recorded for a non-fatal diagnostic, and the
    // accessor is NOT inserted (no silent shadow).
    #[test]
    fn accessor_collision_with_nonaccessor_is_refused() {
        let mut tc = tf_with_scalar_imports();
        // Seed a user binding `v` (a NotDetermined UserFn) BEFORE the deftype.
        tc.symbol_table_mut().insert(
            Symbol::from("v"),
            ModuleEntry::def(
                Scheme { type_vars: vec![], constraints: HashMap::new(), ty: Type::Int },
                DefKind::UserFn { fn_state: cranelisp_types::UserFnState::NotDetermined },
            )
            .visibility(Visibility::Public)
            .build(),
        );
        tc.register_type_def_self(
            &TypeName::from("Box"),
            &None,
            &[],
            &[product_int_field("Box", "v")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // A NotDetermined UserFn is NOT an accessor → the collision is refused.
        // The existing entry is unchanged (still NotDetermined), and the clash
        // is recorded as a deferred collision for the finalize warning.
        match tc.symbol_table().get("v") {
            Some(ModuleEntry::Def { kind, .. }) => assert!(
                matches!(
                    kind.as_ref(),
                    DefKind::UserFn {
                        fn_state: cranelisp_types::UserFnState::NotDetermined
                    }
                ),
                "existing non-accessor `v` must be preserved, not overwritten"
            ),
            other => panic!("`v` must still be the user binding, got {other:?}"),
        }
        assert!(
            tc.state
                .deferred_accessor_collisions
                .iter()
                .any(|(n, _)| n.as_ref() == "v"),
            "the accessor/binding collision must be recorded for a diagnostic"
        );
    }

    // spec: 05-definitions §5.2.6 "Duplicate field names in the same scope" +
    // 08-modules §8.6.5 bare-name ambiguity (user ruling S83 W2) — two product
    // types with the same field name POISON the bare accessor: it becomes
    // ambiguous (`ModuleEntry::Ambiguous`), NOT an argument-type-dispatched
    // overload and NOT a silently-picked winner. The second deftype is not
    // rejected as a duplicate definition; the colliding field's value stays
    // reachable via `match`. The owning types are recorded as the qualified
    // alternatives the ambiguity error lists.
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

        // Before the collision, `v` is a normal concrete first-class accessor.
        assert!(
            matches!(
                tc.symbol_table().get("v"),
                Some(ModuleEntry::Def { kind, .. })
                    if matches!(
                        kind.as_ref(),
                        DefKind::UserFn {
                            fn_state: cranelisp_types::UserFnState::Concrete { .. }
                        }
                    )
            ),
            "single-type accessor `v` is a concrete UserFn before any collision"
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

        // `v` is now POISONED — an `Ambiguous` sentinel, NOT an `Overloaded`
        // base and NOT a winner-picked concrete UserFn.
        match tc.symbol_table().get("v") {
            Some(ModuleEntry::Ambiguous { .. }) => {}
            other => panic!(
                "`v` must be poisoned (Ambiguous) after the cross-type field-name \
                 collision, got {other:?}"
            ),
        }
        // It is NOT folded into the overload mechanism: no `Overloaded` base, no
        // mangled `v$Box`/`v$Cup` variants exist.
        assert!(
            tc.symbol_table().get("v$Box").is_none()
                && tc.symbol_table().get("v$Cup").is_none(),
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
    /// `synthesised_accessor_names`, only in the committed live table.
    fn new_cluster(tc: &mut TestFixture) {
        tc.state.synthesised_accessor_names.clear();
        tc.state.accessor_owning_types.clear();
        tc.state.deferred_accessor_collisions.clear();
    }

    // spec: 05-definitions §5.2.6 + 08-modules §8.6.5 (FIXME 0366) — at the REPL
    // each input is its own cluster, so a duplicate field-name accessor defined
    // in a LATER cluster must still POISON the bare name (ambiguous), re-deriving
    // the collision from the COMMITTED live accessor entry — NOT silently
    // first-wins. This pins the typecheck seam the e2e
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
        assert!(
            matches!(
                tc.symbol_table().get("v"),
                Some(ModuleEntry::Def { kind, .. })
                    if matches!(
                        kind.as_ref(),
                        DefKind::UserFn {
                            fn_state: cranelisp_types::UserFnState::Concrete { .. }
                        }
                    )
            ),
            "single-type accessor `v` is a concrete UserFn after cluster 1"
        );

        // Cluster boundary: fresh per-`CheckState` accessor tracking; the live
        // `v` accessor entry from cluster 1 stays committed.
        new_cluster(&mut tc);

        // Cluster 2: `Cup` with the SAME field name `v`. The set-only classifier
        // would mis-read this as a non-accessor collision (suppress-and-first-
        // wins); the committed-live re-derivation poisons it instead.
        tc.register_type_def_self(
            &TypeName::from("Cup"),
            &None,
            &[],
            &[product_int_field("Cup", "v")],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // `v` is POISONED (`Ambiguous`), exactly as in the single-cluster
        // (`--run`/`--link`) path — NOT first-wins-suppressed.
        match tc.symbol_table().get("v") {
            Some(ModuleEntry::Ambiguous { .. }) => {}
            other => panic!(
                "cross-cluster duplicate-field accessor `v` must be poisoned \
                 (Ambiguous), got {other:?}"
            ),
        }
        // It was NOT routed down the suppress-and-first-wins (non-accessor)
        // refusal path: no deferred collision recorded for `v`.
        assert!(
            !tc.state
                .deferred_accessor_collisions
                .iter()
                .any(|(n, _)| n.as_ref() == "v"),
            "cross-cluster duplicate field must poison, not record a \
             suppress-and-first-wins refusal"
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
        assert!(names.contains(&"Box"), "Box must be an alternative, got {names:?}");
        assert!(names.contains(&"Cup"), "Cup must be an alternative, got {names:?}");
    }

    // spec: 05-definitions §5.2.6 (FIXME 0366) — NEGATIVE: a SINGLE product
    // type's accessor synthesised in its own cluster, with no duplicate field
    // name across types, must remain a normal concrete accessor across cluster
    // boundaries (the legitimate case must not be wrongly poisoned).
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
        // `v` stays a concrete accessor; `w` is a fresh concrete accessor.
        for name in ["v", "w"] {
            assert!(
                matches!(
                    tc.symbol_table().get(name),
                    Some(ModuleEntry::Def { kind, .. })
                        if matches!(
                            kind.as_ref(),
                            DefKind::UserFn {
                                fn_state: cranelisp_types::UserFnState::Concrete { .. }
                            }
                        )
                ),
                "distinct-field accessor `{name}` must remain a concrete UserFn \
                 across clusters (no spurious poison), got {:?}",
                tc.symbol_table().get(name)
            );
        }
    }

    // spec: 05-definitions §5.2.6 (FIXME 0366) — NEGATIVE: re-running the SAME
    // deftype in a later cluster (a redefinition, NOT two distinct types sharing
    // a field name) must NOT poison its accessor — the committed accessor's
    // owning type equals the type being re-synthesised, so it overwrites afresh.
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
        // `v` is still a normal concrete accessor — a same-type redefinition is
        // not a cross-type duplicate-field collision.
        match tc.symbol_table().get("v") {
            Some(ModuleEntry::Def { kind, .. })
                if matches!(
                    kind.as_ref(),
                    DefKind::UserFn {
                        fn_state: cranelisp_types::UserFnState::Concrete { .. }
                    }
                ) => {}
            other => panic!(
                "`v` after a same-type Box redefinition must stay a concrete \
                 accessor, not be poisoned, got {other:?}"
            ),
        }
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
        assert!(tc
            .check_exhaustiveness(&TypeName::from("Color"), &covered, false, Span::SYNTHETIC)
            .is_ok());
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
        assert!(tc
            .check_exhaustiveness(&TypeName::from("Color"), &[], true, Span::SYNTHETIC)
            .is_ok());
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
            if let Some(ModuleEntry::Def { kind, .. }) = table.get(*name) {
                if let DefKind::Constructor { tag, .. } = kind.as_ref() {
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
            if let Some(ModuleEntry::Def { kind, .. }) = table.get(*name)
                && let DefKind::Constructor { tag, .. } = kind.as_ref()
            {
                assert_eq!(*tag, i, "{name} should have tag {i}");
            } else {
                panic!("{name} should be Def(Constructor)");
            }
        }
    }

    // spec: 04-adt §4.2 — constructors are GOT-slotted callable values (0249-a)
    //
    // Every synthesised `DefKind::Constructor` entry must carry a `got_slot`,
    // exactly like a user fn — a constructor reached as a value (`(map Some
    // xs)`, `(let [f None] f)`) needs an address to load. Distinct
    // constructors get distinct slots (monotonic allocator, no aliasing). The
    // +Neg facet: the nullary `None` is slotted too — addressability does not
    // depend on arity, so a naive "only data ctors need slots" implementation
    // (which would leave `None` at `None`) is rejected.
    #[test]
    fn constructors_get_got_slots() {
        let mut tc = tf();
        register_option(&mut tc);

        let table = tc.symbol_table();
        let slot_of = |name: &str| -> Option<usize> {
            match table.get(name) {
                Some(entry @ ModuleEntry::Def { kind, .. }) => {
                    assert!(
                        matches!(kind.as_ref(), DefKind::Constructor { .. }),
                        "{name} should be a Constructor entry"
                    );
                    // S83 (Principle 20): the ctor's slot rides on
                    // `DefKind::Constructor.got_slot`, read via the accessor.
                    entry.callable_got_slot()
                }
                _ => panic!("{name} should be a Def(Constructor) entry"),
            }
        };

        // Data constructor `Some` is slotted.
        let some_slot = slot_of("Some").expect("Some must have a GOT slot");
        // +Neg: the nullary constructor `None` is slotted too — not left at
        // `None` by an arity-gated implementation.
        let none_slot = slot_of("None").expect("nullary None must have a GOT slot");

        // Distinct constructors get distinct slots (monotonic allocator).
        assert_ne!(
            some_slot, none_slot,
            "distinct constructors must not alias the same GOT slot"
        );
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
        if let Some(ModuleEntry::Def { kind, scheme, param_names, .. }) =
            tc.symbol_table().get("Some")
        {
            if let DefKind::Constructor { field_count, .. } = kind.as_ref() {
                assert_eq!(*field_count, 1);
            } else {
                panic!("Some should be DefKind::Constructor");
            }
            assert_eq!(param_names.len(), 1);
            assert_eq!(param_names[0].as_ref(), "val");
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
            .check_exhaustiveness(
                &TypeName::from("Option"),
                &covered,
                false,
                Span::SYNTHETIC,
            )
            .unwrap_err();
        assert!(err.message().contains("None"));

        // Missing Some
        let covered = vec![Symbol::from("None")];
        let err = tc
            .check_exhaustiveness(
                &TypeName::from("Option"),
                &covered,
                false,
                Span::SYNTHETIC,
            )
            .unwrap_err();
        assert!(err.message().contains("Some"));

        // Both covered
        let covered = vec![Symbol::from("None"), Symbol::from("Some")];
        assert!(tc
            .check_exhaustiveness(
                &TypeName::from("Option"),
                &covered,
                false,
                Span::SYNTHETIC,
            )
            .is_ok());
    }

    // spec: 05-definitions §5.2.4 — shortcut product type with bare field names gets type vars
    #[test]
    fn test_shortcut_product_type() {
        // (deftype Pair [first second]) -- bare field names with type vars
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
        if let Some(ModuleEntry::Def { kind, scheme, .. }) = tc.symbol_table().get("MkPair")
            && matches!(kind.as_ref(), DefKind::Constructor { .. })
        {
            assert_eq!(scheme.type_vars.len(), 2, "MkPair should have 2 quantified vars");
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
        if let Some(ModuleEntry::Def { kind, scheme, .. }) = tc.symbol_table().get("Left")
            && matches!(kind.as_ref(), DefKind::Constructor { .. })
        {
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

        let opt_zero =
            TypeExpr::Applied(TypeRef::new(None, TypeName::from("Option")), vec![]);
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
            tag: 0,
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
            tag: 0,
            fields: vec![
                FieldInfo { name: Symbol::from("x"), ty: Type::Int },
                FieldInfo { name: Symbol::from("y"), ty: Type::Int },
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
            tag: 1,
            fields: vec![
                FieldInfo { name: Symbol::from("val"), ty: Type::Var(42) },
            ],
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
        use cranelisp_types::{ModuleEntry, Symbol, FQSymbol, Visibility};
        let tc = tf_io();
        let user_path = ModuleFullPath::from("user");
        // Seed user-module Imports of `Bind` and its parent `IO` type from
        // primitives — what a glob import of primitives materialises (both the
        // constructor name and the type name land as Import entries).
        {
            let mut user_tbl = tc.modules.get_mut(&user_path).unwrap();
            for name in ["Bind", "IO"] {
                user_tbl.insert(
                    Symbol::from(name),
                    ModuleEntry::Import {
                        source: FQSymbol {
                            module: ModuleFullPath::from("primitives"),
                            symbol: Symbol::from(name),
                        },
                        visibility: Visibility::Public,
                    },
                );
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
        assert!(tc
            .check_exhaustiveness_in_module(
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
        assert!(err.message().contains("Effect"), "should report missing Effect, got: {}", err.message());
        // Should NOT mention Bind.
        assert!(!err.message().contains("Bind"), "should not mention internal Bind");
    }
