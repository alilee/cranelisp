    use super::*;
    use crate::builtins::FixtureBuilder;
    use crate::checker::TestFixture;
    use cranelisp_types::{Defn, DefnVariant, FQSymbol, ModuleEntry, ModuleFullPath,
        Span, TraitDecl, TraitImpl, TraitMethodSig, TypeExpr, Visibility,
    };

    /// Empty fixture (FIXME 0243 narrowing). For the startup-negative tests
    /// that assert NOTHING is registered (no traits / no impls / no operators)
    /// — the empty builder is the most honest starting position for "nothing
    /// seeded" and also the minimal one.
    fn tf() -> TestFixture {
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
    fn tf_prims() -> TestFixture {
        TestFixture::with_content(
            FixtureBuilder::new().with_builtin_type_names().with_primitives(),
        )
    }

    /// Seed glob-import edges from `source` into the fixture's CURRENT module,
    /// mirroring `(import [source [*]])`. Import registration is no longer a
    /// typecheck concern (facade `typecheck.md`); tests seed the edges
    /// directly. Inserts an `Import` for every public symbol of `source`.
    fn seed_glob_import(tc: &mut TestFixture, source: &ModuleFullPath) {
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
    fn test_fqtn_trait(name: &str) -> FQTraitName {
        FQTraitName::new(ModuleFullPath::from("test"), TraitName::from(name))
    }

    /// Test helper: create an FQTypeName in the "test" module.
    fn test_fqtn(name: &str) -> FQTypeName {
        FQTypeName::new(ModuleFullPath::from("test"), TypeName::from(name))
    }

    /// Create a TypeChecker with primitives imported into a "test" module.
    /// Narrowed (FIXME 0243) from `TestFixture::new()` (= `full()`) to the
    /// builtin-type-names + primitives content the dependent tests consume.
    fn tc_with_prims() -> TestFixture {
        let mut tc = tf_prims();
        tc.set_current_module(ModuleFullPath::from("test"));
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
        tc
    }

    /// Make a test-only trait decl (not conflicting with builtins).
    fn make_test_trait_decl() -> TraitDecl {
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

    // spec: 07-traits §7.1 — no traits registered at startup
    #[test]
    fn test_no_traits_at_startup() {
        let tc = tf();
        // No traits should be discoverable via lookup
        assert!(tc.lookup_trait_decl(&TraitName::from("TestTrait")).is_none());
    }

    // spec: 07-traits §7.3 — no impls registered at startup
    #[test]
    fn test_no_impls_at_startup() {
        let tc = tf();
        // No impls should be discoverable via has_impl
        assert!(!tc.has_impl(&TraitName::from("Num"), &TypeName::from("Int")));
    }

    // spec: 03-types §3.6.1 — constraint detection: add and get trait constraints
    #[test]
    fn test_active_constraints_add_and_get() {
        let mut ac = ActiveConstraints::default();
        ac.add(0, test_fqtn_trait("Num"));
        assert_eq!(ac.get(0).map(|v| v.len()), Some(1));
        assert!(ac.get(1).is_none());
    }

    // spec: 03-types §3.6.2 — constraint propagation: duplicate adds are idempotent
    #[test]
    fn test_active_constraints_add_is_idempotent() {
        let mut ac = ActiveConstraints::default();
        ac.add(0, test_fqtn_trait("Num"));
        ac.add(0, test_fqtn_trait("Num"));
        ac.add(0, test_fqtn_trait("Eq"));
        ac.add(0, test_fqtn_trait("Eq"));
        let traits = ac.get(0).unwrap();
        assert_eq!(traits.len(), 2, "duplicate adds should be ignored");
        assert_eq!(traits[0].name.as_ref(), "Num");
        assert_eq!(traits[1].name.as_ref(), "Eq");
    }

    // spec: 03-types §3.6.2 — collect constraints for specific type variable set
    #[test]
    fn test_active_constraints_collect_for_vars() {
        let mut ac = ActiveConstraints::default();
        ac.add(0, test_fqtn_trait("Num"));
        ac.add(1, test_fqtn_trait("Eq"));

        let collected = ac.collect_for_vars(&[0, 2]);
        assert!(collected.contains_key(&0));
        assert!(!collected.contains_key(&1));
        assert!(!collected.contains_key(&2));
    }

    // spec: 03-types §3.6.2 — constraint state can be cleared
    #[test]
    fn test_active_constraints_clear() {
        let mut ac = ActiveConstraints::default();
        ac.add(0, test_fqtn_trait("Num"));
        ac.clear();
        assert!(ac.constraints.is_empty());
    }

    // spec: 07-traits §7.4.1 — concrete_type_name maps Int to TypeName
    #[test]
    fn test_concrete_type_name_int() {
        assert_eq!(concrete_type_name(&Type::Int), Some(TypeName::from("Int")));
    }

    // spec: 07-traits §7.4.1 — concrete_type_name maps Float to TypeName
    #[test]
    fn test_concrete_type_name_float() {
        assert_eq!(
            concrete_type_name(&Type::Float),
            Some(TypeName::from("Float"))
        );
    }

    // spec: 07-traits §7.4.1 — concrete_type_name maps Bool to TypeName
    #[test]
    fn test_concrete_type_name_bool() {
        assert_eq!(
            concrete_type_name(&Type::Bool),
            Some(TypeName::from("Bool"))
        );
    }

    // spec: 07-traits §7.4.1 — concrete_type_name maps String to TypeName
    #[test]
    fn test_concrete_type_name_string() {
        assert_eq!(
            concrete_type_name(&Type::String),
            Some(TypeName::from("String"))
        );
    }

    // spec: 07-traits §7.4.1 — concrete_type_name maps ADT to its TypeName
    #[test]
    fn test_concrete_type_name_adt() {
        assert_eq!(
            concrete_type_name(&Type::ADT(test_fqtn("Color"), vec![])),
            Some(TypeName::from("Color"))
        );
    }

    // spec: 07-traits §7.4.1 — type variable has no concrete type name
    #[test]
    fn test_concrete_type_name_var_is_none() {
        assert_eq!(concrete_type_name(&Type::Var(0)), None);
    }

    // spec: 07-traits §7.1 — deftrait registers trait and methods in symbol table
    #[test]
    fn test_register_trait_decl() {
        let mut tc = tf_prims();
        let decl = make_test_trait_decl();
        tc.register_trait_decl_self(&decl).unwrap();

        // Trait should be discoverable via SymbolTable lookup
        assert!(tc.lookup_trait_decl(&TraitName::from("TestTrait")).is_some());
        // Method should be reverse-mapped via trait_origin on ModuleEntry::Def
        assert_eq!(
            tc.method_to_trait(&Symbol::from("test-op")),
            Some(TraitName::from("TestTrait"))
        );
        // Trait should be in symbol table
        assert!(matches!(
            tc.symbol_table().get("TestTrait"),
            Some(ModuleEntry::TraitDecl { .. })
        ));
    }

    // spec: 07-traits §7.1 — a genuinely-DIFFERENT redeclaration of the same
    // trait name is an error. The conflicting decl shares the name `TestTrait`
    // but declares a different method (`other-op` instead of `test-op`), so it
    // is NOT the idempotent retry re-submission accommodated below — it must be
    // rejected.
    #[test]
    fn test_register_conflicting_duplicate_trait_fails() {
        let mut tc = tf_prims();
        let decl = make_test_trait_decl();
        tc.register_trait_decl_self(&decl).unwrap();

        // Same name, DIFFERENT method set — a real conflict.
        let mut conflicting = make_test_trait_decl();
        conflicting.methods[0].name = Symbol::from("other-op");
        let err = tc.register_trait_decl_self(&conflicting).unwrap_err();
        assert!(err.message().contains("already defined"));
    }

    // spec: spec/08-modules.md §8.2 — S86 D3. Re-registering the IDENTICAL trait
    // declaration is idempotent (a no-op), NOT an "already defined" error. The
    // cluster orchestration retries a module's typecheck from the top with no
    // saved resume index when a declared `(mod child)` submodule must load, so a
    // trait-defining module's `(deftrait …)` is re-submitted unchanged on the
    // retry pass; the registration must absorb the re-submission the same way
    // `register_type_def` upserts. Before the D3 fix this errored
    // `trait TestTrait already defined`.
    #[test]
    fn test_register_identical_trait_twice_is_idempotent() {
        let mut tc = tf_prims();
        let decl = make_test_trait_decl();
        tc.register_trait_decl_self(&decl).unwrap();
        // Identical re-submission (the retry-from-top shape) must succeed.
        tc.register_trait_decl_self(&decl)
            .expect("identical re-registration must be idempotent (S86 D3)");
        // The trait is still registered exactly once and resolvable.
        assert!(tc.lookup_trait_decl(&TraitName::from("TestTrait")).is_some());
    }

    // spec: 03-types §3.4.1 — trait method scheme carries trait constraint
    #[test]
    fn test_trait_method_has_constrained_scheme() {
        let mut tc = tf_prims();
        let decl = make_test_trait_decl();
        tc.register_trait_decl_self(&decl).unwrap();

        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("test-op") {
            assert_eq!(scheme.type_vars.len(), 1, "test-op should have 1 quantified var");
            assert!(
                !scheme.constraints.is_empty(),
                "test-op should have TestTrait constraint"
            );
            let var_id = scheme.type_vars[0];
            let traits = scheme.constraints.get(&var_id).unwrap();
            assert_eq!(traits.len(), 1);
            assert_eq!(traits[0].name.as_ref(), "TestTrait");
        } else {
            panic!("test-op should be registered");
        }
    }

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

    /// Nullary trait decl whose only method `z` takes no params and returns
    /// `Self` — the return-type-polymorphic shape (`(deftrait T (z [] self))`,
    /// `(default)`, `(zero)`, `(empty)`). There is no argument to dispatch on.
    fn make_nullary_return_poly_trait_decl() -> TraitDecl {
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
    fn register_nullary_rp_int_impl(tc: &mut TestFixture) {
        tc.register_trait_decl_self(&make_nullary_return_poly_trait_decl())
            .unwrap();
        let impl_ = TraitImpl {
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

    // spec: 07-traits §7.1 — is_trait_method distinguishes trait methods from plain fns
    #[test]
    fn test_is_trait_method() {
        let mut tc = tf_prims();
        let decl = make_test_trait_decl();
        tc.register_trait_decl_self(&decl).unwrap();

        assert!(tc.is_trait_method(&Symbol::from("test-op")));
        assert!(!tc.is_trait_method(&Symbol::from("add-i64")));
    }

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
            &TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Bool"))),
            &Type::Int,
            Span::SYNTHETIC,
            &mut var_map,
            &mut next_id,
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
        )
        .unwrap();
        let r2 = resolve_trait_type_expr(
            &TypeExpr::TypeVar(Symbol::from("b")),
            &Type::Int,
            Span::SYNTHETIC,
            &mut var_map,
            &mut next_id,
        )
        .unwrap();
        assert_eq!(r1, r2);
    }

    // spec: pipeline-orchestration §5 — no core traits at startup (Decision 17 eliminated)
    #[test]
    fn test_no_core_traits_at_startup() {
        let tc = tf();
        // Traits come from prelude .cl files, NOT compiler builtins.
        // No traits should be discoverable via SymbolTable lookup.
        assert!(tc.lookup_trait_decl(&TraitName::from("Num")).is_none(),
            "no traits should be registered at startup");
        assert!(!tc.has_impl(&TraitName::from("Num"), &TypeName::from("Int")),
            "no impls should be registered at startup");
    }

    // spec: pipeline-orchestration §5 — operator symbols NOT in symbol table at startup
    #[test]
    fn test_no_operators_at_startup() {
        let tc = tf();
        let ops = ["+", "-", "*", "/", "=", "!=", "<", ">", "<=", ">="];
        for op in ops {
            assert!(
                tc.symbol_table().get(op).is_none(),
                "operator {op} should NOT be in symbol table at startup"
            );
        }
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

    // -----------------------------------------------------------------------
    // Default method body generation tests
    // -----------------------------------------------------------------------

    use cranelisp_types::Expr;

    /// Helper: check that an expr is `Apply { callee: Var(name), .. }`
    fn assert_apply_callee(expr: &Expr, expected_name: &str) {
        if let Expr::Apply { callee, .. } = expr {
            if let Expr::Var { name, .. } = callee.as_ref() {
                assert_eq!(name.as_ref(), expected_name);
                return;
            }
        }
        panic!("expected Apply with callee Var({expected_name}), got {expr:?}");
    }

    /// Helper: extract Apply args
    fn apply_args(expr: &Expr) -> &[Expr] {
        if let Expr::Apply { args, .. } = expr {
            args.as_slice()
        } else {
            panic!("expected Apply, got {expr:?}");
        }
    }

    /// Helper: assert Var with given name
    fn assert_var(expr: &Expr, expected: &str) {
        if let Expr::Var { name, .. } = expr {
            assert_eq!(name.as_ref(), expected);
        } else {
            panic!("expected Var({expected}), got {expr:?}");
        }
    }

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

    // ---- Sprint 56 Wave 0 §9.4 — mono specialisation ast + distinct GOT slot ----

    /// Register a minimal `Num` trait with `+` and an impl for Int
    /// (identical in intent to `program::tests::register_num_trait_inline`, but
    /// kept local to the traits test module so we don't cross test-module boundaries).
    fn register_num_for_int(tc: &mut TestFixture) {
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

    /// Walk an Expr tree and visit every inferred_type, asserting it is concrete.
    fn assert_types_concrete(expr: &cranelisp_types::Expr) {
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

    // spec: design/typecheck/ast-annotation.md §9.4 — mono specialisation ast + distinct GOT slot
    #[test]
    fn wave0_mono_entry_registered_with_distinct_got_slot() {
        use cranelisp_types::Expr;
        let mut tc = tc_with_prims();
        register_num_for_int(&mut tc);

        // Template: (defn add [x y] (+ x y))
        let add_defn = cranelisp_types::TopLevel::Defn(Defn {
            name: Symbol::from("add"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("+"), Span::new(18, 19))),
                    args: vec![
                        Expr::var(Symbol::from("x"), Span::new(20, 21)),
                        Expr::var(Symbol::from("y"), Span::new(22, 23)),
                    ],
                    span: Span::new(17, 24),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: Span::new(0, 25),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 25),
        });
        tc.check_repl_input_self(&add_defn).unwrap();

        // Concrete call-site triggers monomorphisation: (defn main [] (add 1 2))
        let main_defn = cranelisp_types::TopLevel::Defn(Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("add"), Span::new(200, 203))),
                    args: vec![
                        Expr::IntLit { value: 1, span: Span::new(204, 205), inferred_type: None },
                        Expr::IntLit { value: 2, span: Span::new(206, 207), inferred_type: None },
                    ],
                    span: Span::new(199, 208),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: Span::new(180, 209),
            }],
            visibility: Visibility::Public,
            span: Span::new(180, 209),
        });
        tc.check_repl_input_self(&main_defn).unwrap();

        // Template entry: kind UserFn { constrained_fn: Some(_) }.
        // NOTE: §9.2 of design/typecheck/ast-annotation.md says the template's `ast`
        // "stays None" to signal "skip at codegen". That is the future intent — the
        // filter in `defined_symbols()` (§9.5) gates on `kind`, not `ast`, so the
        // invariant that matters today is `kind`. The mono entry below carries the
        // compilable body.
        let template_got_slot = {
            let st = tc.symbol_table();
            match st.get("add") {
                Some(entry @ ModuleEntry::Def { kind, .. }) => {
                    assert!(
                        matches!(
                            kind.as_ref(),
                            DefKind::UserFn { fn_state: UserFnState::Constrained(_) }
                        ),
                        "template 'add' kind should be UserFn(Constrained), got {:?}",
                        kind
                    );
                    // S83 (Principle 20): a constrained template carries no slot
                    // (read via the accessor) — `None` by construction.
                    entry.callable_got_slot()
                }
                other => panic!("'add' template should be Def entry, got {:?}", other),
            }
        };

        // Mono entry: kind UserFn(Concrete), ast: Some(..), has a GOT slot distinct from template.
        let mono_got_slot = {
            let st = tc.symbol_table();
            match st.get("add$Int+Int") {
                Some(entry @ ModuleEntry::Def { kind, ast, .. }) => {
                    assert!(
                        matches!(
                            kind.as_ref(),
                            DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }
                        ),
                        "mono 'add$Int+Int' kind should be UserFn(Concrete), got {:?}",
                        kind
                    );
                    let defn = ast.as_ref().expect("mono must carry ast: Some(..)");
                    // Per S69 Submission 35: ast: Option<DefnVariant>; the name lives on
                    // the symbol-table key ("add$Int+Int" here), not on the variant.

                    // All inferred types on the mono body are concrete.
                    assert_types_concrete(&defn.body);

                    // The resolved_call on the + call site must be set (SigDispatch or
                    // TraitMethod — both are valid concrete resolutions post-mono).
                    if let Expr::Apply { resolved_call, .. } = &defn.body {
                        assert!(
                            resolved_call.is_some(),
                            "mono body's + call site must have resolved_call set"
                        );
                    } else {
                        panic!("mono body should be Apply, got {:?}", defn.body);
                    }

                    entry.callable_got_slot().expect("mono must have a GOT slot assigned")
                }
                other => panic!("'add$Int+Int' mono should be Def entry, got {:?}", other),
            }
        };

        // Distinctness: template slot (if any) must differ from the mono slot.
        // Constrained templates usually get no slot (`None`); in that case any
        // Some(slot) on the mono is trivially distinct.
        if let Some(t) = template_got_slot {
            assert_ne!(
                t, mono_got_slot,
                "template and mono must have distinct GOT slots"
            );
        }
    }

    // spec: design/typecheck/ast-annotation.md §9.4 — resolved-stage annotations
    // live on the `MonoDefn.defn` AST, not on a side map (FIXME 0033).
    //
    // Pins the invariant that makes the S81 W-G `MonoDefn` side-map drop safe:
    // `monomorphise_call` returns a `MonoDefn` whose `defn` AST already carries
    // every `inferred_type` (concrete) and every call-site `resolved_call`. The
    // dropped `MonoDefn.resolutions` / `MonoDefn.expr_types` Span-keyed maps held
    // exactly this data; with them gone, the single source of truth is the AST.
    // This test reads the returned `MonoDefn` directly (not the registered
    // symbol-table entry) so it asserts the contract on `MonoDefn` itself.
    #[test]
    fn fixme0033_monodefn_annotations_live_on_defn_ast_not_side_maps() {
        use cranelisp_types::Expr;
        let mut tc = tc_with_prims();
        register_num_for_int(&mut tc);

        // Template: (defn add [x y] (+ x y)) — constrained on Num via the `+`.
        let add_defn = cranelisp_types::TopLevel::Defn(Defn {
            name: Symbol::from("add"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("+"), Span::new(18, 19))),
                    args: vec![
                        Expr::var(Symbol::from("x"), Span::new(20, 21)),
                        Expr::var(Symbol::from("y"), Span::new(22, 23)),
                    ],
                    span: Span::new(17, 24),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: Span::new(0, 25),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 25),
        });
        tc.check_repl_input_self(&add_defn).unwrap();

        // Drive `monomorphise_call` directly for `(add 1 2)` and capture the
        // returned `MonoDefn`. Construct the env borrowing individual fields so
        // `&mut tc.state` stays available (the test_support borrow-split idiom).
        let mono = {
            let env = TypeCheckEnv::new(
                &tc.modules,
                &tc.next_id,
                &tc.module_aliases,
                &tc.prelude_fallback,
            );
            env.monomorphise_call(
                &mut tc.state,
                &Symbol::from("add"),
                &[Type::Int, Type::Int],
                Span::new(199, 208),
                None,
            )
            .unwrap()
            .expect("(add 1 2) must monomorphise")
        };

        // The mono body is the single variant's body. Every inferred_type on it
        // is concrete — that is the data the dropped `expr_types` side map held.
        let body = &mono.defn.variants.first().expect("mono has a variant").body;
        assert_types_concrete(body);

        // The `+` call site carries a concrete `resolved_call` directly on the
        // AST node — the data the dropped `resolutions` side map held.
        if let Expr::Apply { resolved_call, .. } = body {
            assert!(
                resolved_call.is_some(),
                "mono body's + call site must carry resolved_call on the AST node \
                 (the dropped MethodResolutions side map is no longer the carrier)"
            );
        } else {
            panic!("mono body should be Apply, got {:?}", body);
        }
    }
