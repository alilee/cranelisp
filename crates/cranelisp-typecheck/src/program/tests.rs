    use super::*;
    use super::finalize::AmbiguousForm;
    use crate::checker::TestFixture;
    use cranelisp_types::{CompileContext, DefnVariant, Expr, FQSymbol, FQTypeName,
        ModuleEntry, ModuleFullPath, MonoDefnVariant, MonoExpr, Symbol,
        TraitDecl, TraitImpl, TraitMethodSig, TraitName, TypeExpr, TypeName, Visibility,
    };

    // spec: spec/05-definitions.md §5.1.2 (0576, MS-8 re-grounding) — the
    // multi-arity ambiguity diagnostic NAMES the offending arity clause + unpinned
    // param (not just the fn name), and NEVER leaks a synthetic `__` binder (0568).
    // S112 re-grounding: it cites §3.11 / the standalone-equivalence rationale (a
    // multi-sig defn is inference-equivalent to separate mutually-recursive
    // functions, so a genuinely-unpinned clause is the §3.11 ambiguity the
    // equivalent standalone function would also raise) — NOT the retired "each
    // arity clause is type-checked independently (§5.1.2)" framing. Message-
    // construction seam test.
    #[test]
    fn ambiguous_form_message_names_clause_and_param() {
        let sp = cranelisp_types::Span::new(0, 0);
        // Multi-arity clause + a named param → names both + cites §3.11.
        let m = AmbiguousForm {
            name: Symbol::from("rp"),
            span: sp,
            clause_arity: Some(2),
            param: Some(Symbol::from("rot")),
        }
        .message();
        assert!(m.contains("2-arg"), "names the offending clause by arity: {m}");
        assert!(m.contains("clause"), "says 'clause': {m}");
        assert!(m.contains("rot"), "names the unpinned param: {m}");
        assert!(m.contains("§3.11"), "cites the §3.11 standalone-equivalence rule: {m}");
        assert!(
            !m.contains("independently"),
            "MS-8: drops the retired 'each arity clause is type-checked \
             independently' framing: {m}"
        );
        assert!(!m.contains("__"), "never leaks a synthetic binder (0568): {m}");

        // Single-sig (no clause arity) + no bound param → the plain fn-level
        // message, still `__`-free.
        let plain = AmbiguousForm {
            name: Symbol::from("main"),
            span: sp,
            clause_arity: None,
            param: None,
        }
        .message();
        assert!(plain.contains("main") && plain.contains("ambiguous type"), "{plain}");
        assert!(!plain.contains("clause"), "single-sig keeps the plain message: {plain}");
        assert!(!plain.contains("__"), "no synthetic binder leak: {plain}");
    }

    /// Seed glob-import edges from `source` into the fixture's CURRENT module,
    /// mirroring `(import [source [*]])`. Import registration is no longer a
    /// typecheck concern (facade `typecheck.md`); tests seed edges directly.
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

    /// Seed specific-import edges for `names` from `source` into the fixture's
    /// CURRENT module, mirroring `(import [source [a b]])`. See `seed_glob_import`.
    fn seed_specific_import(tc: &mut TestFixture, source: &ModuleFullPath, names: &[&str]) {
        for name in names {
            tc.symbol_table_mut().insert(
                Symbol::from(*name),
                ModuleEntry::Import {
                    source: FQSymbol {
                        module: source.clone(),
                        symbol: Symbol::from(*name),
                    },
                    visibility: Visibility::Public,
                },
            );
        }
    }

    /// Test helper: create an FQTypeName in the "test" module (used by tc_with_prims()).
    fn test_fqtn(name: &str) -> FQTypeName {
        FQTypeName::new(ModuleFullPath::from("test"), TypeName::from(name))
    }

    fn span(start: u32, end: u32) -> Span {
        Span::new(start, end)
    }

    /// Create a single-sig Defn (convenience for tests).
    ///
    /// Per S69 Submission 23: `DefnVariant.params: Vec<(Symbol, Option<TypeExpr>)>`
    /// (fused) — the prior parallel-vec `params: Vec<Symbol>` +
    /// `param_annotations: Vec<Option<TypeExpr>>` shape was eliminated.
    fn make_defn(
        name: &str,
        params: Vec<Symbol>,
        param_annotations: Vec<Option<TypeExpr>>,
        body: Expr,
        visibility: Visibility,
        span: Span,
    ) -> Defn {
        assert_eq!(params.len(), param_annotations.len(), "params/annotations must lockstep");
        let fused: Vec<(Symbol, Option<TypeExpr>)> = params
            .into_iter()
            .zip(param_annotations.into_iter())
            .collect();
        Defn {
            name: Symbol::from(name),
            docstring: None,
            variants: vec![DefnVariant {
                params: fused,
                body,
                span,
            }],
            visibility,
            span,
        }
    }

    /// Create a TypeChecker with primitives imported into a "test" module.
    ///
    /// Narrowed (FIXME 0243) from `TestFixture::new()` (= `full()`) to the
    /// content the program-level pipeline tests in this file consume: builtin
    /// type names + the Ring 0/1/3 primitive `Def`s + the synthetic `macros`
    /// module + the IO ADT (`Bind`/`Pure`/`Effect` are referenced directly).
    /// Only `with_special_forms()` is dropped — special forms are resolved at
    /// the AST level, never via symbol-table name lookup, and no test in this
    /// file probes the special-form entries. Bootstrap order requires
    /// `with_builtin_type_names()` before primitives / macros / IO.
    fn tc_with_prims() -> TestFixture {
        let mut tc = TestFixture::with_content(
            crate::builtins::FixtureBuilder::new()
                .with_builtin_type_names()
                .with_primitives()
                .with_macros_sexp()
                .with_io(),
        );
        tc.set_current_module(ModuleFullPath::from("test"));
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
        tc
    }

    /// Test helper: walk an Expr tree, recording whether any node carries an
    /// `inferred_type` annotation and whether all annotations are resolved
    /// (no `Type::Var`). Used by tests that previously inspected
    /// `CheckResult.expr_types` — the post-slim equivalent is reading
    /// `inferred_type` from annotated AST nodes.
    fn walk_inferred_types(expr: &Expr, any_typed: &mut bool, all_resolved: &mut bool) {
        if let Some(ty) = expr.inferred_type() {
            *any_typed = true;
            if let Type::Var(_) = ty {
                *all_resolved = false;
            }
        }
        match expr {
            Expr::Apply { callee, args, .. } => {
                walk_inferred_types(callee, any_typed, all_resolved);
                for a in args {
                    walk_inferred_types(a, any_typed, all_resolved);
                }
            }
            Expr::If { cond, then_branch, else_branch, .. } => {
                walk_inferred_types(cond, any_typed, all_resolved);
                walk_inferred_types(then_branch, any_typed, all_resolved);
                walk_inferred_types(else_branch, any_typed, all_resolved);
            }
            Expr::Let { bindings, body, .. } => {
                for (_, bexpr) in bindings {
                    walk_inferred_types(bexpr, any_typed, all_resolved);
                }
                walk_inferred_types(body, any_typed, all_resolved);
            }
            Expr::Lambda { body, .. } => {
                walk_inferred_types(body, any_typed, all_resolved);
            }
            Expr::Match { scrutinee, arms, .. } => {
                walk_inferred_types(scrutinee, any_typed, all_resolved);
                for arm in arms {
                    walk_inferred_types(&arm.body, any_typed, all_resolved);
                }
            }
            Expr::VecLit { elements, .. } => {
                for e in elements {
                    walk_inferred_types(e, any_typed, all_resolved);
                }
            }
            Expr::Annotate { expr, .. } => {
                walk_inferred_types(expr, any_typed, all_resolved);
            }
            Expr::Trace { body, .. } => {
                walk_inferred_types(body, any_typed, all_resolved);
            }
            Expr::ParBind { bindings, body, .. } => {
                for (_, bexpr) in bindings {
                    walk_inferred_types(bexpr, any_typed, all_resolved);
                }
                walk_inferred_types(body, any_typed, all_resolved);
            }
            _ => {}
        }
    }

    /// Register a minimal Num trait with `+` method, plus an impl for Int,
    /// so tests using `(+ x y)` work after Decision 17 elimination.
    fn register_num_trait_inline(tc: &mut TestFixture) {
        let num_decl = TraitDecl {
            name: TraitName::from("Num"),
            docstring: None,
            // Conventional (kind-`*`) trait, `self`-based (S112 settled model —
            // the `Num self` constraint rides `self`).
            type_params: vec![],
            methods: vec![TraitMethodSig {
                name: Symbol::from("+"),
                docstring: None,
                params: vec![
                    (Symbol::from("lhs"), TypeExpr::SelfType),
                    (Symbol::from("rhs"), TypeExpr::SelfType),
                ],
                ret_type: TypeExpr::SelfType,
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        tc.register_trait_decl_self(&num_decl).unwrap();

        // impl Num for Int: + → add-i64
        let impl_ = TraitImpl {
            head_con_var: None,
            trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Num")),
            target: cranelisp_types::TypeExpr::Named(
                cranelisp_types::TypeRef::new(None, TypeName::from("Int")),
            ),
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
    }

    // spec: 05-definitions §5.1 — defn registers function with inferred type
    #[test]
    fn test_check_program_simple_defn() {
        let mut tc = tc_with_prims();
        // (defn add-one [x] (add-i64 x 1))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("add-one"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None)],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("add-i64"), span(20, 27))),
                    args: vec![
                        Expr::var(Symbol::from("x"), span(28, 29)),
                        Expr::IntLit {
                            value: 1,
                            span: span(30, 31),
                            inferred_type: None,
                        },
                    ],
                    span: span(19, 32),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(0, 33),
            }],
            visibility: Visibility::Public,
            span: span(0, 33),
        })];

        let _result = tc.check_program_self(&program).unwrap();

        // Check the function was registered with correct type: Fn([Int], Int)
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("add-one") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int))
            );
        } else {
            panic!("add-one not found in symbol table");
        }
    }

    // spec: 03-types §3.4 — identity function generalized to polymorphic scheme
    #[test]
    fn test_check_program_identity_is_polymorphic() {
        let mut tc = tc_with_prims();
        // (defn id [x] x)
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("id"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None)],
                body: Expr::var(Symbol::from("x"), span(14, 15)),
                span: span(0, 16),
            }],
            visibility: Visibility::Public,
            span: span(0, 16),
        })];

        tc.check_program_self(&program).unwrap();

        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("id") {
            // Should be forall [a]. Fn([a], a)
            assert_eq!(scheme.type_vars.len(), 1, "id should have 1 quantified var");
            match &scheme.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params.len(), 1);
                    assert_eq!(params[0], **ret);
                }
                _ => panic!("expected Fn type"),
            }
        } else {
            panic!("id not found in symbol table");
        }
    }

    // spec: 03-types §3.5.1 — recursive function inferred as monomorphic via self-reference
    #[test]
    fn test_check_program_recursive_function() {
        let mut tc = tc_with_prims();
        // (defn fact [n] (if (eq-i64 n 0) 1 (mul-i64 n (fact (sub-i64 n 1)))))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("fact"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("n"), None)],
                body: Expr::If {
                    cond: Box::new(Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("eq-i64"), span(20, 26))),
                        args: vec![
                            Expr::var(Symbol::from("n"), span(27, 28)),
                            Expr::IntLit {
                                value: 0,
                                span: span(29, 30),
                                inferred_type: None,
                            },
                        ],
                        span: span(19, 31),
                        resolved_call: None,
                        inferred_type: None,
                    }),
                    then_branch: Box::new(Expr::IntLit {
                        value: 1,
                        span: span(33, 34),
                        inferred_type: None,
                    }),
                    else_branch: Box::new(Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("mul-i64"), span(36, 43))),
                        args: vec![
                            Expr::var(Symbol::from("n"), span(44, 45)),
                            Expr::Apply {
                                callee: Box::new(Expr::var(Symbol::from("fact"), span(47, 51))),
                                args: vec![Expr::Apply {
                                    callee: Box::new(Expr::var(Symbol::from("sub-i64"), span(53, 60))),
                                    args: vec![
                                        Expr::var(Symbol::from("n"), span(61, 62)),
                                        Expr::IntLit {
                                            value: 1,
                                            span: span(63, 64),
                                            inferred_type: None,
                                        },
                                    ],
                                    span: span(52, 65),
                                    resolved_call: None,
                                    inferred_type: None,
                                }],
                                span: span(46, 66),
                                resolved_call: None,
                                inferred_type: None,
                            },
                        ],
                        span: span(35, 67),
                        resolved_call: None,
                        inferred_type: None,
                    }),
                    span: span(15, 68),
                    inferred_type: None,
                },
                span: span(0, 69),
            }],
            visibility: Visibility::Public,
            span: span(0, 69),
        })];

        tc.check_program_self(&program).unwrap();

        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("fact") {
            assert!(
                scheme.type_vars.is_empty(),
                "fact should be monomorphic (Int -> Int)"
            );
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int))
            );
        } else {
            panic!("fact not found in symbol table");
        }
    }

    // spec: 05-definitions §5.2 — deftype registers constructors and enables match
    #[test]
    fn test_check_program_with_typedef() {
        let mut tc = tc_with_prims();
        let program = vec![
            TopLevel::TypeDef {
                name: TypeName::from("Color"),
                docstring: None,
                type_params: vec![],
                constructors: vec![
                    cranelisp_types::ConstructorDef {
                        name: Symbol::from("Red"),
                        docstring: None,
                        fields: vec![],
                        span: Span::SYNTHETIC,
                    },
                    cranelisp_types::ConstructorDef {
                        name: Symbol::from("Green"),
                        docstring: None,
                        fields: vec![],
                        span: Span::SYNTHETIC,
                    },
                ],
                visibility: Visibility::Public,
                span: Span::SYNTHETIC,
            },
            TopLevel::Defn(Defn {
                name: Symbol::from("is-red"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("c"), None)],
                    body: Expr::Match {
                        scrutinee: Box::new(Expr::var(Symbol::from("c"), span(30, 31))),
                        arms: vec![
                            cranelisp_types::MatchArm {
                                pattern: cranelisp_types::Pattern::Constructor {
                                    name: cranelisp_types::SymbolRef::new(None, Symbol::from("Red")),
                                    bindings: vec![],
                                    span: span(33, 36),
                                },
                                body: Expr::BoolLit {
                                    value: true,
                                    span: span(37, 41),
                                    inferred_type: None,
                                },
                                span: span(33, 41),
                            },
                            cranelisp_types::MatchArm {
                                pattern: cranelisp_types::Pattern::Wildcard {
                                    span: span(42, 43),
                                },
                                body: Expr::BoolLit {
                                    value: false,
                                    span: span(44, 49),
                                    inferred_type: None,
                                },
                                span: span(42, 49),
                            },
                        ],
                        span: span(24, 50),
                        compiler_generated: false,
                        inferred_type: None,
                    },
                    span: span(0, 51),
                }],
                visibility: Visibility::Public,
                span: span(0, 51),
            }),
        ];

        let _result = tc.check_program_self(&program).unwrap();

        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("is-red") {
            assert_eq!(
                scheme.ty,
                Type::Fn(
                    vec![Type::ADT(test_fqtn("Color"), vec![])],
                    Box::new(Type::Bool)
                )
            );
        } else {
            panic!("is-red not found in symbol table");
        }

        // Type defs should be in the result
        assert!(tc.lookup_type_def(&TypeName::from("Color")).is_some());
        assert!(tc.lookup_constructor_type("Red").is_some());
    }

    // spec: 03-types §3.8 — unification failure produces type error
    #[test]
    fn test_check_program_type_error() {
        let mut tc = tc_with_prims();
        // (defn bad [x] (add-i64 x true)) -- type error: Bool arg to monomorphic Int primitive
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("bad"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None)],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("add-i64"), span(16, 23))),
                    args: vec![
                        Expr::var(Symbol::from("x"), span(24, 25)),
                        Expr::BoolLit {
                            value: true,
                            span: span(26, 30),
                            inferred_type: None,
                        },
                    ],
                    span: span(15, 31),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(0, 32),
            }],
            visibility: Visibility::Public,
            span: span(0, 32),
        })];

        // add-i64 has monomorphic type (Fn [Int Int] Int) so (add-i64 x true) is a
        // type error: Bool cannot unify with Int.
        let result = tc.check_program_self(&program);
        assert!(result.is_err());
    }

    // spec: 03-types §3.5.1 — all expression types fully resolved after inference
    #[test]
    fn test_check_program_expr_types_resolved() {
        let mut tc = tc_with_prims();
        // (defn inc [x] (add-i64 x 1))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("inc"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None)],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("add-i64"), span(16, 23))),
                    args: vec![
                        Expr::var(Symbol::from("x"), span(24, 25)),
                        Expr::IntLit {
                            value: 1,
                            span: span(26, 27),
                            inferred_type: None,
                        },
                    ],
                    span: span(15, 28),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(0, 29),
            }],
            visibility: Visibility::Public,
            span: span(0, 29),
        })];

        let _result = tc.check_program_self(&program).unwrap();

        // All expr_types should be resolved (no Var types)
        for (span, ty) in &tc.state_expr_types_resolved() {
            if let Type::Var(_) = ty {
                panic!("unresolved Var in expr_types at {span}");
            }
        }
    }

    // spec: 03-types §3.1 — REPL expression inferred as literal type
    #[test]
    fn test_check_repl_expression() {
        let mut tc = tc_with_prims();
        let input = TopLevel::Expr(Expr::IntLit {
            value: 42,
            span: span(0, 2),
            inferred_type: None,
        });
        let result = tc.check_repl_input_self(&input).unwrap();
        assert_eq!(result.display.as_ref().unwrap().ty, Type::Int);
        assert!(result.display.as_ref().unwrap().scheme.is_none());
    }

    // spec: 10-io §10.1 — internal `Bind` constructor rejected in head position.
    //
    // `tc_with_prims()` glob-imports primitives into the `test` module, so
    // `Bind` is reachable exactly as it is in a real REPL/user module. The
    // application head must be rejected because `Bind` is internal. The
    // continuation arg is irrelevant — rejection happens at head resolution.
    #[test]
    fn test_internal_bind_constructor_rejected_in_head_position() {
        let mut tc = tc_with_prims();
        // (Bind (Pure 1) (Pure 2)) — only the head matters for this gate.
        let input = TopLevel::Expr(Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("Bind"), span(1, 5))),
            args: vec![
                Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("Pure"), span(7, 11))),
                    args: vec![Expr::IntLit { value: 1, span: span(12, 13), inferred_type: None }],
                    span: span(6, 14),
                    resolved_call: None,
                    inferred_type: None,
                },
                Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("Pure"), span(16, 20))),
                    args: vec![Expr::IntLit { value: 2, span: span(21, 22), inferred_type: None }],
                    span: span(15, 23),
                    resolved_call: None,
                    inferred_type: None,
                },
            ],
            span: span(0, 24),
            resolved_call: None,
            inferred_type: None,
        });
        let err = tc.check_repl_input_self(&input).expect_err(
            "internal Bind constructor must be rejected in head position",
        );
        assert!(
            err.message().contains("internal"),
            "error should explain Bind is internal, got: {}",
            err.message()
        );
    }

    // spec: 10-io §10.1 — internal `Bind` constructor rejected in pattern position.
    #[test]
    fn test_internal_bind_constructor_rejected_in_pattern_position() {
        let mut tc = tc_with_prims();
        // (match (Pure 1) [(Bind a b) 0 _ 99])
        let input = TopLevel::Expr(Expr::Match {
            scrutinee: Box::new(Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("Pure"), span(8, 12))),
                args: vec![Expr::IntLit { value: 1, span: span(13, 14), inferred_type: None }],
                span: span(7, 15),
                resolved_call: None,
                inferred_type: None,
            }),
            arms: vec![
                cranelisp_types::MatchArm {
                    pattern: cranelisp_types::Pattern::Constructor {
                        name: cranelisp_types::SymbolRef::new(None, Symbol::from("Bind")),
                        bindings: vec![Symbol::from("a"), Symbol::from("b")],
                        span: span(17, 27),
                    },
                    body: Expr::IntLit { value: 0, span: span(28, 29), inferred_type: None },
                    span: span(17, 29),
                },
                cranelisp_types::MatchArm {
                    pattern: cranelisp_types::Pattern::Wildcard { span: span(30, 31) },
                    body: Expr::IntLit { value: 99, span: span(32, 34), inferred_type: None },
                    span: span(30, 34),
                },
            ],
            span: span(0, 35),
            compiler_generated: false,
            inferred_type: None,
        });
        let err = tc.check_repl_input_self(&input).expect_err(
            "internal Bind constructor must be rejected in pattern position",
        );
        assert!(
            err.message().contains("internal"),
            "error should explain Bind is internal, got: {}",
            err.message()
        );
    }

    // spec: 10-io §10.2 — non-internal IO constructor `Pure` is accepted in
    // head position (the internal gate must not over-trigger on public ctors).
    #[test]
    fn test_non_internal_constructor_accepted_in_head_position() {
        let mut tc = tc_with_prims();
        // (Pure 1) — Pure is public; must typecheck cleanly.
        let input = TopLevel::Expr(Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("Pure"), span(1, 5))),
            args: vec![Expr::IntLit { value: 1, span: span(6, 7), inferred_type: None }],
            span: span(0, 8),
            resolved_call: None,
            inferred_type: None,
        });
        let result = tc.check_repl_input_self(&input);
        assert!(
            result.is_ok(),
            "public Pure constructor must be accepted, got: {:?}",
            result.err().map(|e| e.message().to_string())
        );
    }

    // spec: 03-types §3.4 — REPL defn produces polymorphic scheme
    #[test]
    fn test_check_repl_defn() {
        let mut tc = tc_with_prims();
        let input = TopLevel::Defn(Defn {
            name: Symbol::from("id"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None)],
                body: Expr::var(Symbol::from("x"), span(14, 15)),
                span: span(0, 16),
            }],
            visibility: Visibility::Public,
            span: span(0, 16),
        });
        let result = tc.check_repl_input_self(&input).unwrap();

        // The scheme should be polymorphic
        let scheme = result.display.as_ref().unwrap().scheme.clone().unwrap();
        assert_eq!(scheme.type_vars.len(), 1);
    }

    // spec: 05-definitions §5.2 — REPL typedef registers type and constructors
    #[test]
    fn test_check_repl_typedef() {
        let mut tc = tc_with_prims();
        let input = TopLevel::TypeDef {
            name: TypeName::from("Dir"),
            docstring: None,
            type_params: vec![],
            constructors: vec![
                cranelisp_types::ConstructorDef {
                    name: Symbol::from("North"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
                cranelisp_types::ConstructorDef {
                    name: Symbol::from("South"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
            ],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let result = tc.check_repl_input_self(&input).unwrap();
        assert_eq!(result.display.as_ref().unwrap().ty, Type::ADT(test_fqtn("Dir"), vec![]));
        assert!(tc.lookup_type_def(&TypeName::from("Dir")).is_some());
    }

    // spec: 03-types §3.5.1 — forward references resolved via two-pass inference
    #[test]
    fn test_check_program_forward_reference() {
        let mut tc = tc_with_prims();
        // Two functions where the first calls the second
        // (defn double [x] (add-self x))
        // (defn add-self [y] (add-i64 y y))
        //
        // add-i64 is monomorphic (Fn [Int Int] Int), so add-self is pinned to Int.
        // double's type unifies with add-self's type through the call.
        let program = vec![
            TopLevel::Defn(Defn {
                name: Symbol::from("double"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("x"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add-self"), span(18, 26))),
                        args: vec![Expr::var(Symbol::from("x"), span(27, 28))],
                        span: span(17, 29),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(0, 30),
                }],
                visibility: Visibility::Public,
                span: span(0, 30),
            }),
            TopLevel::Defn(Defn {
                name: Symbol::from("add-self"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("y"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add-i64"), span(48, 55))),
                        args: vec![
                            Expr::var(Symbol::from("y"), span(56, 57)),
                            Expr::var(Symbol::from("y"), span(58, 59)),
                        ],
                        span: span(47, 60),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(31, 61),
                }],
                visibility: Visibility::Public,
                span: span(31, 61),
            }),
        ];

        tc.check_program_self(&program).unwrap();

        // add-self is monomorphic: Fn([Int], Int) — add-i64 pins y to Int
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("add-self") {
            assert!(
                scheme.type_vars.is_empty(),
                "add-self should have no quantified vars (monomorphic via add-i64)"
            );
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                "add-self: (Fn [Int] Int)"
            );
        } else {
            panic!("add-self not found in symbol table");
        }

        // double should also be monomorphic (calls add-self with Int)
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("double") {
            assert!(
                scheme.type_vars.is_empty(),
                "double should have no quantified vars (monomorphic via add-self)"
            );
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                "double: (Fn [Int] Int)"
            );
        } else {
            panic!("double not found in symbol table");
        }
    }

    // spec: 03-types §3.9 — type annotation pins parameter type in forward reference
    #[test]
    fn test_check_program_forward_reference_pinned() {
        let mut tc = tc_with_prims();
        // (defn double [:Int x] (add-self x))
        // (defn add-self [y] (add-i64 y y))
        // Both are monomorphic: add-i64 pins y to Int, and annotation pins x to Int.
        let program = vec![
            TopLevel::Defn(Defn {
                name: Symbol::from("double"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("x"), Some(cranelisp_types::TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int")))))],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add-self"), span(118, 126))),
                        args: vec![Expr::var(Symbol::from("x"), span(127, 128))],
                        span: span(117, 129),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(100, 130),
                }],
                visibility: Visibility::Public,
                span: span(100, 130),
            }),
            TopLevel::Defn(Defn {
                name: Symbol::from("add-self"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("y"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add-i64"), span(148, 155))),
                        args: vec![
                            Expr::var(Symbol::from("y"), span(156, 157)),
                            Expr::var(Symbol::from("y"), span(158, 159)),
                        ],
                        span: span(147, 160),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(131, 161),
                }],
                visibility: Visibility::Public,
                span: span(131, 161),
            }),
        ];

        tc.check_program_self(&program).unwrap();

        // double is pinned: Fn([Int], Int) — annotation + add-i64 both constrain to Int
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("double") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int))
            );
        } else {
            panic!("double not found");
        }

        // add-self is also pinned: Fn([Int], Int) — add-i64 constrains y to Int
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("add-self") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int))
            );
        } else {
            panic!("add-self not found");
        }
    }

    // spec: 07-traits §7.5 — builtin function call resolved as BuiltinFn in method resolutions
    #[test]
    fn test_check_program_check_result_has_builtin_resolutions() {
        let mut tc = tc_with_prims();
        // (defn inc [x] (add-i64 x 1))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("inc"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None)],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("add-i64"), span(16, 23))),
                    args: vec![
                        Expr::var(Symbol::from("x"), span(24, 25)),
                        Expr::IntLit {
                            value: 1,
                            span: span(26, 27),
                            inferred_type: None,
                        },
                    ],
                    span: span(15, 28),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(0, 29),
            }],
            visibility: Visibility::Public,
            span: span(0, 29),
        })];

        let _result = tc.check_program_self(&program).unwrap();

        // The add-i64 call site should have a BuiltinFn resolution. Post-slim,
        // resolutions are drained off `state` into annotated ASTs on the
        // unified `check_forms` pipeline (which `check_program_self` now uses),
        // so read them back via `annotated_resolutions()`.
        let method_resolutions = tc.annotated_resolutions();
        assert!(!method_resolutions.is_empty());
        let resolution = method_resolutions.get(&span(15, 28)).unwrap();
        match resolution {
            cranelisp_types::ResolvedCall::BuiltinFn { name } => {
                assert_eq!(name.as_ref(), "add-i64");
            }
            _ => panic!("expected BuiltinFn"),
        }
    }

    // --- Ring 1: Polymorphic ADT program tests ---

    // spec: 05-definitions §5.2.2 — polymorphic typedef registers constructors with type params
    #[test]
    fn test_check_program_polymorphic_typedef() {
        let mut tc = tc_with_prims();
        // (deftype (Option a) None (Some [:a val]))
        // (defn unwrap-or [opt default] (match opt [(Some x) x (None default)]))
        let program = vec![
            TopLevel::TypeDef {
                name: TypeName::from("Option"),
                docstring: None,
                type_params: vec![Symbol::from("a")],
                constructors: vec![
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
                            type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("a")),
                            span: Span::SYNTHETIC,
                        }],
                        span: Span::SYNTHETIC,
                    },
                ],
                visibility: Visibility::Public,
                span: Span::SYNTHETIC,
            },
        ];

        let _result = tc.check_program_self(&program).unwrap();
        assert!(tc.lookup_type_def(&TypeName::from("Option")).is_some());
        assert!(tc.lookup_constructor_type("Some").is_some());
        assert!(tc.lookup_constructor_type("None").is_some());
    }

    // spec: 05-definitions §5.2.2 — REPL polymorphic typedef registers type defs
    #[test]
    fn test_check_repl_polymorphic_typedef() {
        let mut tc = tc_with_prims();
        let input = TopLevel::TypeDef {
            name: TypeName::from("Option"),
            docstring: None,
            type_params: vec![Symbol::from("a")],
            constructors: vec![
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
                        type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("a")),
                        span: Span::SYNTHETIC,
                    }],
                    span: Span::SYNTHETIC,
                },
            ],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let _result = tc.check_repl_input_self(&input).unwrap();
        assert!(tc.lookup_type_def(&TypeName::from("Option")).is_some());
    }

    // spec: 03-types §3.1 — string literal inferred as String type
    #[test]
    fn test_check_repl_string_expression() {
        let mut tc = tc_with_prims();
        let input = TopLevel::Expr(Expr::StringLit {
            value: "hello".to_string(),
            span: span(0, 7),
            inferred_type: None,
        });
        let result = tc.check_repl_input_self(&input).unwrap();
        assert_eq!(result.display.as_ref().unwrap().ty, Type::String);
    }

    // spec: 03-types §3.1 — function returning string literal has String return type
    #[test]
    fn test_check_program_string_in_function() {
        let mut tc = tc_with_prims();
        // (defn greet [] "hello")
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("greet"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::StringLit {
                    value: "hello".to_string(),
                    span: span(16, 23),
                    inferred_type: None,
                },
                span: span(0, 24),
            }],
            visibility: Visibility::Public,
            span: span(0, 24),
        })];

        tc.check_program_self(&program).unwrap();

        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("greet") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![], Box::new(Type::String))
            );
        } else {
            panic!("greet not found in symbol table");
        }
    }

    // --- Ring 2: Constrained polymorphism tests ---

    // A `var_refs` map carrying a `VarRef::Global` entry for EVERY `Var` span in
    // `expr` — so the FIXME-0653 shadow guard (`callee_has_keyed_carrier`, which
    // under the S114 carrier flip discriminates `Global` from `Local`) treats
    // every callee as a genuine keyed TABLE reference. These name-scan-mechanism
    // tests exercise the collector's name matching, not the shadow discipline, so
    // a full-Global map keeps them testing exactly what they did before the guard.
    fn all_var_carriers(expr: &Expr) -> HashMap<Span, cranelisp_types::VarRef> {
        fn walk(e: &Expr, m: &mut HashMap<Span, cranelisp_types::VarRef>) {
            if let Expr::Var { span, .. } = e {
                m.insert(
                    *span,
                    cranelisp_types::VarRef::Global(FQSymbol {
                        module: ModuleFullPath::from("test"),
                        symbol: Symbol::from("x"),
                    }),
                );
            }
            crate::program::for_each_child_expr(e, |c| walk(c, m));
        }
        let mut m = HashMap::new();
        walk(expr, &mut m);
        m
    }

    // spec: 03-types §3.6 — collect_constrained_calls finds direct call to constrained fn
    #[test]
    fn test_collect_constrained_calls_finds_direct_call() {
        let constrained = HashSet::from([Symbol::from("add")]);
        // (add x y) where add is constrained
        let expr = Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("add"), span(1, 4))),
            args: vec![
                Expr::var(Symbol::from("x"), span(5, 6)),
                Expr::var(Symbol::from("y"), span(7, 8)),
            ],
            span: span(0, 9),
            resolved_call: None,
            inferred_type: None,
        };

        let mut calls = Vec::new();
        TypeCheckEnv::<()>::collect_constrained_calls(&expr, &constrained, &all_var_carriers(&expr), &mut calls);

        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].0.as_ref(), "add");
        assert_eq!(calls[0].1.len(), 2); // two arg spans
        assert_eq!(calls[0].2, span(0, 9)); // call span
    }

    // spec: 03-types §3.6 — collect_constrained_calls ignores non-constrained functions
    #[test]
    fn test_collect_constrained_calls_ignores_non_constrained() {
        let constrained = HashSet::from([Symbol::from("add")]);
        // (sub-i64 x y) where sub-i64 is NOT constrained
        let expr = Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("sub-i64"), span(1, 8))),
            args: vec![
                Expr::var(Symbol::from("x"), span(9, 10)),
                Expr::var(Symbol::from("y"), span(11, 12)),
            ],
            span: span(0, 13),
            resolved_call: None,
            inferred_type: None,
        };

        let mut calls = Vec::new();
        TypeCheckEnv::<()>::collect_constrained_calls(&expr, &constrained, &all_var_carriers(&expr), &mut calls);

        assert!(calls.is_empty());
    }

    // spec: 03-types §3.6 — collect_constrained_calls recurses into let bindings
    #[test]
    fn test_collect_constrained_calls_recurses_into_let() {
        let constrained = HashSet::from([Symbol::from("add")]);
        // (let [z (add x y)] z)
        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("z"),
                Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("add"), span(10, 13))),
                    args: vec![
                        Expr::var(Symbol::from("x"), span(14, 15)),
                        Expr::var(Symbol::from("y"), span(16, 17)),
                    ],
                    span: span(9, 18),
                    resolved_call: None,
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::var(Symbol::from("z"), span(20, 21))),
            span: span(0, 22),
            inferred_type: None,
        };

        let mut calls = Vec::new();
        TypeCheckEnv::<()>::collect_constrained_calls(&expr, &constrained, &all_var_carriers(&expr), &mut calls);

        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].0.as_ref(), "add");
    }

    // spec: 03-types §3.6 — collect_constrained_calls recurses into if branches
    #[test]
    fn test_collect_constrained_calls_recurses_into_if() {
        let constrained = HashSet::from([Symbol::from("add")]);
        // (if true (add 1 2) (add 3 4))
        let expr = Expr::If {
            cond: Box::new(Expr::BoolLit { value: true, span: span(4, 8), inferred_type: None, }),
            then_branch: Box::new(Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("add"), span(10, 13))),
                args: vec![
                    Expr::IntLit { value: 1, span: span(14, 15), inferred_type: None, },
                    Expr::IntLit { value: 2, span: span(16, 17), inferred_type: None, },
                ],
                span: span(9, 18),
                resolved_call: None,
                inferred_type: None,
            }),
            else_branch: Box::new(Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("add"), span(20, 23))),
                args: vec![
                    Expr::IntLit { value: 3, span: span(24, 25), inferred_type: None, },
                    Expr::IntLit { value: 4, span: span(26, 27), inferred_type: None, },
                ],
                span: span(19, 28),
                resolved_call: None,
                inferred_type: None,
            }),
            span: span(0, 29),
            inferred_type: None,
        };

        let mut calls = Vec::new();
        TypeCheckEnv::<()>::collect_constrained_calls(&expr, &constrained, &all_var_carriers(&expr), &mut calls);

        assert_eq!(calls.len(), 2, "should find calls in both branches");
    }

    // spec: 03-types §3.6 — batch mode monomorphises constrained fn at concrete call site
    #[test]
    fn test_batch_monomorphise_generates_mono_defn() {
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);
        // Program: (defn add [x y] (+ x y))  -- constrained via +
        //          (defn main [] (add 3 4))   -- concrete Int call site
        let program = vec![
            TopLevel::Defn(Defn {
                name: Symbol::from("add"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("+"), span(18, 19))),
                        args: vec![
                            Expr::var(Symbol::from("x"), span(20, 21)),
                            Expr::var(Symbol::from("y"), span(22, 23)),
                        ],
                        span: span(17, 24),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(0, 25),
                }],
                visibility: Visibility::Public,
                span: span(0, 25),
            }),
            TopLevel::Defn(Defn {
                name: Symbol::from("main"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add"), span(40, 43))),
                        args: vec![
                            Expr::IntLit { value: 3, span: span(44, 45), inferred_type: None, },
                            Expr::IntLit { value: 4, span: span(46, 47), inferred_type: None, },
                        ],
                        span: span(39, 48),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(26, 49),
                }],
                visibility: Visibility::Public,
                span: span(26, 49),
            }),
        ];

        let _result = tc.check_program_self(&program).unwrap();

        // In batch mode, add and main share a substitution during Pass 2.
        // main's (add 3 4) pins add's type vars to Int before generalization.
        // So add becomes monomorphic Fn([Int, Int], Int), not constrained.
        // This is correct HM behavior for same-program references.
        // Constrained polymorphism applies across module boundaries.
        assert!(
            tc.constrained_fn_names_set().is_empty(),
            "within same program, add should be monomorphic due to shared subst"
        );
        assert!(
            tc.mono_defn_names().is_empty(),
            "no constrained fns means no mono_defns needed"
        );

        // Verify add was correctly inferred as Fn([Int, Int], Int)
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("add") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int))
            );
        } else {
            panic!("add not found");
        }

        // The + call site within add didn't get resolved during Pass 2
        // because x/y were still Vars during add's body check.
        // In the same-program case, add is used monomorphically and
        // doesn't need separate mono_defn generation.
    }

    // spec: 03-types §3.6 — constrained fn without callers detected and registered
    #[test]
    fn test_batch_constrained_fn_alone_detected() {
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);
        // (defn add [x y] (+ x y))  -- alone, no callers; should be constrained
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("add"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("+"), span(18, 19))),
                    args: vec![
                        Expr::var(Symbol::from("x"), span(20, 21)),
                        Expr::var(Symbol::from("y"), span(22, 23)),
                    ],
                    span: span(17, 24),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(0, 25),
            }],
            visibility: Visibility::Public,
            span: span(0, 25),
        })];

        let _result = tc.check_program_self(&program).unwrap();

        assert!(
            tc.constrained_fn_names_set().contains(&Symbol::from("add")),
            "add should be in constrained_fn_names"
        );

        // No callers, so no mono_defns
        let mono_names = tc.mono_defn_names();
        assert!(
            mono_names.is_empty(),
            "no call sites means no mono_defns, got: {mono_names:?}"
        );

        // Check the scheme has Num constraint
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("add") {
            assert!(
                !scheme.constraints.is_empty(),
                "add should have Num constraint"
            );
        } else {
            panic!("add not found in symbol table");
        }
    }

    // spec: 03-types §3.3 [S109] / §3.9.2 (u5) — a KNOWN trait-name annotation
    // still takes the constraint path, unaffected by the written-free-var minting
    // rule. `(defn show2 [:Num x] x)` yields a CONSTRAINED polymorphic scheme
    // (Num constraint on the param var), NOT a plain minted free var and NOT an
    // `unknown type Num` error. Pins that the §3.3 free-var fix keys on
    // `TypeExpr::TypeVar` (lowercase) and does not intercept the uppercase
    // `Named` → try-type-then-trait path (FV-14's seam).
    #[test]
    fn u5_trait_constraint_annotation_unaffected_by_free_var_rule() {
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);
        // (defn show2 [:Num x] x)
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("show2"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(
                    Symbol::from("x"),
                    Some(cranelisp_types::TypeExpr::Named(cranelisp_types::TypeRef::new(
                        None,
                        TypeName::from("Num"),
                    ))),
                )],
                body: Expr::var(Symbol::from("x"), span(18, 19)),
                span: span(0, 20),
            }],
            visibility: Visibility::Public,
            span: span(0, 20),
        })];

        // Must type-check (no `unknown type Num` error).
        tc.check_program_self(&program).unwrap();

        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("show2") {
            assert!(
                !scheme.constraints.is_empty(),
                "show2's `:Num` annotation must produce a constrained scheme, not a plain free var"
            );
            assert!(
                !scheme.type_vars.is_empty(),
                "show2 stays polymorphic (constrained), not concrete"
            );
        } else {
            panic!("show2 not found in symbol table");
        }
    }

    // spec: 03-types §3.3.1 [S109 W6.3] (U1) — a BARE written parameter type var
    // is an ORDINARY FLEXIBLE inference variable carrying a display name, NOT a
    // rigid skolem (W6.3 backs out the W6.2 rigid-bare model). Two facets at the
    // program seam: (a) unconstrained → stays polymorphic (`(defn id [:a x] x)` →
    // `∀a. a→a`); (b) a body USE that pins it is ACCEPTED and the scheme reflects
    // the concrete type (`(defn f [:a x] (add-i64 1 x))` → `(Fn [Int] Int)`, row
    // 2) — the defining contrast with the superseded rigid model (which rejected
    // (b) as a skolem escape). Fails on a revert to rigid-bare.
    #[test]
    fn u1_bare_written_param_var_is_flexible_body_may_pin() {
        // (a) a written var the body does not constrain stays polymorphic.
        let mut tc = tc_with_prims();
        let sexps = cranelisp_frontend::parse("(defn id [:a x] x)").expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
        tc.check_program_self(&program).unwrap();
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("id") {
            assert!(!scheme.ty.is_concrete(), "id must stay polymorphic (∀a. a→a)");
            assert!(!scheme.type_vars.is_empty(), "id's `a` must be quantified");
        } else {
            panic!("id not found");
        }

        // (b) a body USE that pins the bare var to a concrete type is ACCEPTED,
        //     and the inferred scheme reflects the pin `(Fn [Int] Int)` (row 2).
        let mut tc2 = tc_with_prims();
        let sexps2 =
            cranelisp_frontend::parse("(defn f [:a x] (add-i64 1 x))").expect("parse");
        let program2 = cranelisp_frontend::build_forms(&sexps2).expect("build_forms");
        tc2.check_program_self(&program2)
            .expect("a bare `:a` pinned by the body MUST be accepted (§3.3.1 MUST (a))");
        let table = tc2.symbol_table();
        let Some(ModuleEntry::Def { scheme, .. }) = table.get("f") else {
            panic!("f not found");
        };
        assert!(
            scheme.ty.is_concrete() && scheme.type_vars.is_empty(),
            "the body pin MUST narrow `a := Int` → concrete `(Fn [Int] Int)`; got {:?}",
            scheme.ty
        );
    }

    // spec: 03-types §3.3.1 / §3.3.5 row 4 [S109 W6.3] (0588) — a bare written
    // param var `:a` and a body VALUE-POSITION annotation `:a "hello"` carrying
    // the SAME name CO-REFER within one definition boundary, via the
    // `written_var_scope` threaded from `register_defn_signature` into
    // `infer_annotate`. The body annotation therefore pins the PARAM to
    // `String`: `(defn f [:a x] :a "hello")` → concrete `(Fn [String] String)`,
    // and `(f 3)` is a unification error. This is the distinguishing cell of
    // 0588 — co-reference held only "when unification incidentally connects
    // them" would leave the param as a free `a` here (`(Fn [a] String)`); the
    // shared scope makes it `String`. Fails on a revert to per-Annotate fresh
    // var maps.
    #[test]
    fn u1b_bare_param_corefers_body_annotation_pins_param_row4() {
        let mut tc = tc_with_prims();
        let sexps =
            cranelisp_frontend::parse("(defn f [:a x] :a \"hello\")").expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
        tc.check_program_self(&program)
            .expect("a body `:a` annotation co-referring the param `:a` MUST be accepted (row 4)");
        let table = tc.symbol_table();
        let Some(ModuleEntry::Def { scheme, .. }) = table.get("f") else {
            panic!("f not found");
        };
        assert!(scheme.type_vars.is_empty(), "the param `a` MUST be pinned, not quantified");
        assert_eq!(
            scheme.ty,
            Type::Fn(vec![Type::String], Box::new(Type::String)),
            "param↔body co-reference MUST pin the param to String → `(Fn [String] String)`; got {:?}",
            scheme.ty
        );
    }

    // spec: 03-types §3.3.2 [S109 W6.3] (U3) — a CONSTRAINT at a parameter
    // position (`:C x`) is held ABSTRACT over `C` for the body-check, at the
    // program seam. R5 (accepted): `(defn f5 [:Num2 x] (nadd x x))` uses only the
    // trait interface → stays constrained-polymorphic. R6 (rejected): `(defn f6
    // [:Num2 x] (add-i64 1 x))` narrows the held-abstract var to Int → a skolem
    // escape type error (never `unknown type`). This is the 0590-convergence
    // guard: the constraint path is the rigid-aware one. Fails on a revert that
    // stops seeding `rigid_vars` from asserted-constraint param vars.
    #[test]
    fn u3_constraint_param_held_abstract_body_narrow_is_skolem_escape() {
        const NUM2: &str = "(deftrait Num2 (nadd [a b] self))\n\
             (impl Num2 Int (defn nadd [a b] (add-i64 a b)))\n";
        // R5 accepted — interface-only use keeps a constrained polymorphic scheme.
        let mut tc = tc_with_prims();
        let sexps = cranelisp_frontend::parse(&format!("{NUM2}(defn f5 [:Num2 x] (nadd x x))"))
            .expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
        tc.check_program_self(&program)
            .expect("interface-only use of a `:Num2` param MUST be accepted (row 5)");
        let table = tc.symbol_table();
        let Some(ModuleEntry::Def { scheme, .. }) = table.get("f5") else {
            panic!("f5 not found");
        };
        assert!(
            !scheme.constraints.is_empty() && !scheme.type_vars.is_empty(),
            "f5 MUST stay constrained-polymorphic `∀a. Num2 a => (Fn [a] a)`; got {:?} / {:?}",
            scheme.ty, scheme.constraints
        );

        // R6 rejected — the body narrows the held-abstract `:Num2` var to Int.
        let mut tc2 = tc_with_prims();
        let sexps2 =
            cranelisp_frontend::parse(&format!("{NUM2}(defn f6 [:Num2 x] (add-i64 1 x))"))
                .expect("parse");
        let program2 = cranelisp_frontend::build_forms(&sexps2).expect("build_forms");
        let err = tc2
            .check_program_self(&program2)
            .expect_err("a `:Num2` param narrowed to Int by its body MUST be rejected (row 6)");
        let msg = format!("{err:?}");
        assert!(
            !msg.contains("unknown type"),
            "the skolem-escape rejection MUST be a type error, never `unknown type` \
             (§3.3.2 MUST (b)); got: {msg}"
        );
    }

    // spec: 03-types §3.3.4 / §3.10 [S109 W6.3 — user ruling] (U7) — a `defn`
    // body that DEFINES a rank-1 polymorphic function value is a legitimate
    // syntactic value; the written `:b` is IRRELEVANT. `(defn mk [] (fn [:b y]
    // y))` and its unwritten twin `(defn mkid [] (fn [y] y))` are the SAME thing
    // — BOTH accepted with the SAME scheme (`∀a. (Fn [] (Fn [a] a))`). Likewise
    // `(defn weird [x] (fn [:b y] x))` == `(defn constf [x] (fn [y] x))`
    // (`∀a b. (Fn [a] (Fn [b] a))`). The former eager escape check
    // ("a polymorphic function cannot be returned or stored as a value: rank-2")
    // OVER-REJECTED the written forms while their unwritten twins compiled; it
    // was removed. This test pins the written≡unwritten PARITY — it fails if the
    // eager check is re-introduced (the written forms would reject again).
    #[test]
    fn u7_rank1_poly_fn_return_written_and_unwritten_parity_accepted() {
        // Accept `src`, return the named entry's generalized scheme (clone).
        fn scheme_of(src: &str, name: &str) -> cranelisp_types::Scheme {
            let mut tc = tc_with_prims();
            let sexps = cranelisp_frontend::parse(src).expect("parse");
            let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
            tc.check_program_self(&program).unwrap_or_else(|e| {
                panic!("`{src}` MUST be accepted (rank-1 poly-return, W6.3 ruling); got {e:?}")
            });
            let table = tc.symbol_table();
            let Some(ModuleEntry::Def { scheme, .. }) = table.get(name) else {
                panic!("{name} not found after checking `{src}`");
            };
            scheme.clone()
        }

        // Shape assertion: `∀a. (Fn [] (Fn [a] a))` — ONE quantified var, a
        // nullary outer fn whose result is the identity fn (inner param ≡ ret).
        fn assert_mk_shape(scheme: &cranelisp_types::Scheme, label: &str) {
            assert_eq!(
                scheme.type_vars.len(),
                1,
                "{label} MUST generalize to ONE quantified var; got {scheme:?}"
            );
            match &scheme.ty {
                Type::Fn(outer_params, outer_ret) => {
                    assert!(outer_params.is_empty(), "{label} outer fn is nullary; got {scheme:?}");
                    match &**outer_ret {
                        Type::Fn(inner_params, inner_ret) => {
                            assert_eq!(inner_params.len(), 1, "{label}: {scheme:?}");
                            assert_eq!(
                                inner_params[0], **inner_ret,
                                "{label} inner fn MUST be the identity (param ≡ ret); got {scheme:?}"
                            );
                        }
                        other => panic!("{label} result MUST be a Fn; got {other:?}"),
                    }
                }
                other => panic!("{label} MUST be a Fn; got {other:?}"),
            }
        }

        // mk (written `:b`) ≡ mkid (unwritten) — same scheme, both accepted.
        assert_mk_shape(&scheme_of("(defn mk [] (fn [:b y] y))", "mk"), "mk (written)");
        assert_mk_shape(&scheme_of("(defn mkid [] (fn [y] y))", "mkid"), "mkid (unwritten)");

        // weird (written `:b`) ≡ constf (unwritten) — `∀a b. (Fn [a] (Fn [b] a))`.
        for (src, name, label) in [
            ("(defn weird [x] (fn [:b y] x))", "weird", "weird (written)"),
            ("(defn constf [x] (fn [y] x))", "constf", "constf (unwritten)"),
        ] {
            let scheme = scheme_of(src, name);
            assert_eq!(
                scheme.type_vars.len(),
                2,
                "{label} MUST generalize to TWO quantified vars; got {scheme:?}"
            );
        }
    }

    // spec: 03-types §3.3.4 / §3.10 / §3.11 [S109 W6.3 — user ruling] (U7) — with
    // the eager poly-as-value escape check REMOVED, defining a rank-1 poly value
    // (applied in place, OR let-stored-and-returned) is accepted; the GENUINE
    // restrictions are enforced by their real mechanisms, NOT an eager check:
    //   - B-1 `(defn f1 [x] ((fn [:b y] y) x))` — applied in place → `∀a. (Fn
    //     [a] a)`, accepted (unchanged);
    //   - mk3 `(defn mk3 [] (let [g (fn [:b y] y)] g))` — the FORMER fence,
    //     now ACCEPTED (it defines a rank-1 poly value; the written `:b` is
    //     irrelevant, cf. its unwritten twin which always compiled);
    //   - MULTI-TYPE use of one instance → the value restriction / unification
    //     (a type conflict), STILL rejected;
    //   - RANK-2 (poly value used at two types inside a callee) → unification,
    //     STILL rejected;
    //   - a RESULT-ONLY var held unresolved → the §3.11 ambiguity gate, STILL
    //     rejected. These three confirm the removed check was purely over-firing.
    #[test]
    fn u7_rank1_poly_value_accepted_genuine_restrictions_enforced_elsewhere() {
        // B-1 accept — `∀a. (Fn [a] a)`, ONE quantified var, inner identity.
        let mut tc = tc_with_prims();
        let sexps =
            cranelisp_frontend::parse("(defn f1 [x] ((fn [:b y] y) x))").expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
        tc.check_program_self(&program).expect(
            "a lambda APPLIED IN PLACE at a generic arg is instantiation-at-use \
             (§3.10) — MUST be accepted (B-1)",
        );
        let table = tc.symbol_table();
        let Some(ModuleEntry::Def { scheme, .. }) = table.get("f1") else {
            panic!("f1 not found");
        };
        assert_eq!(
            scheme.type_vars.len(),
            1,
            "f1 MUST generalize to ONE quantified var (∀a. (Fn [a] a)); got {scheme:?}"
        );
        match &scheme.ty {
            Type::Fn(params, ret) => {
                assert_eq!(params.len(), 1);
                assert_eq!(
                    params[0], **ret,
                    "f1 param and return MUST be the SAME var (identity); got {:?}",
                    scheme.ty
                );
            }
            _ => panic!("f1 MUST be a Fn type; got {:?}", scheme.ty),
        }

        // mk3 accept (FLIPPED from the former reject) — a let-stored-and-returned
        // rank-1 poly value is legitimate; `∀a. (Fn [] (Fn [a] a))`.
        let mut tc2 = tc_with_prims();
        let sexps2 = cranelisp_frontend::parse("(defn mk3 [] (let [g (fn [:b y] y)] g))")
            .expect("parse");
        let program2 = cranelisp_frontend::build_forms(&sexps2).expect("build_forms");
        tc2.check_program_self(&program2).expect(
            "a let-stored-and-returned rank-1 poly `fn` MUST be accepted (W6.3 ruling — \
             the written `:b` is irrelevant, cf. its always-compiling unwritten twin)",
        );

        // MULTI-TYPE use of ONE instance is STILL rejected — by unification, not
        // an eager check: `mkid` yields a fresh `(Fn [a] a)`; using it at String
        // then Int inside a body is a type conflict.
        let mut tc3 = tc_with_prims();
        let sexps3 = cranelisp_frontend::parse(
            "(defn mkid [] (fn [y] y))\n\
             (defn mtu [] (let [f (mkid)] (let [a (f \"x\")] (f 5))))",
        )
        .expect("parse");
        let program3 = cranelisp_frontend::build_forms(&sexps3).expect("build_forms");
        let err3 = tc3.check_program_self(&program3).expect_err(
            "multi-type USE of one poly instance MUST be rejected by unification (value \
             restriction), independent of the removed eager check",
        );
        let msg3 = format!("{err3}").to_lowercase();
        assert!(
            msg3.contains("mismatch") || msg3.contains("expected"),
            "multi-type-use rejection is a unification type conflict; got: {msg3}"
        );

        // RANK-2 (a poly value used at two types inside a callee) is STILL
        // rejected — by unification.
        let mut tc4 = tc_with_prims();
        let sexps4 =
            cranelisp_frontend::parse("(defn apply2 [f] (let [a (f \"x\")] (f 5)))")
                .expect("parse");
        let program4 = cranelisp_frontend::build_forms(&sexps4).expect("build_forms");
        let err4 = tc4.check_program_self(&program4).expect_err(
            "rank-2 (poly arg used at two types) MUST be rejected by unification",
        );
        let msg4 = format!("{err4}").to_lowercase();
        assert!(
            msg4.contains("mismatch") || msg4.contains("expected"),
            "rank-2 rejection is a unification type conflict; got: {msg4}"
        );

        // RESULT-ONLY var held unresolved is STILL rejected — by the §3.11
        // ambiguity gate (pin-the-type), NOT the removed eager check.
        let mut tc5 = tc_with_prims();
        let sexps5 = cranelisp_frontend::parse(
            "(defn constf [x] (fn [y] x))\n(defn g [] (constf 5))",
        )
        .expect("parse");
        let program5 = cranelisp_frontend::build_forms(&sexps5).expect("build_forms");
        let err5 = tc5.check_program_self(&program5).expect_err(
            "a result-only unresolved var at a codegen position MUST be rejected by the \
             §3.11 ambiguity gate",
        );
        let msg5 = format!("{err5}").to_lowercase();
        assert!(
            msg5.contains("ambiguous"),
            "the result-var rejection is the §3.11 ambiguity gate; got: {msg5}"
        );
    }

    // spec: 03-types §3.3.3 [S109 W6.3] (U4 / R12 neg, FIXME 0597) — the
    // value-position satisfaction check MUST reject a CONCRETE but NON-NOMINAL
    // expr type. `concrete_type_name` returns `None` for a `Fn` type; treating
    // `None` as "skip the check" silently ACCEPTED `(defn g1 [] :NumT (fn [:Int
    // y] y))` — a function type implements NO trait (impls are keyed by type
    // name), so MUST (c)'s "iff" requires rejection. The `Type::Var` skip
    // (row 17) is correct; the concrete-non-nominal skip was the false accept.
    #[test]
    fn u4_value_position_constraint_rejects_non_nominal_fn_type() {
        const NUMT: &str = "(deftrait NumT (nadd [a b] self))\n\
             (impl NumT Int (defn nadd [a b] (add-i64 a b)))\n";
        let mut tc = tc_with_prims();
        let sexps = cranelisp_frontend::parse(&format!("{NUMT}(defn g1 [] :NumT (fn [:Int y] y))"))
            .expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
        let err = tc.check_program_self(&program).expect_err(
            "a value-position `:NumT` on a `(Fn [Int] Int)` MUST be rejected — a \
             function type implements no trait (§3.3.3 MUST (c), FIXME 0597)",
        );
        let msg = format!("{err:?}");
        assert!(
            !msg.contains("unknown type"),
            "the failed satisfaction check MUST name the trait, never `unknown type`; got: {msg}"
        );
    }

    // spec: 03-types §3.3.3 [S109 W6.3] (U4) — a value-position CONSTRAINT is a
    // pure SATISFACTION CHECK (`infer_annotate` trait arm): accepted iff the
    // expr's concrete type implements the trait, and it changes NOTHING. R12 pos:
    // `(defn f12 [] :Num2 5)` → `(Fn [] Int)` (Int satisfies Num2; the type of `5`
    // is unchanged). R12 neg: `(defn f12b [] :Num2 "s")` → rejected (String has no
    // Num2 impl), and NEVER `unknown type` (the trait is recognised as a
    // constraint, not resolved as a missing type).
    #[test]
    fn u4_value_position_constraint_is_a_satisfaction_check() {
        const NUM2: &str = "(deftrait Num2 (nadd [a b] self))\n\
             (impl Num2 Int (defn nadd [a b] (add-i64 a b)))\n";
        // R12 pos — Int satisfies Num2; the type of `5` is unchanged.
        let mut tc = tc_with_prims();
        let sexps = cranelisp_frontend::parse(&format!("{NUM2}(defn f12 [] :Num2 5)"))
            .expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
        tc.check_program_self(&program)
            .expect("a value-position `:Num2 5` MUST be an accepted satisfaction check (row 12)");
        let table = tc.symbol_table();
        let Some(ModuleEntry::Def { scheme, .. }) = table.get("f12") else {
            panic!("f12 not found");
        };
        assert_eq!(
            scheme.ty,
            Type::Fn(vec![], Box::new(Type::Int)),
            "`:Num2 5` MUST NOT change the type of `5` — f12 is `(Fn [] Int)`; got {:?}",
            scheme.ty
        );

        // R12 neg — String has no Num2 impl; the satisfaction check rejects it,
        // never `unknown type`.
        let mut tc2 = tc_with_prims();
        let sexps2 = cranelisp_frontend::parse(&format!("{NUM2}(defn f12b [] :Num2 \"s\")"))
            .expect("parse");
        let program2 = cranelisp_frontend::build_forms(&sexps2).expect("build_forms");
        let err = tc2
            .check_program_self(&program2)
            .expect_err("`:Num2 \"s\"` (no String impl) MUST fail the satisfaction check (row 12)");
        let msg = format!("{err:?}");
        assert!(
            !msg.contains("unknown type"),
            "the failed satisfaction check MUST name the trait, never `unknown type`; got: {msg}"
        );
    }

    // spec: 07-traits §7.11.2 edge (c) (F-D2-10, FIXME 0672) — a NULLARY
    // return-type-dispatched method (`(zed)`, `Self` in return) pinned by an
    // annotation to a type with NO impl MUST reject at typecheck with the located
    // "no impl of trait X for type Y" error naming the owning trait — uniform with
    // the unary sibling (F-D2-7), NEVER a codegen `undefined function` leak. The
    // chokepoint is `resolve_deferred_trait_calls`: the nullary dispatch defers at
    // `infer_apply` (return type still a Var), settles under the `:Widget`
    // annotation, and the settlement re-attempt now PROPAGATES the located no-impl
    // error `try_resolve_trait_method` raises (pre-S114 it swallowed it via
    // `if let Ok(Some(..))`). This unit-pins the producer chokepoint the e2e
    // F-D2-10 cells flip against; it FAILS on revert of the Err-propagation.
    #[test]
    fn nullary_return_dispatch_no_impl_rejects_at_typecheck_naming_trait() {
        const SRC: &str = "(deftrait Zeroable (zed [] self))\n\
             (impl Zeroable Int (defn zed [] 0))\n\
             (deftype Widget (MkW [:Int n]))\n\
             (defn getw [] (let [x :Widget (zed)] x))\n";
        let mut tc = tc_with_prims();
        let sexps = cranelisp_frontend::parse(SRC).expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
        let err = tc.check_program_self(&program).expect_err(
            "a nullary return-dispatch `:Widget (zed)` to a type with NO Zeroable \
             impl MUST reject at typecheck (F-D2-10, §7.11.2(c)), never leak to codegen",
        );
        let msg = format!("{err:?}");
        assert!(
            msg.contains("no impl") && msg.contains("Zeroable"),
            "the no-impl reject MUST name the owning trait `Zeroable` \
             (§7.11.2(c)); got: {msg}"
        );
    }

    // spec: 07-traits §7.11.2 edge (c) (F-D2-10 precision twin) — the fix must not
    // over-reject: a nullary return-dispatch pinned to a type that DOES have an
    // impl (`:Int (zed)`) type-checks cleanly. Guards against the Err-propagation
    // rejecting a valid dispatch.
    #[test]
    fn nullary_return_dispatch_with_impl_type_checks_clean() {
        const SRC: &str = "(deftrait Zeroable (zed [] self))\n\
             (impl Zeroable Int (defn zed [] 0))\n\
             (defn getz [] (let [x :Int (zed)] x))\n";
        let mut tc = tc_with_prims();
        let sexps = cranelisp_frontend::parse(SRC).expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
        tc.check_program_self(&program).expect(
            "a nullary return-dispatch `:Int (zed)` to a type WITH a Zeroable impl \
             MUST type-check cleanly (F-D2-10 must not over-reject)",
        );
    }

    // spec: 03-types §3.3.1 × 05-definitions §5.1.2 [S109 W6.3] (U9) — sibling
    // multi-arity clauses are DISJOINT lexical scopes: each clause's bare `:a` is
    // pinned INDEPENDENTLY by its OWN body (co-reference merges NESTED scopes
    // only, never sibling clauses). `(defn h ([:a x] (add-i64 x 1)) ([:a x :Int n]
    // (str-concat x x)))` — clause 1 pins `a := Int` → `(Fn [Int] Int)`, clause 2
    // pins `a := String` → `(Fn [String Int] String)`; the DIFFERENT pins are the
    // clause-independence guard (C-4). The whole defn type-checks (no cross-clause
    // skolem-escape from the two different pins).
    #[test]
    fn u9_multi_arity_clauses_pin_written_var_independently() {
        let mut tc = tc_with_prims();
        let src = "(defn h ([:a x] (add-i64 x 1)) ([:a x :Int n] (str-concat x x)))";
        let sexps = cranelisp_frontend::parse(src).expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
        tc.check_program_self(&program).expect(
            "each clause's bare `:a` pinned by its OWN body MUST be accepted \
             (§3.3.1 MUST (a), §5.1.2 clause independence)",
        );
    }

    // spec: 03-types §3.3.1 [S109 W6.3] (U2) — nested-`fn` lexical CO-REFERENCE
    // SURVIVES the W6.3 backout: the enclosing definition's written-var scope
    // THREADS into the nested `fn` (`infer_lambda` shares `written_var_scope`), so
    // an inner `:a` resolves to the SAME `TypeId` as the enclosing `defn`'s `:a`.
    // `(defn g [:a x] (fn [:a y] y))` MUST have scheme `∀a. (Fn [a] (Fn [a] a))` —
    // ONE quantified var in all three positions (row 8). Under a SHADOW reading
    // the inner `:a` would mint a SECOND var, which this cell rejects (0588).
    #[test]
    fn u2_nested_fn_written_var_corefers_enclosing_same_typeid() {
        let mut tc = tc_with_prims();
        let sexps =
            cranelisp_frontend::parse("(defn g [:a x] (fn [:a y] y))").expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
        tc.check_program_self(&program).unwrap();

        let table = tc.symbol_table();
        let Some(ModuleEntry::Def { scheme, .. }) = table.get("g") else {
            panic!("g not found");
        };
        // Exactly ONE quantified var — co-reference, not a fresh nested shadow.
        assert_eq!(
            scheme.type_vars.len(),
            1,
            "nested `:a` must CO-REFER (one quantified var), not shadow; got scheme {:?}",
            scheme.ty
        );
        // Structural: (Fn [Var(a)] (Fn [Var(a)] Var(a))) — the SAME TypeId in all
        // three positions.
        let Type::Fn(outer_params, outer_ret) = &scheme.ty else {
            panic!("g scheme is not a Fn: {:?}", scheme.ty);
        };
        let Type::Var(a_outer) = outer_params[0] else {
            panic!("outer param not a Var: {:?}", outer_params[0]);
        };
        let Type::Fn(inner_params, inner_ret) = outer_ret.as_ref() else {
            panic!("g result is not a Fn: {:?}", outer_ret);
        };
        assert_eq!(inner_params[0], Type::Var(a_outer), "inner param must be the outer rigid `a`");
        assert_eq!(**inner_ret, Type::Var(a_outer), "inner result must be the outer rigid `a`");
        assert_eq!(scheme.type_vars[0], a_outer, "the one quantified var IS `a`");
    }

    // spec: 03-types §3.6 — REPL expression monomorphises constrained fn on demand
    #[test]
    fn test_repl_expr_monomorphise() {
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);

        // First, define a constrained fn: (defn add [x y] (+ x y))
        let defn_input = TopLevel::Defn(Defn {
            name: Symbol::from("add"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("+"), span(18, 19))),
                    args: vec![
                        Expr::var(Symbol::from("x"), span(20, 21)),
                        Expr::var(Symbol::from("y"), span(22, 23)),
                    ],
                    span: span(17, 24),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(0, 25),
            }],
            visibility: Visibility::Public,
            span: span(0, 25),
        });
        let _ = tc.check_repl_input_self(&defn_input).unwrap();

        // Now evaluate an expression that calls the constrained fn: (add 3 4)
        let expr_input = TopLevel::Expr(Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("add"), span(100, 103))),
            args: vec![
                Expr::IntLit { value: 3, span: span(104, 105), inferred_type: None, },
                Expr::IntLit { value: 4, span: span(106, 107), inferred_type: None, },
            ],
            span: span(99, 108),
            resolved_call: None,
            inferred_type: None,
        });
        let _result = tc.check_repl_input_self(&expr_input).unwrap();

        // Should have mono_defns populated (entry on SymbolTable post-slim)
        let mono_names = tc.mono_defn_names();
        assert!(
            !mono_names.is_empty(),
            "REPL expr should generate mono_defns for constrained fn calls"
        );
        assert!(
            // FIXME 0519: mono names are home-qualified `{home}/{bare}$sig`.
            mono_names.iter().any(|n| n.as_ref() == "test/add$Int+Int"),
            "expected test/add$Int+Int in mono entries, got {mono_names:?}"
        );
    }

    // spec: design/arch/concrete-boundary-type.md §2.4 — Phase 2b mono-population
    // seam. A monomorphised instance (`add$Int+Int` from a generic `add`) now
    // carries a concrete-boundary `MonoDefnVariant` whose `MonoExpr` body is
    // fully `ConcreteType`-annotated. `MonoExpr::from_expr` runs at the seam for
    // every instance (the validation payoff) and the produced variant is retained
    // on `CheckState.mono_variants` (produces-but-unused for codegen in Phase 2).
    #[test]
    fn mono_instance_carries_concrete_boundary_monoexpr_body() {
        use cranelisp_types::ConcreteType;

        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);

        // (defn add [x y] (+ x y)) — a generic, trait-constrained fn.
        let defn_input = TopLevel::Defn(Defn {
            name: Symbol::from("add"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("+"), span(18, 19))),
                    args: vec![
                        Expr::var(Symbol::from("x"), span(20, 21)),
                        Expr::var(Symbol::from("y"), span(22, 23)),
                    ],
                    span: span(17, 24),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(0, 25),
            }],
            visibility: Visibility::Public,
            span: span(0, 25),
        });
        let _ = tc.check_repl_input_self(&defn_input).unwrap();

        // (add 3 4) — pins `add` to `Int`, minting `add$Int+Int`.
        let expr_input = TopLevel::Expr(Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("add"), span(100, 103))),
            args: vec![
                Expr::IntLit { value: 3, span: span(104, 105), inferred_type: None },
                Expr::IntLit { value: 4, span: span(106, 107), inferred_type: None },
            ],
            span: span(99, 108),
            resolved_call: None,
            inferred_type: None,
        });
        let _ = tc.check_repl_input_self(&expr_input).unwrap();

        // The seam produced a `MonoDefnVariant` for the instance, with a concrete
        // `MonoExpr` body. `from_expr` succeeded (no error returned above), which
        // is itself the validation payoff; assert the variant is observable and
        // its body's root type is a `ConcreteType`.
        let variants = tc.mono_variants();
        let v = variants
            .iter()
            .find(|v| v.name.as_ref() == "test/add$Int+Int")
            .unwrap_or_else(|| {
                panic!(
                    "expected a MonoDefnVariant for test/add$Int+Int, got {:?}",
                    variants.iter().map(|v| v.name.as_ref()).collect::<Vec<_>>()
                )
            });
        // The body's root concrete type is Int (the `(+ x y)` result at Int).
        assert_eq!(
            v.body.ty(),
            &ConcreteType::Int,
            "mono body root must be a ConcreteType (Int)"
        );
        // Params survive (names only; TypeExprs erased).
        assert_eq!(
            v.params,
            vec![Symbol::from("x"), Symbol::from("y")],
            "mono variant params preserved"
        );
    }

    // spec: design/arch/concrete-boundary-type.md §3.0/§3.1 + FIXME 0394/0395 —
    // the CALLER's `codegen_view` is built POST-mono. A concrete defn `main`
    // calling a generic `id` (`(id 7)`) has its `(id 7)` call rewritten by the
    // mono pass to `SigDispatch{id$Int}`. The fix (Part A) rebuilds `main`'s
    // `codegen_view` from the post-mono-annotated `ast` at the finalize
    // re-annotation seam, so the view's call node carries the correct
    // `SigDispatch` dispatch — NOT the stale pre-mono `resolved_call: None` that
    // would mis-dispatch to the slot-less generic `id` ("undefined function: id").
    // This is the SSOT proof the backend reads `codegen_view` on the live path.
    #[test]
    fn caller_codegen_view_carries_post_mono_sigdispatch() {
        use cranelisp_types::{MonoExpr, ResolvedCall};

        let mut tc = tc_with_prims();

        // (defn id [x] x) — pure-parametric generic.
        let id_defn = TopLevel::Defn(Defn {
            name: Symbol::from("id"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None)],
                body: Expr::var(Symbol::from("x"), span(10, 11)),
                span: span(0, 12),
            }],
            visibility: Visibility::Public,
            span: span(0, 12),
        });

        // (defn main [] (id 7)) — concrete caller; the call pins `id` to Int,
        // minting `id$Int` and rewriting the call to `SigDispatch{id$Int}`.
        let main_defn = TopLevel::Defn(Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("id"), span(40, 42))),
                    args: vec![Expr::IntLit { value: 7, span: span(43, 44), inferred_type: None }],
                    span: span(39, 45),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(26, 46),
            }],
            visibility: Visibility::Public,
            span: span(26, 46),
        });

        tc.check_program_self(&[id_defn, main_defn]).unwrap();

        // The mono instance `id$Int` is minted (home-qualified, FIXME 0519).
        let mono_names = tc.mono_defn_names();
        assert!(
            mono_names.iter().any(|n| n.as_ref() == "test/id$Int"),
            "expected test/id$Int mono instance, got {mono_names:?}"
        );

        // `main` is a Concrete{slot} codegen target carrying a POST-mono
        // `codegen_view`. Walk its MonoExpr body for the `(id 7)` Apply's
        // resolved_call — it MUST be SigDispatch{id$Int}, proving the view was
        // rebuilt AFTER the mono pass rewrote the dispatch.
        let st = tc.symbol_table();
        let main_view = match st.get("main") {
            Some(ModuleEntry::Def { codegen_view: Some(v), .. }) => v.clone(),
            other => panic!("main has no codegen_view: {other:?}"),
        };

        fn collect_sig_dispatch(e: &MonoExpr, out: &mut Vec<String>) {
            let rc = match e {
                MonoExpr::Apply { callee, args, resolved_call, .. } => {
                    collect_sig_dispatch(callee, out);
                    for a in args {
                        collect_sig_dispatch(a, out);
                    }
                    resolved_call.as_deref()
                }
                MonoExpr::Var { resolved_call, .. } => resolved_call.as_deref(),
                MonoExpr::Let { bindings, body, .. } => {
                    for (_, b) in bindings {
                        collect_sig_dispatch(b, out);
                    }
                    collect_sig_dispatch(body, out);
                    None
                }
                MonoExpr::If { cond, then_branch, else_branch, .. } => {
                    collect_sig_dispatch(cond, out);
                    collect_sig_dispatch(then_branch, out);
                    collect_sig_dispatch(else_branch, out);
                    None
                }
                _ => None,
            };
            if let Some(ResolvedCall::SigDispatch { mangled_name }) = rc {
                out.push(mangled_name.as_ref().to_string());
            }
        }

        let mut dispatches = Vec::new();
        collect_sig_dispatch(&main_view.body, &mut dispatches);
        assert!(
            // FIXME 0519: SigDispatch names the home-qualified mono `test/id$Int`.
            dispatches.iter().any(|d| d == "test/id$Int"),
            "main's codegen_view must carry the post-mono SigDispatch{{test/id$Int}} \
             for the (id 7) call; found dispatches: {dispatches:?}"
        );
    }

    // ---------------------------------------------------------------------
    // S110 0583 producer top-up (FIXME 0616) — the three carrier legs the W0
    // writer missed. Each pins `resolved_target: Some(fq)` at the RIGHT span in
    // the concrete codegen view; the carrier rides UNREAD (W0.1 is
    // behaviour-invariant), so these assert the PRODUCER, not backend consumption.
    // spec: design/arch/backend-keyed-consumer.md §1.1
    // ---------------------------------------------------------------------

    /// Walk a `MonoExpr` collecting `(node_label, resolved_target)` for every
    /// `Var` (labelled by its `name`) and `Apply` (labelled `"@apply"`) node.
    ///
    /// **S114 carrier flip.** The `Option<FQSymbol>` carrier the pre-flip tests
    /// assert against is now the typed `VarRef`/`ApplyRef` sums. This helper
    /// projects the typed verdict back onto the pre-flip `Option<FQSymbol>` shape
    /// so every downstream assertion (a table reference carries `Some(fq)`, a
    /// local / ViaCallee carries `None`) reads unchanged: `VarRef::Global(fq)` /
    /// `ApplyRef::Dispatch(fq)` → `Some(fq)`; `VarRef::Local` / `ApplyRef::ViaCallee`
    /// → `None`.
    fn collect_resolved_targets(
        e: &MonoExpr,
        out: &mut Vec<(String, Option<FQSymbol>)>,
    ) {
        match e {
            MonoExpr::Var { name, resolution, .. } => {
                let rt = match resolution {
                    cranelisp_types::VarRef::Global(fq) => Some(fq.clone()),
                    cranelisp_types::VarRef::Local { .. } => None,
                };
                out.push((name.as_ref().to_string(), rt));
            }
            MonoExpr::Apply { callee, args, dispatch, .. } => {
                let rt = match dispatch {
                    cranelisp_types::ApplyRef::Dispatch(fq) => Some(fq.clone()),
                    cranelisp_types::ApplyRef::ViaCallee => None,
                };
                out.push(("@apply".to_string(), rt));
                collect_resolved_targets(callee, out);
                for a in args {
                    collect_resolved_targets(a, out);
                }
            }
            MonoExpr::If { cond, then_branch, else_branch, .. } => {
                collect_resolved_targets(cond, out);
                collect_resolved_targets(then_branch, out);
                collect_resolved_targets(else_branch, out);
            }
            MonoExpr::Let { bindings, body, .. } => {
                for (_, b) in bindings {
                    collect_resolved_targets(b, out);
                }
                collect_resolved_targets(body, out);
            }
            MonoExpr::Lambda { body, .. } => collect_resolved_targets(body, out),
            MonoExpr::Match { scrutinee, arms, .. } => {
                collect_resolved_targets(scrutinee, out);
                for arm in arms {
                    collect_resolved_targets(&arm.body, out);
                }
            }
            _ => {}
        }
    }

    fn main_codegen_view_of(tc: &TestFixture, name: &str) -> MonoDefnVariant {
        match tc.symbol_table().get(name) {
            Some(ModuleEntry::Def { codegen_view: Some(v), .. }) => v.clone(),
            other => panic!("{name} has no codegen_view: {other:?}"),
        }
    }

    /// Every current-module symbol name whose bare key CONTAINS `substr` — used
    /// to locate a minted mono instance (`idpoly$Int`, `ga$Int`, …) without
    /// hard-coding the home-qualified mangle grammar.
    fn symbol_names_containing(tc: &TestFixture, substr: &str) -> Vec<String> {
        tc.symbol_table()
            .all_symbols()
            .map(|(n, _)| n.as_ref().to_string())
            .filter(|n| n.contains(substr))
            .collect()
    }

    /// The `codegen_view` of the first current-module symbol whose key contains
    /// `substr` (the minted mono instance).
    fn mono_instance_view_containing(tc: &TestFixture, substr: &str) -> MonoDefnVariant {
        let key = tc
            .symbol_table()
            .all_symbols()
            .find(|(n, e)| {
                n.as_ref().contains(substr)
                    && matches!(e, ModuleEntry::Def { codegen_view: Some(_), .. })
            })
            .map(|(n, _)| n.as_ref().to_string())
            .unwrap_or_else(|| panic!("no mono instance with codegen_view contains `{substr}`"));
        main_codegen_view_of(tc, &key)
    }

    // §11.8.3 leg D3 — a poly callee (`idpoly`) reached ONLY from a MULTI-SIG
    // clause body MUST have its concrete mono instance minted. Pre-fix the
    // multi-sig defn was filtered out of the mono-collect (`collect_single_sig_defns`
    // drops it; `Defn::body()` panics on it), so `idpoly$Int` was never harvested
    // and the call reached codegen as `undefined function`. The `MultiSig` harvest
    // family scans the clause bodies post-Phase-A.
    #[test]
    fn multi_sig_clause_body_poly_callee_monomorphised_d3() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn idpoly [x] x)\n\
             (defn build ([n] (build n 0)) \
                         ([n acc] (if (eq-i64 n 0) acc \
                             (build (sub-i64 n 1) (add-i64 acc (idpoly n))))))",
        );
        assert!(
            !symbol_names_containing(&tc, "idpoly$").is_empty(),
            "`idpoly`'s Int mono instance MUST be minted from `build`'s multi-sig \
             clause body (leg D3); current-module symbols: {:?}",
            symbol_names_containing(&tc, "idpoly"),
        );
    }

    // §11.8.3 leg R2 — a call to a MULTI-SIG BASE (`h`) inside a monomorphised
    // body (`ga$Int`) MUST get its `resolved_target` carrier. Pre-fix the inner
    // scans handled only constrained self-recursion and pure-parametric hops —
    // never an overloaded-base dispatch — so `(h 1)` reached codegen with no
    // carrier (`class=carrier-loss`). `resolve_inner_multi_sig_dispatch` writes it.
    #[test]
    fn multi_sig_base_dispatch_in_mono_body_carrier_r2() {
        let mut tc = tc_with_prims();
        // `(add-i64 (h 1) 0)` pins `(h 1)`'s node to Int (so a single-cluster
        // batch mono of `ga$Int` settles cleanly), while `(h 1)` is still a
        // multi-sig-BASE dispatch inside the monomorphised body — the exact
        // carrier R2 must write.
        check_src(
            &mut tc,
            "(defn h ([x] (add-i64 x 1)) ([a b] a))\n\
             (defn ga [:a x] (add-i64 (h 1) 0))\n\
             (defn use-ga [] (ga 5))",
        );
        let view = mono_instance_view_containing(&tc, "ga$");
        let mut targets = Vec::new();
        collect_resolved_targets(&view.body, &mut targets);
        // The `(h 1)` dispatch inside `ga$Int` carries its resolved_target at the
        // APPLY span (SigDispatch), naming the concrete clause `h$Int` — not absent
        // (the carrier-loss shape the backend keyed read would hard-fail on).
        let has_h_dispatch = targets.iter().any(|(l, fq)| {
            l == "@apply"
                && matches!(fq, Some(fq) if fq.symbol.as_ref().contains("h$"))
        });
        assert!(
            has_h_dispatch,
            "the multi-sig-base call `(h 1)` inside the monomorphised `ga$Int` body \
             MUST carry a resolved_target to the concrete clause `h$Int` at its \
             Apply span (leg R2); collected: {targets:?}"
        );
    }

    // §11.8.3 leg R2 — W2a /review Important 1a (TEMPLATE-select). A multi-sig
    // dispatch inside a mono body that selects a genuinely-POLY clause (`(h 1 2)`
    // → the `([a b] a)` `$Var+Var` template) MUST monomorphise that clause to a
    // CONCRETE instance and dispatch to it — never write the slot-less `$Var+Var`
    // TEMPLATE mangle into the frozen view (pre-fix `undefined function:
    // h$Var+Var`). The scoped drain gives R2 the full concrete/template
    // bifurcation. `check_src` panics on the residual/undefined path.
    #[test]
    fn multi_sig_dispatch_template_clause_monomorphised_r2a() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn h ([x] (add-i64 x 1)) ([a b] a))\n\
             (defn ga [:a x] (add-i64 (h 1 2) 0))\n\
             (defn use-ga [] (ga 5))",
        );
        // The `([a b] a)` template clause, selected by `(h 1 2)`, was instantiated
        // at Int (a `h$Var+Var$…` concrete mono instance exists) — proving R2 did
        // NOT freeze the slot-less `$Var+Var` template mangle into the view.
        assert!(
            !symbol_names_containing(&tc, "h$Var+Var$").is_empty(),
            "the poly 2-arg clause selected by `(h 1 2)` MUST be monomorphised to a \
             concrete instance (leg R2, Important 1a) — never dispatched to the \
             slot-less `$Var+Var` template; symbols: {:?}",
            symbol_names_containing(&tc, "h$Var+Var"),
        );
    }

    // §11.8.3 leg R2 — W2a /review Important 1b (post-drain drop). A poly fn
    // (`poly2`) reached ONLY from a MULTI-SIG clause body is monomorphised in the
    // D3 harvest, which runs AFTER the single top-level drain. Its inner multi-sig
    // dispatch `(h2 1)` defers a pending that the top-level drain has already
    // taken — pre-fix it was DROPPED, leaving `(h2 1)` a residual unbound var →
    // misleading residual-var wrong-reject. The scoped drain inside
    // `recheck_body_for_mono` resolves it in-place. `check_src` panics on the
    // residual wrong-reject, so a clean return IS the assertion.
    #[test]
    fn multi_sig_dispatch_in_d3_harvested_body_drained_r2b() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn h2 ([x] (add-i64 x 1)) ([a b] a))\n\
             (defn poly2 [p] (let [q (h2 1)] p))\n\
             (defn build3 ([n] (build3 n 0)) ([n acc] (poly2 acc)))\n\
             (defn use-build3 [] (build3 3))",
        );
        // poly2 was monomorphised from build3's clause body AND its inner `(h2 1)`
        // dispatch drained (the instance minted cleanly, no residual var).
        assert!(
            !symbol_names_containing(&tc, "poly2$").is_empty(),
            "poly2 reached from build3's multi-sig clause body MUST monomorphise \
             cleanly with its inner `(h2 1)` dispatch drained in-recheck (leg R2, \
             Important 1b); symbols: {:?}",
            symbol_names_containing(&tc, "poly2"),
        );
    }

    // W2a /review Important 2 (P24 mirror in `verify_constraints`). A constrained
    // fn whose bound trait is imported METHOD-ONLY (not the trait) must
    // monomorphise: `verify_constraints` roots the impl lookup at the trait's HOME
    // (`fq_trait.module`, held on the constraint) via `has_impl_in_home`, NOT a
    // bare re-resolve of the trait NAME in the caller's scope (`has_impl_with_state`)
    // — the caller has no in-scope trait name. Pre-fix: `(wrap 1)` monomorphises
    // wrap$Int → `verify_constraints` → "no impl of trait blib/Bump for type Int".
    // `check_src` panics on that wrong-reject.
    #[test]
    fn method_only_import_constrained_fn_verify_constraints_home_rooted_d2() {
        let mut tc = tc_with_prims();
        // blib: trait Bump (method `bump`) + Int impl.
        let blib = ModuleFullPath::from("blib");
        tc.set_current_module(blib.clone());
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
        register_int_returning_trait(&mut tc, "Bump", "bump");
        // user: import ONLY the method `bump` — NOT the trait `Bump`.
        let user = ModuleFullPath::from("user");
        tc.set_current_module(user.clone());
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
        seed_specific_import(&mut tc, &blib, &["bump"]);
        // Submission 1 — `wrap` is a genuine constrained-poly fn (Bump a). Checked
        // in its OWN cluster so it commits constrained (a same-cluster concrete
        // call would collapse it to Int before pass-4 ever mono'd it — the batch
        // regeneralize). This mirrors the REPL multi-submission the e2e reproduces.
        check_src(&mut tc, "(defn wrap [x] (bump x))");
        // Submission 2 — `(wrap 1)` monomorphises wrap$Int → `verify_constraints`
        // checks the Bump/Int impl. Home-rooted (blib, held on the constraint), so
        // it resolves. Pre-fix: bare re-resolve of "Bump" in user scope →
        // "no impl of trait blib/Bump for type Int". `check_src` panics on it.
        check_src(&mut tc, "(defn use-int [] (wrap 1))");
        assert!(
            !symbol_names_containing(&tc, "wrap$").is_empty(),
            "wrap$Int must be minted (proving verify_constraints ran + passed \
             home-rooted); symbols: {:?}",
            symbol_names_containing(&tc, "wrap"),
        );
    }

    // §11.8.3 leg R1 — a CROSS-ARITY sibling self-call from a genuinely-poly
    // multi-sig clause, monomorphised at a call site, MUST resolve (dispatch to
    // the concrete sibling clause) rather than wrong-reject with an internal-name
    // leak. `(g2 5)` monomorphises the 1-arg poly clause at Int; its body's
    // `(g2 1 2)` targets the concrete 2-arg sibling. `check_src` panics on the
    // wrong-reject, so a clean return IS the assertion.
    #[test]
    fn cross_arity_sibling_self_call_resolves_r1() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn g2 ([:a x] (g2 1 2)) ([:primitives/Int a :primitives/Int b] (add-i64 a b)))\n\
             (defn use-g2 [] (g2 5))",
        );
    }

    // Leg 1 (dispatch/operator): an operator call — a trait method the primitive
    // short-circuit collapses to `add-i64` — carries its dispatch-leg carrier at
    // the APPLY span (`primitives/add-i64`). `(+ 1 2)` is the named W1 failure
    // scenario; the W0 writer produced NO Apply-span carrier at all.
    #[test]
    fn resolved_target_operator_call_carries_primitive_fq_at_apply_span() {
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);
        // (defn main [] (+ 1 2))
        let program = vec![TopLevel::Defn(make_defn(
            "main",
            vec![],
            vec![],
            Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("+"), span(10, 11))),
                args: vec![
                    Expr::IntLit { value: 1, span: span(12, 13), inferred_type: None },
                    Expr::IntLit { value: 2, span: span(14, 15), inferred_type: None },
                ],
                span: span(9, 16),
                resolved_call: None,
                inferred_type: None,
            },
            Visibility::Public,
            span(0, 17),
        ))];
        tc.check_program_self(&program).unwrap();

        let view = main_codegen_view_of(&tc, "main");
        let mut targets = Vec::new();
        collect_resolved_targets(&view.body, &mut targets);
        let apply_fq = targets
            .iter()
            .find(|(label, _)| label == "@apply")
            .and_then(|(_, fq)| fq.clone());
        assert_eq!(
            apply_fq,
            Some(FQSymbol {
                module: ModuleFullPath::from("primitives"),
                symbol: Symbol::from("add-i64"),
            }),
            "operator (+ 1 2) Apply must carry resolved_target primitives/add-i64 \
             (leg 1); collected: {targets:?}"
        );
    }

    // Leg 2 (self-recursion): a concrete recursive fn's self-call resolves the
    // env-shadowed recursion LOCAL, yet the backend keys it through the fn's own
    // storage slot — so the self-reference `Var` carries the enclosing defn's own
    // FQ (`test/fact`). The env-shadow gate skipped it entirely in W0.
    #[test]
    fn resolved_target_self_recursion_carries_own_fq_at_var_span() {
        let mut tc = tc_with_prims();
        // (defn fact [n] (if (eq-i64 n 0) 1 (mul-i64 n (fact (sub-i64 n 1)))))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("fact"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("n"), None)],
                body: Expr::If {
                    cond: Box::new(Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("eq-i64"), span(20, 26))),
                        args: vec![
                            Expr::var(Symbol::from("n"), span(27, 28)),
                            Expr::IntLit { value: 0, span: span(29, 30), inferred_type: None },
                        ],
                        span: span(19, 31),
                        resolved_call: None,
                        inferred_type: None,
                    }),
                    then_branch: Box::new(Expr::IntLit { value: 1, span: span(33, 34), inferred_type: None }),
                    else_branch: Box::new(Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("mul-i64"), span(36, 43))),
                        args: vec![
                            Expr::var(Symbol::from("n"), span(44, 45)),
                            Expr::Apply {
                                callee: Box::new(Expr::var(Symbol::from("fact"), span(47, 51))),
                                args: vec![Expr::Apply {
                                    callee: Box::new(Expr::var(Symbol::from("sub-i64"), span(53, 60))),
                                    args: vec![
                                        Expr::var(Symbol::from("n"), span(61, 62)),
                                        Expr::IntLit { value: 1, span: span(63, 64), inferred_type: None },
                                    ],
                                    span: span(52, 65),
                                    resolved_call: None,
                                    inferred_type: None,
                                }],
                                span: span(46, 66),
                                resolved_call: None,
                                inferred_type: None,
                            },
                        ],
                        span: span(35, 67),
                        resolved_call: None,
                        inferred_type: None,
                    }),
                    span: span(15, 68),
                    inferred_type: None,
                },
                span: span(0, 69),
            }],
            visibility: Visibility::Public,
            span: span(0, 69),
        })];
        tc.check_program_self(&program).unwrap();

        let view = main_codegen_view_of(&tc, "fact");
        let mut targets = Vec::new();
        collect_resolved_targets(&view.body, &mut targets);
        let self_fq = targets
            .iter()
            .find(|(label, _)| label == "fact")
            .and_then(|(_, fq)| fq.clone());
        assert_eq!(
            self_fq,
            Some(FQSymbol {
                module: ModuleFullPath::from("test"),
                symbol: Symbol::from("fact"),
            }),
            "self-call `fact` Var must carry resolved_target test/fact (leg 2); \
             collected: {targets:?}"
        );
    }

    /// Walk a `MonoExpr` collecting `(name, VarRef)` for every `Var` node — the
    /// typed-carrier sibling of `collect_resolved_targets` (S114 binder-provenance
    /// pins).
    fn collect_var_resolutions(e: &MonoExpr, out: &mut Vec<(String, cranelisp_types::VarRef)>) {
        if let MonoExpr::Var { name, resolution, .. } = e {
            out.push((name.as_ref().to_string(), resolution.clone()));
        }
        match e {
            MonoExpr::Apply { callee, args, .. } => {
                collect_var_resolutions(callee, out);
                for a in args {
                    collect_var_resolutions(a, out);
                }
            }
            MonoExpr::If { cond, then_branch, else_branch, .. } => {
                collect_var_resolutions(cond, out);
                collect_var_resolutions(then_branch, out);
                collect_var_resolutions(else_branch, out);
            }
            MonoExpr::Let { bindings, body, .. } => {
                for (_, b) in bindings {
                    collect_var_resolutions(b, out);
                }
                collect_var_resolutions(body, out);
            }
            MonoExpr::Lambda { body, .. } => collect_var_resolutions(body, out),
            MonoExpr::Match { scrutinee, arms, .. } => {
                collect_var_resolutions(scrutinee, out);
                for arm in arms {
                    collect_var_resolutions(&arm.body, out);
                }
            }
            _ => {}
        }
    }

    // spec: design/typecheck/typed-resolution-carrier.md §3 (test plan §3.4 item 3)
    // — binder-identity provenance: a §4.6 LOCAL reference records `VarRef::Local`
    // carrying the binder name + the span of the BINDING FORM that introduced it.
    // A defn-param reference and a `let` reference resolve in DIFFERENT frames, so
    // their `binding_span`s DIFFER (the shadow-frame disambiguation grain) — and
    // neither is `Span::SYNTHETIC` (a real binding form has a real span). This pins
    // the `ScopeStack.frame_spans` provenance plumbing threaded through the six
    // `push_scope` seams; it fails if a seam drops its form span (all-SYNTHETIC) or
    // shares one frame span across forms.
    #[test]
    fn local_var_ref_carries_binding_form_span_per_frame() {
        let mut tc = tc_with_prims();
        // (defn f [x] (let [y x] (add-i64 x y)))
        //  - `x` is a defn PARAM → binding_span = the defn form span
        //  - `y` is a LET name    → binding_span = the let node span
        check_src(&mut tc, "(defn f [x] (let [y x] (add-i64 x y)))");
        let view = main_codegen_view_of(&tc, "f");
        let mut vars = Vec::new();
        collect_var_resolutions(&view.body, &mut vars);

        let x_span = vars.iter().find_map(|(n, r)| match (n.as_str(), r) {
            ("x", cranelisp_types::VarRef::Local { binding_span, .. }) => Some(*binding_span),
            _ => None,
        });
        let y_span = vars.iter().find_map(|(n, r)| match (n.as_str(), r) {
            ("y", cranelisp_types::VarRef::Local { binding_span, .. }) => Some(*binding_span),
            _ => None,
        });
        let x_span = x_span.expect("param `x` reference must record VarRef::Local");
        let y_span = y_span.expect("let name `y` reference must record VarRef::Local");
        assert_ne!(
            x_span, Span::SYNTHETIC,
            "the defn-param binding-form span must be real, not SYNTHETIC"
        );
        assert_ne!(
            y_span, Span::SYNTHETIC,
            "the let binding-form span must be real, not SYNTHETIC"
        );
        assert_ne!(
            x_span, y_span,
            "a param reference and a let reference bind in DIFFERENT forms — their \
             binding_spans MUST differ (the shadow-frame disambiguation grain)"
        );
    }

    // ---------------------------------------------------------------------
    // FIXME 0619 item 2 — the self-recursion carve-out must fire ONLY for a
    // GENUINE self-recursive reference, never for a same-named nested USER
    // binding (a `let`/`fn` rebinding, or a param). Such a reference is a
    // LOCAL — nothing table-resolved HIT (§1.1), so no carrier entry (the
    // backend's local-`variables` check handles it). These pin the producer.
    // spec: design/arch/backend-keyed-consumer.md §1.1 (local row)
    // ---------------------------------------------------------------------

    /// The enclosing fn's own storage FQ, for the "must NOT carry this" asserts.
    fn enclosing_test_fq(name: &str) -> FQSymbol {
        FQSymbol { module: ModuleFullPath::from("test"), symbol: Symbol::from(name) }
    }

    // A nested `let` rebinds `f` to a lambda; the inner `(f 3)` calls the
    // let-LOCAL, resolving in a deeper frame than the recursion binding. The
    // callee `Var` must NOT carry the enclosing fn's storage FQ.
    #[test]
    fn self_recursion_carveout_skips_nested_let_shadow() {
        let mut tc = tc_with_prims();
        check_src(&mut tc, "(defn f [] (let [f (fn [x] x)] (f 3)))");
        let view = main_codegen_view_of(&tc, "f");
        let mut targets = Vec::new();
        collect_resolved_targets(&view.body, &mut targets);
        assert!(
            targets.iter().any(|(l, _)| l == "f"),
            "the inner `(f 3)` callee `Var` must be present in the view; \
             collected: {targets:?}"
        );
        let f_carrier = targets
            .iter()
            .find(|(l, _)| l == "f")
            .and_then(|(_, fq)| fq.clone());
        assert_ne!(
            f_carrier,
            Some(enclosing_test_fq("f")),
            "nested let-local `f` is a LOCAL; its `Var` must NOT carry the \
             enclosing fn's storage FQ (0619 item 2); collected: {targets:?}"
        );
    }

    // A param named identically to the fn (`(defn f [f] …)`) shadows the
    // recursion name: the `f` in `(f 3)` is the PARAM (a backend local), so its
    // callee `Var` must NOT carry the enclosing fn's storage FQ. (The `add-i64`
    // wrapper only forces the return type concrete so the defn carries a
    // `codegen_view` to inspect — the bare `(defn f [f] (f 3))` is rank-1
    // polymorphic and view-less; the shadow scenario is identical.)
    #[test]
    fn self_recursion_carveout_skips_param_shadow() {
        let mut tc = tc_with_prims();
        check_src(&mut tc, "(defn f [f] (add-i64 (f 3) 1))");
        let view = main_codegen_view_of(&tc, "f");
        let mut targets = Vec::new();
        collect_resolved_targets(&view.body, &mut targets);
        assert!(
            targets.iter().any(|(l, _)| l == "f"),
            "the `(f 3)` callee `Var` must be present in the view; \
             collected: {targets:?}"
        );
        let f_carrier = targets
            .iter()
            .find(|(l, _)| l == "f")
            .and_then(|(_, fq)| fq.clone());
        assert_ne!(
            f_carrier,
            Some(enclosing_test_fq("f")),
            "param-shadowed `f` is a LOCAL; its `Var` must NOT carry the \
             enclosing fn's storage FQ (0619 item 2); collected: {targets:?}"
        );
    }

    // Control: a GENUINE self-recursive reference (no shadowing binding) MUST
    // still carry the enclosing fn's storage FQ — the carve-out is tightened,
    // not disabled.
    #[test]
    fn self_recursion_carveout_fires_for_genuine_recursion() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn f [n] (if (eq-i64 n 0) 0 (f (sub-i64 n 1))))",
        );
        let view = main_codegen_view_of(&tc, "f");
        let mut targets = Vec::new();
        collect_resolved_targets(&view.body, &mut targets);
        let f_carrier = targets
            .iter()
            .find(|(l, _)| l == "f")
            .and_then(|(_, fq)| fq.clone());
        assert_eq!(
            f_carrier,
            Some(enclosing_test_fq("f")),
            "genuine self-call `f` Var must still carry resolved_target test/f; \
             collected: {targets:?}"
        );
    }

    // §11.8.7 ruling 5 — the overload-gate LOCAL-SCOPE-FIRST guard. A `let`
    // binding shadows a MULTI-SIG base `m1`; the shadowed call `(m1 x)` inside
    // the let body MUST resolve to the LOCAL binding (an indirect call, no
    // dispatch carrier), NOT enter the global overload path. On HEAD the
    // `infer.rs:604` gate consulted `state.overloads` by name without checking
    // local scope, so the call deferred past the drain and t1 wrong-rejected
    // (`undefined variable: t1`). The `add-i64` wrapper forces t1 concrete so it
    // carries a `codegen_view` to inspect. The `(m1 x)` callee `Var` must carry
    // NO `resolved_target` (a local indirect call), unlike a genuine overload
    // dispatch which would carry a `SigDispatch` mangle.
    #[test]
    fn overload_gate_skips_let_shadowed_multi_sig_base() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn m1 ([x] x) ([a b] a))\n\
             (defn t1 [x] (add-i64 (let [m1 (fn [y] y)] (m1 x)) 1))",
        );
        // t1 defined (not wrong-rejected) and concrete → has a codegen_view.
        let view = main_codegen_view_of(&tc, "t1");
        let mut targets = Vec::new();
        collect_resolved_targets(&view.body, &mut targets);
        // The `(m1 x)` callee `Var m1` must resolve to the LOCAL let binding —
        // no dispatch carrier (the shadowed base is not the overload dispatch).
        let m1_carrier = targets
            .iter()
            .find(|(l, _)| l == "m1")
            .map(|(_, fq)| fq.clone());
        assert_eq!(
            m1_carrier,
            Some(None),
            "the let-shadowed `(m1 x)` callee `Var` must carry NO resolved_target \
             (it is the LOCAL `(fn [y] y)`, an indirect call — the overload gate \
             MUST NOT bypass local scope); collected: {targets:?}"
        );
    }

    // Fix 1 (/arch-directed) — during a mono recheck, a `(s1 x)` whose callee is a
    // `let`-binding SHADOWING the base MUST record NO self-recursion dispatch: the
    // frame-guarded `is_recursion_self_ref` verdict (via record_reference_target)
    // left the callee carrier absent, so `record_self_recursion_dispatch` skips it.
    // Pre-fix it recorded `SigDispatch{s1$Int}` on the shadowed inner call → the
    // backend emitted a self-call (TCO loop → hang). The `add-i64` wrapper forces
    // `s1` concrete so `(s1 5)` mints an inspectable `s1$Int`. TAIL cell.
    #[test]
    fn mono_recheck_shadowed_self_call_records_no_dispatch() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn s1 [x] (let [s1 (fn [y] y)] (s1 x)))\n\
             (defn use-s1 [] (add-i64 (s1 5) 0))",
        );
        let view = mono_instance_view_containing(&tc, "s1$");
        let mut targets = Vec::new();
        collect_resolved_targets(&view.body, &mut targets);
        // No node in s1$Int's body may dispatch to a `s1$…` mono instance (the
        // shadowed `(s1 x)` is the LOCAL identity, an indirect call).
        let leaks_self_dispatch = targets.iter().any(|(_, fq)| {
            matches!(fq, Some(fq) if fq.symbol.as_ref().contains("s1$"))
        });
        assert!(
            !leaks_self_dispatch,
            "the let-shadowed `(s1 x)` inside `s1$Int` MUST NOT record a \
             self-recursion dispatch to `s1$Int` (Fix 1 — it is the LOCAL \
             identity); collected: {targets:?}"
        );
    }

    // Fix 1 non-tail sibling (/arch-required, typecheck half). Same shadow, but the
    // shadowed `(s1 x)` is NOT in tail position (`(add-i64 (… (s1 x)) 1)`) — no TCO
    // loop, but a mis-recorded self-dispatch would give the WRONG VALUE (call
    // `s1$Int` instead of the local identity). Typecheck assertion: still no
    // self-dispatch. (/testing lands the wrong-value e2e cell.)
    #[test]
    fn mono_recheck_shadowed_self_call_non_tail_records_no_dispatch() {
        let mut tc = tc_with_prims();
        // `(s1 x)` is bound to `r` (non-tail), keeping `s1` poly so it still
        // monomorphises to an inspectable `s1$Int`.
        check_src(
            &mut tc,
            "(defn s1 [x] (let [s1 (fn [y] y)] (let [r (s1 x)] r)))\n\
             (defn use-s1 [] (s1 5))",
        );
        let view = mono_instance_view_containing(&tc, "s1$");
        let mut targets = Vec::new();
        collect_resolved_targets(&view.body, &mut targets);
        assert!(
            !targets.iter().any(|(_, fq)| matches!(fq, Some(fq) if fq.symbol.as_ref().contains("s1$"))),
            "the non-tail let-shadowed `(s1 x)` MUST NOT record a self-recursion \
             dispatch (Fix 1 non-tail cell); collected: {targets:?}"
        );
    }

    // Fix 2 (MC-X2) — an IMPORTED multi-sig base `h` (defined in `mlib`) called
    // from `user` must dispatch AND its carrier must be keyed by the base's HOME
    // module (`mlib`), not `current_module` (`user`). Pre-fix the imported base
    // never entered the overload machinery → `undefined function: h`; and the
    // `SigDispatch` carrier hard-coded `current_module`. The `(h 1)` Apply must
    // carry a resolved_target `{mlib, h$Int}`.
    #[test]
    fn imported_multi_sig_base_carrier_keyed_by_home_mc_x2() {
        let mut tc = tc_with_prims();
        let mlib = ModuleFullPath::from("mlib");
        tc.set_current_module(mlib.clone());
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
        check_src(&mut tc, "(defn h ([x] (add-i64 x 1)) ([a b] (add-i64 a b)))");
        let user = ModuleFullPath::from("user");
        tc.set_current_module(user.clone());
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
        seed_specific_import(&mut tc, &mlib, &["h"]);
        // Simulate fresh per-cluster overload state (the real pipeline builds a
        // fresh CheckState per cluster; TestFixture reuses one, leaking `mlib`'s
        // local `h` overload into `user`'s cluster and masking the imported-base
        // rehydration path this test exercises).
        tc.state.overloads.clear();
        tc.state.resolved_overloads.clear();
        tc.state.overload_homes.clear();
        // `(add-i64 (h 1) 0)` pins use-h concrete → inspectable codegen_view.
        check_src(&mut tc, "(defn use-h [] (add-i64 (h 1) 0))");
        let view = main_codegen_view_of(&tc, "use-h");
        let mut targets = Vec::new();
        collect_resolved_targets(&view.body, &mut targets);
        let home_keyed = targets.iter().any(|(l, fq)| {
            l == "@apply"
                && matches!(fq, Some(fq)
                    if fq.module == mlib && fq.symbol.as_ref().contains("h$"))
        });
        assert!(
            home_keyed,
            "the imported multi-sig base call `(h 1)` MUST carry a resolved_target \
             keyed by the base's HOME module `mlib` (MC-X2, P24 storage identity — \
             NOT `user`); collected: {targets:?}"
        );
    }

    // Fix A (MC-X2 qualified face) — a QUALIFIED imported multi-sig call
    // `(mlib/h 1)` must dispatch to the STORED mangled identity `h$Int` keyed by
    // `mlib`, NOT re-derive from the written name (`mangle_sig("mlib/h",…)` =
    // `mlib/h$Int` → the bad `mlib/mlib/h$Int` no-entry). The `(mlib/h 1)` Apply
    // must carry `{mlib, h$Int}` — the symbol MUST NOT contain the `mlib/` prefix.
    #[test]
    fn imported_multi_sig_base_qualified_call_stored_identity_fix_a() {
        let mut tc = tc_with_prims();
        let mlib = ModuleFullPath::from("mlib");
        tc.set_current_module(mlib.clone());
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
        check_src(&mut tc, "(defn h ([x] (add-i64 x 1)) ([a b] (add-i64 a b)))");
        let user = ModuleFullPath::from("user");
        tc.set_current_module(user.clone());
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
        // Fresh per-cluster overload state (see the bare-face test).
        tc.state.overloads.clear();
        tc.state.resolved_overloads.clear();
        tc.state.overload_homes.clear();
        // Qualified reference `mlib/h` — resolves directly to the committed module
        // (no import needed).
        check_src(&mut tc, "(defn use-h [] (add-i64 (mlib/h 1) 0))");
        let view = main_codegen_view_of(&tc, "use-h");
        let mut targets = Vec::new();
        collect_resolved_targets(&view.body, &mut targets);
        let good = targets.iter().any(|(l, fq)| {
            l == "@apply"
                && matches!(fq, Some(fq)
                    if fq.module == mlib
                        && fq.symbol.as_ref() == "h$Int")
        });
        assert!(
            good,
            "the qualified imported call `(mlib/h 1)` MUST carry the STORED identity \
             `{{mlib, h$Int}}` (Fix A) — NOT the re-derived `mlib/h$Int` (which \
             renders `mlib/mlib/h$Int`, no entry); collected: {targets:?}"
        );
    }

    // Fix 1 / ruling-5 composition (/arch-flagged): §11.8.7's "during a mono
    // recheck the base is not locally bound" is FALSIFIED by a let-rebinds-base
    // case. A multi-sig base `m` shadowed by a `let` INSIDE a mono recheck
    // (`poly$Int`) must skip BOTH the overload gate AND the self-call classifier.
    // The ruling-5 gate does NOT rely on "base not locally bound" — it checks
    // `env.lookup(m).is_none() || is_recursion_self_ref(m)`: here env.lookup(m) is
    // Some (the let) and is_recursion_self_ref is false → gate false → the overload
    // path is skipped and `(m p)` resolves to the LOCAL. `check_src` panics if it
    // wrong-rejects; the mono instance's `(m p)` must carry no `m$…` dispatch.
    #[test]
    fn ruling5_composition_let_shadowed_multi_sig_base_in_mono_recheck() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn m ([x] x) ([a b] a))\n\
             (defn poly [p] (let [m (fn [y] y)] (m p)))\n\
             (defn use-poly [] (poly 5))",
        );
        let view = mono_instance_view_containing(&tc, "poly$");
        let mut targets = Vec::new();
        collect_resolved_targets(&view.body, &mut targets);
        assert!(
            !targets.iter().any(|(_, fq)| matches!(fq, Some(fq) if fq.symbol.as_ref().contains("m$"))),
            "the let-shadowed multi-sig base call `(m p)` inside `poly$Int` MUST \
             resolve to the LOCAL (no `m$…` overload dispatch) — the ruling-5 gate \
             composes under a mono recheck even when the base IS locally bound; \
             collected: {targets:?}"
        );
    }

    // Fix 1 control — a GENUINE monomorphic self-recursion (no shadow) MUST still
    // record its self-dispatch to the mono instance (the carrier is present via
    // the frame-guarded verdict). `cnt` is poly in `x`; `(cnt 5 3)` mints
    // `cnt$Int+Int` whose body's `(cnt x (sub-i64 n 1))` self-call dispatches to it
    // — the fix must not disable genuine self-recursion.
    #[test]
    fn mono_recheck_genuine_self_recursion_still_records() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn cnt [x n] (if (eq-i64 n 0) x (cnt x (sub-i64 n 1))))\n\
             (defn use-cnt [] (cnt 5 3))",
        );
        let view = mono_instance_view_containing(&tc, "cnt$");
        let mut targets = Vec::new();
        collect_resolved_targets(&view.body, &mut targets);
        assert!(
            targets.iter().any(|(_, fq)| matches!(fq, Some(fq) if fq.symbol.as_ref().contains("cnt$"))),
            "the genuine self-call `(cnt x (sub-i64 n 1))` MUST still dispatch to \
             the mono instance `cnt$Int+Int` (Fix 1 must not break genuine \
             self-recursion); collected: {targets:?}"
        );
    }

    // Fix B / FIXME 0653 — site 1 (pass-4 collector over a CONCRETE caller). A
    // let-shadowed parametric fn `(idp n)` MUST resolve to the LOCAL — the
    // name-scan collector (`collect_local_parametric_calls`) MUST NOT mint the
    // top-level `idp`'s mono (its callee has no keyed carrier — the shadow gate
    // declined it). Control: the UNSHADOWED call DOES mint `idp$Int`.
    #[test]
    fn shadowed_parametric_in_concrete_caller_no_mint_fix_b() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn idp [x] x)\n\
             (defn caller [n] (add-i64 (let [idp (fn [y] (add-i64 y 1))] (idp n)) 0))\n\
             (defn use-c [] (caller 5))",
        );
        assert!(
            symbol_names_containing(&tc, "idp$").is_empty(),
            "the let-shadowed `(idp n)` MUST NOT mint the top-level `idp`'s mono \
             (FIXME 0653); symbols: {:?}",
            symbol_names_containing(&tc, "idp"),
        );
        // Control — an UNSHADOWED `(idp n)` mints `idp$Int`.
        let mut tc2 = tc_with_prims();
        check_src(
            &mut tc2,
            "(defn idp [x] x)\n\
             (defn caller2 [n] (add-i64 (idp n) 0))\n\
             (defn use-c2 [] (caller2 5))",
        );
        assert!(
            !symbol_names_containing(&tc2, "idp$").is_empty(),
            "the UNSHADOWED `(idp n)` control MUST still mint `idp$Int`; symbols: {:?}",
            symbol_names_containing(&tc2, "idp"),
        );
    }

    // Fix B / FIXME 0653 — site 4 (mono-recheck epilogue, parametric hop). Inside a
    // monomorphised `poly$Int` body, a let-shadowed parametric `(tgt p)` MUST
    // resolve to the LOCAL — `monomorphise_inner_parametric_hops` MUST NOT record a
    // `tgt$…` dispatch. Control: the unshadowed twin.
    #[test]
    fn shadowed_parametric_in_mono_body_no_record_fix_b() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn tgt [x] x)\n\
             (defn poly [p] (let [tgt (fn [y] y)] (tgt p)))\n\
             (defn use-poly [] (poly 5))",
        );
        let view = mono_instance_view_containing(&tc, "poly$");
        let mut targets = Vec::new();
        collect_resolved_targets(&view.body, &mut targets);
        assert!(
            !targets.iter().any(|(_, fq)| matches!(fq, Some(fq) if fq.symbol.as_ref().contains("tgt$"))),
            "the shadowed `(tgt p)` in `poly$Int` MUST NOT record a `tgt$…` dispatch \
             (FIXME 0653 site 4); collected: {targets:?}"
        );
    }

    // Fix B / FIXME 0653 — site 3 (mono-recheck epilogue, constrained call). Inside
    // `poly$Int`, a let-shadowed constrained `(cadd p)` MUST resolve to the LOCAL —
    // `resolve_inner_constrained_calls` MUST NOT record a `cadd$…` dispatch.
    #[test]
    fn shadowed_constrained_in_mono_body_no_record_fix_b() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn cadd [x] (add-i64 x x))\n\
             (defn poly [p] (let [cadd (fn [y] y)] (cadd p)))\n\
             (defn use-poly [] (poly 5))",
        );
        let view = mono_instance_view_containing(&tc, "poly$");
        let mut targets = Vec::new();
        collect_resolved_targets(&view.body, &mut targets);
        assert!(
            !targets.iter().any(|(_, fq)| matches!(fq, Some(fq) if fq.symbol.as_ref().contains("cadd$"))),
            "the shadowed `(cadd p)` in `poly$Int` MUST NOT record a `cadd$…` \
             dispatch (FIXME 0653 site 3); collected: {targets:?}"
        );
    }

    // Leg 3 (dotted `Type.member`): a dotted ctor reference resolves through the
    // inverted-model member core, invisible to the W0 bare-name re-probe. It
    // carries `(fqtn.module, member_key)` at the Var span. `(Maybe.Some 3)` is
    // the always-works dotted spelling (S109); the type-only-import failure
    // scenario shares this producer path.
    #[test]
    fn resolved_target_dotted_ctor_carries_member_key_at_var_span() {
        let mut tc = tc_with_prims();
        // (deftype Maybe Nothing (Some [:Int v]))  then  (defn use-some [] (Maybe.Some 3))
        let program = vec![
            TopLevel::TypeDef {
                name: TypeName::from("Maybe"),
                docstring: None,
                type_params: vec![],
                constructors: vec![
                    cranelisp_types::ConstructorDef {
                        name: Symbol::from("Nothing"),
                        docstring: None,
                        fields: vec![],
                        span: Span::SYNTHETIC,
                    },
                    cranelisp_types::ConstructorDef {
                        name: Symbol::from("Some"),
                        docstring: None,
                        fields: vec![cranelisp_types::FieldDef {
                            name: Symbol::from("v"),
                            type_expr: TypeExpr::Named(cranelisp_types::TypeRef::new(
                                None,
                                TypeName::from("Int"),
                            )),
                            span: Span::SYNTHETIC,
                        }],
                        span: Span::SYNTHETIC,
                    },
                ],
                visibility: Visibility::Public,
                span: Span::SYNTHETIC,
            },
            TopLevel::Defn(make_defn(
                "use-some",
                vec![],
                vec![],
                Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("Maybe.Some"), span(80, 90))),
                    args: vec![Expr::IntLit { value: 3, span: span(91, 92), inferred_type: None }],
                    span: span(79, 93),
                    resolved_call: None,
                    inferred_type: None,
                },
                Visibility::Public,
                span(70, 94),
            )),
        ];
        tc.check_program_self(&program).unwrap();

        let view = main_codegen_view_of(&tc, "use-some");
        let mut targets = Vec::new();
        collect_resolved_targets(&view.body, &mut targets);
        let dotted_fq = targets
            .iter()
            .find(|(label, _)| label == "Maybe.Some")
            .and_then(|(_, fq)| fq.clone());
        assert_eq!(
            dotted_fq,
            Some(FQSymbol {
                module: ModuleFullPath::from("test"),
                symbol: cranelisp_types::member_key(&TypeName::from("Maybe"), "Some"),
            }),
            "dotted `Maybe.Some` Var must carry resolved_target test/Maybe.Some \
             (leg 3); collected: {targets:?}"
        );
    }

    // ---------------------------------------------------------------------
    // S110 W0.1b (§1.1.1) — the two further producer legs the cross-module
    // ruling fixed. Behaviour-invariant (carriers ride UNREAD until W1); these
    // assert the PRODUCER writes the right STORAGE module.
    // spec: design/arch/backend-keyed-consumer.md §1.1.1
    // ---------------------------------------------------------------------

    // W0.1b AutoCurry plain leg: a partial application of an IMPORTED fn carries
    // the TARGET's storage home at the auto-curry Apply span (transported from
    // the callee Var's already-recorded carrier), NOT the caller's module. The
    // pre-W0.1b `{current_module, target}` derivation named the caller ("test")
    // for an imported target whose Def lives in "lib".
    #[test]
    fn resolved_target_autocurry_imported_target_records_targets_home() {
        let mut tc = tc_with_prims();
        // `adder` (2-arg concrete) lives in module `lib`.
        tc.set_current_module(ModuleFullPath::from("lib"));
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
        check_src(&mut tc, "(defn adder [a b] (add-i64 a b))");
        // Back in `test`: import `adder`, then curry-apply it: ((adder 10) 20).
        tc.set_current_module(ModuleFullPath::from("test"));
        seed_specific_import(&mut tc, &ModuleFullPath::from("lib"), &["adder"]);
        check_src(&mut tc, "(defn main [] ((adder 10) 20))");

        let view = main_codegen_view_of(&tc, "main");
        let mut targets = Vec::new();
        collect_resolved_targets(&view.body, &mut targets);
        let want = FQSymbol {
            module: ModuleFullPath::from("lib"),
            symbol: Symbol::from("adder"),
        };
        assert!(
            targets
                .iter()
                .any(|(label, fq)| label == "@apply" && fq.as_ref() == Some(&want)),
            "the auto-curry Apply of imported `adder` must carry lib/adder (leg 2), \
             not the caller's module; collected: {targets:?}"
        );
    }

    // W0.1b fn-value mono-rewrite carrier: a generic fn passed as a VALUE into a
    // HOF is minted as `test/iden$Int` and its arg-position `Var` rewritten; the
    // span-keyed carrier is updated to the minted instance's STORAGE identity
    // (caller's module) so the rebuilt codegen view names the mono, not the
    // slot-less template. Without the fix the carrier stayed stale/absent and
    // the W2 0585 keyed read would hard-fail this valid program.
    #[test]
    fn resolved_target_fn_value_mono_rewrite_carries_mangled_carrier() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn iden [x] x)\n\
             (defn call1 [f x] (f x))\n\
             (defn use1 [] (call1 iden 5))",
        );
        let view = main_codegen_view_of(&tc, "use1");
        let mut targets = Vec::new();
        collect_resolved_targets(&view.body, &mut targets);
        let want = FQSymbol {
            module: ModuleFullPath::from("test"),
            symbol: Symbol::from("test/iden$Int"),
        };
        let got = targets
            .iter()
            .find(|(label, _)| label == "test/iden$Int")
            .and_then(|(_, fq)| fq.clone());
        assert_eq!(
            got,
            Some(want),
            "the rewritten fn-value Var `test/iden$Int` must carry its mono \
             storage carrier test/test/iden$Int at the arg span (leg 3); \
             collected: {targets:?}"
        );
    }

    // ---------------------------------------------------------------------
    // S110 W1.1 (§1.1.2, FIXME 0620) — the alias-class close. For a
    // member-canonical-keyed symbol (sum ctor, field accessor) OR a renamed
    // import, `Resolved.fq` composes the WRITTEN alias spelling; the recorder
    // now records `resolved.storage_fq()` (the terminal STORAGE key the walk
    // surfaced) so W1's `entry_at` direct read lands on the real Def. Carriers
    // ride UNREAD until W1 — these assert the PRODUCER records the storage key.
    // spec: design/arch/backend-keyed-consumer.md §1.1.2
    // ---------------------------------------------------------------------

    // Member-aliased BARE ctor: `(Some 3)` where `Some` is a bare Import alias
    // of the canonical `member_key(Maybe, Some)` = `Maybe.Some`. The bare Var
    // must carry `test/Maybe.Some` (terminal storage key), NOT `test/Some`
    // (the written alias `resolved.fq` composed pre-flip).
    #[test]
    fn resolved_target_bare_ctor_carrier_is_canonical_member_key() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(deftype Maybe Nothing (Some [:Int v]))\n\
             (defn use-some [] (Some 3))",
        );
        let view = main_codegen_view_of(&tc, "use-some");
        let mut targets = Vec::new();
        collect_resolved_targets(&view.body, &mut targets);
        let bare_fq =
            targets.iter().find(|(l, _)| l == "Some").and_then(|(_, fq)| fq.clone());
        assert_eq!(
            bare_fq,
            Some(FQSymbol {
                module: ModuleFullPath::from("test"),
                symbol: cranelisp_types::member_key(&TypeName::from("Maybe"), "Some"),
            }),
            "bare ctor `Some` Var must carry the canonical member_key storage \
             identity test/Maybe.Some, not the written alias test/Some; \
             collected: {targets:?}"
        );
    }

    // Member-aliased BARE field accessor: `(v b)` where `v` is a bare Import
    // alias of the canonical `member_key(Box, v)` = `Box.v` (a plain `UserFn`
    // Def — nothing on the entry identifies its `Type.field` key, so ONLY the
    // walk-surfaced storage key recovers it). The bare Var must carry
    // `test/Box.v`, NOT the written alias `test/v`.
    #[test]
    fn resolved_target_bare_accessor_carrier_is_canonical_member_key() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(deftype Box [:Int v])\n\
             (defn get-v [:Box b] (v b))",
        );
        let view = main_codegen_view_of(&tc, "get-v");
        let mut targets = Vec::new();
        collect_resolved_targets(&view.body, &mut targets);
        let accessor_fq =
            targets.iter().find(|(l, _)| l == "v").and_then(|(_, fq)| fq.clone());
        assert_eq!(
            accessor_fq,
            Some(FQSymbol {
                module: ModuleFullPath::from("test"),
                symbol: cranelisp_types::member_key(&TypeName::from("Box"), "v"),
            }),
            "bare accessor `v` Var must carry the canonical member_key storage \
             identity test/Box.v, not the written alias test/v; \
             collected: {targets:?}"
        );
    }

    // Renamed import `[lib [foo as bar]]`: the local key is `bar`, the source
    // storage key is `foo`. Referencing `bar` must carry the SOURCE storage key
    // `lib/foo` (what `entry_at` reads), NOT `lib/bar` (the home + written
    // spelling `resolved.fq` composed pre-flip — no such entry exists).
    #[test]
    fn resolved_target_renamed_import_carrier_is_source_storage_key() {
        let mut tc = tc_with_prims();
        // `foo` (0-arg, returns Int) lives in module `lib`.
        tc.set_current_module(ModuleFullPath::from("lib"));
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
        check_src(&mut tc, "(defn foo [] 0)");
        // Back in `test`: import `foo` RENAMED to `bar`, then call `(bar)`.
        tc.set_current_module(ModuleFullPath::from("test"));
        tc.symbol_table_mut().insert(
            Symbol::from("bar"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: ModuleFullPath::from("lib"),
                    symbol: Symbol::from("foo"),
                },
                visibility: Visibility::Public,
            },
        );
        check_src(&mut tc, "(defn use-bar [] (bar))");
        let view = main_codegen_view_of(&tc, "use-bar");
        let mut targets = Vec::new();
        collect_resolved_targets(&view.body, &mut targets);
        let bar_fq =
            targets.iter().find(|(l, _)| l == "bar").and_then(|(_, fq)| fq.clone());
        assert_eq!(
            bar_fq,
            Some(FQSymbol {
                module: ModuleFullPath::from("lib"),
                symbol: Symbol::from("foo"),
            }),
            "renamed-import `bar` Var must carry the SOURCE storage key lib/foo, \
             not the written alias lib/bar; collected: {targets:?}"
        );
    }

    // FIXME 0619 leg 1 (Important) — `builtin_storage_fq` must NOT capture a
    // same-named USER fn when grounding a `BuiltinFn` jit name. In a
    // prelude-suppressed module (no primitives glob) a local `(defn add-i64 …)`
    // prelude-suppressed module (no primitives glob) a local `(defn add-i64 …)`
    // is legal (add-i64 is not in scope, §8.6.4 does not fire); `(+ 1 2)`
    // short-circuits to `BuiltinFn { add-i64 }` (FIXME 0185), and the Apply-span
    // carrier MUST ground at `primitives/add-i64` (the primitive the backend
    // emits), never the shadowing local `test/add-i64`. The kind gate
    // (Primitive/PrimitiveExtern only) is what rejects the user fn. Without the
    // gate the carrier would name test/add-i64 → wrong dispatch at W1.
    // spec: design/arch/backend-keyed-consumer.md §1.1.1 (BuiltinFn leg)
    #[test]
    fn resolved_target_builtin_fq_ignores_shadowing_user_fn() {
        let mut tc = tc_with_prims();
        // `+` dispatches to the Int impl (short-circuit → jit name add-i64).
        register_num_trait_inline(&mut tc);
        // Model the prelude-suppressed shadow: a local UserFn named `add-i64`
        // (the primitive's JIT name) installed OVER the primitives-import in the
        // test module. `builtin_storage_fq` resolves the jit name through this
        // scope; the kind gate must reject this non-primitive Def and ground the
        // carrier at `primitives/add-i64` regardless.
        let local_add = cranelisp_types::ModuleEntry::def(
            cranelisp_types::Scheme {
                type_vars: vec![],
                constraints: Default::default(),
                ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            },
            cranelisp_types::DefKind::UserFn {
                fn_state: cranelisp_types::UserFnState::Concrete {
                    got_slot: 99,
                    mode_summary: None,
                },
            },
        )
        .param_names(vec![Symbol::from("a"), Symbol::from("b")])
        .build();
        tc.symbol_table_mut().insert(Symbol::from("add-i64"), local_add);
        check_src(&mut tc, "(defn main [] (+ 1 2))");

        let view = main_codegen_view_of(&tc, "main");
        let mut targets = Vec::new();
        collect_resolved_targets(&view.body, &mut targets);
        let apply_fq = targets
            .iter()
            .find(|(label, _)| label == "@apply")
            .and_then(|(_, fq)| fq.clone());
        assert_eq!(
            apply_fq,
            Some(FQSymbol {
                module: ModuleFullPath::from("primitives"),
                symbol: Symbol::from("add-i64"),
            }),
            "builtin_storage_fq must ground the PRIMITIVE home, not the shadowing \
             user fn test/add-i64 (FIXME 0619 leg 1); collected: {targets:?}"
        );
    }

    // W0.b (§5 proof obligation 1) — every synthesised field accessor's
    // codegen_view carries its pattern arm's `resolved_ctor` = the owner product
    // ctor's canonical STORAGE key (the bare type name for a product), populated
    // DIRECTLY at synthesis (`Span::SYNTHETIC` is outside span-keyed transport).
    // This is what CLOSES the backend's S19 `resolved_ctor: None` synthetic
    // fallback (byte-identical CLIF verified by golden class 02).
    // spec: design/arch/backend-keyed-consumer.md §5
    #[test]
    fn w0b_synth_accessor_view_carries_resolved_ctor() {
        let mut tc = tc_with_prims();
        // (deftype Point [:Int x :Int y]) — a product (ctor name == type name).
        check_src(&mut tc, "(deftype Point [:Int x :Int y])");
        let accessor_key = cranelisp_types::member_key(&TypeName::from("Point"), "x");
        let view = match tc.symbol_table().get(accessor_key.as_ref()) {
            Some(ModuleEntry::Def { codegen_view: Some(v), .. }) => v.clone(),
            other => panic!("accessor {accessor_key} has no codegen_view: {other:?}"),
        };
        let ctor = match &view.body {
            MonoExpr::Match { arms, .. } => arms.iter().find_map(|a| a.resolved_ctor.clone()),
            other => panic!("accessor body is not a Match: {other:?}"),
        };
        assert_eq!(
            ctor,
            Some(FQSymbol {
                module: ModuleFullPath::from("test"),
                symbol: Symbol::from("Point"),
            }),
            "accessor pattern arm must carry resolved_ctor test/Point at synthesis (§5)"
        );
    }

    // ---------------------------------------------------------------------
    // S110 W3.1 (§1.1.3, FIXME 0622) — the map-provenance close. A mono
    // instance of a generic ctor-pattern template must carry its match arm's
    // `resolved_ctor` = the ctor's canonical STORAGE key. The mono view is
    // built at `finalize_mono_codegen_view` from the PER-INSTANCE recheck's
    // `MethodResolutions` (the check-run pairing rule) — NOT the enclosing
    // run's `pattern_ctors`, which lacks the template's pattern spans whenever
    // the template was checked in a DIFFERENT run: cross-module (the filed
    // repro) OR cross-run same-module (REPL-incremental — the run-1 map is
    // swept at finalize before the run-2 mint). The recheck re-records every
    // ctor-pattern span under the `home` switch, so the per-instance map is
    // complete for all three carriers; the fix is read-the-right-map.
    // Cross-module + cross-run pins are RED on main (the arm carried `None`);
    // the same-run pin is the regression guard (correct on main too).
    // spec: design/arch/backend-keyed-consumer.md §1.1.3
    // ---------------------------------------------------------------------

    /// Walk a `MonoExpr` collecting every reachable `MonoMatchArm.resolved_ctor`
    /// (source order).
    fn collect_resolved_ctors(e: &MonoExpr, out: &mut Vec<Option<FQSymbol>>) {
        match e {
            MonoExpr::Match { scrutinee, arms, .. } => {
                collect_resolved_ctors(scrutinee, out);
                for arm in arms {
                    out.push(arm.resolved_ctor.clone());
                    collect_resolved_ctors(&arm.body, out);
                }
            }
            MonoExpr::Apply { callee, args, .. } => {
                collect_resolved_ctors(callee, out);
                for a in args {
                    collect_resolved_ctors(a, out);
                }
            }
            MonoExpr::If { cond, then_branch, else_branch, .. } => {
                collect_resolved_ctors(cond, out);
                collect_resolved_ctors(then_branch, out);
                collect_resolved_ctors(else_branch, out);
            }
            MonoExpr::Let { bindings, body, .. } => {
                for (_, b) in bindings {
                    collect_resolved_ctors(b, out);
                }
                collect_resolved_ctors(body, out);
            }
            MonoExpr::Lambda { body, .. } => collect_resolved_ctors(body, out),
            _ => {}
        }
    }

    /// Find a mono-instance ctor-pattern view in `module`: scan every mangled
    /// mono `Def` (name contains `mangle_frag`) whose `codegen_view` body holds
    /// a ctor-pattern arm, and return that FIRST arm's `resolved_ctor`. Outer
    /// `Option` = a mono ctor-pattern view was found; inner = its carrier.
    fn mono_match_arm_ctor(
        tc: &TestFixture,
        module: &str,
        mangle_frag: &str,
    ) -> Option<Option<FQSymbol>> {
        let st = tc.modules.get(&ModuleFullPath::from(module))?;
        for (name, entry) in st.all_symbols() {
            if !name.as_ref().contains(mangle_frag) {
                continue;
            }
            if let ModuleEntry::Def { codegen_view: Some(v), .. } = entry {
                let mut ctors = Vec::new();
                collect_resolved_ctors(&v.body, &mut ctors);
                if let Some(first) = ctors.into_iter().next() {
                    return Some(first);
                }
            }
        }
        None
    }

    // Pin (iii) — same-run regression guard. Template + first concrete call in
    // ONE check run: the live map accumulates the `Box` pattern span across the
    // run, so P7 reads it correctly regardless of the fix. Must stay GREEN.
    #[test]
    fn mono_ctor_pattern_view_same_run_carries_resolved_ctor() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(deftype (Box a) (Box [:a val]))\n\
             (defn get [b] (match b [(Box v) v]))\n\
             (defn use-box [] :primitives/Int (get (Box 5)))",
        );
        let arm_ctor = mono_match_arm_ctor(&tc, "test", "get$")
            .expect("get$Int mono instance with a ctor-pattern view must exist");
        assert_eq!(
            arm_ctor,
            Some(FQSymbol {
                module: ModuleFullPath::from("test"),
                symbol: Symbol::from("Box"),
            }),
            "same-run mono ctor-pattern arm must carry test/Box (regression pin)"
        );
    }

    // Pin (ii) — cross-run same-module (REPL-incremental) twin. RED on main.
    #[test]
    fn mono_ctor_pattern_view_cross_run_same_module_carries_resolved_ctor() {
        let mut tc = tc_with_prims();
        // Run 1: define the generic ctor-pattern template. Its `Box` pattern
        // span is recorded into run 1's `MethodResolutions`, then TAKEN (swept)
        // at finalize — gone by run 2.
        check_src(
            &mut tc,
            "(deftype (Box a) (Box [:a val]))\n\
             (defn get [b] (match b [(Box v) v]))",
        );
        // Run 2: the first concrete call mints get$Int. The enclosing run-2 map
        // has NO `Box` pattern span (run 1's was swept), so the pre-fix
        // view-build read `None`; the per-instance recheck re-records it.
        check_src(&mut tc, "(defn use-box [] :primitives/Int (get (Box 5)))");
        let arm_ctor = mono_match_arm_ctor(&tc, "test", "get$")
            .expect("get$Int mono instance with a ctor-pattern view must exist");
        assert_eq!(
            arm_ctor,
            Some(FQSymbol {
                module: ModuleFullPath::from("test"),
                symbol: Symbol::from("Box"),
            }),
            "cross-run same-module mono ctor-pattern arm must carry test/Box \
             (0622: was None on main — run-1's map was swept before the run-2 mint)"
        );
    }

    // Pin (i) — cross-module twin (the filed 0622 repro). RED on main.
    #[test]
    fn mono_ctor_pattern_view_cross_module_carries_resolved_ctor() {
        let mut tc = tc_with_prims();
        // The generic ctor-pattern template lives in module `lib`.
        tc.set_current_module(ModuleFullPath::from("lib"));
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
        check_src(
            &mut tc,
            "(deftype (Box a) (Box [:a val]))\n\
             (defn get [b] (match b [(Box v) v]))",
        );
        // The caller in `test` imports the ctor + fn and calls at a concrete
        // type; pass4 mints the cross-module mono, whose recheck runs under the
        // `home = lib` switch and re-records the `Box` pattern in lib's scope.
        tc.set_current_module(ModuleFullPath::from("test"));
        seed_specific_import(&mut tc, &ModuleFullPath::from("lib"), &["Box", "get"]);
        check_src(&mut tc, "(defn use-box [] :primitives/Int (get (Box 5)))");
        let arm_ctor = mono_match_arm_ctor(&tc, "test", "get$")
            .expect("cross-module get$Int mono with a ctor-pattern view must exist");
        assert_eq!(
            arm_ctor,
            Some(FQSymbol {
                module: ModuleFullPath::from("lib"),
                symbol: Symbol::from("Box"),
            }),
            "cross-module mono ctor-pattern arm must carry lib/Box (the DEFINING \
             module's storage key), resolved by the per-instance recheck under \
             the home switch (0622: was None on main)"
        );
    }

    // W0.b (§5 proof obligation 2) — the TOTALIZATION pin: every codegen-reached
    // `defined_symbols()` entry carries a codegen_view after check (the backend's
    // view-absent hard error is the runtime twin). Ctor + accessor synthetic
    // bodies and concrete defns must ALL be viewed — no `None` reaches codegen.
    // spec: design/arch/backend-keyed-consumer.md §5
    #[test]
    fn w0b_every_codegen_reached_entry_carries_a_view() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(deftype Box [:Int v])\n\
             (deftype Color (Red) (Green))\n\
             (defn main [] (v (Box 7)))",
        );
        let st = tc.symbol_table();
        let missing: Vec<Symbol> = st
            .defined_symbols()
            .filter(|(_, e)| e.codegen_view().is_none())
            .map(|(k, _)| k.clone())
            .collect();
        assert!(
            missing.is_empty(),
            "every codegen-reached entry must carry a codegen_view post-W0.b; \
             missing: {missing:?}"
        );
    }

    // spec: 03-types §3.6 — REPL defn body triggers monomorphisation of constrained calls
    #[test]
    fn test_repl_defn_body_monomorphise() {
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);

        // Define a constrained fn: (defn add [x y] (+ x y))
        let defn_input = TopLevel::Defn(Defn {
            name: Symbol::from("add"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("+"), span(18, 19))),
                    args: vec![
                        Expr::var(Symbol::from("x"), span(20, 21)),
                        Expr::var(Symbol::from("y"), span(22, 23)),
                    ],
                    span: span(17, 24),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(0, 25),
            }],
            visibility: Visibility::Public,
            span: span(0, 25),
        });
        let _ = tc.check_repl_input_self(&defn_input).unwrap();

        // Define a function that calls the constrained fn: (defn main [] (add 1 2))
        let main_input = TopLevel::Defn(Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("add"), span(200, 203))),
                    args: vec![
                        Expr::IntLit { value: 1, span: span(204, 205), inferred_type: None, },
                        Expr::IntLit { value: 2, span: span(206, 207), inferred_type: None, },
                    ],
                    span: span(199, 208),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(180, 209),
            }],
            visibility: Visibility::Public,
            span: span(180, 209),
        });
        let _result = tc.check_repl_input_self(&main_input).unwrap();

        // Should have mono_defns from the defn body scan (entry on SymbolTable post-slim)
        let mono_names = tc.mono_defn_names();
        assert!(
            !mono_names.is_empty(),
            "REPL defn should generate mono_defns for constrained fn calls in body"
        );
        assert!(
            // FIXME 0519: mono names are home-qualified `{home}/{bare}$sig`.
            mono_names.iter().any(|n| n.as_ref() == "test/add$Int+Int"),
            "expected test/add$Int+Int in mono entries, got {mono_names:?}"
        );
    }

    // spec: 03-types §3.6 — program without constrained fns produces empty mono results
    #[test]
    fn test_batch_mono_no_constrained_fns_produces_empty() {
        let mut tc = tc_with_prims();
        // (defn inc [x] (add-i64 x 1)) — no constrained fns, all monomorphic
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("inc"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None)],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("add-i64"), span(16, 23))),
                    args: vec![
                        Expr::var(Symbol::from("x"), span(24, 25)),
                        Expr::IntLit { value: 1, span: span(26, 27), inferred_type: None, },
                    ],
                    span: span(15, 28),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(0, 29),
            }],
            visibility: Visibility::Public,
            span: span(0, 29),
        })];

        let _result = tc.check_program_self(&program).unwrap();

        assert!(tc.constrained_fn_names_set().is_empty());
        assert!(tc.mono_defn_names().is_empty());
    }

    // --- Multi-sig defn tests ---

    /// Helper to build a CompileContext for test module.
    fn test_ctx() -> CompileContext {
        CompileContext {
            module: ModuleFullPath::from("test"),
            codegen: cranelisp_types::CodegenBehaviour::InMemoryAndObject,
        }
    }

    /// Helper to build a multi-sig Defn.
    fn make_multi_defn(
        name: &str,
        variants: Vec<DefnVariant>,
        span: Span,
    ) -> Defn {
        Defn {
            name: Symbol::from(name),
            docstring: None,
            variants,
            visibility: Visibility::Public,
            span,
        }
    }

    // spec: 05-definitions §5.1.2 — multi-sig defn with different arities
    #[test]
    fn test_multi_sig_different_arities() {
        let mut tc = tc_with_prims();

        // (defn add
        //   ([x y] (add-i64 x y))
        //   ([x y z] (add-i64 x (add-i64 y z))))
        let program = vec![TopLevel::Defn(make_multi_defn(
            "add",
            vec![
                DefnVariant {
                    params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add-i64"), span(10, 17))),
                        args: vec![
                            Expr::var(Symbol::from("x"), span(18, 19)),
                            Expr::var(Symbol::from("y"), span(20, 21)),
                        ],
                        span: span(9, 22),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(5, 23),
                },
                DefnVariant {
                    params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None), (Symbol::from("z"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add-i64"), span(30, 37))),
                        args: vec![
                            Expr::var(Symbol::from("x"), span(38, 39)),
                            Expr::Apply {
                                callee: Box::new(Expr::var(Symbol::from("add-i64"), span(41, 48))),
                                args: vec![
                                    Expr::var(Symbol::from("y"), span(49, 50)),
                                    Expr::var(Symbol::from("z"), span(51, 52)),
                                ],
                                span: span(40, 53),
                                resolved_call: None,
                                inferred_type: None,
                            },
                        ],
                        span: span(29, 54),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(25, 55),
                },
            ],
            span(0, 56),
        ))];

        let _result = tc.check(&program, &test_ctx(), cranelisp_types::ModuleStrategy::Additive).unwrap();

        // The base name "add" should be registered as Overloaded
        let table_guard = tc.symbol_table();
        let entry = table_guard.get("add");
        assert!(entry.is_some(), "base name 'add' should be registered");
        if let Some(ModuleEntry::Def { kind, .. }) = entry {
            assert!(
                matches!(kind.as_ref(), DefKind::Overloaded { variants } if variants.len() == 2),
                "add should be Overloaded with 2 variants"
            );
        } else {
            panic!("add should be a Def entry");
        }

        // Mangled names should be registered: add$Int+Int and add$Int+Int+Int
        assert!(
            tc.symbol_table().get("add$Int+Int").is_some(),
            "add$Int+Int should be registered"
        );
        assert!(
            tc.symbol_table().get("add$Int+Int+Int").is_some(),
            "add$Int+Int+Int should be registered"
        );

        // The multi-sig defns live on SymbolTable post-slim (Wave 2 step 4).
        // The `default_method_defns` CheckResult field was retired; the mangled
        // entries are directly observable on the symbol table instead.
        let mangled_count = tc
            .symbol_table()
            .all_symbols()
            .filter(|(name, _)| name.as_ref().starts_with("add$"))
            .count();
        assert_eq!(
            mangled_count, 2,
            "should produce 2 mangled defns for the backend"
        );
    }

    // spec: 05-definitions §5.1.2 — multi-sig with same arity but different types
    #[test]
    fn test_multi_sig_same_arity_different_types() {
        let mut tc = tc_with_prims();

        // (defn process
        //   ([:Int x] (add-i64 x 1))
        //   ([:Bool x] (if x 1 0)))
        let program = vec![TopLevel::Defn(make_multi_defn(
            "process",
            vec![
                DefnVariant {
                    params: vec![(Symbol::from("x"), Some(TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int")))))],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add-i64"), span(110, 117))),
                        args: vec![
                            Expr::var(Symbol::from("x"), span(118, 119)),
                            Expr::IntLit { value: 1, span: span(120, 121), inferred_type: None, },
                        ],
                        span: span(109, 122),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(105, 123),
                },
                DefnVariant {
                    params: vec![(Symbol::from("x"), Some(TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Bool")))))],
                    body: Expr::If {
                        cond: Box::new(Expr::var(Symbol::from("x"), span(130, 131))),
                        then_branch: Box::new(Expr::IntLit { value: 1, span: span(132, 133), inferred_type: None, }),
                        else_branch: Box::new(Expr::IntLit { value: 0, span: span(134, 135), inferred_type: None, }),
                        span: span(127, 136),
                        inferred_type: None,
                    },
                    span: span(125, 137),
                },
            ],
            span(100, 138),
        ))];

        let _result = tc.check(&program, &test_ctx(), cranelisp_types::ModuleStrategy::Additive).unwrap();

        // Mangled names should be different: process$Int vs process$Bool
        assert!(
            tc.symbol_table().get("process$Int").is_some(),
            "process$Int should be registered"
        );
        assert!(
            tc.symbol_table().get("process$Bool").is_some(),
            "process$Bool should be registered"
        );

        // 2 mangled defns produced (observable on SymbolTable post-slim).
        let mangled_count = tc
            .symbol_table()
            .all_symbols()
            .filter(|(name, _)| name.as_ref().starts_with("process$"))
            .count();
        assert_eq!(mangled_count, 2);
    }

    // spec: 05-definitions §5.1.2 — duplicate signatures produce an error
    #[test]
    fn test_multi_sig_duplicate_signatures_error() {
        let mut tc = tc_with_prims();

        // (defn dup
        //   ([:Int x] (add-i64 x 1))
        //   ([:Int y] (add-i64 y 2)))
        // Both variants have the same signature (Int) -> Int — should error.
        let program = vec![TopLevel::Defn(make_multi_defn(
            "dup",
            vec![
                DefnVariant {
                    params: vec![(Symbol::from("x"), Some(TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int")))))],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add-i64"), span(210, 217))),
                        args: vec![
                            Expr::var(Symbol::from("x"), span(218, 219)),
                            Expr::IntLit { value: 1, span: span(220, 221), inferred_type: None, },
                        ],
                        span: span(209, 222),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(205, 223),
                },
                DefnVariant {
                    params: vec![(Symbol::from("y"), Some(TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int")))))],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add-i64"), span(230, 237))),
                        args: vec![
                            Expr::var(Symbol::from("y"), span(238, 239)),
                            Expr::IntLit { value: 2, span: span(240, 241), inferred_type: None, },
                        ],
                        span: span(229, 242),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(225, 243),
                },
            ],
            span(200, 244),
        ))];

        let err = tc.check(&program, &test_ctx(), cranelisp_types::ModuleStrategy::Additive);
        assert!(err.is_err(), "duplicate signatures should produce an error");
        let msg = format!("{}", err.unwrap_err());
        assert!(
            msg.contains("duplicate signature"),
            "error should mention 'duplicate signature', got: {msg}"
        );
    }

    // spec: 05-definitions §5.1.2 — call site resolves to correct variant
    #[test]
    fn test_multi_sig_call_site_resolution() {
        let mut tc = tc_with_prims();

        // Define multi-sig:
        // (defn add
        //   ([:Int x :Int y] (add-i64 x y))
        //   ([:Int x :Int y :Int z] (add-i64 x (add-i64 y z))))
        //
        // Then call it:
        // (add 1 2)  -- should resolve to add$Int+Int

        let multi_defn = TopLevel::Defn(make_multi_defn(
            "add",
            vec![
                DefnVariant {
                    params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add-i64"), span(310, 317))),
                        args: vec![
                            Expr::var(Symbol::from("x"), span(318, 319)),
                            Expr::var(Symbol::from("y"), span(320, 321)),
                        ],
                        span: span(309, 322),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(305, 323),
                },
                DefnVariant {
                    params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None), (Symbol::from("z"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add-i64"), span(330, 337))),
                        args: vec![
                            Expr::var(Symbol::from("x"), span(338, 339)),
                            Expr::Apply {
                                callee: Box::new(Expr::var(Symbol::from("add-i64"), span(341, 348))),
                                args: vec![
                                    Expr::var(Symbol::from("y"), span(349, 350)),
                                    Expr::var(Symbol::from("z"), span(351, 352)),
                                ],
                                span: span(340, 353),
                                resolved_call: None,
                                inferred_type: None,
                            },
                        ],
                        span: span(329, 354),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(325, 355),
                },
            ],
            span(300, 356),
        ));

        // Expression that calls add with 2 args: (add 1 2)
        let call_span = span(400, 410);
        let call_expr = TopLevel::Expr(Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("add"), span(401, 404))),
            args: vec![
                Expr::IntLit { value: 1, span: span(405, 406), inferred_type: None, },
                Expr::IntLit { value: 2, span: span(407, 408), inferred_type: None, },
            ],
            span: call_span,
            resolved_call: None,
            inferred_type: None,
        });

        let program = vec![multi_defn, call_expr];
        let _result = tc.check(&program, &test_ctx(), cranelisp_types::ModuleStrategy::Additive).unwrap();

        // The call site should have a SigDispatch resolution to "add$Int+Int".
        // Post-slim (Wave 2 step 4): resolutions live on annotated AST nodes.
        let resolutions = tc.annotated_resolutions();
        let resolution = resolutions.get(&call_span);
        assert!(
            resolution.is_some(),
            "call site should have a resolution"
        );
        match resolution.unwrap() {
            ResolvedCall::SigDispatch { mangled_name } => {
                assert_eq!(
                    mangled_name.as_ref(), "add$Int+Int",
                    "should dispatch to add$Int+Int"
                );
            }
            other => {
                panic!("expected SigDispatch, got {:?}", other);
            }
        }
    }

    // =========================================================================
    // Per-Form Typecheck API tests (Sprint 40 Wave 2)
    // =========================================================================
    //
    // These tests exercise the new check_form / merge_form_result / finalize_check_result
    // API introduced for the v4 pipeline. They validate:
    // 1. Behavioral identity: check() via check_form produces same results
    // 2. Per-form basics: individual forms through check_form
    // 3. Two-pass correctness: register-then-check ordering
    // 4. Multi-form programs with interactions
    // 5. Edge cases from the design doc
    // 6. Negative tests (error cases)

    /// Helper: create a CompileContext for the "test" module (check_form tests).
    fn cf_test_ctx() -> CompileContext {
        CompileContext {
            module: ModuleFullPath::from("test"),
            codegen: cranelisp_types::CodegenBehaviour::InMemoryAndObject,
        }
    }

    /// Helper: build an "inc" defn: (defn inc [x] (add-i64 x 1))
    fn make_inc_defn() -> Defn {
        make_defn(
            "inc",
            vec![Symbol::from("x")],
            vec![None],
            Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("add-i64"), span(16, 23))),
                args: vec![
                    Expr::var(Symbol::from("x"), span(24, 25)),
                    Expr::IntLit {
                        value: 1,
                        span: span(26, 27),
                        inferred_type: None,
                    },
                ],
                span: span(15, 28),
                resolved_call: None,
                inferred_type: None,
            },
            Visibility::Public,
            span(0, 29),
        )
    }

    /// Helper: build a Color typedef with Red and Green constructors.
    fn make_color_typedef() -> TopLevel {
        TopLevel::TypeDef {
            name: TypeName::from("Color"),
            docstring: None,
            type_params: vec![],
            constructors: vec![
                cranelisp_types::ConstructorDef {
                    name: Symbol::from("Red"),
                    docstring: None,
                    fields: vec![],
                    span: span(200, 203),
                },
                cranelisp_types::ConstructorDef {
                    name: Symbol::from("Green"),
                    docstring: None,
                    fields: vec![],
                    span: span(204, 209),
                },
            ],
            visibility: Visibility::Public,
            span: span(190, 210),
        }
    }

    /// Helper: build an is-red defn that matches on Color.
    fn make_is_red_defn() -> Defn {
        Defn {
            name: Symbol::from("is-red"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("c"), None)],
                body: Expr::Match {
                    scrutinee: Box::new(Expr::var(Symbol::from("c"), span(230, 231))),
                    arms: vec![
                        cranelisp_types::MatchArm {
                            pattern: cranelisp_types::Pattern::Constructor {
                                name: cranelisp_types::SymbolRef::new(None, Symbol::from("Red")),
                                bindings: vec![],
                                span: span(233, 236),
                            },
                            body: Expr::BoolLit {
                                value: true,
                                span: span(237, 241),
                                inferred_type: None,
                            },
                            span: span(233, 241),
                        },
                        cranelisp_types::MatchArm {
                            pattern: cranelisp_types::Pattern::Wildcard {
                                span: span(242, 243),
                            },
                            body: Expr::BoolLit {
                                value: false,
                                span: span(244, 249),
                                inferred_type: None,
                            },
                            span: span(242, 249),
                        },
                    ],
                    span: span(224, 250),
                    compiler_generated: false,
                    inferred_type: None,
                },
                span: span(211, 251),
            }],
            visibility: Visibility::Public,
            span: span(211, 251),
        }
    }

    /// Helper: build the forward-reference program (double calls add-self).
    fn make_forward_ref_program() -> Vec<TopLevel> {
        vec![
            TopLevel::Defn(Defn {
                name: Symbol::from("double"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("x"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add-self"), span(318, 326))),
                        args: vec![Expr::var(Symbol::from("x"), span(327, 328))],
                        span: span(317, 329),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(300, 330),
                }],
                visibility: Visibility::Public,
                span: span(300, 330),
            }),
            TopLevel::Defn(Defn {
                name: Symbol::from("add-self"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("y"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add-i64"), span(348, 355))),
                        args: vec![
                            Expr::var(Symbol::from("y"), span(356, 357)),
                            Expr::var(Symbol::from("y"), span(358, 359)),
                        ],
                        span: span(347, 360),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(331, 361),
                }],
                visibility: Visibility::Public,
                span: span(331, 361),
            }),
        ]
    }

    // ---- Category 1: Behavioral Identity ----

    // spec: design/typecheck/check-form-api.md — check() via check_form produces identical CheckResult
    #[test]
    fn test_check_form_identity_simple_defn() {
        // Run a simple defn program through check() and verify the result matches expectations.
        // Since check() now internally uses check_form(), this tests behavioral identity.
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();
        let program = vec![TopLevel::Defn(make_inc_defn())];

        let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // Verify the function was registered with correct type
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("inc") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                "inc should be (Fn [Int] Int)"
            );
        } else {
            panic!("inc not found in symbol table after check()");
        }

        // Verify annotated ASTs carry inferred types on body expressions.
        // Post-slim (Wave 2 step 4): `expr_types` is no longer on CheckResult.
        let mut any_typed = false;
        let mut all_resolved = true;
        if let Some(ModuleEntry::Def { ast: Some(defn), .. }) = tc.symbol_table().get("inc") {
            walk_inferred_types(&defn.body, &mut any_typed, &mut all_resolved);
        }
        assert!(any_typed, "expr_types should be populated on annotated AST");
        assert!(all_resolved, "all expr_types should be resolved (no Var types)");

        // Verify method_resolutions populated (add-i64 call site resolved)
        assert!(
            !tc.annotated_resolutions().is_empty(),
            "method_resolutions should have add-i64 call site"
        );
    }

    // spec: design/typecheck/check-form-api.md — typedef + defn identity
    #[test]
    fn test_check_form_identity_typedef_plus_defn() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();
        let program = vec![
            make_color_typedef(),
            TopLevel::Defn(make_is_red_defn()),
        ];

        let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // type_defs and constructor_to_type should be populated
        assert!(tc.lookup_type_def(&TypeName::from("Color")).is_some());
        assert!(tc.lookup_constructor_type("Red").is_some());
        assert!(tc.lookup_constructor_type("Green").is_some());

        // is-red should have correct type
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("is-red") {
            assert_eq!(
                scheme.ty,
                Type::Fn(
                    vec![Type::ADT(test_fqtn("Color"), vec![])],
                    Box::new(Type::Bool)
                )
            );
        } else {
            panic!("is-red not found in symbol table");
        }

        // expr_types should be populated on annotated AST (post-slim).
        let mut any_typed = false;
        let mut _all_resolved = true;
        if let Some(ModuleEntry::Def { ast: Some(defn), .. }) = tc.symbol_table().get("is-red") {
            walk_inferred_types(&defn.body, &mut any_typed, &mut _all_resolved);
        }
        assert!(any_typed);
    }

    // spec: design/typecheck/check-form-api.md — forward reference identity
    #[test]
    fn test_check_form_identity_forward_reference() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();
        let program = make_forward_ref_program();

        let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // Both should be monomorphic Int -> Int
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("double") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int)),
            );
        } else {
            panic!("double not found");
        }

        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("add-self") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int)),
            );
        } else {
            panic!("add-self not found");
        }

        // expr_types should be populated on annotated AST (post-slim).
        let mut any_typed = false;
        let mut _all_resolved = true;
        if let Some(ModuleEntry::Def { ast: Some(defn), .. }) = tc.symbol_table().get("add-self") {
            walk_inferred_types(&defn.body, &mut any_typed, &mut _all_resolved);
        }
        assert!(any_typed);
    }

    // spec: design/typecheck/check-form-api.md — constrained fn identity
    #[test]
    fn test_check_form_identity_constrained_fn() {
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);
        let ctx = cf_test_ctx();

        // (defn add [x y] (+ x y)) — constrained by Num trait
        let program = vec![TopLevel::Defn(make_defn(
            "add",
            vec![Symbol::from("x"), Symbol::from("y")],
            vec![None, None],
            Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("+"), span(400, 401))),
                args: vec![
                    Expr::var(Symbol::from("x"), span(402, 403)),
                    Expr::var(Symbol::from("y"), span(404, 405)),
                ],
                span: span(399, 406),
                resolved_call: None,
                inferred_type: None,
            },
            Visibility::Public,
            span(390, 407),
        ))];

        let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // Should be detected as constrained polymorphic (entry on SymbolTable
        // post-slim; derived from `DefKind::UserFn { constrained_fn: Some(_) }`).
        assert!(
            tc.constrained_fn_names_set().contains(&Symbol::from("add")),
            "add should be detected as constrained polymorphic"
        );
    }

    // spec: design/typecheck/check-form-api.md — expression-only identity
    #[test]
    fn test_check_form_identity_expr() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();
        let program = vec![TopLevel::Expr(Expr::IntLit {
            value: 42,
            span: span(500, 502),
            inferred_type: None,
        })];

        let result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // Display info should show Int type
        assert!(result.display.is_some());
        assert_eq!(result.display.as_ref().unwrap().ty, Type::Int);

        // expr_types should contain the literal's type. Post-slim (Wave 2
        // step 4), `__expr` carries its annotated AST on the symbol table.
        let mut any_typed = false;
        let mut _all_resolved = true;
        if let Some(ModuleEntry::Def { ast: Some(defn), .. }) = tc.symbol_table().get("__expr") {
            walk_inferred_types(&defn.body, &mut any_typed, &mut _all_resolved);
        }
        assert!(any_typed, "expr_types should contain the literal's type");
    }

    // spec: design/typecheck/check-form-api.md — multi-sig defn identity
    #[test]
    fn test_check_form_identity_multi_sig() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();

        // Multi-sig: (defn add ([x] (add-i64 x 1)) ([x y] (add-i64 x y)))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("add"),
            docstring: None,
            variants: vec![
                DefnVariant {
                    params: vec![(Symbol::from("x"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add-i64"), span(610, 617))),
                        args: vec![
                            Expr::var(Symbol::from("x"), span(618, 619)),
                            Expr::IntLit { value: 1, span: span(620, 621), inferred_type: None, },
                        ],
                        span: span(609, 622),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(600, 623),
                },
                DefnVariant {
                    params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add-i64"), span(640, 647))),
                        args: vec![
                            Expr::var(Symbol::from("x"), span(648, 649)),
                            Expr::var(Symbol::from("y"), span(650, 651)),
                        ],
                        span: span(639, 652),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(630, 653),
                },
            ],
            visibility: Visibility::Public,
            span: span(590, 654),
        })];

        let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // The base name should be Overloaded in symbol table
        if let Some(ModuleEntry::Def { kind, .. }) = tc.symbol_table().get("add") {
            match kind.as_ref() {
                DefKind::Overloaded { variants } => {
                    assert_eq!(variants.len(), 2, "should have 2 overload variants");
                }
                other => panic!("expected Overloaded, got {:?}", other),
            }
        } else {
            panic!("add not found in symbol table");
        }

        // expr_types should be populated from both variant bodies (post-slim).
        let mut any_typed = false;
        let mut _all_resolved = true;
        if let Some(ModuleEntry::Def { ast: Some(defn), .. }) =
            tc.symbol_table().get("add$Int+Int")
        {
            walk_inferred_types(&defn.body, &mut any_typed, &mut _all_resolved);
        }
        assert!(any_typed);
    }

    // ---- Category 2: Per-Form Basics ----

    // spec: design/typecheck/check-form-api.md §check_form — single defn Register pass
    #[test]
    fn test_check_form_single_defn_register() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let defn = make_inc_defn();
        let form = TopLevel::Defn(defn);
        let result = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();

        // Register pass should produce empty method_resolutions and expr_types
        assert!(result.method_resolutions.is_empty(), "Register pass produces no method resolutions");
        assert!(result.expr_types.is_empty(), "Register pass produces no expr types");
        assert!(result.constrained_fn.is_none(), "Register pass has no constrained fn");
        assert!(result.mono_defns.is_empty(), "Register pass has no mono defns");

        // Signature should be registered in the accumulator's defn_type_vars
        assert!(
            accumulator.defn_type_vars.contains_key(&Symbol::from("inc")),
            "defn_type_vars should contain 'inc' after Register pass"
        );

        // Signature should be registered in symbol table
        assert!(
            tc.symbol_table().get("inc").is_some(),
            "inc should be in symbol table after Register pass"
        );
    }

    // spec: design/typecheck/check-form-api.md §check_form — single defn CheckBody pass
    #[test]
    fn test_check_form_single_defn_check_body() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let defn = make_inc_defn();
        let form = TopLevel::Defn(defn);

        // Must register first
        let reg_result = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, reg_result);

        // Now check body
        let body_result = tc.check_form(&module, &form, CheckPass::CheckBody, &mut accumulator).unwrap();

        // CheckBody pass should produce expr_types (body expressions typed)
        assert!(
            !body_result.expr_types.is_empty(),
            "CheckBody should produce expr_types for body expressions"
        );

        // CheckBody pass should produce method_resolutions for add-i64 call
        assert!(
            !body_result.method_resolutions.is_empty(),
            "CheckBody should have method resolution for add-i64 call"
        );

        // No constrained fn (inc is monomorphic)
        assert!(body_result.constrained_fn.is_none());
    }

    // spec: design/typecheck/check-form-api.md §check_form — TypeDef Register pass
    #[test]
    fn test_check_form_typedef_register() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let form = make_color_typedef();
        let result = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();

        // Registration should be mostly empty result (type is registered internally)
        assert!(result.default_method_defns.is_empty());

        // Constructors should be registered in symbol table
        assert!(
            tc.symbol_table().get("Red").is_some(),
            "Red constructor should be in symbol table"
        );
        assert!(
            tc.symbol_table().get("Green").is_some(),
            "Green constructor should be in symbol table"
        );
    }

    // spec: design/typecheck/check-form-api.md §check_form — TypeDef CheckBody is no-op
    #[test]
    fn test_check_form_typedef_check_body_noop() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let form = make_color_typedef();
        // Register first
        let _ = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();

        // CheckBody on TypeDef should be a no-op
        let result = tc.check_form(&module, &form, CheckPass::CheckBody, &mut accumulator).unwrap();
        assert!(result.method_resolutions.is_empty());
        assert!(result.expr_types.is_empty());
        assert!(result.constrained_fn.is_none());
        assert!(result.mono_defns.is_empty());
    }

    // spec: design/typecheck/check-form-api.md §check_form — TraitDecl Register pass
    #[test]
    fn test_check_form_trait_decl_register() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let decl = TraitDecl {
            name: TraitName::from("Eq"),
            docstring: None,
            type_params: vec![],
            methods: vec![TraitMethodSig {
                name: Symbol::from("eq"),
                docstring: None,
                params: vec![
                    (Symbol::from("lhs"), TypeExpr::SelfType),
                    (Symbol::from("rhs"), TypeExpr::SelfType),
                ],
                ret_type: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Bool"))),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let form = TopLevel::TraitDecl(decl);
        let result = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();

        // Should produce an empty result (registration is internal)
        assert!(result.method_resolutions.is_empty());
        assert!(result.expr_types.is_empty());
        assert!(result.default_method_defns.is_empty());
    }

    // spec: design/typecheck/check-form-api.md §check_form — TraitDecl CheckBody is no-op
    #[test]
    fn test_check_form_trait_decl_check_body_noop() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let decl = TraitDecl {
            name: TraitName::from("Show"),
            docstring: None,
            type_params: vec![],
            methods: vec![TraitMethodSig {
                name: Symbol::from("show"),
                docstring: None,
                params: vec![(Symbol::from("x"), TypeExpr::SelfType)],
                ret_type: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("String"))),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let form = TopLevel::TraitDecl(decl);

        // Register first
        let _ = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();

        // CheckBody should be no-op
        let result = tc.check_form(&module, &form, CheckPass::CheckBody, &mut accumulator).unwrap();
        assert!(result.method_resolutions.is_empty());
        assert!(result.expr_types.is_empty());
    }

    // spec: design/typecheck/check-form-api.md §check_form — TraitImpl Register pass
    #[test]
    fn test_check_form_trait_impl_register() {
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // Register a new trait (Eq) then impl it for Int
        let decl = TraitDecl {
            name: TraitName::from("Eq"),
            docstring: None,
            type_params: vec![],
            methods: vec![TraitMethodSig {
                name: Symbol::from("eq"),
                docstring: None,
                params: vec![
                    (Symbol::from("a"), TypeExpr::SelfType),
                    (Symbol::from("b"), TypeExpr::SelfType),
                ],
                ret_type: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Bool"))),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let decl_form = TopLevel::TraitDecl(decl);
        let _ = tc.check_form(&module, &decl_form, CheckPass::Register, &mut accumulator).unwrap();

        // Now impl Eq for Int
        let impl_ = TraitImpl {
            head_con_var: None,
            trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Eq")),
            target: cranelisp_types::TypeExpr::Named(
                cranelisp_types::TypeRef::new(None, TypeName::from("Int")),
            ),
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("eq"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("a"), None), (Symbol::from("b"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("eq-i64"), Span::SYNTHETIC)),
                        args: vec![
                            Expr::var(Symbol::from("a"), Span::SYNTHETIC),
                            Expr::var(Symbol::from("b"), Span::SYNTHETIC),
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
        let impl_form = TopLevel::TraitImpl(impl_);
        let result = tc.check_form(&module, &impl_form, CheckPass::Register, &mut accumulator).unwrap();

        // Impl registration should succeed (no error).
        // default_method_defns contains mangled-name defns for each impl method
        // (e.g., "Eq.eq$Int") that need signature registration and body checking.
        assert!(
            !result.default_method_defns.is_empty(),
            "impl should produce mangled method defns for backend compilation"
        );
        // The mangled defn name should follow the pattern Trait.method$Type
        assert!(
            result.default_method_defns.iter().any(|d| d.name.as_ref().contains("Eq.eq$primitives/Int")),
            "should contain Eq.eq$primitives/Int mangled defn (S102 FQ `$Type` suffix)"
        );
    }

    // spec: design/typecheck/check-form-api.md §check_form — Expr wrapped as __expr
    #[test]
    fn test_check_form_expr_register_and_check() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // Wrap expr as synthetic defn (matching what check() does internally)
        let expr = Expr::IntLit { value: 42, span: span(700, 702), inferred_type: None, };
        let synthetic_defn = Defn {
            name: Symbol::from("__expr"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: expr,
                span: span(700, 702),
            }],
            visibility: Visibility::Public,
            span: span(699, 703),
        };
        let form = TopLevel::Defn(synthetic_defn);

        // Register pass
        let reg_result = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, reg_result);

        assert!(accumulator.defn_type_vars.contains_key(&Symbol::from("__expr")));

        // CheckBody pass
        let body_result = tc.check_form(&module, &form, CheckPass::CheckBody, &mut accumulator).unwrap();

        // expr_types should contain the literal's type
        assert!(
            !body_result.expr_types.is_empty(),
            "CheckBody should produce expr_types for the expression"
        );
    }

    // ---- Category 3: Two-Pass Correctness ----

    // spec: design/typecheck/check-form-api.md §Invariant 1 — forward reference resolves via two-pass
    #[test]
    fn test_check_form_two_pass_mutual_reference() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let program = make_forward_ref_program();

        // Pass 1: Register both defns
        for form in &program {
            let result = tc.check_form(&module, form, CheckPass::Register, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }

        // Both signatures should be registered
        assert!(accumulator.defn_type_vars.contains_key(&Symbol::from("double")));
        assert!(accumulator.defn_type_vars.contains_key(&Symbol::from("add-self")));

        // Pass 2: Check bodies of both
        for form in &program {
            let result = tc.check_form(&module, form, CheckPass::CheckBody, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }

        // Both should have produced expr_types
        assert!(!accumulator.expr_types.is_empty(), "accumulated expr_types should be non-empty");

        // Finalize to get final types
        let _result = tc.finalize_check_result(
            &module, &mut accumulator, &program, ModuleStrategy::Replace,
        ).unwrap();

        // After finalization, all expr_types should be resolved on annotated ASTs.
        for name in ["double", "add-self"] {
            if let Some(ModuleEntry::Def { ast: Some(defn), .. }) =
                tc.symbol_table().get(name)
            {
                let mut _any = false;
                let mut all_resolved = true;
                walk_inferred_types(&defn.body, &mut _any, &mut all_resolved);
                assert!(
                    all_resolved,
                    "unresolved Var in expr_types after finalize for {name}"
                );
            } else {
                panic!("{name} should be registered after finalize");
            }
        }
    }

    // spec: design/typecheck/check-form-api.md §Invariant 1 — CheckBody before Register errors
    #[test]
    fn test_check_form_check_body_before_register_errors() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let defn = make_inc_defn();
        let form = TopLevel::Defn(defn);

        // Try CheckBody without registering first — should error
        let result = tc.check_form(&module, &form, CheckPass::CheckBody, &mut accumulator);
        assert!(
            result.is_err(),
            "CheckBody before Register should produce an error"
        );
    }

    // spec: design/typecheck/check-form-api.md §Invariant 1 — Register populates defn_type_vars
    #[test]
    fn test_check_form_register_populates_defn_type_vars() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let defn = make_inc_defn();
        let form = TopLevel::Defn(defn);

        let _ = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();

        // defn_type_vars should contain the defn's name with type vars
        let (param_types, _ret_ty) = accumulator.defn_type_vars.get(&Symbol::from("inc"))
            .expect("inc should be in defn_type_vars");

        // inc has 1 parameter
        assert_eq!(param_types.len(), 1, "inc has 1 parameter");
    }

    // spec: design/typecheck/check-form-api.md §Invariant 2 — TypeDef before defn using constructors
    #[test]
    fn test_check_form_typedef_before_defn() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // Register TypeDef(Color) first
        let typedef_form = make_color_typedef();
        let result = tc.check_form(&module, &typedef_form, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);

        // Then register Defn(is-red) which uses Color constructors
        let defn_form = TopLevel::Defn(make_is_red_defn());
        let result = tc.check_form(&module, &defn_form, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);

        // Pass 2: check body — should resolve constructor types correctly
        // TypeDef is no-op in CheckBody
        let _ = tc.check_form(&module, &typedef_form, CheckPass::CheckBody, &mut accumulator).unwrap();

        let body_result = tc.check_form(&module, &defn_form, CheckPass::CheckBody, &mut accumulator).unwrap();

        // Should succeed and produce expr_types
        assert!(!body_result.expr_types.is_empty(), "is-red body should have expr_types");
    }

    // spec: design/typecheck/check-form-api.md §Invariant 2 — TraitDecl before TraitImpl
    #[test]
    fn test_check_form_trait_decl_before_impl() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // Register TraitDecl(Eq) first
        let decl = TraitDecl {
            name: TraitName::from("Eq"),
            docstring: None,
            type_params: vec![],
            methods: vec![TraitMethodSig {
                name: Symbol::from("eq"),
                docstring: None,
                params: vec![
                    (Symbol::from("a"), TypeExpr::SelfType),
                    (Symbol::from("b"), TypeExpr::SelfType),
                ],
                ret_type: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Bool"))),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let decl_form = TopLevel::TraitDecl(decl);
        let result = tc.check_form(&module, &decl_form, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);

        // Then register TraitImpl(Eq for Int) — should succeed because decl was registered first
        let impl_ = TraitImpl {
            head_con_var: None,
            trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Eq")),
            target: cranelisp_types::TypeExpr::Named(
                cranelisp_types::TypeRef::new(None, TypeName::from("Int")),
            ),
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("eq"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("a"), None), (Symbol::from("b"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("eq-i64"), Span::SYNTHETIC)),
                        args: vec![
                            Expr::var(Symbol::from("a"), Span::SYNTHETIC),
                            Expr::var(Symbol::from("b"), Span::SYNTHETIC),
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
        let impl_form = TopLevel::TraitImpl(impl_);
        let result = tc.check_form(&module, &impl_form, CheckPass::Register, &mut accumulator);

        // Should succeed — no error
        assert!(result.is_ok(), "TraitImpl after TraitDecl should succeed");
    }

    // ---- Category 4: Multi-Form Programs ----

    // spec: design/typecheck/check-form-api.md §Invariant 3 — shared substitution
    #[test]
    fn test_check_form_multi_defn_shared_substitution() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // Three defns: h uses add-i64 (pins to Int), g calls h, f calls g
        let h = TopLevel::Defn(make_defn(
            "h",
            vec![Symbol::from("x"), Symbol::from("y")],
            vec![None, None],
            Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("add-i64"), span(800, 807))),
                args: vec![
                    Expr::var(Symbol::from("x"), span(808, 809)),
                    Expr::var(Symbol::from("y"), span(810, 811)),
                ],
                span: span(799, 812),
                resolved_call: None,
                inferred_type: None,
            },
            Visibility::Public,
            span(790, 813),
        ));
        let g = TopLevel::Defn(make_defn(
            "g",
            vec![Symbol::from("a")],
            vec![None],
            Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("h"), span(830, 831))),
                args: vec![
                    Expr::var(Symbol::from("a"), span(832, 833)),
                    Expr::var(Symbol::from("a"), span(834, 835)),
                ],
                span: span(829, 836),
                resolved_call: None,
                inferred_type: None,
            },
            Visibility::Public,
            span(820, 837),
        ));
        let f = TopLevel::Defn(make_defn(
            "f",
            vec![Symbol::from("z")],
            vec![None],
            Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("g"), span(860, 861))),
                args: vec![
                    Expr::var(Symbol::from("z"), span(862, 863)),
                ],
                span: span(859, 864),
                resolved_call: None,
                inferred_type: None,
            },
            Visibility::Public,
            span(850, 865),
        ));

        let program = vec![f, g, h];

        // Pass 1: Register all
        for form in &program {
            let result = tc.check_form(&module, form, CheckPass::Register, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }

        // Pass 2: Check all bodies
        for form in &program {
            let result = tc.check_form(&module, form, CheckPass::CheckBody, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }

        // Finalize
        let _result = tc.finalize_check_result(
            &module, &mut accumulator, &program, ModuleStrategy::Replace,
        ).unwrap();

        // All three should be monomorphic Int via shared substitution
        for name in &["f", "g", "h"] {
            if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get(*name) {
                assert!(
                    scheme.type_vars.is_empty(),
                    "{} should be monomorphic (pinned to Int via shared substitution)", name
                );
            } else {
                panic!("{} not found in symbol table", name);
            }
        }
    }

    // spec: design/typecheck/check-form-api.md — accumulator merge grows with each form
    #[test]
    fn test_check_form_accumulator_merge() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let program = make_forward_ref_program();

        // Pass 1: Register all
        for form in &program {
            let result = tc.check_form(&module, form, CheckPass::Register, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }

        // Pass 2: Check bodies and verify accumulator grows
        let et_before_first = accumulator.expr_types.len();
        let form0_result = tc.check_form(&module, &program[0], CheckPass::CheckBody, &mut accumulator).unwrap();
        let form0_et = form0_result.expr_types.len();
        tc.merge_form_result(&module, &mut accumulator, form0_result);
        let et_after_first = accumulator.expr_types.len();

        assert!(
            et_after_first > et_before_first,
            "accumulator should grow after first form's CheckBody"
        );

        let form1_result = tc.check_form(&module, &program[1], CheckPass::CheckBody, &mut accumulator).unwrap();
        let form1_et = form1_result.expr_types.len();
        tc.merge_form_result(&module, &mut accumulator, form1_result);
        let et_after_second = accumulator.expr_types.len();

        assert!(
            et_after_second > et_after_first,
            "accumulator should grow after second form's CheckBody"
        );
        assert_eq!(
            et_after_second,
            et_before_first + form0_et + form1_et,
            "total expr_types should be sum of per-form contributions"
        );
    }

    // spec: design/typecheck/check-form-api.md — finalize resolves pending and produces complete result
    #[test]
    fn test_check_form_finalize_produces_complete_result() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let program = vec![TopLevel::Defn(make_inc_defn())];

        // Full two-pass processing
        for form in &program {
            let result = tc.check_form(&module, form, CheckPass::Register, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }
        for form in &program {
            let result = tc.check_form(&module, form, CheckPass::CheckBody, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }

        let _result = tc.finalize_check_result(
            &module, &mut accumulator, &program, ModuleStrategy::Replace,
        ).unwrap();

        // finalize should produce complete annotated ASTs + method resolutions.
        // Post-slim (Wave 2 step 4): resolutions live on annotated AST nodes;
        // expr_types live on `Expr::inferred_type`.
        let mut any_typed = false;
        let mut all_resolved = true;
        if let Some(ModuleEntry::Def { ast: Some(defn), .. }) = tc.symbol_table().get("inc") {
            walk_inferred_types(&defn.body, &mut any_typed, &mut all_resolved);
        }
        assert!(any_typed, "finalized result should have expr_types");
        assert!(all_resolved, "all expr_types should be fully resolved");
        assert!(
            !tc.annotated_resolutions().is_empty(),
            "finalized result should have method_resolutions"
        );
    }

    // ---- Category 5: Edge Cases ----

    // spec: design/typecheck/check-form-api.md §DefnMulti — multi-sig Register
    #[test]
    fn test_check_form_defn_multi_register() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // Multi-sig defn: two variants
        let multi = TopLevel::Defn(Defn {
            name: Symbol::from("add"),
            docstring: None,
            variants: vec![
                DefnVariant {
                    params: vec![(Symbol::from("x"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add-i64"), span(1010, 1017))),
                        args: vec![
                            Expr::var(Symbol::from("x"), span(1018, 1019)),
                            Expr::IntLit { value: 1, span: span(1020, 1021), inferred_type: None, },
                        ],
                        span: span(1009, 1022),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(1000, 1023),
                },
                DefnVariant {
                    params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add-i64"), span(1040, 1047))),
                        args: vec![
                            Expr::var(Symbol::from("x"), span(1048, 1049)),
                            Expr::var(Symbol::from("y"), span(1050, 1051)),
                        ],
                        span: span(1039, 1052),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(1030, 1053),
                },
            ],
            visibility: Visibility::Public,
            span: span(990, 1054),
        });

        let result = tc.check_form(&module, &multi, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);

        // Internal variant defns should be in defn_type_vars
        assert!(
            accumulator.defn_type_vars.contains_key(&Symbol::from("add__v0")),
            "add__v0 should be in defn_type_vars"
        );
        assert!(
            accumulator.defn_type_vars.contains_key(&Symbol::from("add__v1")),
            "add__v1 should be in defn_type_vars"
        );

        // Base name should be in symbol table as Overloaded placeholder
        if let Some(ModuleEntry::Def { kind, .. }) = tc.symbol_table().get("add") {
            match kind.as_ref() {
                DefKind::Overloaded { .. } => {} // expected
                other => panic!("expected Overloaded placeholder, got {:?}", other),
            }
        } else {
            panic!("add base name not found in symbol table");
        }
    }

    // spec: design/typecheck/check-form-api.md §Constrained polymorphism — detection
    #[test]
    fn test_check_form_constrained_fn_detection() {
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // (defn add [x y] (+ x y)) — constrained by Num
        let defn_form = TopLevel::Defn(make_defn(
            "add",
            vec![Symbol::from("x"), Symbol::from("y")],
            vec![None, None],
            Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("+"), span(1100, 1101))),
                args: vec![
                    Expr::var(Symbol::from("x"), span(1102, 1103)),
                    Expr::var(Symbol::from("y"), span(1104, 1105)),
                ],
                span: span(1099, 1106),
                resolved_call: None,
                inferred_type: None,
            },
            Visibility::Public,
            span(1090, 1107),
        ));

        // Register
        let reg = tc.check_form(&module, &defn_form, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, reg);

        // Check body
        let body = tc.check_form(&module, &defn_form, CheckPass::CheckBody, &mut accumulator).unwrap();

        // Should detect constrained fn
        assert!(
            body.constrained_fn.is_some(),
            "add should be detected as constrained"
        );
        assert_eq!(
            body.constrained_fn.as_ref().unwrap().as_ref(),
            "add",
        );
    }

    // spec: design/typecheck/check-form-api.md — expr_types fully resolved after finalize
    #[test]
    fn test_check_form_expr_types_no_unresolved_vars() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();

        // Use a polymorphic identity function called with Int to test resolution
        let program = vec![
            TopLevel::Defn(make_defn(
                "id",
                vec![Symbol::from("x")],
                vec![None],
                Expr::var(Symbol::from("x"), span(1214, 1215)),
                Visibility::Public,
                span(1200, 1216),
            )),
            TopLevel::Defn(make_defn(
                "use-id",
                vec![Symbol::from("y")],
                vec![None],
                Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("id"), span(1230, 1232))),
                    args: vec![Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add-i64"), span(1234, 1241))),
                        args: vec![
                            Expr::var(Symbol::from("y"), span(1242, 1243)),
                            Expr::IntLit { value: 1, span: span(1244, 1245), inferred_type: None, },
                        ],
                        span: span(1233, 1246),
                        resolved_call: None,
                        inferred_type: None,
                    }],
                    span: span(1229, 1247),
                    resolved_call: None,
                    inferred_type: None,
                },
                Visibility::Public,
                span(1220, 1248),
            )),
        ];

        let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // expr_types in MONOMORPHIC function bodies must be fully resolved. A
        // genuinely POLYMORPHIC body legitimately carries `Type::Var` entries
        // (design/typecheck/inference.md §"Polymorphic Type Variables in
        // expr_types": `(defn id [x] x)` records `x` as `Var(N)` — correct for a
        // Ring-0/1 polymorphic def; monomorphisation produces the concrete
        // specialised copies). Post-FIXME-0344, `id` correctly stays polymorphic
        // here (it is generalized before its `use-id` caller is checked), so its
        // body `x` is a Var — that is the corrected inference, not a regression.
        // Guard resolution only for monomorphic-scheme defns.
        for (_name, entry) in tc.symbol_table().all_symbols() {
            if let ModuleEntry::Def { ast: Some(defn), scheme, .. } = entry {
                if !scheme.type_vars.is_empty() {
                    // Polymorphic def — Var entries in its body are expected.
                    continue;
                }
                let mut _any = false;
                let mut all_resolved = true;
                walk_inferred_types(&defn.body, &mut _any, &mut all_resolved);
                assert!(
                    all_resolved,
                    "unresolved Var in a MONOMORPHIC defn body after check()",
                );
            }
        }
    }

    // spec: design/typecheck/check-form-api.md — warnings accumulated across forms
    #[test]
    fn test_check_form_warnings_accumulated() {
        // This tests that the merge mechanism for warnings works.
        // We verify structurally that warnings from FormCheckResult are collected.
        let mut accumulator = ModuleCheckAccumulator::new();
        assert!(accumulator.warnings.is_empty());

        // Simulate a FormCheckResult with a warning
        let result_with_warning = FormCheckResult {
            method_resolutions: HashMap::new(),
            pattern_ctors: HashMap::new(),
            var_refs: HashMap::new(),
            apply_refs: HashMap::new(),
            expr_types: HashMap::new(),
            constrained_fn: None,
            mono_defns: Vec::new(),
            default_method_defns: Vec::new(),
            multi_sig_defns: Vec::new(),
            warnings: vec![Warning {
                kind: cranelisp_types::WarningKind::Other,
                message: "test warning".to_string(),
                span: Span::SYNTHETIC,
            }],
            call_graph_edges: Vec::new(),
        };

        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        tc.merge_form_result(&module, &mut accumulator, result_with_warning);

        assert_eq!(accumulator.warnings.len(), 1);
        assert_eq!(accumulator.warnings[0].message, "test warning");
    }

    // ---- Negative Tests ----

    // spec: design/typecheck/check-form-api.md — type error propagates from CheckBody
    #[test]
    fn test_check_form_type_error_propagates() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // (defn bad [x] (add-i64 x true)) — type error
        let bad_defn = TopLevel::Defn(make_defn(
            "bad",
            vec![Symbol::from("x")],
            vec![None],
            Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("add-i64"), span(1316, 1323))),
                args: vec![
                    Expr::var(Symbol::from("x"), span(1324, 1325)),
                    Expr::BoolLit { value: true, span: span(1326, 1330), inferred_type: None, },
                ],
                span: span(1315, 1331),
                resolved_call: None,
                inferred_type: None,
            },
            Visibility::Public,
            span(1300, 1332),
        ));

        // Register should succeed
        let reg = tc.check_form(&module, &bad_defn, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, reg);

        // CheckBody should produce an error
        let result = tc.check_form(&module, &bad_defn, CheckPass::CheckBody, &mut accumulator);
        assert!(result.is_err(), "type error in body should propagate as Err");
    }

    // spec: design/typecheck/check-form-api.md — unknown trait in TraitImpl errors
    #[test]
    fn test_check_form_trait_impl_unknown_trait_error() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // TraitImpl referencing undeclared trait
        let impl_ = TraitImpl {
            head_con_var: None,
            trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("NonexistentTrait")),
            target: cranelisp_types::TypeExpr::Named(
                cranelisp_types::TypeRef::new(None, TypeName::from("Int")),
            ),
            type_constraints: vec![],
            methods: vec![],
            span: Span::SYNTHETIC,
        };
        let form = TopLevel::TraitImpl(impl_);
        let result = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator);

        assert!(result.is_err(), "TraitImpl for undeclared trait should error");
    }

    // ---- AST Annotation Tests (Step 1b) ----

    /// Walk an Expr tree and collect all (span, inferred_type) pairs.
    fn collect_inferred_types(expr: &Expr, out: &mut Vec<(Span, Option<Type>)>) {
        out.push((expr.span(), expr.inferred_type().cloned()));
        match expr {
            Expr::Apply { callee, args, .. } => {
                collect_inferred_types(callee, out);
                for arg in args {
                    collect_inferred_types(arg, out);
                }
            }
            Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
                for (_, binding_expr) in bindings {
                    collect_inferred_types(binding_expr, out);
                }
                collect_inferred_types(body, out);
            }
            Expr::If { cond, then_branch, else_branch, .. } => {
                collect_inferred_types(cond, out);
                collect_inferred_types(then_branch, out);
                collect_inferred_types(else_branch, out);
            }
            Expr::Lambda { body, .. } => {
                collect_inferred_types(body, out);
            }
            Expr::Match { scrutinee, arms, .. } => {
                collect_inferred_types(scrutinee, out);
                for arm in arms {
                    collect_inferred_types(&arm.body, out);
                }
            }
            Expr::Annotate { expr: inner, .. } => {
                collect_inferred_types(inner, out);
            }
            Expr::VecLit { elements, .. } => {
                for elem in elements {
                    collect_inferred_types(elem, out);
                }
            }
            Expr::Trace { body, .. } => {
                collect_inferred_types(body, out);
            }
            _ => {}
        }
    }

    /// Find the resolved_call on an Apply node with a given span.
    fn find_resolved_call(expr: &Expr, target_span: Span) -> Option<ResolvedCall> {
        if let Expr::Apply { resolved_call, span, callee, args, .. } = expr {
            if *span == target_span {
                return resolved_call.as_ref().map(|rc| *rc.clone());
            }
            if let Some(rc) = find_resolved_call(callee, target_span) {
                return Some(rc);
            }
            for arg in args {
                if let Some(rc) = find_resolved_call(arg, target_span) {
                    return Some(rc);
                }
            }
        }
        match expr {
            Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
                for (_, binding_expr) in bindings {
                    if let Some(rc) = find_resolved_call(binding_expr, target_span) {
                        return Some(rc);
                    }
                }
                find_resolved_call(body, target_span)
            }
            Expr::If { cond, then_branch, else_branch, .. } => {
                find_resolved_call(cond, target_span)
                    .or_else(|| find_resolved_call(then_branch, target_span))
                    .or_else(|| find_resolved_call(else_branch, target_span))
            }
            Expr::Lambda { body, .. } => find_resolved_call(body, target_span),
            Expr::Match { scrutinee, arms, .. } => {
                find_resolved_call(scrutinee, target_span)
                    .or_else(|| arms.iter().find_map(|arm| find_resolved_call(&arm.body, target_span)))
            }
            Expr::Annotate { expr: inner, .. } | Expr::Trace { body: inner, .. } => {
                find_resolved_call(inner, target_span)
            }
            _ => None,
        }
    }

    // spec: design/arch/ast-annotation-examples.md §3.1 — simple fn resolved_call
    #[test]
    fn test_ast_annotation_simple_fn_resolved_call() {
        // (defn double [x] (add-i64 x x))
        // After typecheck, the add-i64 Apply should have:
        // - inferred_type: Some(Int) (concrete, no Var)
        // - resolved_call: Some(BuiltinFn) (since add-i64 is a primitive)
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();

        let add_span = span(100, 115);
        let program = vec![TopLevel::Defn(make_defn(
            "double",
            vec![Symbol::from("x")],
            vec![None],
            Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("add-i64"), span(101, 108))),
                args: vec![
                    Expr::var(Symbol::from("x"), span(109, 110)),
                    Expr::var(Symbol::from("x"), span(111, 112)),
                ],
                span: add_span,
                resolved_call: None,
                inferred_type: None,
            },
            Visibility::Public,
            span(90, 120),
        ))];

        let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // Retrieve the annotated AST from the symbol table
        let st = tc.symbol_table();
        let entry = st.get("double").expect("double should be in symbol table");
        if let ModuleEntry::Def { ast: Some(defn), .. } = entry {
            let body = &defn.body;

            // All inferred_types should be concrete (no Var)
            let mut types = Vec::new();
            collect_inferred_types(body, &mut types);
            for (s, ty) in &types {
                let ty = ty.as_ref().unwrap_or_else(|| panic!("no inferred_type at span {:?}", s));
                assert!(
                    !ty.contains_var(),
                    "inferred_type at span {:?} contains Var: {:?}", s, ty
                );
            }

            // The Apply node should have inferred_type = Int
            assert_eq!(
                body.inferred_type().unwrap(),
                &Type::Int,
                "Apply (add-i64 x x) should have type Int"
            );

            // Check that resolved_call is present on the Apply (BuiltinFn for add-i64)
            let rc = find_resolved_call(body, add_span);
            assert!(rc.is_some(), "Apply (add-i64 x x) should have resolved_call");
            match rc.unwrap() {
                ResolvedCall::BuiltinFn { name } => {
                    assert_eq!(name.as_ref(), "add-i64");
                }
                other => panic!("expected BuiltinFn, got {:?}", other),
            }
        } else {
            panic!("double should have ast: Some(..), got {:?}", entry);
        }
    }

    // spec: design/arch/ast-annotation-examples.md §3.1 — trait method resolved_call
    #[test]
    fn test_ast_annotation_trait_method_resolved_call() {
        // (defn double [x] (+ x x))  with Num trait
        // (double 5)
        // After typecheck, the + Apply should have resolved_call = TraitMethod
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);
        let ctx = cf_test_ctx();

        let plus_span = span(200, 210);
        let call_span = span(220, 230);
        let program = vec![
            TopLevel::Defn(make_defn(
                "double",
                vec![Symbol::from("x")],
                vec![None],
                Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("+"), span(201, 202))),
                    args: vec![
                        Expr::var(Symbol::from("x"), span(203, 204)),
                        Expr::var(Symbol::from("x"), span(205, 206)),
                    ],
                    span: plus_span,
                    resolved_call: None,
                    inferred_type: None,
                },
                Visibility::Public,
                span(190, 215),
            )),
            // Call site: (double 5)
            TopLevel::Defn(make_defn(
                "__expr",
                vec![],
                vec![],
                Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("double"), span(221, 227))),
                    args: vec![
                        Expr::IntLit { value: 5, span: span(228, 229), inferred_type: None },
                    ],
                    span: call_span,
                    resolved_call: None,
                    inferred_type: None,
                },
                Visibility::Public,
                span(219, 231),
            )),
        ];

        let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // Verify the annotated ASTs carry the trait method resolution.
        // Post-slim (Wave 2 step 4): resolutions live on AST nodes, not on
        // a side map inside CheckResult.
        assert!(
            tc.annotated_resolutions().contains_key(&plus_span),
            "annotated ASTs should carry a resolution for + call"
        );

        // Verify the AST has the same resolution. FIXME 0185: primitive
        // trait-method resolution short-circuits to ResolvedCall::BuiltinFn
        // when the impl_type is a Ring 0 primitive and the (trait, method,
        // impl_type) tuple is in the inline-substitution table. (Num.+ on
        // Int) → BuiltinFn { name: "add-i64" }.
        let st = tc.symbol_table();
        let entry = st.get("double").expect("double should be in symbol table");
        if let ModuleEntry::Def { ast: Some(defn), .. } = entry {
            let body = &defn.body;
            let rc = find_resolved_call(body, plus_span);
            assert!(rc.is_some(), "Apply (+ x x) should have resolved_call on AST node");
            match rc.unwrap() {
                ResolvedCall::BuiltinFn { name } => {
                    assert_eq!(name.as_ref(), "add-i64");
                }
                other => panic!("expected BuiltinFn (primitive trait-method short-circuit per FIXME 0185), got {:?}", other),
            }

            // All types should be concrete
            let mut types = Vec::new();
            collect_inferred_types(body, &mut types);
            for (s, ty) in &types {
                let ty = ty.as_ref().unwrap_or_else(|| panic!("no inferred_type at span {:?}", s));
                assert!(
                    !ty.contains_var(),
                    "inferred_type at span {:?} contains Var: {:?}", s, ty
                );
            }
        } else {
            panic!("double should have ast: Some(..)");
        }
    }

    // spec: design/arch/ast-annotation-examples.md §3.7 — let binding concrete types
    #[test]
    fn test_ast_annotation_let_binding_concrete_type() {
        // (defn f [] (let [x (add-i64 1 2)] x))
        // All inferred_type fields should be concrete (Int, no Var).
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();

        let add_span = span(310, 325);
        let program = vec![TopLevel::Defn(make_defn(
            "f",
            vec![],
            vec![],
            Expr::Let {
                bindings: vec![(
                    Symbol::from("x"),
                    Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add-i64"), span(311, 318))),
                        args: vec![
                            Expr::IntLit { value: 1, span: span(319, 320), inferred_type: None },
                            Expr::IntLit { value: 2, span: span(321, 322), inferred_type: None },
                        ],
                        span: add_span,
                        resolved_call: None,
                        inferred_type: None,
                    },
                )],
                body: Box::new(Expr::var(Symbol::from("x"), span(330, 331))),
                span: span(300, 340),
                inferred_type: None,
            },
            Visibility::Public,
            span(295, 345),
        ))];

        let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        let st = tc.symbol_table();
        let entry = st.get("f").expect("f should be in symbol table");
        if let ModuleEntry::Def { ast: Some(defn), .. } = entry {
            let body = &defn.body;

            // All inferred_types should be concrete
            let mut types = Vec::new();
            collect_inferred_types(body, &mut types);
            for (s, ty) in &types {
                let ty = ty.as_ref().unwrap_or_else(|| panic!("no inferred_type at span {:?}", s));
                assert!(
                    !ty.contains_var(),
                    "inferred_type at span {:?} contains Var: {:?}", s, ty
                );
            }

            // The Let expression should have type Int
            assert_eq!(body.inferred_type().unwrap(), &Type::Int);

            // The binding expression (add-i64 1 2) should have resolved_call
            let rc = find_resolved_call(body, add_span);
            assert!(rc.is_some(), "Apply (add-i64 1 2) should have resolved_call");
        } else {
            panic!("f should have ast: Some(..)");
        }
    }

    // spec: design/arch/ast-annotation-examples.md §3.6 — self-recursive all resolved
    #[test]
    fn test_ast_annotation_self_recursive_all_resolved() {
        // (defn fact [n acc]
        //   (if (eq-i64 n 0)
        //     acc
        //     (fact (sub-i64 n 1) (mul-i64 n acc))))
        // All inferred_types should be concrete Int.
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();

        let eq_span = span(410, 425);
        let sub_span = span(440, 455);
        let mul_span = span(460, 475);
        let fact_span = span(430, 480);
        let program = vec![TopLevel::Defn(make_defn(
            "fact",
            vec![Symbol::from("n"), Symbol::from("acc")],
            vec![None, None],
            Expr::If {
                cond: Box::new(Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("eq-i64"), span(411, 417))),
                    args: vec![
                        Expr::var(Symbol::from("n"), span(418, 419)),
                        Expr::IntLit { value: 0, span: span(420, 421), inferred_type: None },
                    ],
                    span: eq_span,
                    resolved_call: None,
                    inferred_type: None,
                }),
                then_branch: Box::new(Expr::var(Symbol::from("acc"), span(426, 429))),
                else_branch: Box::new(Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("fact"), span(431, 435))),
                    args: vec![
                        Expr::Apply {
                            callee: Box::new(Expr::var(Symbol::from("sub-i64"), span(441, 448))),
                            args: vec![
                                Expr::var(Symbol::from("n"), span(449, 450)),
                                Expr::IntLit { value: 1, span: span(451, 452), inferred_type: None },
                            ],
                            span: sub_span,
                            resolved_call: None,
                            inferred_type: None,
                        },
                        Expr::Apply {
                            callee: Box::new(Expr::var(Symbol::from("mul-i64"), span(461, 468))),
                            args: vec![
                                Expr::var(Symbol::from("n"), span(469, 470)),
                                Expr::var(Symbol::from("acc"), span(471, 474)),
                            ],
                            span: mul_span,
                            resolved_call: None,
                            inferred_type: None,
                        },
                    ],
                    span: fact_span,
                    resolved_call: None,
                    inferred_type: None,
                }),
                span: span(400, 490),
                inferred_type: None,
            },
            Visibility::Public,
            span(395, 495),
        ))];

        let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        let st = tc.symbol_table();
        let entry = st.get("fact").expect("fact should be in symbol table");
        if let ModuleEntry::Def { ast: Some(defn), .. } = entry {
            let body = &defn.body;

            // All inferred_types should be concrete
            let mut types = Vec::new();
            collect_inferred_types(body, &mut types);
            for (s, ty) in &types {
                let ty = ty.as_ref().unwrap_or_else(|| panic!("no inferred_type at span {:?}", s));
                assert!(
                    !ty.contains_var(),
                    "inferred_type at span {:?} contains Var: {:?}", s, ty
                );
            }

            // Builtin calls should have resolved_call
            let eq_rc = find_resolved_call(body, eq_span);
            assert!(eq_rc.is_some(), "eq-i64 Apply should have resolved_call");
            let sub_rc = find_resolved_call(body, sub_span);
            assert!(sub_rc.is_some(), "sub-i64 Apply should have resolved_call");
            let mul_rc = find_resolved_call(body, mul_span);
            assert!(mul_rc.is_some(), "mul-i64 Apply should have resolved_call");

            // The recursive call to fact should NOT have resolved_call (it's a plain user fn)
            let fact_rc = find_resolved_call(body, fact_span);
            assert!(fact_rc.is_none(), "recursive fact call should have resolved_call = None (plain user fn)");
        } else {
            panic!("fact should have ast: Some(..)");
        }
    }

    // spec: design/arch/ast-annotation-examples.md §3.2 — constrained fn with shared subst
    #[test]
    fn test_ast_annotation_constrained_fn_pinned_by_call_site() {
        // (defn add [x y] (+ x y))
        // (defn main [] (add 1 2))
        // Within the same program, the shared substitution pins add's type vars
        // to Int. The AST on ModuleEntry::Def.ast for `add` should have fully
        // concrete types (Int), and the + Apply should have a TraitMethod resolution.
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);

        let plus_span = span(500, 510);
        let program = vec![
            TopLevel::Defn(make_defn(
                "add",
                vec![Symbol::from("x"), Symbol::from("y")],
                vec![None, None],
                Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("+"), span(501, 502))),
                    args: vec![
                        Expr::var(Symbol::from("x"), span(503, 504)),
                        Expr::var(Symbol::from("y"), span(505, 506)),
                    ],
                    span: plus_span,
                    resolved_call: None,
                    inferred_type: None,
                },
                Visibility::Public,
                span(490, 515),
            )),
            TopLevel::Defn(make_defn(
                "main",
                vec![],
                vec![],
                Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("add"), span(521, 524))),
                    args: vec![
                        Expr::IntLit { value: 1, span: span(525, 526), inferred_type: None },
                        Expr::IntLit { value: 2, span: span(527, 528), inferred_type: None },
                    ],
                    span: span(520, 530),
                    resolved_call: None,
                    inferred_type: None,
                },
                Visibility::Public,
                span(518, 531),
            )),
        ];

        let _result = tc.check_program_self(&program).unwrap();

        // The `add` function should have a fully annotated AST on ModuleEntry::Def.ast.
        // The shared substitution pins add's type vars to Int.
        let st = tc.symbol_table();
        let entry = st.get("add").expect("add should be in symbol table");
        if let ModuleEntry::Def { ast: Some(defn), .. } = entry {
            let body = &defn.body;

            // All inferred_types should be concrete (Int, no Var)
            let mut types = Vec::new();
            collect_inferred_types(body, &mut types);
            for (s, ty) in &types {
                let ty = ty.as_ref().unwrap_or_else(|| panic!("no inferred_type at span {:?}", s));
                assert!(
                    !ty.contains_var(),
                    "inferred_type at span {:?} contains Var: {:?}", s, ty
                );
            }

            // The + call should have resolved_call set (resolved via
            // deferred trait call resolution after the call site pins types).
            // FIXME 0185: (Num, +, Int) short-circuits to BuiltinFn so backend
            // emits the primitive inline without paying the impl-body call frame.
            let rc = find_resolved_call(body, plus_span);
            assert!(rc.is_some(), "Apply (+ x x) should have resolved_call on AST node");
            match rc.unwrap() {
                ResolvedCall::BuiltinFn { name } => {
                    assert_eq!(name.as_ref(), "add-i64");
                }
                other => panic!("expected BuiltinFn (primitive trait-method short-circuit per FIXME 0185), got {:?}", other),
            }
        } else {
            panic!("add should have ast: Some(..)");
        }
    }

    // spec: design/arch/ast-annotation-examples.md — qualified cross-module extern
    // A defn body that calls macros/sconcat via qualified name must have
    // resolved_call set on the Apply node. This is the pattern quasiquote
    // ~@ generates inside macro clause bodies.
    //
    // FIXME(/dev frontend): test references `cranelisp_frontend::build_program`
    // which was renamed to `build_form` returning `Vec<ParsedEntry>` per
    // the Wave 3a-β FIXME 0156 pivot. The test wiring needs to land
    // after frontend's parallel /dev work completes.
    #[cfg(any())]
    #[test]
    fn test_ast_annotation_qualified_extern_resolved_call() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();

        let sexps = cranelisp_frontend::parse(
            "(defn concat-nils [] (macros/sconcat macros/SNil macros/SNil))"
        ).unwrap();
        let program = cranelisp_frontend::build_program(&sexps).unwrap();

        let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        let st = tc.symbol_table();
        let entry = st.get("concat-nils").expect("concat-nils should be in symbol table");
        if let ModuleEntry::Def { ast: Some(defn), .. } = entry {
            let body = &defn.body;

            // Find the Apply node (there's only one)
            fn find_any_apply(expr: &Expr) -> Option<&Expr> {
                if matches!(expr, Expr::Apply { .. }) {
                    return Some(expr);
                }
                match expr {
                    Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
                        for (_, e) in bindings { if let Some(a) = find_any_apply(e) { return Some(a); } }
                        find_any_apply(body)
                    }
                    Expr::If { cond, then_branch, else_branch, .. } => {
                        find_any_apply(cond).or_else(|| find_any_apply(then_branch)).or_else(|| find_any_apply(else_branch))
                    }
                    Expr::Lambda { body, .. } | Expr::Annotate { expr: body, .. } | Expr::Trace { body, .. } => find_any_apply(body),
                    _ => None,
                }
            }
            let apply = find_any_apply(body).expect("should have an Apply node");
            if let Expr::Apply { resolved_call, .. } = apply {
                assert!(
                    resolved_call.is_some(),
                    "Apply (macros/sconcat ...) should have resolved_call on AST node"
                );
                match resolved_call.as_deref().unwrap() {
                    ResolvedCall::BuiltinFn { name } => {
                        assert_eq!(name.as_ref(), "sconcat");
                    }
                    other => panic!("expected BuiltinFn for macros/sconcat, got {:?}", other),
                }
            }

            let ty = body.inferred_type().expect("Apply should have inferred_type");
            assert!(!ty.contains_var(), "inferred_type should be concrete, got {:?}", ty);
        } else {
            panic!("concat-nils should have ast: Some(..)");
        }
    }

    // =========================================================================
    // AST annotation tests — trait impl methods
    // =========================================================================

    // SIGSEGV isolation: trait impl method using trait dispatch in body
    // must NOT be marked as constrained fn after body check pass.
    //
    // Reproduces the Sprint 55 regression where check_form_body_single_defn
    // re-infers the impl method body with fresh type vars, finds trait
    // constraints (from + operator), and marks the method as constrained_fn.
    // Codegen then skips it (constrained fns are deferred for monomorphisation),
    // leaving a null GOT slot -> SIGSEGV on dispatch.
    #[test]
    fn test_impl_method_not_marked_constrained_after_body_check() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        register_num_trait_inline(&mut tc);

        let mut accumulator = ModuleCheckAccumulator::new();

        // Register Double trait: (deftrait Double (double [self] self))
        let double_decl = TraitDecl {
            name: TraitName::from("Double"),
            docstring: None,
            type_params: vec![],
            methods: vec![TraitMethodSig {
                name: Symbol::from("double"),
                docstring: None,
                params: vec![(Symbol::from("x"), TypeExpr::SelfType)],
                ret_type: TypeExpr::SelfType,
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let decl_form = TopLevel::TraitDecl(double_decl);
        let result = tc.check_form(&module, &decl_form, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);

        // Impl Double for Int: (defn double [x] (+ x x))
        let impl_ = TraitImpl {
            head_con_var: None,
            trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Double")),
            target: cranelisp_types::TypeExpr::Named(
                cranelisp_types::TypeRef::new(None, TypeName::from("Int")),
            ),
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("double"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("x"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("+"), span(100, 101))),
                        args: vec![
                            Expr::var(Symbol::from("x"), span(102, 103)),
                            Expr::var(Symbol::from("x"), span(104, 105)),
                        ],
                        span: span(99, 106),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(90, 110),
                }],
                visibility: Visibility::Public,
                span: span(90, 110),
            }],
            span: span(80, 120),
        };
        let impl_form = TopLevel::TraitImpl(impl_);
        let result = tc.check_form(&module, &impl_form, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);

        // The register pass should produce the mangled defn (S102 FQ `$Type`
        // suffix: `primitives/Int`, lock-step with the dispatch site).
        let mangled_name = Symbol::from("Double.double$primitives/Int");
        assert!(
            !accumulator.default_method_defns.is_empty(),
            "register should produce default_method_defns"
        );
        assert!(
            accumulator.default_method_defns.iter().any(|d| d.name == mangled_name),
            "should contain Double.double$primitives/Int"
        );

        // Step: Run register for the mangled defn (like register_default_methods does)
        let defaults = std::mem::take(&mut accumulator.default_method_defns);
        for defn in &defaults {
            let form = TopLevel::Defn(defn.clone());
            let result = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }
        accumulator.default_method_defns = defaults;

        // Step: Run CheckBody for the mangled defn (like finalize_module does)
        let defaults_for_body = accumulator.default_method_defns.clone();
        for defn in &defaults_for_body {
            let form = TopLevel::Defn(defn.clone());
            let result = tc.check_form(&module, &form, CheckPass::CheckBody, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }

        // KEY ASSERTION: The mangled method must NOT be constrained.
        // If it is, codegen will skip it -> null GOT slot -> SIGSEGV.
        let table = tc.symbol_table();
        if let Some(ModuleEntry::Def { kind, scheme, .. }) = table.get(mangled_name.as_ref()) {
            match kind.as_ref() {
                DefKind::UserFn { fn_state } => {
                    assert!(
                        !matches!(fn_state, UserFnState::Constrained(_)),
                        "BUG: trait impl method '{}' was marked as constrained fn \
                        (scheme: {}). This causes codegen to skip it, leaving a null \
                        GOT slot -> SIGSEGV on dispatch.",
                        mangled_name, scheme.ty
                    );
                }
                other => panic!("expected UserFn, got {:?}", other),
            }

            // Also verify the scheme is concrete
            assert!(
                scheme.type_vars.is_empty() && scheme.constraints.is_empty(),
                "impl method scheme should be concrete (no vars/constraints), got: {:?}",
                scheme,
            );
        } else {
            panic!("mangled method '{}' not found in symbol table", mangled_name);
        }

        // Verify AST annotations are concrete (no Var(N))
        if let Some(ModuleEntry::Def { ast: Some(annotated), .. }) = table.get(mangled_name.as_ref()) {
            let body = &annotated.body;
            if let Some(ty) = body.inferred_type() {
                assert!(
                    !ty.contains_var(),
                    "impl method body inferred_type should be concrete, got: {:?}",
                    ty
                );
            }
        }
    }

    // ---- Sprint 56 Wave 0 §9.3 — mangled multi-sig variant ast pre-materialisation ----

    /// Build a two-variant multi-sig `add` defn:
    ///   (defn add
    ///     ([:Int a :Int b]   (add-i64 a b))
    ///     ([:Float a :Float b] (add-f64 a b)))
    fn make_add_multi_sig_int_float() -> Defn {
        make_multi_defn(
            "add",
            vec![
                DefnVariant {
                    params: vec![(Symbol::from("a"), Some(TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int"))))), (Symbol::from("b"), Some(TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int")))))],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add-i64"), span(510, 517))),
                        args: vec![
                            Expr::var(Symbol::from("a"), span(518, 519)),
                            Expr::var(Symbol::from("b"), span(520, 521)),
                        ],
                        span: span(509, 522),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(505, 523),
                },
                DefnVariant {
                    params: vec![(Symbol::from("a"), Some(TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Float"))))), (Symbol::from("b"), Some(TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Float")))))],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add-f64"), span(530, 537))),
                        args: vec![
                            Expr::var(Symbol::from("a"), span(538, 539)),
                            Expr::var(Symbol::from("b"), span(540, 541)),
                        ],
                        span: span(529, 542),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: span(525, 543),
                },
            ],
            span(500, 544),
        )
    }

    // spec: design/typecheck/ast-annotation.md §9.3 — mangled multi-sig variant ast pre-materialisation
    #[test]
    fn wave0_mangled_variant_carries_ast() {
        let mut tc = tc_with_prims();
        let program = vec![TopLevel::Defn(make_add_multi_sig_int_float())];
        tc.check(&program, &test_ctx(), ModuleStrategy::Additive).unwrap();

        let st = tc.symbol_table();

        // add$Int+Int: Def entry with ast: Some(DefnVariant). Per S69 Submission 35,
        // `ast` is now `Option<DefnVariant>` (the single meaningful payload), so the
        // name lives on the symbol-table key and "single variant" is enforced by the
        // type itself — no `.variants` to assert against.
        match st.get("add$Int+Int") {
            Some(ModuleEntry::Def { ast: Some(_defn), kind, .. }) => {
                assert!(
                    matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }
                    ),
                    "mangled variant kind should be UserFn(Concrete), got {:?}",
                    kind
                );
            }
            other => panic!("add$Int+Int should be Def {{ ast: Some(..), .. }}, got {:?}", other),
        }

        // add$Float+Float: same shape.
        match st.get("add$Float+Float") {
            Some(ModuleEntry::Def { ast: Some(_defn), kind, .. }) => {
                assert!(matches!(
                    kind.as_ref(),
                    DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }
                ));
            }
            other => panic!("add$Float+Float should be Def {{ ast: Some(..), .. }}, got {:?}", other),
        }
    }

    // spec: design/typecheck/ast-annotation.md §9.3 — annotations fully substituted on mangled variant
    #[test]
    fn wave0_mangled_variant_ast_is_annotated() {
        let mut tc = tc_with_prims();
        let program = vec![TopLevel::Defn(make_add_multi_sig_int_float())];
        tc.check(&program, &test_ctx(), ModuleStrategy::Additive).unwrap();

        let st = tc.symbol_table();
        let entry = st.get("add$Int+Int").expect("add$Int+Int must be registered");
        let defn = match entry {
            ModuleEntry::Def { ast: Some(d), .. } => d,
            other => panic!("expected ast: Some(..), got {:?}", other),
        };

        // Walk every Expr node in the body; every inferred_type must be concrete
        // (no Type::Var leaks after final substitution).
        let body = &defn.body;
        let mut types = Vec::new();
        collect_inferred_types(body, &mut types);
        assert!(!types.is_empty(), "body should have at least one Expr node");
        for (s, ty) in &types {
            let ty = ty
                .as_ref()
                .unwrap_or_else(|| panic!("no inferred_type at span {:?}", s));
            assert!(
                !ty.contains_var(),
                "inferred_type at span {:?} contains Type::Var: {:?}",
                s,
                ty
            );
        }

        // The body root (the add-i64 Apply) should be concretely typed as Int.
        assert_eq!(
            body.inferred_type(),
            Some(&Type::Int),
            "add$Int+Int body should be Int"
        );
    }

    // spec: design/typecheck/ast-annotation.md §9.3 — overloaded base has no ast
    #[test]
    fn wave0_overloaded_base_has_no_ast() {
        let mut tc = tc_with_prims();
        let program = vec![TopLevel::Defn(make_add_multi_sig_int_float())];
        tc.check(&program, &test_ctx(), ModuleStrategy::Additive).unwrap();

        let st = tc.symbol_table();
        match st.get("add") {
            Some(ModuleEntry::Def { ast, kind, .. }) => {
                assert!(
                    ast.is_none(),
                    "overloaded base 'add' must have ast: None (bodies live on mangled variants)"
                );
                assert!(
                    matches!(kind.as_ref(), DefKind::Overloaded { variants } if variants.len() == 2),
                    "overloaded base kind should be Overloaded with 2 variants, got {:?}",
                    kind
                );
            }
            other => panic!("'add' base should be Def {{ Overloaded, ast: None }}, got {:?}", other),
        }
    }

    // --- §0.8 macro-clause same-module-helper diagnostic (FIXME 0262) ---

    #[test]
    fn macro_clause_defn_name_is_recognised() {
        assert!(is_macro_clause_defn_name("__macro_m_clause_0"));
        assert!(is_macro_clause_defn_name("__macro_make-def-name_clause_3"));
        // Not a macro-clause shape: ordinary user defns, REPL exprs, trait impls.
        assert!(!is_macro_clause_defn_name("helper"));
        assert!(!is_macro_clause_defn_name("__expr"));
        assert!(!is_macro_clause_defn_name("Double.double$Int"));
        assert!(!is_macro_clause_defn_name("clause_only"));
    }

    #[test]
    fn undefined_var_in_macro_clause_gets_dependency_diagnostic() {
        // §0.8: a same-module non-macro reference inside a macro clause body
        // must surface a clear diagnostic naming the symbol AND the
        // dependency-module rule — not the bare "undefined variable".
        let err = CranelispError::TypeError {
            message: "undefined variable: helper".to_string(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        };
        let enriched = enrich_macro_clause_resolution_error("__macro_m_clause_0", err);
        let CranelispError::TypeError { message, .. } = enriched else {
            panic!("expected TypeError");
        };
        // Offending symbol name is preserved (callers substring-match on it).
        assert!(message.contains("helper"), "message: {message}");
        // The §0.8 dependency-module direction is present.
        assert!(
            message.contains("same-module") || message.contains("dependency"),
            "message: {message}"
        );
    }

    #[test]
    fn undefined_var_outside_macro_clause_is_unchanged() {
        // A plain user defn keeps the generic message — no false enrichment.
        let original = "undefined variable: helper".to_string();
        let err = CranelispError::TypeError {
            message: original.clone(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        };
        let passed = enrich_macro_clause_resolution_error("f", err);
        let CranelispError::TypeError { message, .. } = passed else {
            panic!("expected TypeError");
        };
        assert_eq!(message, original);
    }

    #[test]
    fn non_undefined_var_error_in_macro_clause_is_unchanged() {
        // Only "undefined variable" errors are rewritten; other type errors
        // (e.g. unification mismatch) pass through untouched even inside a
        // macro-clause defn.
        let original = "type mismatch: Int vs String".to_string();
        let err = CranelispError::TypeError {
            message: original.clone(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        };
        let passed = enrich_macro_clause_resolution_error("__macro_m_clause_0", err);
        let CranelispError::TypeError { message, .. } = passed else {
            panic!("expected TypeError");
        };
        assert_eq!(message, original);
    }

    // =========================================================================
    // ModuleEntry::Def AST-annotation shape + CheckResult slim shape
    // (harvested from tests/legacy/wave2_g6.rs per FIXME 0117, typecheck half).
    //
    // wave2_g6 was a Layer-3 integration file observing the Sprint 57 Wave 2
    // (G6) write paths via the Rust API. Two of its observations are
    // typecheck-internal contracts and are harvested here; the backend half
    // (the `Code { ptr }` write onto `ModuleEntry::Def.code` via the
    // `CodeFinalizer` trait, and the `/clif`/`/source` introspection +
    // cross-module-call read-path guards) stays for the W-C backend sweep.
    //
    // 1. Phase-1 AST annotation: after `check`, a user `(defn ...)` is
    //    registered as `ModuleEntry::Def` carrying `ast: Some(_)` (the
    //    annotated `Defn`). This is the typecheck-owned half of the legacy
    //    `g6_code_on_entry_after_compile` assertion — the `code.is_some()`
    //    half is the backend write path (W-C).
    // 2. `CheckResult` slim shape: the boundary type carries exactly
    //    `{ warnings, display }` after Wave 2's slim-down — the legacy
    //    `g6_check_result_slim_shape` structural guard.
    // =========================================================================

    // spec: design/typecheck/ast-annotation.md §10.2 — Phase-1 annotation writes
    // the annotated `Defn` onto `ModuleEntry::Def.ast` for a user function.
    #[test]
    fn def_entry_carries_annotated_ast_after_check() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();
        let sexps = cranelisp_frontend::parse("(defn trivial [] 42)").unwrap();
        let program = cranelisp_frontend::build_forms(&sexps).unwrap();

        tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        let st = tc.symbol_table();
        let entry = st.get("trivial").expect("'trivial' must be registered after check");
        match entry {
            ModuleEntry::Def { ast, .. } => {
                assert!(
                    ast.is_some(),
                    "ModuleEntry::Def.ast must be Some(_) after Phase-1 AST annotation"
                );
                // The annotated body must carry a resolved (var-free) type.
                let defn = ast.as_ref().unwrap();
                let body = &defn.body;
                let ty = body.inferred_type().expect("annotated body must carry inferred_type");
                assert!(!ty.contains_var(), "inferred_type must be concrete, got {ty:?}");
            }
            other => panic!("expected Def entry for 'trivial', got {other:?}"),
        }
    }

    // spec: spec/07-traits.md §7.8 + design/arch/principles/20-model-invariants-by-representation.md
    //   — deferred GOT-slot allocation: the determination-point redefinition
    //   slot-reuse seam (S83, FIXME 0356/0357; amends Decision 0035).
    //
    // The named non-mechanical seam. Pass-1 registers a user fn slot-less
    // (`UserFnState::NotDetermined`); the slot is allocated at the Pass-2
    // determination point. On REPL redefinition of a concrete fn over a prior
    // concrete entry, the determination arm MUST REUSE the prior slot
    // (`existing_callable_slot` carry-forward) — reallocating would orphan the
    // live GOT pointer the prior `Code::Jit` installed (a use-after-free). This
    // pins all three transitions:
    //   - concrete → concrete redef: REUSE slot N (the UAF guard).
    //   - concrete → constrained redef: new entry is slot-less `Constrained`
    //     (old slot dropped; a constrained template is never call-resolved, so
    //     no live pointer is orphaned).
    //   - constrained → concrete redef: allocate FRESH (nothing to reuse).
    #[test]
    fn redefine_concrete_fn_reuses_existing_got_slot() {
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);
        let ctx = cf_test_ctx();

        // Helper: read a name's concrete callable slot via the single
        // read-through accessor (None for NotDetermined / Constrained).
        let slot_of = |tc: &TestFixture, name: &str| -> Option<usize> {
            tc.symbol_table().get(name).and_then(|e| e.callable_got_slot())
        };
        // Helper: is the entry a slot-less constrained template?
        let is_constrained = |tc: &TestFixture, name: &str| -> bool {
            matches!(
                tc.symbol_table().get(name),
                Some(ModuleEntry::Def { kind, .. })
                    if matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state: UserFnState::Constrained(_) }
                    )
            )
        };

        // (defn idf [:Int x] x) — unconstrained AND fully concrete → Concrete,
        // slot allocated at the determination point. The `:Int` annotation is
        // load-bearing: an UNANNOTATED `(defn idf [x] x)` is `∀a. a→a` —
        // unconstrained but NON-concrete (a residual `Type::Var`), which the
        // S84 slot gate (FIXME 0374, slot ⟺ concrete) routes to the slot-less
        // `Polymorphic` arm, NOT `Concrete`. This test pins the concrete→concrete
        // redef slot-reuse, so the example must be genuinely concrete.
        let idf = |s: u32| TopLevel::Defn(make_defn(
            "idf",
            vec![Symbol::from("x")],
            vec![Some(cranelisp_types::TypeExpr::Named(
                cranelisp_types::TypeRef::new(None, TypeName::from("Int")),
            ))],
            Expr::var(Symbol::from("x"), span(s, s + 1)),
            Visibility::Public,
            span(s, s + 2),
        ));
        tc.check(&[idf(10)], &ctx, ModuleStrategy::Additive).unwrap();
        let slot_n = slot_of(&tc, "idf").expect("concrete idf must carry a slot");

        // Redefine idf with the SAME (concrete) shape — the determination point
        // must REUSE slot N, not allocate N+1.
        tc.check(&[idf(20)], &ctx, ModuleStrategy::Additive).unwrap();
        let slot_after = slot_of(&tc, "idf").expect("redefined concrete idf must carry a slot");
        assert_eq!(
            slot_after, slot_n,
            "concrete→concrete redefinition MUST reuse the existing GOT slot \
             (use-after-free guard); got {slot_after} expected {slot_n}",
        );

        // (defn cadd [x y] (+ x y)) — `+` is the Num trait method, so the
        // inferred scheme carries a Num constraint → Constrained template,
        // slot-less by construction.
        let cadd = || TopLevel::Defn(make_defn(
            "cadd",
            vec![Symbol::from("x"), Symbol::from("y")],
            vec![None, None],
            Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("+"), span(31, 32))),
                args: vec![
                    Expr::var(Symbol::from("x"), span(33, 34)),
                    Expr::var(Symbol::from("y"), span(35, 36)),
                ],
                span: span(30, 37),
                resolved_call: None,
                inferred_type: None,
            },
            Visibility::Public,
            span(29, 38),
        ));
        tc.check(&[cadd()], &ctx, ModuleStrategy::Additive).unwrap();
        assert!(
            is_constrained(&tc, "cadd"),
            "cadd '(+ x y)' must be a constrained template",
        );
        assert_eq!(
            slot_of(&tc, "cadd"),
            None,
            "a constrained template carries NO slot (slot-less by construction)",
        );

        // constrained → concrete redef: redefine cadd as
        // `(defn cadd [:Int x :Int y] x)` (no constraint, fully concrete).
        // Nothing to reuse (the template was slot-less), so a FRESH slot is
        // allocated and the entry becomes Concrete. The `:Int` annotations are
        // load-bearing under the S84 slot gate (slot ⟺ concrete, FIXME 0374):
        // an unannotated `(defn cadd [x y] x)` is `∀a b. (Fn [a b] a)` —
        // unconstrained but NON-concrete → slot-less `Polymorphic`, not
        // `Concrete`.
        let int_ann = || Some(cranelisp_types::TypeExpr::Named(
            cranelisp_types::TypeRef::new(None, TypeName::from("Int")),
        ));
        let cadd_concrete = TopLevel::Defn(make_defn(
            "cadd",
            vec![Symbol::from("x"), Symbol::from("y")],
            vec![int_ann(), int_ann()],
            Expr::var(Symbol::from("x"), span(40, 41)),
            Visibility::Public,
            span(39, 42),
        ));
        tc.check(&[cadd_concrete], &ctx, ModuleStrategy::Additive).unwrap();
        assert!(
            !is_constrained(&tc, "cadd"),
            "constrained→concrete redef must yield a concrete (callable) entry",
        );
        let cadd_concrete_slot =
            slot_of(&tc, "cadd").expect("constrained→concrete redef must allocate a fresh slot");

        // concrete → constrained redef: redefine cadd back to the constrained
        // shape. The old slot is dropped; the new entry is slot-less Constrained
        // (no phantom slot survives — the constrained template is never
        // call-resolved, so dropping the slot orphans no live pointer).
        tc.check(&[cadd()], &ctx, ModuleStrategy::Additive).unwrap();
        assert!(
            is_constrained(&tc, "cadd"),
            "concrete→constrained redef must yield a constrained template",
        );
        assert_eq!(
            slot_of(&tc, "cadd"),
            None,
            "concrete→constrained redef must be slot-less (no phantom slot survives)",
        );
        // Sanity: the dropped concrete slot was a real allocated index.
        let _ = cadd_concrete_slot;
    }

    // spec: spec/03-types.md §3.10 — Rank-1 HM: a GOT slot is the value-
    //   capability of a CONCRETE callable (slot ⟺ `is_concrete()`). A generic-
    //   unconstrained def (`id : ∀a. a→a`) is NON-concrete → slot-less
    //   `UserFnState::Polymorphic`, NOT `Concrete` with a slot.
    //
    // FIXME(/typecheck 0374): the structural slot gate — test seam (a). Pins
    //   that the unannotated identity def lands in the slot-less `Polymorphic`
    //   arm (`callable_got_slot()` → `None`) so a residual `Type::Var` can never
    //   reach `classify(Type::Var)` as a callable address. Only its concrete
    //   mono instances are slotted (test seam (b) below).
    #[test]
    fn generic_unconstrained_def_is_slotless() {
        let mut tc = tc_with_prims();
        // (defn id [x] x) — unconstrained but NON-concrete (∀a. a→a).
        let sexps = cranelisp_frontend::parse("(defn id [x] x)").expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
        tc.check_program_self(&program).unwrap();

        match tc.symbol_table().get("id") {
            Some(ModuleEntry::Def { kind, scheme, .. }) => {
                assert!(
                    matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state: UserFnState::Polymorphic(_) }
                    ),
                    "a generic-unconstrained def must be slot-less Polymorphic, \
                     got {kind:?}",
                );
                assert!(
                    !scheme.ty.is_concrete(),
                    "id's scheme must be non-concrete (carries a Type::Var)",
                );
            }
            other => panic!("id not a Def: {other:?}"),
        }
        assert_eq!(
            tc.symbol_table().get("id").and_then(|e| e.callable_got_slot()),
            None,
            "a Polymorphic def carries NO callable slot (slot ⟺ concrete)",
        );
    }

    // spec: spec/03-types.md §3.10 — the concrete monomorphised instance of a
    //   generic def DOES carry a slot and IS concrete (the slot ⟺ concrete
    //   invariant's positive half).
    //
    // FIXME(/typecheck 0374): test seam (a)/(b) — a generic def used at a
    //   concrete type mints a `Concrete { got_slot: Some(_) }` mono instance
    //   whose stored scheme `is_concrete()`. The generic template stays
    //   slot-less `Polymorphic`; only the instance is callable.
    #[test]
    fn concrete_instance_of_generic_def_is_slotted() {
        let mut tc = tc_with_prims();
        // `id` used at Int through `neg` (an annotated concrete helper). The
        // call `(id (neg 5))` instantiates `id` at Int → `id$Int` mono.
        let src = "\
            (defn id [x] x)\n\
            (defn neg [:primitives/Int x] :primitives/Int (sub-i64 0 x))\n\
            (defn use-id [] :primitives/Int (id (neg 5)))";
        let sexps = cranelisp_frontend::parse(src).expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
        tc.check_program_self(&program).unwrap();

        // The generic template stays slot-less Polymorphic.
        assert!(
            matches!(
                tc.symbol_table().get("id"),
                Some(ModuleEntry::Def { kind, .. })
                    if matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state: UserFnState::Polymorphic(_) }
                    )
            ),
            "the generic `id` template must stay slot-less Polymorphic",
        );

        // The mono instance `id$Int` is Concrete, slotted, and concrete-typed
        // (home-qualified `test/id$Int`, FIXME 0519).
        match tc.symbol_table().get("test/id$Int") {
            Some(ModuleEntry::Def { kind, scheme, .. }) => {
                let slot = match kind.as_ref() {
                    DefKind::UserFn { fn_state: UserFnState::Concrete { got_slot, .. } } => {
                        Some(*got_slot)
                    }
                    other => panic!("id$Int must be Concrete, got {other:?}"),
                };
                assert!(slot.is_some(), "id$Int must carry a GOT slot");
                assert!(
                    scheme.ty.is_concrete(),
                    "id$Int's stored type must be fully concrete, got {:?}",
                    scheme.ty,
                );
            }
            other => panic!("id$Int mono instance not registered: {other:?}"),
        }
    }

    // spec: spec/05-definitions.md §5.1.2 — FIXME 0432 Face A (S91 Wave-7):
    //   a multi-clause annotated `defn` whose body contains an in-body self-call
    //   must carry that self-call's mangled `SigDispatch` resolution ON the AST
    //   node of the MANGLED variant entry. The seam: `register_mangled_variants`
    //   removes the internal `{name}__v{i}` keys and reinserts the variant
    //   entries under their mangled names; the finalize re-annotation block must
    //   re-annotate under the MANGLED keys (not the stale internal keys) so the
    //   self-call's `SigDispatch` (written by `resolve_pending_overloads`) lands
    //   on the body. Before the fix the lookup missed and the body's self-call
    //   node carried NO `resolved_call` — the backend then fell back to the
    //   undefined bare name `h` (`undefined function: h` at codegen).
    //
    // This is the unit-tier guard for the e2e
    // `tests/spec_05_definitions::defn_multi_clause_annotated_self_call_minimal_repro`.
    #[test]
    fn multi_sig_self_call_carries_mangled_sig_dispatch() {
        let mut tc = tc_with_prims();
        // `h` variant 1 = `[:Int n] (h n n)`; the in-body 2-arg self-call must
        // dispatch to variant 2 (`h$Int+Int`). The mangled entry for variant 1
        // is `h$Int`; its body Apply node must carry SigDispatch{h$Int+Int}.
        let src = "\
            (defn h \
                ([:primitives/Int n] (h n n)) \
                ([:primitives/Int a :primitives/Int b] (add-i64 a b)))";
        let sexps = cranelisp_frontend::parse(src).expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
        tc.check_program_self(&program).unwrap();

        // Walk a body Expr tree collecting every `SigDispatch` mangled name.
        fn collect_sig_dispatch(expr: &Expr, out: &mut Vec<String>) {
            let rc = match expr {
                Expr::Apply { callee, args, resolved_call, .. } => {
                    collect_sig_dispatch(callee, out);
                    for a in args {
                        collect_sig_dispatch(a, out);
                    }
                    resolved_call.as_deref()
                }
                Expr::Var { resolved_call, .. } => resolved_call.as_deref(),
                Expr::If { cond, then_branch, else_branch, .. } => {
                    collect_sig_dispatch(cond, out);
                    collect_sig_dispatch(then_branch, out);
                    collect_sig_dispatch(else_branch, out);
                    None
                }
                Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
                    for (_, b) in bindings {
                        collect_sig_dispatch(b, out);
                    }
                    collect_sig_dispatch(body, out);
                    None
                }
                Expr::Lambda { body, .. }
                | Expr::Annotate { expr: body, .. }
                | Expr::Trace { body, .. } => {
                    collect_sig_dispatch(body, out);
                    None
                }
                _ => None,
            };
            if let Some(ResolvedCall::SigDispatch { mangled_name }) = rc {
                out.push(mangled_name.as_ref().to_string());
            }
        }

        // The variant-1 entry lives under the MANGLED key `h$Int` (the internal
        // `h__v0` key was removed by `register_mangled_variants`).
        let st = tc.symbol_table();
        let entry = st
            .get("h$Int")
            .expect("mangled variant `h$Int` must be registered");
        let body = match entry {
            ModuleEntry::Def { ast: Some(variant), .. } => &variant.body,
            other => panic!("h$Int must carry an annotated ast: {other:?}"),
        };

        let mut dispatches = Vec::new();
        collect_sig_dispatch(body, &mut dispatches);
        assert!(
            dispatches.iter().any(|d| d == "h$Int+Int"),
            "the in-body self-call `(h n n)` must carry SigDispatch{{h$Int+Int}} \
             on the mangled variant body (not a bare unresolved name); \
             found dispatches: {dispatches:?}",
        );
    }

    // spec: spec/12-runtime.md §12.1 — no unresolved type variable reaches code
    //   generation: a polymorphic fn passed THROUGH a HOF whose result is a
    //   generic ADT carrying a `Type::Var` field is monomorphised to a concrete
    //   instance (the `(Box a)`-field-through-HOF gap).
    //
    // FIXME(/typecheck 0374): test seam (b) — the unit counterpart of the
    //   Wave-0 e2e `mono_tier2_generic_adt_field_through_hof_no_crash`. `mk`
    //   (returns `(Box a)`) is passed as a fn-value through the HOF `thru`. The
    //   `(Box a)` field must be pinned to `(Box Int)` at the reachable instance:
    //   the worklist mints `mk$Int` (concrete params, concrete `(Box Int)`
    //   result), so its body's `Box` field classifies cleanly — no residual
    //   `Type::Var` at the RC boundary.
    #[test]
    fn box_field_through_hof_monomorphises_concrete() {
        let mut tc = tc_with_prims();
        let src = "\
            (deftype (Box a) (Box [:a val]))\n\
            (defn mk [x] (Box x))\n\
            (defn thru [g x] (g x))\n\
            (defn get [b] (match b [(Box v) v]))\n\
            (defn use-box [] :primitives/Int (get (thru mk (sub-i64 0 5))))";
        let sexps = cranelisp_frontend::parse(src).expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
        tc.check_program_self(&program).unwrap();

        // The generic `mk` template is slot-less Polymorphic.
        assert!(
            matches!(
                tc.symbol_table().get("mk"),
                Some(ModuleEntry::Def { kind, .. })
                    if matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state: UserFnState::Polymorphic(_) }
                    )
            ),
            "the generic `mk` template must be slot-less Polymorphic",
        );

        // The fn-value-argument worklist minted `mk$Int` (mangled by `mk`'s
        // own concrete param type `Int`) — a concrete, slotted mono instance
        // with a fully-concrete `(Fn [Int] (Box Int))` stored type (no residual
        // `Type::Var` ADT field).
        match tc.symbol_table().get("test/mk$Int") {
            Some(ModuleEntry::Def { kind, scheme, .. }) => {
                assert!(
                    matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }
                    ),
                    "mk$Int must be a Concrete (slotted) mono instance, got {kind:?}",
                );
                assert!(
                    scheme.ty.is_concrete(),
                    "mk$Int's stored type must be fully concrete (no Type::Var \
                     ADT field), got {:?}",
                    scheme.ty,
                );
                // The result type must be a concrete `(Box Int)`, not `(Box a)`.
                if let Type::Fn(_, ret) = &scheme.ty {
                    assert!(
                        matches!(
                            ret.as_ref(),
                            Type::ADT(name, args)
                                if name.name.as_ref() == "Box"
                                    && args.len() == 1
                                    && args[0] == Type::Int
                        ),
                        "mk$Int's result must be (Box Int), got {ret:?}",
                    );
                }
            }
            other => panic!("mk$Int mono instance not registered: {other:?}"),
        }
    }

    // spec: spec/05-definitions.md §5.1.2 — multi-clause `defn` self-call
    //   (S112 leg a back-flow; UW-7 unit counterpart, was FIXME 0432 Face B).
    //   A multi-signature `defn` is inference-equivalent to its clauses written
    //   as separate mutually-recursive functions, so an UNannotated `sum-to`
    //   whose 1-arg clause delegates `(sum-to n 0)` to the 2-arg clause — whose
    //   own `add-i64`/`sub-i64`/`eq-i64` pin it to `(Fn [Int Int] Int)` — now
    //   INFERS: the delegation pins `n : Int`. It MUST type-check cleanly (no
    //   `ambiguous` error, no monomorphiser panic — the residual `Var` the old
    //   drifted §5.1.2 left is dissolved by the back-flow).
    #[test]
    fn multi_clause_defn_self_call_backflow_infers_not_ambiguous() {
        let mut tc = tc_with_prims();
        // The 0642/0432 shape verbatim: 1-arg clause delegates to the 2-arg
        // clause, which self-recurses; all arithmetic qualified/concrete.
        let src = "\
            (defn sum-to ([n] (sum-to n 0))\n\
                         ([n acc] (if (primitives/eq-i64 n 0) acc\n\
                                      (sum-to (primitives/sub-i64 n 1) (primitives/add-i64 acc n)))))";
        let sexps = cranelisp_frontend::parse(src).expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
        // MUST be Ok — NEVER a panic and NEVER an ambiguity error. Drives the
        // full pipeline in a debug build (the build the old `:1016`
        // `debug_assert!` was live in), so it also guards the no-panic property.
        tc.check_program_self(&program).expect(
            "the delegating 1-arg clause pins `n : Int` through the 2-arg sibling \
             (§5.1.2 back-flow) — `sum-to` MUST infer, not be ambiguous",
        );
    }

    // spec: spec/05-definitions.md §5.1.2 (u2/u3, §11.3(B)) — a clause pinned
    //   concrete by a sibling self-call (the back-flow) is registered `Concrete`
    //   under its CONCRETE mangle; NO `$Var`-mangled entry survives finalize, and
    //   the drain's `SigDispatch` name is that same concrete mangle (one
    //   `mangle_sig` source ⇒ entry-name and dispatch-name agree, Principle 7).
    #[test]
    fn multi_sig_backflow_pins_clause_concrete_no_var_entry_survives() {
        let mut tc = tc_with_prims();
        // rp4: the 2-arg clause delegates to the concrete 3-arg sibling, which
        // pins its params to Int (back-flow). Pre-drain the 2-arg clause is a
        // `$Var` Polymorphic template; post-drain it is a `Concrete` `rp4$Int+Int`.
        let src = "(defn rp4 ([p rot] (let [q (rp4 p rot 0)] p)) \
                             ([p rot idx] (primitives/add-i64 p (primitives/add-i64 rot idx))))";
        let program =
            cranelisp_frontend::build_forms(&cranelisp_frontend::parse(src).unwrap()).unwrap();
        tc.check_program_self(&program).expect("rp4 back-flow infers");
        let st = tc.symbol_table();
        match st.get("rp4$Int+Int") {
            Some(ModuleEntry::Def { kind, scheme, .. }) => {
                assert!(
                    matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }
                    ),
                    "the back-flow-pinned 2-arg clause must be Concrete, got {kind:?}"
                );
                assert!(
                    scheme.ty.is_concrete(),
                    "rp4$Int+Int scheme must be fully concrete, got {:?}",
                    scheme.ty
                );
            }
            other => panic!("rp4$Int+Int concrete sibling not registered: {other:?}"),
        }
        // §11.3(B): the stale `$Var` template must NOT survive.
        assert!(
            st.get("rp4$Var+Var").is_none(),
            "no `$Var` entry may survive for a back-flow-pinned clause (§11.3(B))"
        );
        // The concrete 3-arg clause is its own concrete callable.
        assert!(
            matches!(
                st.get("rp4$Int+Int+Int"),
                Some(ModuleEntry::Def { kind, .. })
                    if matches!(kind.as_ref(), DefKind::UserFn { fn_state: UserFnState::Concrete { .. } })
            ),
            "the 3-arg clause must be Concrete rp4$Int+Int+Int"
        );
    }

    // spec: spec/05-definitions.md §5.1.2 (u3, §11.3.2) — the B1 fix + I3 pin:
    //   in a ≥2-hop self-call delegation chain (`f3`), every self-call's recorded
    //   `SigDispatch` MUST name an entry that EXISTS in the final symbol table —
    //   i.e. recorded-dispatch-name ≡ registered-entry-name over the FINALISED
    //   post-drain types. This is the case that escaped W2: the pass-1 self-call
    //   dispatch was derived MID-drain, when clause 2's params were still `Var`, so
    //   clause 1 recorded a `$Var` template name that finalize later removed →
    //   `f3$Var+Var` reached codegen. Deferring the derivation post-drain (one
    //   `mangle_sig` over the finalised params) makes every recorded dispatch name a
    //   live entry (no `$Var` residue), order-independent (Principle 24).
    #[test]
    fn multi_sig_delegation_chain_self_call_dispatches_name_live_entries_no_var_residue() {
        let mut tc = tc_with_prims();
        // f3: clause [a] delegates to [a b]; [a b] delegates to [a b c]; the 3-arg
        // leaf pins every clause to Int through the chain (the review's B1 repro).
        let src = "(defn f3 ([a] (f3 a 0)) ([a b] (f3 a b 1)) \
                             ([a b c] (primitives/add-i64 a (primitives/add-i64 b c))))";
        let program =
            cranelisp_frontend::build_forms(&cranelisp_frontend::parse(src).unwrap()).unwrap();
        tc.check_program_self(&program)
            .expect("the delegation chain back-flow-pins every clause to Int (§5.1.2)");

        let st = tc.symbol_table();
        // Every clause is a live Concrete entry under its finalised concrete mangle;
        // NO `$Var` template survives any clause of a fully back-flow-pinned chain.
        for concrete in ["f3$Int", "f3$Int+Int", "f3$Int+Int+Int"] {
            assert!(
                matches!(
                    st.get(concrete),
                    Some(ModuleEntry::Def { kind, .. })
                        if matches!(kind.as_ref(), DefKind::UserFn { fn_state: UserFnState::Concrete { .. } })
                ),
                "clause entry `{concrete}` must be a live Concrete entry",
            );
        }
        for var_key in ["f3$Var", "f3$Var+Var", "f3$Var+Var+Var"] {
            assert!(
                st.get(var_key).is_none(),
                "no `$Var` template (`{var_key}`) may survive a fully pinned chain (§11.3.2)",
            );
        }

        // The I3 invariant: walk each mangled clause body; every `SigDispatch`
        // mangled name MUST resolve to an existing symbol-table entry (no dangling
        // `$Var` dispatch), and none may contain `$Var`.
        fn collect_sig_dispatch(expr: &Expr, out: &mut Vec<String>) {
            let rc = match expr {
                Expr::Apply { callee, args, resolved_call, .. } => {
                    collect_sig_dispatch(callee, out);
                    for a in args {
                        collect_sig_dispatch(a, out);
                    }
                    resolved_call.as_deref()
                }
                Expr::Var { resolved_call, .. } => resolved_call.as_deref(),
                Expr::If { cond, then_branch, else_branch, .. } => {
                    collect_sig_dispatch(cond, out);
                    collect_sig_dispatch(then_branch, out);
                    collect_sig_dispatch(else_branch, out);
                    None
                }
                Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
                    for (_, b) in bindings {
                        collect_sig_dispatch(b, out);
                    }
                    collect_sig_dispatch(body, out);
                    None
                }
                Expr::Lambda { body, .. }
                | Expr::Annotate { expr: body, .. }
                | Expr::Trace { body, .. } => {
                    collect_sig_dispatch(body, out);
                    None
                }
                _ => None,
            };
            if let Some(ResolvedCall::SigDispatch { mangled_name }) = rc {
                out.push(mangled_name.as_ref().to_string());
            }
        }

        let mut all_dispatches = Vec::new();
        for concrete in ["f3$Int", "f3$Int+Int", "f3$Int+Int+Int"] {
            if let Some(ModuleEntry::Def { ast: Some(variant), .. }) = st.get(concrete) {
                collect_sig_dispatch(&variant.body, &mut all_dispatches);
            }
        }
        // The chain's two hops must be recorded (proving the deferral fired), and
        // every recorded dispatch names a live bare-keyed entry with no `$Var`.
        assert!(
            all_dispatches.iter().any(|d| d == "f3$Int+Int"),
            "clause [a]'s self-call `(f3 a 0)` must dispatch to the live f3$Int+Int \
             (not a dangling `$Var`); found: {all_dispatches:?}",
        );
        assert!(
            all_dispatches.iter().any(|d| d == "f3$Int+Int+Int"),
            "clause [a b]'s self-call `(f3 a b 1)` must dispatch to f3$Int+Int+Int; \
             found: {all_dispatches:?}",
        );
        for d in &all_dispatches {
            assert!(
                !d.contains("$Var"),
                "no self-call `SigDispatch` may name a `$Var` template ({d}) — every \
                 recorded dispatch must name a finalised concrete entry (§11.3.2)",
            );
            assert!(
                st.get(d).is_some(),
                "the recorded dispatch name `{d}` must resolve to a live symbol-table \
                 entry (recorded-dispatch-name ≡ registered-entry-name, Principle 7)",
            );
        }
    }

    // spec: spec/05-definitions.md §5.1.2 (§11.3.1 caveat (b), the I1 fix) — a
    //   genuinely-polymorphic RECURSIVE clause of a multi-sig defn is inference-
    //   equivalent to the standalone recursive function (which accepts + runs). The
    //   1-arg clause `([x] (if true x (g x)))` monomorphises at an external `(g 5)`;
    //   during the template's mono recheck the inner self-call `(g x)` is
    //   monomorphic recursion to THIS instance, resolved inline against the origin
    //   base — NOT deferred to a pending entry the sole drain has already taken (the
    //   residual-var wrong-reject with the internal `g$Var$Int` mangle leak).
    #[test]
    fn recursive_poly_multi_sig_clause_monomorphises_inline_no_residual() {
        let mut tc = tc_with_prims();
        let src = "(defn g ([x] (if true x (g x))) ([a b] a))\n\
                   (defn use-g [] :primitives/Int (g 5))";
        let program =
            cranelisp_frontend::build_forms(&cranelisp_frontend::parse(src).unwrap()).unwrap();
        // MUST accept: P7 `finalize_mono_codegen_view` hard-errors on a residual
        // `Var` in the mono body, so a clean accept proves the inner self-call was
        // resolved (the instance body is fully concrete).
        tc.check_program_self(&program).expect(
            "g's recursive poly clause is inference-equivalent to the standalone \
             recursive fn — MUST accept, not wrong-reject with an internal mangle leak",
        );
        // The concrete instance is a live, fully-concrete Concrete entry.
        let st = tc.symbol_table();
        match st.get("test/g$Var$Int") {
            Some(ModuleEntry::Def { kind, scheme, .. }) => {
                assert!(
                    matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }
                    ),
                    "the mono instance `g$Var$Int` must be Concrete, got {kind:?}",
                );
                assert!(
                    scheme.ty.is_concrete(),
                    "the mono instance's stored type must be fully concrete \
                     (the inner self-call left no residual `Var`), got {:?}",
                    scheme.ty,
                );
            }
            other => panic!("the `(g 5)` mono instance `test/g$Var$Int` is missing: {other:?}"),
        }
    }

    // spec: spec/05-definitions.md §5.1.2 (u1) — the post-drain per-clause
    //   ambiguity classification: a genuinely-polymorphic clause is ADMISSIBLE
    //   (skipped); a concrete-signature clause with an internally-unpinned var
    //   reaching a codegen position is the §3.11 ambiguity — the same disposition
    //   the equivalent standalone function would get.
    #[test]
    fn multi_sig_clause_admissible_poly_vs_genuinely_unpinned() {
        // Admissible: `([:a x] x)` is genuinely polymorphic → accepted.
        let mut tc = tc_with_prims();
        let ok = "(defn f ([:a x] x) ([:Int x :Int y] (primitives/add-i64 x y)))";
        let p = cranelisp_frontend::build_forms(&cranelisp_frontend::parse(ok).unwrap()).unwrap();
        tc.check_program_self(&p)
            .expect("a genuinely-polymorphic clause is admissible (§5.1.2)");

        // Ambiguous: a concrete-signature clause `([:Int n] (let [u []] n))` whose
        // internal `u = []` carries a free `(Vec a)` into a codegen position. The
        // sibling `([a b] a)` is admissibly poly (skipped); the defn errors on the
        // unpinned clause.
        let mut tc2 = tc_with_prims();
        let bad = "(defn f ([:primitives/Int n] (let [u []] n)) ([a b] a))";
        let p2 = cranelisp_frontend::build_forms(&cranelisp_frontend::parse(bad).unwrap()).unwrap();
        let err = tc2
            .check_program_self(&p2)
            .expect_err("an internally-unpinned concrete clause is §3.11 ambiguous");
        assert!(
            format!("{err}").to_lowercase().contains("ambiguous"),
            "the unpinned-clause rejection must be a §3.11 ambiguity, got: {err}"
        );
    }

    // spec: spec/05-definitions.md §5.1.2 (u7/u8/u9, §11.4) — a trait-constrained
    //   clause of a multi-sig defn is a single-variant `Constrained` TEMPLATE under
    //   its normalized `$Var` mangle (never a bogus `Concrete{got_slot}`); dispatch
    //   to it routes through per-call-site monomorphisation, minting a concrete
    //   instance — exactly as a standalone constrained fn.
    #[test]
    fn constrained_multi_sig_clause_is_template_and_dispatches_via_mono() {
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);
        // g: a constrained 1-arg clause `([:a x] (+ x x))` (Num a) + a concrete
        // 2-arg clause; a use `(g 3)` at Int.
        let src = "(defn g ([:a x] (+ x x)) ([:primitives/Int x :primitives/Int y] (primitives/add-i64 x y)))\n\
                   (defn use-g [] :primitives/Int (g 3))";
        let p = cranelisp_frontend::build_forms(&cranelisp_frontend::parse(src).unwrap()).unwrap();
        tc.check_program_self(&p)
            .expect("the constrained clause is admissible at a non-overlapping arity (§11.4)");
        let st = tc.symbol_table();
        // u7: the non-concrete-param clause is a SLOT-LESS TEMPLATE under its
        // normalized `$Var` mangle (`Constrained` with a real Num prelude, or
        // `Polymorphic` in this reduced fixture where `+`'s constraint does not
        // accrue) — never a bogus `Concrete{got_slot}` over the `Var` param
        // (§11.4 step 2 / §11.3(B); the constrained-specific path is exercised
        // end-to-end by `spec_05_definitions::constrained_clause_*` with the real
        // TestStandard Num).
        match st.get("g$Var") {
            Some(ModuleEntry::Def { kind, .. }) => assert!(
                matches!(
                    kind.as_ref(),
                    DefKind::UserFn {
                        fn_state:
                            UserFnState::Constrained(_) | UserFnState::Polymorphic(_)
                    }
                ),
                "g$Var must be a slot-less template (never Concrete over Var), got {kind:?}"
            ),
            other => panic!("the clause template `g$Var` is missing: {other:?}"),
        }
        // u8/u9: `(g 3)` monomorphised the clause template at Int — a concrete
        // instance of `g$Var` at Int exists.
        assert!(
            st.all_symbols()
                .any(|(n, e)| n.as_ref().contains("g$Var")
                    && n.as_ref().contains("Int")
                    && matches!(e, ModuleEntry::Def { kind, .. }
                        if matches!(kind.as_ref(), DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }))),
            "`(g 3)` must monomorphise the constrained clause template to a concrete \
             Int instance (§11.4 step 4)"
        );
    }

    // spec: spec/05-definitions.md §5.1.1 (MS-6/CP-2) — two SAME-ARITY clauses
    //   whose signatures can UNIFY are a dispatch-ambiguity reported AT the
    //   DEFINITION (no call required), naming both clauses; distinct-arity and
    //   distinct-concrete pairs are fine.
    #[test]
    fn multi_sig_same_arity_unifiable_clauses_rejected_at_definition() {
        // `[:Int x]` + `[:a x]` — same arity, can unify → definition-site error.
        let mut tc = tc_with_prims();
        let overlap = "(defn f ([:primitives/Int x] x) ([:a x] x))";
        let p = cranelisp_frontend::build_forms(&cranelisp_frontend::parse(overlap).unwrap()).unwrap();
        let err = tc
            .check_program_self(&p)
            .expect_err("same-arity-unifiable clauses are a §5.1.1 definition-site ambiguity");
        let m = format!("{err}").to_lowercase();
        assert!(m.contains("ambiguous") && m.contains("clause"), "got: {err}");

        // Distinct concrete types at the same arity are NOT an overlap.
        let mut tc2 = tc_with_prims();
        let ok = "(defn f ([:primitives/Int x] x) ([:primitives/String x] x))";
        let p2 = cranelisp_frontend::build_forms(&cranelisp_frontend::parse(ok).unwrap()).unwrap();
        tc2.check_program_self(&p2)
            .expect("distinct-concrete same-arity clauses dispatch cleanly");
    }

    // spec: spec/03-types.md §3.11 — Ambiguous Types: a generic *definition*
    //   (`(defn id [x] x)`) is NOT ambiguous — its scheme vars are quantified,
    //   not free-at-root — so it lands in the sound slot-less `Polymorphic` arm.
    //
    // FIXME(/typecheck 0374): the slot-gate companion of the §3.11 rule. The
    //   POSITIVE ambiguity-rejection test (an unannotated top-level value
    //   literal being rejected) is DEFERRED with the ambiguity-check enforcement
    //   — spec §3.11's "reject bare `None`/`[]` at the REPL" conflicts with the
    //   pre-existing self-documenting-REPL display of those forms, pending /spec
    //   + /repl arbitration (FIXME 0378). This negative companion stays: a
    //   generic defn must NEVER be an ambiguity error.

    // spec: spec/03-types.md §3.11 — NEGATIVE companion: a generic top-level
    //   defn is a sound `Polymorphic` template, NOT an ambiguity error. This
    //   distinguishes a quantified scheme variable (fine) from a free-at-root
    //   un-generalisable var (ambiguous).
    #[test]
    fn generic_defn_is_polymorphic_not_ambiguous() {
        let mut tc = tc_with_prims();
        let sexps = cranelisp_frontend::parse("(defn id [x] x)").expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
        // A generic defn must check cleanly (no ambiguity error) and land in the
        // slot-less Polymorphic arm.
        tc.check_program_self(&program)
            .expect("a generic defn must NOT be rejected as ambiguous");
        assert!(
            matches!(
                tc.symbol_table().get("id"),
                Some(ModuleEntry::Def { kind, .. })
                    if matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state: UserFnState::Polymorphic(_) }
                    )
            ),
            "a generic defn is a sound Polymorphic template, not an error",
        );
    }

    // spec: spec/03-types.md §3.4 — a polymorphic accumulator threaded through a
    //   recursive fold helper MUST generalize so a sibling Vec-accumulator use
    //   does not collapse the helper/caller scheme.
    //
    // FIXME(/typecheck 0344): UNIT repro of the vec-reduce over-unification
    //   defect (FIXME 0344). This is the tighter seam for the e2e
    //   `tests/spec_04_expressions.rs::polymorphic_accumulator_fold_does_not_over_unify`.
    //
    //   Shape (inlined, no stdlib): a caller `reduce` + a recursive helper
    //   `reduce-loop` that threads a polymorphic accumulator `acc` (type b)
    //   distinct from the Vec element type (type a, via `vec-get`), PLUS one
    //   sibling use `collect` that puts a `(Vec a)` in accumulator position.
    //
    //   The sibling `collect` must instantiate a FRESH copy of `reduce`'s
    //   generalized scheme; instead inference monomorphises `reduce`'s
    //   accumulator type variable to `(Vec a)`, so the later Int-accumulator
    //   use `(reduce add-i64 0 v)` fails to unify.
    //
    //   SEAM (isolated in-session, throwaway probe; FIXME 0344): the collapse
    //   is caused ENTIRELY by the sibling use, NOT by the recursive helper.
    //   Checked in isolation:
    //     - `reduce-loop` alone     => CORRECT: forall a b. (Fn [(Fn [b a] b) b (Vec a) Int Int] b)
    //     - `reduce` + `reduce-loop` => CORRECT: forall a b. (Fn [(Fn [b a] b) b (Vec a)] b)
    //     - + sibling `collect`      => COLLAPSED: forall a. (Fn [(Fn [(Vec a) (Vec a)] (Vec a)) (Vec a) (Vec a)] (Vec a))
    //   So the recursive-helper inference is sound; the defect lives at the
    //   call-site treatment of `reduce` inside `collect`. `(reduce vec-push []
    //   vv)` must instantiate a FRESH copy of `reduce`'s generalized scheme
    //   (vec-push :: (Fn [(Vec a) a] (Vec a)), `[]` :: (Vec a)) at that one
    //   call. Instead the call unifies into `reduce`'s OWN, not-yet-frozen
    //   accumulator type variable `b`, forcing b ≡ (Vec a); that collapse then
    //   back-propagates into the STORED schemes of both `reduce` and
    //   `reduce-loop`. Net: cross-defn generalize/instantiate ordering — a
    //   defn's scheme is not generalized-and-frozen before a sibling defn in
    //   the same cluster is checked against it, so the sibling monomorphises
    //   it. (`check_program_self` returns Ok here because this minimal cluster
    //   has no Int-accumulator use to surface the mismatch; the COLLAPSED
    //   STORED SCHEME is the durable witness — the e2e's `main` Int call is
    //   where the collapse becomes an outright type error.)
    //
    //   EXPECTED (correct, post-fix): `check_program_self` succeeds; `reduce`
    //     generalizes to `forall a b. (Fn [(Fn [b a] b) b (Vec a)] b)` — a
    //     polymorphic scheme with >= 2 type vars whose accumulator parameter
    //     and result are the SAME var `b`, NOT `(Vec _)`.
    //   ACTUAL (today, FAILING): every type variable collapses to `(Vec a)`;
    //     `reduce :: (Fn [(Fn [(Vec a) (Vec a)] (Vec a)) (Vec a) (Vec (Vec a))]
    //     (Vec a))`. Because the accumulator no longer generalizes across the
    //     two sibling uses, the program either errors at check time or `reduce`
    //     carries the collapsed scheme. This assertion FAILS until inference
    //     stops over-unifying the accumulator var.
    #[test]
    fn fold_polymorphic_accumulator_does_not_over_unify() {
        let mut tc = tc_with_prims();
        // tc_with_prims glob-imports `primitives` into `test`, so add-i64,
        // ge-i64, vec-len, vec-get, vec-push resolve as bare names — no
        // `(import ...)` form needed (and no stdlib dependency).
        let src = "\
            (defn reduce [f init v] (reduce-loop f init v (vec-len v) 0))\n\
            (defn reduce-loop [f acc v :primitives/Int len :primitives/Int i]\n  \
              (if (ge-i64 i len) acc\n    \
                (reduce-loop f (f acc (vec-get v i)) v len (add-i64 i 1))))\n\
            (defn collect [vv] (reduce vec-push [] vv))";
        let sexps = cranelisp_frontend::parse(src).expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");

        // CORRECT inference: the whole program type-checks. Today this FAILS
        // because the sibling `(Vec a)` accumulator use over-unifies `reduce`'s
        // accumulator type variable, collapsing the polymorphic scheme.
        let result = tc.check_program_self(&program);
        assert!(
            result.is_ok(),
            "polymorphic-accumulator fold must type-check; the sibling Vec \
             accumulator use must NOT over-unify reduce's accumulator var \
             (FIXME 0344). got error: {:?}",
            result.as_ref().err().map(|e| e.message().to_string()),
        );

        // And `reduce`'s scheme must stay polymorphic in its accumulator: its
        // accumulator parameter must NOT have collapsed to `(Vec _)`. The
        // accumulator is the SECOND parameter of `reduce` (f, init, v) and is
        // the same var as the result.
        let scheme = match tc.symbol_table().get("reduce") {
            Some(ModuleEntry::Def { scheme, .. }) => scheme.clone(),
            other => panic!("reduce not a Def in symbol table: {other:?}"),
        };
        assert!(
            scheme.type_vars.len() >= 2,
            "reduce must generalize over (at least) the element AND accumulator \
             type vars; collapsed scheme had {} vars: {:?} (FIXME 0344)",
            scheme.type_vars.len(),
            scheme,
        );
        // Pin the EXACT correct scheme shape: `(Fn [(Fn [b a] b) b (Vec a)] b)`
        // with b (accumulator/result) ≠ a (element) — the canonical reduce type.
        if let Type::Fn(params, ret) = &scheme.ty {
            assert_eq!(params.len(), 3, "reduce takes (f init v)");
            // accumulator (init) is params[1]; result is ret. Neither may be a
            // concrete `(Vec _)` — over-unification stamps Vec onto both.
            assert!(
                !is_vec(&params[1]) && !is_vec(ret),
                "reduce's accumulator param and result must stay polymorphic, \
                 not collapse to (Vec _): init={:?} ret={:?} (FIXME 0344)",
                params[1], ret,
            );
            // params[0] is the folding fn `(Fn [b a] b)`.
            let (b_acc, a_elem) = match &params[0] {
                Type::Fn(f_params, f_ret) => {
                    assert_eq!(f_params.len(), 2, "fold fn takes (acc elem)");
                    let b = match &f_params[0] {
                        Type::Var(id) => *id,
                        other => panic!("fold-fn accumulator param must be a Var, got {other:?}"),
                    };
                    let a = match &f_params[1] {
                        Type::Var(id) => *id,
                        other => panic!("fold-fn element param must be a Var, got {other:?}"),
                    };
                    // Fold fn returns the accumulator type `b`.
                    assert_eq!(
                        f_ret.as_ref(), &Type::Var(b),
                        "fold fn must return the accumulator var b, got {f_ret:?}",
                    );
                    (b, a)
                }
                other => panic!("reduce's first param must be a fold fn, got {other:?}"),
            };
            // b ≠ a — the accumulator type is INDEPENDENT of the element type.
            assert_ne!(
                b_acc, a_elem,
                "accumulator var b and element var a must be DISTINCT (FIXME 0344)",
            );
            // init (params[1]) and result (ret) are both the accumulator var b.
            assert_eq!(params[1], Type::Var(b_acc), "init must be the accumulator var b");
            assert_eq!(ret.as_ref(), &Type::Var(b_acc), "result must be the accumulator var b");
            // v (params[2]) is `(Vec a)` — element type a.
            match &params[2] {
                Type::ADT(name, args) if name.name.as_ref() == "Vec" => {
                    assert_eq!(args.len(), 1, "Vec is unary");
                    assert_eq!(args[0], Type::Var(a_elem), "v must be (Vec a) over the element var");
                }
                other => panic!("reduce's third param must be (Vec a), got {other:?}"),
            }
        } else {
            panic!("reduce scheme is not a function type: {:?}", scheme.ty);
        }

        // The concrete Int-accumulator use `(reduce add-i64 0 [1 2 3])`, checked
        // AS A FOLLOW-ON REPL FORM after the cluster, must type-check and infer
        // `Int` — the observable downstream contract from the FIXME. It
        // instantiates a FRESH copy of reduce's now-generalized scheme; before
        // the fix this fails with `expected (Vec t…), got Int`. Checking it as a
        // single trailing form (not in the 4-defn batch) makes `compute_display`
        // populate the subst-resolved result type.
        let call_sexps = cranelisp_frontend::parse("(reduce add-i64 0 [1 2 3])").expect("parse call");
        let call_prog = cranelisp_frontend::build_forms(&call_sexps).expect("build_forms call");
        assert_eq!(call_prog.len(), 1, "expected a single trailing expression form");
        let call_result = tc
            .check_program_self(&call_prog)
            .expect("Int-accumulator reduce call must type-check (FIXME 0344)");
        let display = call_result
            .display
            .expect("trailing expression must produce a display type");
        assert_eq!(
            display.ty, Type::Int,
            "(reduce add-i64 0 [1 2 3]) must infer Int (FIXME 0344), got {:?}",
            display.ty,
        );
    }

    // spec: spec/03-types.md §3.4 — monomorphisation must create the concrete
    //   mono variant for a call to a polymorphic fn REGARDLESS of whether the
    //   callee was defined before or after the helper it forward-references.
    //
    // FIXME(/typecheck 0349): the final layer of 0344. Even with the 0344
    //   over-unification fixed (the stored schemes of `reduce`/`reduce-loop`
    //   are correctly polymorphic), a FORWARD-REFERENCE definition order
    //   (`reduce` BEFORE `reduce-loop`) left a concrete CALLER (`main`,
    //   `(reduce add-i64 0 [1 2 3])`) spuriously polymorphic: `reduce` was
    //   generalized after its body-check, but its body call to the
    //   not-yet-body-checked `reduce-loop` did not yet tie its accumulator to
    //   its result var, so `reduce` generalized with init/result as INDEPENDENT
    //   vars. The caller then bound its own result to `reduce`'s loose result
    //   var, staying `(IO t)` — which (a) marked `main` itself "constrained"
    //   (polymorphic + ast), so its body was skipped by pass4 and the
    //   `reduce$Int+Vec` mono variant was NEVER created, and (b) left `main`
    //   calling the polymorphic template (returns the initial accumulator, 0)
    //   instead of the specialised fold.
    //
    //   The fix: pass4 (1) scans EVERY defn body for concrete constrained calls,
    //   excluding only self-recursion, so a constrained/polymorphic caller's
    //   concrete call sites are still collected; (2) `monomorphise_call`
    //   propagates the concrete return type back to the call site, pinning the
    //   caller's result var; (3) finalize re-generalizes after pass4 so the
    //   caller's STORED scheme collapses to its true monomorphic form.
    //
    //   This UNIT pins the order-independence at the typecheck seam; the e2e
    //   `tests/spec_04_expressions.rs::polymorphic_accumulator_fold_does_not_over_unify`
    //   pins the end-to-end value (`(reduce add-i64 0 [1 2 3])` => 6).
    #[test]
    fn forward_reference_polymorphic_call_creates_mono_variant() {
        let mut tc = tc_with_prims();
        // FORWARD reference: `reduce` is defined BEFORE the helper it calls
        // (`reduce-loop`). Plus a concrete caller `main` that folds with Int.
        let src = "\
            (defn reduce [f init v] (reduce-loop f init v (vec-len v) 0))\n\
            (defn reduce-loop [f acc v :primitives/Int len :primitives/Int i]\n  \
              (if (ge-i64 i len) acc\n    \
                (reduce-loop f (f acc (vec-get v i)) v len (add-i64 i 1))))\n\
            (defn main [] (reduce add-i64 0 [1 2 3]))";
        let sexps = cranelisp_frontend::parse(src).expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");

        let result = tc.check_program_self(&program);
        assert!(
            result.is_ok(),
            "forward-reference polymorphic fold must type-check (FIXME 0349); \
             got error: {:?}",
            result.as_ref().err().map(|e| e.message().to_string()),
        );

        // A concrete mono variant for the Int-accumulator call MUST have been
        // created — regardless of the forward-reference definition order. Before
        // the fix NO `reduce$…` entry exists (the caller was skipped by pass4).
        let mono_count = tc
            .symbol_table()
            .all_symbols()
            .filter(|(name, _)| name.as_ref().contains("reduce$"))
            .count();
        assert!(
            mono_count >= 1,
            "a `reduce$…` mono variant must be created for the concrete \
             Int-accumulator call under forward-reference ordering (FIXME 0349); \
             found mono variants: {:?}",
            tc.symbol_table()
                .all_symbols()
                .filter(|(n, _)| n.as_ref().starts_with("reduce$"))
                .map(|(n, _)| n.as_ref().to_string())
                .collect::<Vec<_>>(),
        );

        // And the concrete caller `main` must collapse to its true MONOMORPHIC
        // scheme `(Fn [] Int)` — NOT stay spuriously polymorphic. A leftover
        // free var in `main`'s scheme is the witness of the forward-ref defect.
        let main_scheme = match tc.symbol_table().get("main") {
            Some(ModuleEntry::Def { scheme, .. }) => scheme.clone(),
            other => panic!("main not a Def in symbol table: {other:?}"),
        };
        assert!(
            main_scheme.type_vars.is_empty(),
            "main must be monomorphic after pass4 re-generalization \
             (FIXME 0349); got polymorphic scheme {main_scheme:?}",
        );
        match &main_scheme.ty {
            Type::Fn(params, ret) => {
                assert!(params.is_empty(), "main takes no args");
                assert_eq!(
                    ret.as_ref(), &Type::Int,
                    "main folds Ints to an Int (FIXME 0349); got ret {:?}",
                    ret,
                );
            }
            other => panic!("main scheme is not a function type: {other:?}"),
        }
    }

    // spec: design/arch/concrete-boundary-type.md §4-A — Phase-4 part A
    //   mono-completeness: the fold helper mints ONLY the genuine concrete
    //   `reduce-loop$Int+Vec+Int+Int` instance, NOT the spurious partial
    //   `reduce-loop$Vec+Int+Int`. The spurious partial was minted by
    //   `monomorphise_inner_parametric_hops` recursing into `reduce`'s body
    //   while `reduce` is still generic (`f`/`acc`/element are `reduce`'s own
    //   scheme vars), bypassing the all-args-concrete gate via the bare-var-
    //   result trigger. After part A's all-args-concrete guard + trigger collapse,
    //   no partial is minted; every minted instance is fully concrete, so
    //   `MonoExpr::from_expr` succeeds on each (the carve-out deletion's
    //   completeness proof — the check below returning Ok IS that proof for the
    //   fold shape, since an instance with a residual var would now raise the
    //   ambiguity TypeError instead of being swallowed).
    #[test]
    fn fold_helper_mints_only_concrete_instance_no_partial() {
        let mut tc = tc_with_prims();
        // The 0344 fold shape with a CONCRETE caller `main` (Int accumulator).
        let src = "\
            (defn reduce [f init v] (reduce-loop f init v (vec-len v) 0))\n\
            (defn reduce-loop [f acc v :primitives/Int len :primitives/Int i]\n  \
              (if (ge-i64 i len) acc\n    \
                (reduce-loop f (f acc (vec-get v i)) v len (add-i64 i 1))))\n\
            (defn main [] (reduce add-i64 0 [1 2 3]))";
        let sexps = cranelisp_frontend::parse(src).expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");

        // The check must SUCCEED — with the `allowed_vars` carve-out deleted, a
        // surviving residual var in any minted instance would now surface as the
        // ambiguity / could-not-monomorphise TypeError at the mono seam. Success
        // is the completeness proof for the fold shape.
        let result = tc.check_program_self(&program);
        assert!(
            result.is_ok(),
            "fold must type-check AND every minted instance must be fully \
             concrete (Phase-4 part A — `from_expr` succeeds on every instance); \
             got error: {:?}",
            result.as_ref().err().map(|e| e.message().to_string()),
        );

        // The genuine concrete instance MUST be minted; the SPURIOUS partial
        // (Var-dropping lossy name) MUST NOT.
        let mono_names: Vec<String> = tc
            .mono_variants()
            .iter()
            .map(|v| v.name.as_ref().to_string())
            .collect();
        // FIXME 0519: the mono name is home-qualified with a lossless recursive
        // sig (`f`'s `Fn` type recursed, the `(Vec Int)` arg recursed FQ), so the
        // exact string is `test/reduce-loop$Fn(...)+Int+.../Vec$Int+Int+Int`. The
        // test's invariant is unchanged: exactly ONE genuine concrete instance,
        // and NO spurious partial (a residual `Var` token in the sig).
        let reduce_loop_monos: Vec<&String> =
            mono_names.iter().filter(|n| n.contains("reduce-loop$")).collect();
        assert!(
            !reduce_loop_monos.is_empty(),
            "the genuine concrete `reduce-loop` mono must be minted; \
             mono variants: {mono_names:?}",
        );
        assert!(
            !reduce_loop_monos.iter().any(|n| n.contains("Var")),
            "the SPURIOUS partial `reduce-loop` mint (a residual-`Var` lossy sig) \
             must NOT be minted (Phase-4 part A suppresses the generic-caller \
             recursion mint); mono variants: {mono_names:?}",
        );
    }

    // spec: design/arch/concrete-boundary-type.md §3.0 — Phase-3 (FIXME 0392)
    // codegen_view population. EVERY codegen-bound entry — an ordinary concrete
    // defn AND a monomorphised instance — ends with `Some(codegen_view)` whose
    // `MonoExpr` body is fully `ConcreteType`-annotated; a `Polymorphic`
    // template (a mono SOURCE, never a codegen target) ends with `None`.
    #[test]
    fn codegen_view_populated_for_concrete_and_mono_none_for_template() {
        use cranelisp_types::ConcreteType;

        let mut tc = tc_with_prims();
        // `id` is a pure-parametric generic (slot-less `Polymorphic` template).
        // `f` is an ordinary concrete defn. `main` calls `(id 5)`, minting the
        // concrete `id$Int` instance.
        let src = "\
            (defn id [x] x)\n\
            (defn f [x] (add-i64 x 1))\n\
            (defn main [] (id 5))";
        let sexps = cranelisp_frontend::parse(src).expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
        tc.check_program_self(&program).expect("check");

        // 1. The ordinary concrete defn `f` carries a concrete-boundary view
        //    whose body root type is concrete (`Int` — the `(add-i64 x 1)`
        //    result).
        let table = tc.symbol_table();
        let f_view = table
            .get("f")
            .and_then(|e| e.codegen_view().cloned())
            .expect("concrete defn `f` must carry Some(codegen_view)");
        assert_eq!(
            f_view.body.ty(),
            &ConcreteType::Int,
            "concrete defn body root must be a ConcreteType (Int)"
        );

        // 2. The minted mono instance `id$Int` carries a view whose body root is
        //    `Int` (the identity body `x` at `Int`).
        let id_int_view = table
            .get("test/id$Int")
            .and_then(|e| e.codegen_view().cloned())
            .expect("mono instance `test/id$Int` must carry Some(codegen_view)");
        assert_eq!(
            id_int_view.body.ty(),
            &ConcreteType::Int,
            "mono instance body root must be a ConcreteType (Int)"
        );

        // 3. The `Polymorphic` template `id` is a mono SOURCE, not a codegen
        //    target — it carries NO view.
        let id_entry = table.get("id").expect("`id` template must be registered");
        assert!(
            matches!(
                id_entry,
                ModuleEntry::Def { kind, .. }
                    if matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state: UserFnState::Polymorphic(_) }
                    )
            ),
            "`id` must be a slot-less Polymorphic template"
        );
        assert!(
            id_entry.codegen_view().is_none(),
            "a Polymorphic template must carry NO codegen_view (it is a mono \
             source, never a compile_to_module target)"
        );
    }

    /// Register a single-method trait `name` whose method `method` takes a
    /// `Self`-typed param and returns `Int`, plus an `impl name for Int` whose
    /// method body is `(add-i64 self self)` — into the fixture's CURRENT module.
    /// Used by the cross-module mono test so an imported constrained fn's body
    /// has a trait method to dispatch (FIXME 0355). `add-i64` is a Ring-0
    /// primitive (`(Fn [Int Int] Int)`); applying it to `self` twice keeps the
    /// impl body trivially `(Fn [Int] Int)`-typed.
    fn register_int_returning_trait(tc: &mut TestFixture, name: &str, method: &str) {
        let decl = TraitDecl {
            name: TraitName::from(name),
            docstring: None,
            type_params: vec![],
            methods: vec![TraitMethodSig {
                name: Symbol::from(method),
                docstring: None,
                params: vec![(Symbol::from("self"), TypeExpr::SelfType)],
                ret_type: TypeExpr::Named(cranelisp_types::TypeRef::new(
                    None,
                    TypeName::from("Int"),
                )),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        tc.register_trait_decl_self(&decl).unwrap();

        let impl_ = TraitImpl {
            head_con_var: None,
            trait_name: cranelisp_types::TraitRef::new(None, TraitName::from(name)),
            target: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int"))),
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from(method),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("self"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add-i64"), Span::SYNTHETIC)),
                        args: vec![
                            Expr::var(Symbol::from("self"), Span::SYNTHETIC),
                            Expr::var(Symbol::from("self"), Span::SYNTHETIC),
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

    // spec: spec/03-types.md §3.9 + spec/08-modules.md §8.6 — a constrained
    //   (trait-bound) function DEFINED in an imported module and CALLED from
    //   another module must produce a cross-module monomorphisation variant
    //   whose body is re-checked in the DEFINING module's import context.
    //
    // FIXME 0355 (the feature half of the resolved 0354 SIGSEGV). Today the
    //   call is cleanly rejected: `pass4_monomorphise` collects call sites only
    //   for the cluster's OWN constrained defns, so an imported `cmp` (a
    //   `ModuleEntry::Import` in the caller) is never seen → no `cmp$Int`
    //   variant is created. This pins BOTH crux points at the typecheck seam:
    //   (1) the imported constrained call site IS collected (a `cmp$Int` mono
    //   entry appears in the CALLER's module), and (2) the mono body re-checks
    //   in the DEFINING module's scope — its inner `show` resolves to `helper`'s
    //   `Display.show$Int` impl, NOT a caller-scope `no impl of Display`
    //   error (which is exactly the wall 0354's isolation hit). The companion
    //   e2e `tests/spec_07_traits.rs::cross_module_stacked_trait_bound_call_runs_to_clean_exit`
    //   upgrades to "runs to exit 2" once /backend wires the GOT.
    // W2a /review Suggestion 7 — the fn-value-rewrite multi-sig corner, PINNED as
    // BENIGN. A poly fn-value (`mk`) passed as a HOF argument inside a CONCRETE
    // multi-sig clause body is collected + monomorphised (`mk$Int` minted — the
    // `mono_scan_bodies` D3 extension reaches the clause bodies) and its span
    // carrier (`resolved_targets → mk$Int`) is written UNCONDITIONALLY. Only the
    // belt-and-braces AST `Var`-rename skips (its target `st.symbols.get_mut(base)`
    // is the `Overloaded` base entry with `ast: None` — the clause bodies live
    // under the MANGLED variant entries). That skip is benign: the mangled
    // variant's `codegen_view` is rebuilt from `resolved_targets`, so the backend
    // keyed-read resolves `mk → mk$Int` (BC §3 inv. 10) without the name rewrite.
    // This test pins BOTH facts (mint + carrier), so a regression that drops
    // either — turning the benign skip into a real slot-less leak — goes RED.
    #[test]
    fn fn_value_in_concrete_multi_sig_clause_minted_and_carried_sugg7() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn mk [x] x)\n\
             (defn thru [f n] (f n))\n\
             (defn ms ([:primitives/Int a] (thru mk a)) ([a b] a))\n\
             (defn use-ms [] (ms 5))",
        );
        // 1. The poly fn-value `mk` was monomorphised to `mk$Int` from the
        //    multi-sig clause body (the D3 clause-body scan reached it).
        assert!(
            !symbol_names_containing(&tc, "mk$Int").is_empty(),
            "the poly fn-value `mk` in `ms`'s concrete clause body MUST be \
             monomorphised to `mk$Int`; symbols: {:?}",
            symbol_names_containing(&tc, "mk"),
        );
        // 2. The carrier covers the base-entry AST-rename skip: `ms$Int`'s
        //    codegen_view resolves the `mk` fn-value `Var` to `mk$Int` (benign).
        let view = mono_instance_view_containing(&tc, "ms$Int");
        let mut targets = Vec::new();
        collect_resolved_targets(&view.body, &mut targets);
        let mk_carrier = targets.iter().any(|(l, fq)| {
            l == "mk" && matches!(fq, Some(fq) if fq.symbol.as_ref().contains("mk$Int"))
        });
        assert!(
            mk_carrier,
            "`ms$Int`'s codegen_view MUST carry `mk → mk$Int` (the keyed carrier \
             covers the belt-and-braces AST-rename skip on the Overloaded base — \
             benign, Suggestion 7); collected: {targets:?}"
        );
    }

    #[test]
    fn find_trait_method_decl_home_hop_finds_self_returning_method_d2() {
        let mut tc = tc_with_prims();
        let zlib = ModuleFullPath::from("zlib");
        tc.set_current_module(zlib.clone());
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
        // Trait `Zero` with a nullary Self-returning method `z` (`(z [] self)`).
        let decl = TraitDecl {
            name: TraitName::from("Zero"),
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
        };
        tc.register_trait_decl_self(&decl).unwrap();
        tc.clear_transient_state();
        // user imports ONLY the method `z` — NOT the trait `Zero`.
        let user = ModuleFullPath::from("user");
        tc.set_current_module(user.clone());
        seed_specific_import(&mut tc, &zlib, &["z"]);
        let state = CheckState::new(user.clone());
        assert!(
            tc.env().method_self_in_return(&state, "z"),
            "a method-only-imported Self-returning method MUST be found via the \
             D2 home-hop in find_trait_method_decl (Suggestion 6)"
        );
    }

    // W2a /review Important 3 — a trait method imported METHOD-ONLY whose
    // dispatch type is NOT in the caller's scope must still dispatch. The seam is
    // `try_resolve_trait_method` building the impl type's `FQTypeName`: pre-fix it
    // re-resolved the dispatch type's NAME (`Int`) in the CALLER's scope
    // (`resolve_type`) → "unknown type Int (from module user)" when user imported
    // only `sh`. The fix roots that resolution at the trait's HOME (zlib, where
    // the trait was declared and its impl mangle formed) via
    // `resolve_type_in_module` (D2/§7.0.1 P24). `check_src` panics on the
    // wrong-reject; a clean check is the assertion.
    #[test]
    fn method_only_import_foreign_dispatch_type_resolves_at_home_d2() {
        let mut tc = tc_with_prims();
        let zlib = ModuleFullPath::from("zlib");
        tc.set_current_module(zlib.clone());
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
        register_int_returning_trait(&mut tc, "Show", "sh");
        let user = ModuleFullPath::from("user");
        tc.set_current_module(user.clone());
        // user imports ONLY `sh` — NOT `Int`, NOT the trait `Show`.
        seed_specific_import(&mut tc, &zlib, &["sh"]);
        check_src(&mut tc, "(defn get-s [] (sh 5))");
    }

    #[test]
    fn cross_module_imported_constrained_fn_monomorphises_in_defining_scope() {
        let mut tc = tc_with_prims();
        let helper = ModuleFullPath::from("helper");
        let caller = ModuleFullPath::from("caller");

        // --- Build the DEFINING module `helper` --------------------------------
        // A trait `Display` (method `show`: `(Fn [Self] Int)`) + an Int impl, and
        // a constrained fn `cmp` whose body dispatches the trait method:
        //   (defn cmp [:Display a] (show a))
        // `cmp` generalizes to `forall a where Display a. (Fn [a] Int)` — a
        // genuine constrained `Def` living in `helper`.
        tc.set_current_module(helper.clone());
        // `helper` needs the primitives (`int-id`, used by the impl body) in scope.
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
        register_int_returning_trait(&mut tc, "Display", "show");

        let cmp = Defn {
            name: Symbol::from("cmp"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(
                    Symbol::from("a"),
                    Some(TypeExpr::Bounds(vec![cranelisp_types::TraitRef::new(
                        None,
                        TraitName::from("Display"),
                    )])),
                )],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("show"), Span::new(20, 24))),
                    args: vec![Expr::var(Symbol::from("a"), Span::new(25, 26))],
                    span: Span::new(19, 27),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: Span::new(0, 28),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 28),
        };
        tc.check_program_self(&[TopLevel::Defn(cmp)])
            .expect("constrained `cmp` must type-check in its defining module");

        // Sanity: `cmp` is registered as a CONSTRAINED UserFn in `helper`.
        match tc.modules.get(&helper).unwrap().get("cmp") {
            Some(ModuleEntry::Def { kind, .. }) => assert!(
                matches!(
                    kind.as_ref(),
                    DefKind::UserFn { fn_state: UserFnState::Constrained(_) }
                ),
                "cmp must be a constrained UserFn in `helper`, got {kind:?}",
            ),
            other => panic!("cmp not a Def in helper: {other:?}"),
        }

        // --- Build the CALLER module `caller` ----------------------------------
        // Import `cmp` (and `show`, mirroring the real import surface), then call
        // it with a concrete Int: (defn run [] (cmp 5)).
        tc.set_current_module(caller.clone());
        seed_specific_import(&mut tc, &helper, &["cmp", "show"]);

        let run = Defn {
            name: Symbol::from("run"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("cmp"), Span::new(120, 123))),
                    args: vec![Expr::IntLit {
                        value: 5,
                        span: Span::new(124, 125),
                        inferred_type: None,
                    }],
                    span: Span::new(119, 126),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: Span::new(100, 127),
            }],
            visibility: Visibility::Public,
            span: Span::new(100, 127),
        };

        // CRUX 2: this MUST type-check. If the mono body were re-checked in the
        // caller's scope (the as-built bug), `show` would mis-resolve and the
        // check would fail (`no impl of trait Display ...`). It succeeds only
        // because the body is re-checked in `helper`'s import context.
        tc.check_program_self(&[TopLevel::Defn(run)]).expect(
            "imported constrained call must type-check; the mono body re-checks \
             in the DEFINING module's scope so `show` resolves there (FIXME 0355)",
        );

        // CRUX 1: a `cmp$Int` mono variant was COLLECTED and registered in the
        // CALLER's module (`caller`), as a concrete `UserFn` owning its own GOT
        // slot — exactly what /backend wires into the caller's GOT.
        let monos: Vec<(String, bool)> = tc
            .modules
            .get(&caller)
            .unwrap()
            .all_symbols()
            // FIXME 0519: mono name is home-qualified by cmp's DEFINING module.
            .filter(|(name, _)| name.as_ref().contains("cmp$"))
            .map(|(name, entry)| {
                let concrete = matches!(
                    entry,
                    ModuleEntry::Def {
                        kind,
                        ..
                    } if matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }
                    )
                );
                (name.as_ref().to_string(), concrete)
            })
            .collect();
        assert!(
            monos.iter().any(|(n, _)| n == "helper/cmp$Int"),
            "a `helper/cmp$Int` mono variant must be created in the CALLER module \
             for the imported constrained call (FIXME 0355; home-qualified by cmp's \
             defining module `helper`, FIXME 0519); found: {monos:?}",
        );
        assert!(
            monos.iter().find(|(n, _)| n == "helper/cmp$Int").map(|(_, c)| *c).unwrap_or(false),
            "the `cmp$Int` mono entry must be a concrete UserFn owning its own \
             GOT slot (Option-A concrete-shape-owns-the-slot); found: {monos:?}",
        );
    }

    // spec: spec/08-modules.md §8.8.1 — a pure-parametric polymorphic fn provided
    //   ONLY through the implicit prelude (bare call, no explicit
    //   import) must mint its concrete mono in the CONSUMING module, exactly like
    //   the explicit-import path. DEF-1 (S86): the mono-collection chokepoint
    //   `collect_imported_constrained_calls` resolved the callee with
    //   `resolve_terminal_entry_and_home(current_module, name)` — rooted at the
    //   current module ONLY, NOT consulting the prelude-fallback hop the value /
    //   type / ctor / trait chokepoints already consult (S78 §2). So a bare
    //   `count` reached via the implicit-prelude fallback was invisible to the
    //   collector → no `monomorphise_call` → no `count$Vec` mono → codegen later
    //   fails `undefined function: count`.
    //
    //   This UNIT pins the fix at the typecheck seam: a bare prelude-fallback-
    //   resolved polymorphic call MUST register a concrete `count$..` mono in the
    //   CONSUMING module's table. The companion e2e is
    //   `tests/spec_08_modules.rs::def1_prelude_provided_defn_called_bare_enters_codegen_batch`.
    #[test]
    fn def1_bare_prelude_fallback_polymorphic_call_mints_mono_in_consumer() {
        let mut tc = tc_with_prims();
        let prelude = ModuleFullPath::from("prelude");
        let consumer = ModuleFullPath::from("consumer");

        // --- DEFINE the polymorphic `count` in the PRELUDE module --------------
        // `(defn count [v] (vec-len v))` generalizes to
        // `forall a. (Fn [(Vec a)] Int)` — a pure-parametric polymorphic Def
        // (slot-less template) living in `prelude`. Its body wraps the
        // GOT-dispatched primitive `vec-len`, the representative DEF-1 shape.
        tc.set_current_module(prelude.clone());
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
        let count_src = "(defn count [v] (vec-len v))";
        let count_sexps = cranelisp_frontend::parse(count_src).expect("parse count");
        let count_prog = cranelisp_frontend::build_forms(&count_sexps).expect("build count");
        tc.check_program_self(&count_prog)
            .expect("polymorphic `count` must type-check in `prelude`");

        // Sanity: `count` is a PUBLIC pure-parametric polymorphic UserFn in
        // `prelude` (a slot-less template — the mono-collectible shape).
        match tc.modules.get(&prelude).unwrap().get("count") {
            Some(ModuleEntry::Def { kind, scheme, .. }) => {
                assert!(
                    matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state }
                            if !matches!(fn_state, UserFnState::Constrained(_))
                    ),
                    "count must be a non-constrained UserFn template, got {kind:?}",
                );
                assert!(
                    !scheme.type_vars.is_empty(),
                    "count must be polymorphic (a generic template), got {scheme:?}",
                );
            }
            other => panic!("count not a Def in prelude: {other:?}"),
        }

        // --- BUILD the CONSUMER module -----------------------------------------
        // The consumer turns the implicit-prelude fallback on (the
        // `PreludeFallback` bit) but does NOT import `count` — exactly the
        // bare/glob path. `vec-len` etc. are NOT in the consumer's table; the
        // bare `count` call must resolve through the prelude fallback hop.
        tc.set_current_module(consumer.clone());
        tc.prelude_fallback.insert(consumer.clone(), true);
        // The consumer still needs primitive type names / Vec-literal support; a
        // glob of primitives gives `Vec`, the int primitives etc. WITHOUT giving
        // `count` (count lives only in prelude). This mirrors the e2e's
        // `(export [primitives [*]])` re-export reaching the consumer, while
        // `count` reaches ONLY via the implicit-prelude fallback.
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
        assert!(
            tc.modules.get(&consumer).unwrap().get("count").is_none(),
            "the consumer must NOT have an explicit `count` entry — it reaches \
             `count` ONLY via the implicit-prelude fallback",
        );

        // `(defn main [] (count [10 20 30]))` — a BARE call to the
        // prelude-provided polymorphic `count` with a concrete `(Vec Int)`.
        let main_src = "(defn main [] (count [10 20 30]))";
        let main_sexps = cranelisp_frontend::parse(main_src).expect("parse main");
        let main_prog = cranelisp_frontend::build_forms(&main_sexps).expect("build main");
        tc.check_program_self(&main_prog).expect(
            "bare prelude-fallback `count` call must type-check; its mono must be \
             collected via the prelude-fallback hop (DEF-1)",
        );

        // CRUX: a concrete `count$..` mono variant MUST be registered in the
        // CONSUMER's module. Before the fix the collector never saw the
        // prelude-fallback-resolved callee, so no mono was minted (and codegen
        // later failed `undefined function: count`).
        let monos: Vec<(String, bool)> = tc
            .modules
            .get(&consumer)
            .unwrap()
            .all_symbols()
            // FIXME 0519: mono name is home-qualified by count's DEFINING module.
            .filter(|(name, _)| name.as_ref().contains("count$"))
            .map(|(name, entry)| {
                let concrete = matches!(
                    entry,
                    ModuleEntry::Def { kind, .. }
                        if matches!(
                            kind.as_ref(),
                            DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }
                        )
                );
                (name.as_ref().to_string(), concrete)
            })
            .collect();
        assert!(
            !monos.is_empty(),
            "a concrete `count$..` mono variant must be minted in the CONSUMER \
             module for the bare prelude-fallback call (DEF-1); found none",
        );
        assert!(
            monos.iter().all(|(_, c)| *c),
            "every minted `count$..` mono must be a concrete UserFn owning its \
             own GOT slot; found: {monos:?}",
        );
    }

    // Vec has no dedicated `Type` variant; it is encoded as
    // `Type::ADT(primitives/Vec, [elem])` (see builtins.rs
    // `register_builtin_type_names`). The over-unification defect stamps this
    // ADT onto the accumulator var.
    fn is_vec(t: &Type) -> bool {
        matches!(t, Type::ADT(name, _) if name.name.as_ref() == "Vec")
    }

    /// Register a minimal single-method trait `name` (method `method` with a
    /// `Self`-typed parameter and `Bool` return) in the fixture's current
    /// module, so a `Bounds([..])` param annotation can resolve it.
    fn register_marker_trait(tc: &mut TestFixture, name: &str, method: &str) {
        let decl = TraitDecl {
            name: TraitName::from(name),
            docstring: None,
            type_params: vec![],
            methods: vec![TraitMethodSig {
                name: Symbol::from(method),
                docstring: None,
                params: vec![(Symbol::from("self"), TypeExpr::SelfType)],
                ret_type: TypeExpr::Named(cranelisp_types::TypeRef::new(
                    None,
                    TypeName::from("Bool"),
                )),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        tc.register_trait_decl_self(&decl).unwrap();
        tc.clear_transient_state();
    }

    // spec: spec/03-types.md §3.9.3 — a stacked trait-bound parameter annotation
    //   (`[:Eq :Display a]`) resolves the binder to a FRESH type variable
    //   constrained by ALL stacked traits (try-type-then-trait), accumulating
    //   both traits onto the defn's generalized `Scheme.constraints`.
    //
    // This is the TYPECHECK half of defect 0341 (the frontend parse half lands
    // separately). Constructed at the typecheck seam — the param annotation is a
    // `TypeExpr::Bounds([Eq, Display])` (the shape the frontend will emit), so
    // no frontend dependency. (FIXME 0346 carrier; FIXME 0341 typecheck half.)
    #[test]
    fn stacked_trait_bounds_param_accumulates_constraints() {
        let mut tc = tc_with_prims();
        register_marker_trait(&mut tc, "Eq", "eq?");
        register_marker_trait(&mut tc, "Display", "show");

        // (defn identity [:Eq :Display x] x) — the param `x` carries a run of
        // two stacked trait bounds; the body returns it unchanged so its type
        // stays the constrained binder var.
        let bounds = TypeExpr::Bounds(vec![
            cranelisp_types::TraitRef::new(None, TraitName::from("Eq")),
            cranelisp_types::TraitRef::new(None, TraitName::from("Display")),
        ]);
        let defn = Defn {
            name: Symbol::from("identity"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), Some(bounds))],
                body: Expr::var(Symbol::from("x"), Span::SYNTHETIC),
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let program = vec![TopLevel::Defn(defn)];
        tc.check_program_self(&program)
            .expect("defn with stacked trait-bound param must type-check");

        let scheme = match tc.symbol_table().get("identity") {
            Some(ModuleEntry::Def { scheme, .. }) => scheme.clone(),
            other => panic!("identity not a Def: {other:?}"),
        };

        // The scheme generalizes over the single binder var, and that var
        // carries BOTH trait constraints (Eq AND Display).
        assert_eq!(
            scheme.type_vars.len(), 1,
            "identity generalizes over its single constrained binder: {scheme:?}",
        );
        let binder = scheme.type_vars[0];
        let constraints = scheme
            .constraints
            .get(&binder)
            .unwrap_or_else(|| panic!("binder var {binder} has no constraints: {scheme:?}"));
        let names: std::collections::HashSet<&str> =
            constraints.iter().map(|t| t.name.as_ref()).collect();
        assert!(
            names.contains("Eq") && names.contains("Display"),
            "binder must be constrained by BOTH Eq and Display, got {names:?} \
             (FIXME 0341 typecheck half)",
        );
        // The function shape is `(Fn [a] a)` over that single binder.
        match &scheme.ty {
            Type::Fn(params, ret) => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0], Type::Var(binder));
                assert_eq!(ret.as_ref(), &Type::Var(binder));
            }
            other => panic!("identity scheme not a fn type: {other:?}"),
        }
    }

    // spec: spec/03-types.md §3.9.3 — Annotation Resolution (S86 D4). A SINGLE
    //   annotation `:Eq a` is ambiguous (could be a concrete type OR a trait).
    //   The typechecker first attempts to resolve it as a concrete type; if NO
    //   type with that name exists, it resolves as a TRAIT CONSTRAINT
    //   (try-type-then-trait). The frontend deliberately leaves a run-of-length-1
    //   annotation as the resolved `TypeExpr::Named` (NOT `Bounds`) — see
    //   `cranelisp-frontend::ast_builder::annotation_run_carrier` — delegating the
    //   disambiguation to this seam. This is the typecheck half of FIXME 0346 /
    //   0341 that was missing: before the D4 fix `:Eq a` errored
    //   `unknown type \`Eq\` (from module \`\`)` because the `Named` arm only
    //   tried type resolution and never fell back to a trait bound.
    #[test]
    fn single_trait_bound_param_resolves_via_try_type_then_trait() {
        let mut tc = tc_with_prims();
        register_marker_trait(&mut tc, "Eq", "eq?");

        // (defn use-it [:Eq a] a) — `a` carries a SINGLE `:Eq` annotation, which
        // the frontend leaves as `TypeExpr::Named(Eq)`. `Eq` is a trait, not a
        // type, so type resolution fails and the binder must resolve as a trait
        // constraint.
        let single = TypeExpr::Named(cranelisp_types::TypeRef::new(
            None,
            TypeName::from("Eq"),
        ));
        let defn = Defn {
            name: Symbol::from("use-it"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("a"), Some(single))],
                body: Expr::var(Symbol::from("a"), Span::SYNTHETIC),
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let program = vec![TopLevel::Defn(defn)];
        tc.check_program_self(&program).expect(
            "defn with a single trait-bound param `:Eq a` must type-check via \
             try-type-then-trait (spec §3.9.3, S86 D4)",
        );

        let scheme = match tc.symbol_table().get("use-it") {
            Some(ModuleEntry::Def { scheme, .. }) => scheme.clone(),
            other => panic!("use-it not a Def: {other:?}"),
        };
        // The single binder is generalized and carries the `Eq` constraint.
        assert_eq!(
            scheme.type_vars.len(), 1,
            "use-it generalizes over its single constrained binder: {scheme:?}",
        );
        let binder = scheme.type_vars[0];
        let constraints = scheme
            .constraints
            .get(&binder)
            .unwrap_or_else(|| panic!("binder var {binder} has no constraints: {scheme:?}"));
        let names: std::collections::HashSet<&str> =
            constraints.iter().map(|t| t.name.as_ref()).collect();
        assert!(
            names.contains("Eq"),
            "binder must be constrained by Eq (single-bound try-type-then-trait), \
             got {names:?} (S86 D4)",
        );
    }

    // spec: spec/03-types.md §3.9.3 — a single annotation naming a CONCRETE TYPE
    //   (`:Int x`) still resolves as a type, NOT a trait (the try-type-then-trait
    //   fallback only fires when type resolution fails). Negative guard that the
    //   D4 fix does not over-trigger and turn every single annotation into a
    //   constrained var.
    #[test]
    fn single_concrete_type_annotation_stays_concrete_neg() {
        let mut tc = tc_with_prims();
        // (defn id-int [:Int x] x) — `Int` is a real type, so the binder MUST be
        // the concrete `Int`, never a constrained var.
        let int_ann = TypeExpr::Named(cranelisp_types::TypeRef::new(
            None,
            TypeName::from("Int"),
        ));
        let defn = Defn {
            name: Symbol::from("id-int"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), Some(int_ann))],
                body: Expr::var(Symbol::from("x"), Span::SYNTHETIC),
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let program = vec![TopLevel::Defn(defn)];
        tc.check_program_self(&program)
            .expect("defn with concrete `:Int` param must type-check");

        let scheme = match tc.symbol_table().get("id-int") {
            Some(ModuleEntry::Def { scheme, .. }) => scheme.clone(),
            other => panic!("id-int not a Def: {other:?}"),
        };
        // No constrained generalization — the param is the concrete `Int`.
        assert!(
            scheme.constraints.is_empty(),
            "a concrete `:Int` annotation must NOT become a constrained var: {scheme:?}",
        );
        match &scheme.ty {
            Type::Fn(params, _) => assert_eq!(
                params[0],
                Type::Int,
                "param annotated `:Int` must be the concrete Int type, got {:?}",
                params[0],
            ),
            other => panic!("id-int scheme not a fn type: {other:?}"),
        }
    }

    // spec: design/typecheck/ast-annotation.md §10.2.3 — CheckResult has only
    // { warnings, display }. Structural guard: if a retired field
    // (method_resolutions / mono_defns / default_method_defns /
    // constrained_fn_names / expr_types) is reintroduced, this won't compile.
    #[test]
    fn check_result_slim_shape() {
        use crate::result::CheckResult;
        // Only the nameable fields are constructed; constructing with exactly
        // them (and reading them back) pins the slim shape.
        let r = CheckResult {
            warnings: Vec::new(),
            display: None,
            unresolved_dispatch: Vec::new(),
        };
        let _ = &r.warnings;
        let _ = &r.display;
        assert_eq!(r.warnings.len(), 0);
        assert!(r.display.is_none());
        assert!(r.unresolved_dispatch.is_empty());
    }

    // spec: spec/09-macros.md §9.3.4 — forward reference to undefined macro is
    // not expanded. Harvested from
    // `tests/legacy/ring3_repl.rs::r3_neg_forward_reference_not_expanded`
    // (FIXME 0125, REGRESSION-GUARD). Macro expansion is a frontend concern;
    // the typecheck-internal fact this guards is the consequence: calling a
    // name that was never defined as a macro is treated as an ordinary
    // application of an undefined symbol and MUST fail to typecheck (it is NOT
    // silently macro-expanded into success). This pins the "no implicit
    // forward-ref expansion" guarantee at the typecheck seam.
    #[test]
    fn r3_neg_forward_reference_not_expanded() {
        let mut tc = tc_with_prims();
        let sexps = cranelisp_frontend::parse("(defn use-it [] (not-yet-defined 42))")
            .expect("parse must succeed");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms must succeed");
        let result = tc.check(&program, &test_ctx(), cranelisp_types::ModuleStrategy::Additive);
        assert!(
            result.is_err(),
            "a forward reference to an undefined name must fail to typecheck, \
             not be silently macro-expanded; got Ok"
        );
    }

    // =========================================================================
    // S82 harvest (FIXME 0134): `assert_type_error(...)` callsites from the
    // quarantined legacy ring0/ring1 files, reduced to direct `tc.check()`
    // Err-expecting unit tests. Each pins a typecheck-internal rejection that
    // is not separately covered by the existing infer/program unit suite.
    // Source programs are reproduced verbatim from the legacy file; assertions
    // assert ONLY that the program fails to typecheck (error message text is
    // not pinned — the legacy `assert_type_error` passed `""`).
    // =========================================================================

    /// Parse + build a whole program from source and assert it fails to check.
    /// Mirrors the legacy `assert_type_error(src, "")` helper at the typecheck
    /// seam (no REPL / no binary).
    fn assert_check_rejects(src: &str) {
        let mut tc = tc_with_prims();
        let sexps = cranelisp_frontend::parse(src).expect("parse must succeed");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms must succeed");
        let result = tc.check(&program, &test_ctx(), cranelisp_types::ModuleStrategy::Additive);
        assert!(result.is_err(), "expected a type error for {src:?}, got Ok");
    }

    // spec: spec/03-types.md §3.5 — Float cannot be passed to an Int-typed
    // primitive. Harvested from `tests/legacy/ring0.rs::float_type_error_mixed`.
    #[test]
    fn harvest_float_type_error_mixed() {
        assert_check_rejects("(defn main [] (add-i64 1 1.5))");
    }

    // spec: spec/03-types.md §3.5 — String cannot be passed where Int is
    // expected. Harvested from
    // `tests/legacy/ring1.rs::error_string_where_int_expected`.
    #[test]
    fn harvest_error_string_where_int_expected() {
        assert_check_rejects("(defn main [] (add-i64 \"hello\" 1))");
    }

    // spec: spec/03-types.md §3.5 — Int cannot be passed where String is
    // expected (str-len arg). Harvested from
    // `tests/legacy/ring1.rs::error_int_where_string_expected`.
    #[test]
    fn harvest_error_int_where_string_expected() {
        assert_check_rejects("(defn main [] (str-len 42))");
    }

    // spec: spec/05-definitions.md §5.2.7 — a constructor field's declared type
    // is enforced at the call site (Bool where the field is :Int). Harvested
    // from `tests/legacy/ring1.rs::error_adt_constructor_wrong_type`.
    #[test]
    fn harvest_error_adt_constructor_wrong_type() {
        assert_check_rejects(
            "(deftype Point [:Int x :Int y]) (defn main [] (match (Point true 2) [(Point x y) x]))",
        );
    }

    // spec: spec/04-expressions.md §4.4 — `if` branches must unify; a String
    // then-branch and an Int else-branch is a type error. Harvested from
    // `tests/legacy/ring1.rs::error_if_branches_type_mismatch_string_int`.
    #[test]
    fn harvest_error_if_branches_type_mismatch_string_int() {
        assert_check_rejects("(defn main [] (if true \"hello\" 42))");
    }

    // spec: spec/07-traits.md §7.8 — a constrained-fn template is NOT directly
    // callable (only its monomorphised variants are).
    //
    // **Re-pointed for the S83 reshape (FIXME 0356/0357, Principle 20).** The
    // S82 `mark_constrained_template` flip-and-clear sole-writer and the
    // `assert_well_formed` phantom-slot guard are RETIRED — callability is now a
    // structural property of `UserFnState`, so the once-illegal pairing (a
    // constrained template holding a callable slot) is unconstructable rather
    // than asserted-against. This is now a structural guard: a `Concrete`
    // UserFn is callable through its slot; a `Constrained` UserFn carries no
    // slot, so `callable_got_slot()` answers `None` by construction — a
    // cross-module constrained call can never lower to a null `call_indirect`
    // (the SIGSEGV) because there is no slot to read.
    #[test]
    fn constrained_template_carries_no_callable_slot() {
        use cranelisp_types::ConstrainedFn as CF;
        // A concrete user fn IS callable through its slot.
        let concrete: ModuleEntry = ModuleEntry::def(
            crate::scheme::mono(Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0)))),
            DefKind::UserFn { fn_state: UserFnState::Concrete { got_slot: 7, mode_summary: None } },
        )
        .build();
        assert_eq!(concrete.callable_got_slot(), Some(7));
        assert!(!concrete.is_constrained_template());

        // A constrained template carries NO slot — structurally unconstructable
        // to hold one (the `Constrained` variant has no `got_slot` field).
        let cf = CF {
            variant: DefnVariant {
                params: vec![(Symbol::from("a"), None)],
                body: Expr::var(Symbol::from("a"), span(0, 1)),
                span: span(0, 1),
            },
            scheme: crate::scheme::mono(Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0)))),
        };
        let template: ModuleEntry = ModuleEntry::def(
            crate::scheme::mono(Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0)))),
            DefKind::UserFn { fn_state: UserFnState::Constrained(Box::new(cf)) },
        )
        .build();
        assert!(template.is_constrained_template());
        assert_eq!(template.callable_got_slot(), None);
    }

    // spec: spec/07-traits.md §7.8 — polymorphic-result hop monomorphisation
    //
    // FIXME 0373 (Tier 1) + /arch ruling (A): the durable correct fix for the
    // polymorphic-result-hop SIGSEGV is MONOMORPHISATION (not a runtime tag).
    // A polymorphic-result hop reached at a concrete instantiation must produce
    // a mono instance whose RESULT type is CONCRETE (`Int`), so the backend's RC
    // classifier sees `NeverHeap` instead of `Type::Var -> Mixed` and never emits
    // the unsound `< 1024` guarded RC-inc that dereferences a negative/large Int.
    //
    // The repro is a two-hop chain: `main` calls `(h1 neg)`; `h1` calls `(h2 f)`;
    // `h2` calls `(f 5)`. Both `h1` and `h2` have polymorphic (unbound type var)
    // result types when compiled generically. This test asserts that, after
    // checking the program, the symbol table carries mono instances for BOTH
    // hops (the concrete-instantiation propagation through the chain), and that
    // each mono instance's result type is concrete `Int`, NOT a `Type::Var`.
    #[test]
    fn polymorphic_result_hops_monomorphise_with_concrete_result_type() {
        let mut tc = tc_with_prims();
        // tc_with_prims glob-imports `primitives`, so `sub-i64` is a bare name —
        // no stdlib dependency, no (import ...) form needed.
        let src = "\
            (defn neg [:primitives/Int x] :primitives/Int (sub-i64 0 x))\n\
            (defn h1 [f] (h2 f))\n\
            (defn h2 [f] (f 5))\n\
            (defn main [] (h1 neg))";
        let sexps = cranelisp_frontend::parse(src).expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");

        tc.check_program_self(&program)
            .expect("two-hop polymorphic-result program must type-check");

        // Both hops must have a monomorphised instance. FIXME 0519: the mono name
        // is home-qualified with a lossless recursive sig — the `Fn`-typed `f`
        // param is now RECURSED (not dropped), so the names are
        // `test/h1$Fn(Int;Int)` / `test/h2$Fn(Int;Int)`. The presence of an `h2$`
        // mono is the multi-hop propagation guarantee: `h2` only became concrete
        // during `h1`'s recheck.
        let mono = tc.mono_defn_names();
        let mono_strs: Vec<String> = mono.iter().map(|s| s.as_ref().to_string()).collect();
        assert!(
            mono_strs.iter().any(|n| n.contains("h1$")),
            "h1 must be monomorphised (FIXME 0373 Tier 1); mono entries: {mono_strs:?}",
        );
        assert!(
            mono_strs.iter().any(|n| n.contains("h2$")),
            "h2 must ALSO be monomorphised — the concrete instantiation must \
             propagate through the hop chain (FIXME 0373 Tier 1, multi-hop); \
             mono entries: {mono_strs:?}",
        );

        // Each hop's mono instance must carry a CONCRETE `Int` result type — the
        // whole point of the fix. A `Type::Var` result here would reproduce the
        // RC-guard SIGSEGV at codegen.
        let assert_concrete_int_result = |tc: &TestFixture, prefix: &str| {
            let st = tc.symbol_table();
            let (name, entry) = st
                .all_symbols()
                // FIXME 0519: mono name home-qualified; match the `hN$` infix.
                .find(|(n, _)| n.as_ref().contains(prefix))
                .unwrap_or_else(|| panic!("no mono entry for {prefix}"));
            match entry {
                ModuleEntry::Def { scheme, .. } => match &scheme.ty {
                    Type::Fn(_, ret) => assert_eq!(
                        ret.as_ref(),
                        &Type::Int,
                        "{name}'s mono result must be concrete Int, not {:?} \
                         (FIXME 0373 Tier 1 — a Type::Var result reproduces the \
                         RC-classification SIGSEGV)",
                        ret,
                    ),
                    other => panic!("{name} mono scheme not a Fn: {other:?}"),
                },
                other => panic!("{name} mono entry not a Def: {other:?}"),
            }
        };
        assert_concrete_int_result(&tc, "h1$");
        assert_concrete_int_result(&tc, "h2$");
    }

    // spec: spec/07-traits.md §7.8 — CROSS-MODULE polymorphic-result hop mono
    //
    // FIXME 0373 (Tier 1.5) + /arch ruling (A): the cross-module analogue of the
    // Tier-1 fix above. When the intervening hops `h1`/`h2` live in an IMPORTED
    // module, the top-level pass (`collect_imported_constrained_calls`) collects
    // `(h1 neg)` and monomorphises `h1` re-checking its body in `h1`'s DEFINING
    // module (`hop`). The inner hop `(h2 f)` only becomes concrete during that
    // recheck, so `monomorphise_inner_parametric_hops` must follow the import
    // chain and re-monomorphise `h2` IN ITS DEFINING SCOPE (`hop`) — NOT in the
    // caller's module, where `h2` is not even imported.
    //
    // The bug this guards: `recheck_body_for_mono` restores `state.current_module`
    // to the caller (`caller`) BEFORE `monomorphise_inner_parametric_hops` runs.
    // The pre-fix gate computed `inner_home` against `recheck_module` (`hop`), so
    // a same-`recheck_module` inner hop got `None`, which made the recursive
    // `monomorphise_call` look `h2` up in the (restored) caller module — where it
    // does not exist → `None` → `h2` keeps a `Type::Var` result → RC-guard
    // SIGSEGV one hop deeper. The fix gates on `state.current_module` so a hop in
    // a different (defining) module is rooted at `Some(callee_home)`.
    //
    // This asserts BOTH cross-module hops monomorphise with a concrete `Int`
    // result, the mono entries living in the CALLER's module (their codegen home).
    #[test]
    fn cross_module_polymorphic_result_hops_monomorphise_with_concrete_result_type() {
        let mut tc = tc_with_prims();
        let hop = ModuleFullPath::from("hop");
        let caller = ModuleFullPath::from("caller");

        // --- DEFINING module `hop`: the two polymorphic-result hops ------------
        // (defn h1 [f] (h2 f)) ; result type generalizes to an unbound var
        // (defn h2 [f] (f 5))  ; result type generalizes to an unbound var
        tc.set_current_module(hop.clone());
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
        let hop_src = "\
            (defn h1 [f] (h2 f))\n\
            (defn h2 [f] (f 5))";
        let hop_sexps = cranelisp_frontend::parse(hop_src).expect("parse hop");
        let hop_program = cranelisp_frontend::build_forms(&hop_sexps).expect("build hop");
        tc.check_program_self(&hop_program)
            .expect("hop module must type-check");

        // --- CALLER module: imports `h1`, defines `neg`, calls `(h1 neg)` ------
        tc.set_current_module(caller.clone());
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
        seed_specific_import(&mut tc, &hop, &["h1"]);
        let caller_src = "\
            (defn neg [:primitives/Int x] :primitives/Int (sub-i64 0 x))\n\
            (defn main [] (h1 neg))";
        let caller_sexps = cranelisp_frontend::parse(caller_src).expect("parse caller");
        let caller_program = cranelisp_frontend::build_forms(&caller_sexps).expect("build caller");
        tc.check_program_self(&caller_program)
            .expect("cross-module two-hop polymorphic-result program must type-check");

        // Both cross-module hops must be monomorphised, with their mono entries
        // registered in the CALLER's module (the 0355 caller-GOT-slot home).
        let assert_concrete_int_result = |tc: &TestFixture, prefix: &str| {
            let module = tc.modules.get(&caller).unwrap();
            let (name, entry) = module
                .all_symbols()
                // FIXME 0519: mono name home-qualified; match the `hN$` infix.
                .find(|(n, _)| n.as_ref().contains(prefix))
                .unwrap_or_else(|| {
                    let all: Vec<String> = module
                        .all_symbols()
                        .map(|(n, _)| n.as_ref().to_string())
                        .collect();
                    panic!("no mono entry for {prefix} in caller; symbols: {all:?}")
                });
            match entry {
                ModuleEntry::Def { scheme, kind, .. } => {
                    assert!(
                        matches!(
                            kind.as_ref(),
                            DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }
                        ),
                        "{name} mono must be a Concrete UserFn (its own GOT slot), got {kind:?}",
                    );
                    match &scheme.ty {
                        Type::Fn(_, ret) => assert_eq!(
                            ret.as_ref(),
                            &Type::Int,
                            "{name}'s CROSS-MODULE mono result must be concrete Int, \
                             not {ret:?} (FIXME 0373 Tier 1.5 — a Type::Var result \
                             reproduces the cross-module RC-classification SIGSEGV)",
                        ),
                        other => panic!("{name} mono scheme not a Fn: {other:?}"),
                    }
                }
                other => panic!("{name} mono entry not a Def: {other:?}"),
            }
        };
        assert_concrete_int_result(&tc, "h1$");
        assert_concrete_int_result(&tc, "h2$");
    }

    // =====================================================================
    // S84 Wave 1b (FIXME 0374/0378) — TOTAL slot⟺concrete: retire the
    // result-only-var carve-out; test-fns as mono roots; scoped §3.11.1.
    // =====================================================================

    /// Register an `Option` ADT (`None` | `(Some [v])`) in the current `test`
    /// module — the result-only-var shape needs `None`. Returns the TopLevel.
    fn option_typedef() -> TopLevel {
        TopLevel::TypeDef {
            name: TypeName::from("Option"),
            docstring: None,
            type_params: vec![Symbol::from("a")],
            constructors: vec![
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
                        name: Symbol::from("v"),
                        type_expr: TypeExpr::TypeVar(Symbol::from("a")),
                        span: Span::SYNTHETIC,
                    }],
                    span: Span::SYNTHETIC,
                },
            ],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        }
    }

    // spec: spec/03-types.md §3.11 / FIXME 0374/0378 — the slot gate is TOTAL
    //       (slot ⟺ is_concrete()). A RESULT-ONLY-var def (`(defn empty [] [])`
    //       → `(Fn [] (Vec a))`) is now slot-less `Polymorphic`, NOT
    //       `Concrete`-with-a-slot. This pins the carve-out retirement: the
    //       former `fn_type_is_monomorphisable_from_params` kept such defs
    //       `Concrete`; the TOTAL gate routes them to `Polymorphic`.
    #[test]
    fn result_only_var_def_is_polymorphic_not_concrete() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();
        // (defn empty [] []) — `[]` is `(Vec a)`, `a` is result-only and free.
        // Under the TOTAL slot gate this is slot-less `Polymorphic`.
        let empty = TopLevel::Defn(make_defn(
            "empty",
            vec![],
            vec![],
            Expr::VecLit { elements: vec![], span: span(10, 12), inferred_type: None },
            Visibility::Public,
            span(8, 13),
        ));
        tc.check(&[empty], &ctx, ModuleStrategy::Additive).unwrap();
        let table = tc.symbol_table();
        let entry = table.get("empty").expect("empty registered");
        assert!(
            matches!(
                entry,
                ModuleEntry::Def { kind, .. }
                    if matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state: UserFnState::Polymorphic(_) }
                    )
            ),
            "a result-only-var def `(defn empty [] [])` must be slot-less \
             `Polymorphic` under the TOTAL slot gate (carve-out retired), got {entry:?}",
        );
        assert_eq!(
            entry.callable_got_slot(),
            None,
            "a `Polymorphic` (non-concrete) def carries NO slot (slot ⟺ concrete)",
        );
    }

    // spec: spec/03-types.md §3.11.3 / FIXME 0378 issue 3 — a `test-*` fn is
    //       registered as a monomorphisation ROOT. The degenerate
    //       `(defn test-x [] None)` (type `(Fn [] (Option a))`) is slot-less
    //       `Polymorphic`, but the test-fn-root pass mints a concrete
    //       `(Fn [] (Option String))` instance UNDER THE BARE NAME with a slot
    //       — so discovery (which reads `callable_got_slot()`) still finds it.
    #[test]
    fn test_fn_registered_as_mono_root_gets_concrete_instance() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();
        // (deftype Option None (Some [v])) + (defn test-x [] None)
        let test_x = TopLevel::Defn(make_defn(
            "test-x",
            vec![],
            vec![],
            Expr::var(Symbol::from("None"), span(40, 44)),
            Visibility::Public,
            span(38, 45),
        ));
        tc.check(&[option_typedef(), test_x], &ctx, ModuleStrategy::Additive)
            .unwrap();
        let table = tc.symbol_table();
        let entry = table.get("test-x").expect("test-x registered");
        // After the mono-root pass the BARE-name entry is `Concrete{slot}` with
        // a concrete `(Fn [] (Option String))` scheme.
        entry
            .callable_got_slot()
            .expect("test-x must carry a concrete callable slot after mono-root minting");
        match entry {
            ModuleEntry::Def { scheme, kind, .. } => {
                assert!(
                    matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }
                    ),
                    "test-x must be `Concrete{{slot}}` after mono-root minting, got {kind:?}",
                );
                // Scheme is the concrete `(Fn [] (Option String))`.
                match &scheme.ty {
                    Type::Fn(params, ret) => {
                        assert!(params.is_empty(), "test-x is nullary");
                        match ret.as_ref() {
                            Type::ADT(fqtn, args) => {
                                assert_eq!(fqtn.name.as_ref(), "Option");
                                assert_eq!(args.len(), 1);
                                assert!(
                                    matches!(args[0], Type::String),
                                    "the minted instance pins the result var to \
                                     String — got {:?}",
                                    args[0],
                                );
                            }
                            other => panic!("test-x result not (Option …): {other:?}"),
                        }
                    }
                    other => panic!("test-x scheme not a Fn: {other:?}"),
                }
            }
            other => panic!("test-x entry not a Def: {other:?}"),
        }
    }

    // spec: spec/05-definitions.md §5.1.2 — a caller whose body calls an
    //       overloaded/multi-arity fn must generalize over the SETTLED return
    //       type of that call, NOT a still-deferred fresh var. `(h 7)` targets an
    //       overloaded base, so `infer.rs` DEFERS resolution (a fresh return var
    //       pushed onto `pending_overload_resolutions`); it is
    //       `resolve_pending_overloads` that unifies that var with the selected
    //       variant's concrete `Int` return — but that drain runs AFTER the
    //       FIXME-0349 `regeneralize_defn_schemes` that fixes caller schemes, so
    //       the caller is generalized while its return var is still free. This
    //       test pins the finalize SCOPED-RESLOT fix (S110 C-4): the
    //       `regeneralize_only_polymorphic` pass, run after the overload drain,
    //       re-settles a still-`Polymorphic` caller whose scheme is now concrete
    //       to `(Fn [] Int)` `Concrete{slot}`. If that scoped pass is removed,
    //       `caller` stays slot-less `Polymorphic` (the e2e "entry module has no
    //       `main` function" misdirect,
    //       `spec_05_definitions::multi_arity_call_from_main_batch_no_main_neg`).
    // defect: class=wrong-reject locus=crates/cranelisp-typecheck/src/program/finalize.rs::finalize_check_result_inner found=S110 owner=/dev
    #[test]
    fn overloaded_call_caller_generalizes_over_resolved_return_not_deferred_var() {
        let mut tc = tc_with_prims();
        let int_ann = || {
            Some(TypeExpr::Named(cranelisp_types::TypeRef::new(
                None,
                TypeName::from("Int"),
            )))
        };
        // (defn h ([:Int x] x) ([:Int x :Int y] x)) — an overloaded multi-arity fn.
        let h = TopLevel::Defn(make_multi_defn(
            "h",
            vec![
                DefnVariant {
                    params: vec![(Symbol::from("x"), int_ann())],
                    body: Expr::var(Symbol::from("x"), span(10, 11)),
                    span: span(5, 12),
                },
                DefnVariant {
                    params: vec![
                        (Symbol::from("x"), int_ann()),
                        (Symbol::from("y"), int_ann()),
                    ],
                    body: Expr::var(Symbol::from("x"), span(20, 21)),
                    span: span(15, 22),
                },
            ],
            span(0, 23),
        ));
        // (defn caller [] (h 7)) — a nullary caller whose ONLY body form is the
        // deferred overloaded call. Its return type is knowable only after
        // `resolve_pending_overloads` pins `(h 7)`'s fresh var to `Int`.
        let caller = TopLevel::Defn(make_defn(
            "caller",
            vec![],
            vec![],
            Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("h"), span(31, 32))),
                args: vec![Expr::IntLit {
                    value: 7,
                    span: span(33, 34),
                    inferred_type: None,
                }],
                span: span(30, 35),
                resolved_call: None,
                inferred_type: None,
            },
            Visibility::Public,
            span(25, 36),
        ));
        tc.check(&[h, caller], &test_ctx(), cranelisp_types::ModuleStrategy::Additive)
            .unwrap();
        let table = tc.symbol_table();
        let entry = table.get("caller").expect("caller registered");
        // The caller must be `Concrete{slot}` — NOT a spuriously-`Polymorphic`
        // scheme with the deferred return var quantified.
        match entry {
            ModuleEntry::Def { scheme, kind, .. } => {
                assert!(
                    matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }
                    ),
                    "caller of an overloaded fn must be `Concrete{{slot}}` (its \
                     deferred return var is pinned by `resolve_pending_overloads`, \
                     then the scoped `regeneralize_only_polymorphic` reslots it \
                     concrete) — got {kind:?}",
                );
                match &scheme.ty {
                    Type::Fn(params, ret) => {
                        assert!(params.is_empty(), "caller is nullary");
                        assert!(
                            matches!(ret.as_ref(), Type::Int),
                            "caller returns the variant's concrete `Int`, not a \
                             quantified var — got {:?}",
                            ret,
                        );
                    }
                    other => panic!("caller scheme not a Fn: {other:?}"),
                }
                assert!(
                    scheme.type_vars.is_empty(),
                    "caller's concrete scheme quantifies NO vars — the deferred \
                     overload return var must be settled, not generalized; got \
                     type_vars {:?}",
                    scheme.type_vars,
                );
            }
            other => panic!("caller entry not a Def: {other:?}"),
        }
        entry
            .callable_got_slot()
            .expect("a Concrete caller carries a callable slot");
    }

    // spec: spec/05-definitions.md §5.1.2 — the S110 finalize DUTY-SPLIT seam.
    //   A deferred-overload return var read in a VALUE position
    //   (`(let [r (h 7)] r)`) is unified to the selected variant's concrete
    //   return ONLY by `resolve_pending_overloads` (the single drain), so the
    //   §3.11.1 value-position scan MUST run POST-drain. Pinned here at unit
    //   tier: a single-clause caller whose body binds the deferred overload call
    //   in a `let` and returns it MUST check CLEAN (no spurious `ambiguous`) and
    //   settle `Concrete` `Int`. On a revert that runs the value scan PRE-drain
    //   (the pre-split composition), `r` carries the still-unresolved fresh
    //   return var minted at `infer.rs:585` and the scan false-rejects — this
    //   test flips RED, guarding the split against re-collapse (B1 wrong-reject
    //   at the seam; the e2e face is
    //   `spec_03_types::multi_arity_overload_call_in_let_not_spuriously_ambiguous`).
    // defect: class=wrong-reject locus=crates/cranelisp-typecheck/src/program/finalize.rs::finalize_check_result_inner found=S110 owner=/dev
    #[test]
    fn deferred_overload_return_var_in_let_value_resolves_post_drain() {
        let mut tc = tc_with_prims();
        let int_ann = || {
            Some(TypeExpr::Named(cranelisp_types::TypeRef::new(
                None,
                TypeName::from("Int"),
            )))
        };
        // (defn h ([:Int x] x) ([:Int x :Int y] x)) — the overloaded base.
        let h = TopLevel::Defn(make_multi_defn(
            "h",
            vec![
                DefnVariant {
                    params: vec![(Symbol::from("x"), int_ann())],
                    body: Expr::var(Symbol::from("x"), span(10, 11)),
                    span: span(5, 12),
                },
                DefnVariant {
                    params: vec![
                        (Symbol::from("x"), int_ann()),
                        (Symbol::from("y"), int_ann()),
                    ],
                    body: Expr::var(Symbol::from("x"), span(20, 21)),
                    span: span(15, 22),
                },
            ],
            span(0, 23),
        ));
        // (defn caller [] (let [r (h 7)] r)) — the deferred overload call bound in
        // a `let` VALUE position, then returned. This is the exact B1 shape.
        let call = Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("h"), span(41, 42))),
            args: vec![Expr::IntLit { value: 7, span: span(43, 44), inferred_type: None }],
            span: span(40, 45),
            resolved_call: None,
            inferred_type: None,
        };
        let body = Expr::Let {
            bindings: vec![(Symbol::from("r"), call)],
            body: Box::new(Expr::var(Symbol::from("r"), span(47, 48))),
            span: span(35, 49),
            inferred_type: None,
        };
        let caller = TopLevel::Defn(make_defn(
            "caller",
            vec![],
            vec![],
            body,
            Visibility::Public,
            span(25, 50),
        ));
        tc.check(&[h, caller], &test_ctx(), ModuleStrategy::Additive).expect(
            "a deferred-overload call bound in a `let` VALUE position must NOT be \
             spuriously rejected — the §3.11.1 value scan runs POST-drain so `r` \
             is settled `Int` before the verdict (B1)",
        );
        let table = tc.symbol_table();
        let entry = table.get("caller").expect("caller registered");
        match entry {
            ModuleEntry::Def { scheme, kind, .. } => {
                assert!(
                    matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }
                    ),
                    "caller settles `Concrete` (its `let`-bound overload return is \
                     pinned to `Int` by the drain, then reslotted by \
                     `regeneralize_only_polymorphic`) — got {kind:?}",
                );
                match &scheme.ty {
                    Type::Fn(params, ret) => {
                        assert!(params.is_empty(), "caller is nullary");
                        assert!(
                            matches!(ret.as_ref(), Type::Int),
                            "caller returns the variant's concrete `Int` — got {ret:?}",
                        );
                    }
                    other => panic!("caller scheme not a Fn: {other:?}"),
                }
            }
            other => panic!("caller entry not a Def: {other:?}"),
        }
    }

    // spec: spec/03-types.md §3.11.1 — a CODEGEN-REACHING unpinned polymorphic
    //       value is an ambiguity error. A `let`-bound `None` whose type stays
    //       `(Option a)` (the `match` scrutinises only the tag) must be
    //       REJECTED. Mirrors the e2e
    //       `regression::mono_ambiguous_unconstrained_top_level_var_rejected_neg`.
    #[test]
    fn ambiguity_check_rejects_codegen_reaching_unpinned_let_binding() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();
        // (defn m [] (let [x None] (match x [None 0 (Some _) 1])))
        // `x : (Option a)`, `a` unpinned (match reads only the tag) — §3.11.1.
        let body = Expr::Let {
            bindings: vec![(
                Symbol::from("x"),
                Expr::var(Symbol::from("None"), span(60, 64)),
            )],
            body: Box::new(Expr::Match {
                scrutinee: Box::new(Expr::var(Symbol::from("x"), span(70, 71))),
                arms: vec![
                    cranelisp_types::MatchArm {
                        pattern: cranelisp_types::Pattern::Constructor {
                            name: cranelisp_types::SymbolRef::new(None, Symbol::from("None")),
                            bindings: vec![],
                            span: span(73, 77),
                        },
                        body: Expr::IntLit { value: 0, span: span(78, 79), inferred_type: None },
                        span: span(73, 79),
                    },
                    cranelisp_types::MatchArm {
                        pattern: cranelisp_types::Pattern::Constructor {
                            name: cranelisp_types::SymbolRef::new(None, Symbol::from("Some")),
                            bindings: vec![Symbol::from("_")],
                            span: span(82, 87),
                        },
                        body: Expr::IntLit { value: 1, span: span(88, 89), inferred_type: None },
                        span: span(82, 89),
                    },
                ],
                span: span(66, 90),
                compiler_generated: false,
                inferred_type: None,
            }),
            span: span(55, 91),
            inferred_type: None,
        };
        let m = TopLevel::Defn(make_defn(
            "m", vec![], vec![], body, Visibility::Public, span(50, 92),
        ));
        let result = tc.check(&[option_typedef(), m], &ctx, ModuleStrategy::Additive);
        let err = result.expect_err(
            "a codegen-reaching unpinned `let`-bound `(Option a)` value must be \
             rejected as ambiguous (§3.11.1)",
        );
        let msg = format!("{err}").to_lowercase();
        assert!(
            msg.contains("ambiguous"),
            "the §3.11.1 rejection must name 'ambiguous'; got: {msg}",
        );
    }

    // spec: spec/03-types.md §3.11.3 — a NAMED polymorphic defn with
    //       result-only free vars is ADMITTED (sound, dead-for-codegen). The
    //       §3.11.1 check MUST NOT fire on `(defn ambig [] None)`. Mirrors the
    //       e2e `regression::mono_ambiguous_neg_does_not_reach_codegen`.
    #[test]
    fn ambiguity_check_admits_named_polymorphic_defn() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();
        // (defn ambig [] None) — `(Fn [] (Option a))`, result-only var. ADMIT.
        let ambig = TopLevel::Defn(make_defn(
            "ambig",
            vec![],
            vec![],
            Expr::var(Symbol::from("None"), span(40, 44)),
            Visibility::Public,
            span(38, 45),
        ));
        tc.check(&[option_typedef(), ambig], &ctx, ModuleStrategy::Additive)
            .expect("a named result-only-var defn is sound and must be admitted (§3.11.3)");
        // It is slot-less `Polymorphic` (NOT a `test-*` fn, so no mono root).
        let table = tc.symbol_table();
        let entry = table.get("ambig").expect("ambig registered");
        assert!(
            matches!(
                entry,
                ModuleEntry::Def { kind, .. }
                    if matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state: UserFnState::Polymorphic(_) }
                    )
            ),
            "a named result-only-var defn is slot-less `Polymorphic`, got {entry:?}",
        );
    }

    // =====================================================================
    // §7(e) POSITION-COMPLETE §3.11.1 (S84, FIXME 0379/0380 → tightened 0386).
    // An ADT-with-free-var (`(Option a)`, `a` unpinned) reaching a codegen
    // value position in a NON-`let` slot — match scrutinee, fn-call arg, vec
    // element, ctor field, if-branch — must be REJECTED as ambiguous. The old
    // scanner only checked `let` bindings; the position-complete scanner checks
    // every value-producing child. The `let`-position case stays an asserted
    // positive control
    // (`ambiguity_check_rejects_codegen_reaching_unpinned_let_binding`).
    //
    // TIGHTENED §3.11.1 (commit 2290aa9, FIXME 0386): the verdict is FULL
    // CONCRETENESS (`!ty.is_concrete()`) — NO representation exemption. A
    // free-at-root `(Vec a)`/`(Fn [a] a)` value at a codegen-reaching position
    // is now REJECTED too (it was admitted under the old
    // representation-determinacy verdict). Result-only free vars (a definition's
    // own scheme vars, §3.11.3) stay admitted — they are quantified, pinned
    // per-instantiation, not free-at-root.
    // =====================================================================

    /// `(defn identity [x] x)` — the polymorphic identity, used to produce an
    /// unpinned `(Option a)` value as `(identity None)` (the call does not pin
    /// the var; `identity`'s result is `a`, instantiated to `(Option a)`).
    fn identity_defn() -> TopLevel {
        TopLevel::Defn(make_defn(
            "identity",
            vec![Symbol::from("x")],
            vec![None],
            Expr::var(Symbol::from("x"), span(20, 21)),
            Visibility::Public,
            span(10, 22),
        ))
    }

    /// `(identity None)` — an `Apply` producing the unpinned `(Option a)` value.
    fn identity_none(call_span: Span) -> Expr {
        Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("identity"), span(call_span.start, call_span.start + 8))),
            args: vec![Expr::var(Symbol::from("None"), span(call_span.start + 9, call_span.end))],
            span: call_span,
            resolved_call: None,
            inferred_type: None,
        }
    }

    /// `(defn consume [y] 0)` — discards its arg, returns a concrete `Int`. Used
    /// to bury an ambiguous value in a value position while keeping the enclosing
    /// defn `m`'s OWN result type concrete (`(Fn [] Int)`, no free var) so the
    /// offending var is genuinely free-at-root, not quantified into `m`'s scheme.
    fn consume_defn() -> TopLevel {
        TopLevel::Defn(make_defn(
            "consume",
            vec![Symbol::from("y")],
            vec![None],
            Expr::IntLit { value: 0, span: span(30, 31), inferred_type: None },
            Visibility::Public,
            span(28, 32),
        ))
    }

    /// Wrap `inner` (the value position under test) in `(consume <inner>)` so the
    /// enclosing `m`'s result is concrete `Int`. Returns the wrapping body.
    fn consume_wrap(inner: Expr) -> Expr {
        let inner_span = inner.span();
        Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("consume"), span(101, 108))),
            args: vec![inner],
            span: span(100, inner_span.end + 1),
            resolved_call: None,
            inferred_type: None,
        }
    }

    /// Assert checking `[Option, identity, consume, defn m with `body`]` rejects
    /// with an "ambiguous" error (the §3.11.1 position-complete verdict). `m`'s
    /// own result is kept concrete by `consume_wrap` so the offending var is
    /// free-at-root (not a quantified scheme var).
    fn assert_ambiguous(body: Expr, what: &str) {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();
        let m = TopLevel::Defn(make_defn(
            "m", vec![], vec![], body, Visibility::Public, span(100, 200),
        ));
        let result = tc.check(
            &[option_typedef(), identity_defn(), consume_defn(), m],
            &ctx,
            ModuleStrategy::Additive,
        );
        let err = result.err().unwrap_or_else(|| {
            panic!("an unpinned `(Option a)` value in a {what} must be rejected as ambiguous (§3.11.1)")
        });
        let msg = format!("{err}").to_lowercase();
        assert!(
            msg.contains("ambiguous"),
            "the §3.11.1 rejection at a {what} must name 'ambiguous'; got: {msg}",
        );
    }

    // spec: spec/03-types.md §3.11.1 — MATCH SCRUTINEE position (non-`let`).
    #[test]
    fn mixed_adt_free_var_in_match_scrutinee_is_ambiguous() {
        // (defn m [] (match (identity None) [None 0 (Some _) 1]))
        let body = Expr::Match {
            scrutinee: Box::new(identity_none(span(110, 124))),
            arms: vec![
                cranelisp_types::MatchArm {
                    pattern: cranelisp_types::Pattern::Constructor {
                        name: cranelisp_types::SymbolRef::new(None, Symbol::from("None")),
                        bindings: vec![],
                        span: span(126, 130),
                    },
                    body: Expr::IntLit { value: 0, span: span(131, 132), inferred_type: None },
                    span: span(126, 132),
                },
                cranelisp_types::MatchArm {
                    pattern: cranelisp_types::Pattern::Constructor {
                        name: cranelisp_types::SymbolRef::new(None, Symbol::from("Some")),
                        bindings: vec![Symbol::from("_")],
                        span: span(135, 140),
                    },
                    body: Expr::IntLit { value: 1, span: span(141, 142), inferred_type: None },
                    span: span(135, 142),
                },
            ],
            span: span(105, 145),
            compiler_generated: false,
            inferred_type: None,
        };
        assert_ambiguous(body, "match scrutinee");
    }

    // spec: spec/03-types.md §3.11.1 — FUNCTION-CALL ARGUMENT position (non-`let`).
    #[test]
    fn mixed_adt_free_var_in_call_arg_is_ambiguous() {
        // (defn m [] (consume (identity None))) — `(identity None)` : `(Option a)`,
        // unpinned (the call to `consume` discards its arg, pins nothing). `m`'s
        // result is concrete `Int` (consume returns 0), so `a` is free-at-root.
        let body = consume_wrap(identity_none(span(115, 129)));
        assert_ambiguous(body, "call argument");
    }

    // spec: spec/03-types.md §3.11.1 — VEC ELEMENT position (non-`let`). The
    // value INSIDE the vec is `(Option a)`-with-free-var (the vec's own type
    // `(Vec (Option a))` is admitted, but its element is checked too).
    #[test]
    fn mixed_adt_free_var_in_vec_element_is_ambiguous() {
        // (defn m [] (consume [(identity None)]))
        let body = consume_wrap(Expr::VecLit {
            elements: vec![identity_none(span(116, 130))],
            span: span(115, 131),
            inferred_type: None,
        });
        assert_ambiguous(body, "vec element");
    }

    // spec: spec/03-types.md §3.11.1 — CONSTRUCTOR FIELD position (non-`let`).
    #[test]
    fn mixed_adt_free_var_in_ctor_field_is_ambiguous() {
        // (defn m [] (consume (Some (identity None)))) — the `Some` field holds an
        // unpinned `(Option a)`; `consume` keeps `m`'s result concrete `Int`.
        let body = consume_wrap(Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("Some"), span(116, 120))),
            args: vec![identity_none(span(121, 135))],
            span: span(115, 136),
            resolved_call: None,
            inferred_type: None,
        });
        assert_ambiguous(body, "constructor field");
    }

    // spec: spec/03-types.md §3.11.1 — IF BRANCH position (non-`let`).
    #[test]
    fn mixed_adt_free_var_in_if_branch_is_ambiguous() {
        // (defn m [] (consume (if true (identity None) (identity None))))
        let body = consume_wrap(Expr::If {
            cond: Box::new(Expr::BoolLit { value: true, span: span(118, 122), inferred_type: None }),
            then_branch: Box::new(identity_none(span(123, 137))),
            else_branch: Box::new(identity_none(span(138, 152))),
            span: span(115, 155),
            inferred_type: None,
        });
        assert_ambiguous(body, "if branch");
    }

    // spec: spec/03-types.md §3.11.3 — a RESULT-ONLY free var (a definition's
    // own scheme var, NOT free-at-root) is ADMITTED. `(defn m [] [[]])` has type
    // `(Fn [] (Vec (Vec a)))`; `a` is quantified into `m`'s scheme and pinned
    // per-instantiation by monomorphisation, so the inner `(Vec a)` element is
    // sound (disposition 1, dead-for-codegen until a concrete use). The §4.4
    // `allowed_vars` filter excludes `m`'s scheme vars, so the full-concreteness
    // verdict does NOT over-fire on a definition. (This is distinct from the
    // free-at-root `(Vec a)` rejection below — there the var is NOT in any
    // enclosing scheme.)
    #[test]
    fn vec_result_only_free_var_definition_is_admitted() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();
        // (defn m [] [[]]) — outer `(Vec (Vec a))`, inner element `(Vec a)` free.
        let body = Expr::VecLit {
            elements: vec![Expr::VecLit {
                elements: vec![],
                span: span(106, 108),
                inferred_type: None,
            }],
            span: span(105, 109),
            inferred_type: None,
        };
        let m = TopLevel::Defn(make_defn(
            "m", vec![], vec![], body, Visibility::Public, span(100, 110),
        ));
        tc.check(&[m], &ctx, ModuleStrategy::Additive)
            .expect("a result-only `(Vec a)` defn (§3.11.3 disposition 1) MUST be admitted");
    }

    // spec: spec/03-types.md §3.11.1 — TIGHTENED full-concreteness verdict
    // (FIXME 0386): a FREE-AT-ROOT `(Vec a)` value at a codegen-reaching value
    // position is REJECTED as ambiguous. `(consume (identity []))` — `[]` is
    // `(Vec a)`, `(identity [])` keeps `a` free, `consume` discards it (pinning
    // nothing) and keeps `m`'s result concrete `Int`, so `a` is free-at-root.
    // No representation exemption: `Vec` being uniformly heap-allocated does NOT
    // rescue the unpinned element var. This is the seam witness for the e2e
    // `regression::mono_vec_free_var_value_rejected_neg`.
    #[test]
    fn vec_free_at_root_value_position_is_ambiguous() {
        // (defn m [] (consume (identity []))) — `(identity [])` : `(Vec a)`,
        // `a` free-at-root.
        let empty_vec = Expr::VecLit {
            elements: vec![],
            span: span(125, 127),
            inferred_type: None,
        };
        let identity_empty_vec = Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("identity"), span(116, 124))),
            args: vec![empty_vec],
            span: span(115, 128),
            resolved_call: None,
            inferred_type: None,
        };
        assert_ambiguous(consume_wrap(identity_empty_vec), "vec value (free-at-root)");
    }

    // spec: spec/03-types.md §3.11.1 — TIGHTENED full-concreteness verdict
    // (FIXME 0386): a FREE-AT-ROOT `(Fn [a] a)` polymorphic-function value at a
    // codegen-reaching position is REJECTED as ambiguous. `(consume identity)` —
    // `identity` : `(Fn [a] a)`, passed to `consume` which discards it. A
    // closure's uniform machine shape does NOT rescue the unpinned type var.
    // Seam witness for `regression::mono_fn_free_var_value_rejected_neg`.
    #[test]
    fn fn_free_at_root_value_position_is_ambiguous() {
        // (defn m [] (consume identity)) — `identity` : `(Fn [a] a)`, free-at-root.
        let identity_value = Expr::var(Symbol::from("identity"), span(115, 123));
        assert_ambiguous(consume_wrap(identity_value), "fn value (free-at-root)");
    }

    // spec: spec/03-types.md §3.11.1 — the full-concreteness verdict ADMITS a
    // fully concrete value at a codegen-reaching position. `(consume (identity
    // 7))` — `(identity 7)` : `Int` (fully concrete, no free var), so the check
    // MUST NOT fire. Pairs with the free-at-root rejections above (same
    // `consume`-wrap shape; only the inner type differs).
    #[test]
    fn concrete_value_position_is_admitted() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();
        // (defn m [] (consume (identity 7)))
        let identity_int = Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("identity"), span(116, 124))),
            args: vec![Expr::IntLit { value: 7, span: span(125, 126), inferred_type: None }],
            span: span(115, 127),
            resolved_call: None,
            inferred_type: None,
        };
        let m = TopLevel::Defn(make_defn(
            "m", vec![], vec![], consume_wrap(identity_int), Visibility::Public, span(100, 130),
        ));
        tc.check(
            &[identity_defn(), consume_defn(), m],
            &ctx,
            ModuleStrategy::Additive,
        )
        .expect("a fully concrete `Int` value at a codegen position MUST be admitted (§3.11.1)");
    }

    // spec: spec/07-traits.md §7.1.5 + spec/08-modules.md §8.6 — DEFECT D1 (S86):
    //   a SYNTHESIZED default-method body's free names MUST resolve in the trait's
    //   DEFINING module, not the impl-writer's (caller's) module. A trait `Foo`
    //   declared in module `trait_mod` (which globs primitives) has a default
    //   method `bar` whose body references the bare primitive `add-i64`. An impl
    //   in module `user` (NO primitives glob) omits `bar`, so
    //   `generate_default_methods` synthesizes the body and `check_impl_method_with_sig`
    //   checks it. Before the fix, that check runs in `user`'s `current_module`, so
    //   `add-i64` resolves there and fails (`undefined variable: add-i64`). The fix
    //   mirrors `recheck_body_for_mono`'s defining-module switch into the
    //   default-method check path, so the body re-checks in `trait_mod`'s import
    //   context and `add-i64` resolves.
    #[test]
    fn default_method_body_resolves_in_trait_defining_module() {
        let mut tc = tc_with_prims();
        let trait_mod = ModuleFullPath::from("trait_mod");
        let user = ModuleFullPath::from("user");

        // --- DEFINING module `trait_mod`: globs primitives; declares `Foo` with a
        //     required `req` and a DEFAULT `bar` whose body uses bare `add-i64`. ---
        tc.set_current_module(trait_mod.clone());
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));

        let default_bar_body = Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("add-i64"), Span::SYNTHETIC)),
            args: vec![
                Expr::var(Symbol::from("a"), Span::SYNTHETIC),
                Expr::var(Symbol::from("b"), Span::SYNTHETIC),
            ],
            span: Span::SYNTHETIC,
            resolved_call: None,
            inferred_type: None,
        };
        let decl = TraitDecl {
            name: TraitName::from("Foo"),
            docstring: None,
            type_params: vec![],
            methods: vec![
                // Required method: (req [self] Self) — must be supplied by the impl.
                TraitMethodSig {
                    name: Symbol::from("req"),
                    docstring: None,
                    params: vec![(Symbol::from("self"), TypeExpr::SelfType)],
                    ret_type: TypeExpr::SelfType,
                    span: Span::SYNTHETIC,
                    hkt_param_index: None,
                    default_body: None,
                },
                // Default method: (bar [a b] Int (add-i64 a b)) — body uses a
                // bare primitive in scope ONLY in `trait_mod`.
                TraitMethodSig {
                    name: Symbol::from("bar"),
                    docstring: None,
                    params: vec![
                        (Symbol::from("a"), TypeExpr::SelfType),
                        (Symbol::from("b"), TypeExpr::SelfType),
                    ],
                    ret_type: TypeExpr::Named(cranelisp_types::TypeRef::new(
                        None,
                        TypeName::from("Int"),
                    )),
                    span: Span::SYNTHETIC,
                    hkt_param_index: None,
                    default_body: Some(default_bar_body),
                },
            ],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        tc.register_trait_decl_self(&decl)
            .expect("`Foo` declares in its defining module");

        // --- IMPL module `user`: does NOT glob primitives; imports the trait +
        //     methods, and registers an impl that OMITS `bar` (forcing default
        //     synthesis + check). `add-i64` is NOT bare-in-scope here. ---
        tc.set_current_module(user.clone());
        seed_specific_import(&mut tc, &trait_mod, &["Foo", "req", "bar"]);
        // `user` needs `Int` reachable for the impl target / sig resolution, but
        // explicitly NOT `add-i64`.
        seed_specific_import(&mut tc, &ModuleFullPath::from("primitives"), &["Int"]);

        let impl_ = TraitImpl {
            head_con_var: None,
            trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Foo")),
            target: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int"))),
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("req"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("self"), None)],
                    body: Expr::var(Symbol::from("self"), Span::SYNTHETIC),
                    span: Span::SYNTHETIC,
                }],
                visibility: Visibility::Public,
                span: Span::SYNTHETIC,
            }],
            span: Span::SYNTHETIC,
        };

        // CRUX: registering the impl synthesizes + checks the default `bar` body.
        // Before the fix this fails with `undefined variable: add-i64` (the body
        // is checked in `user`'s scope). After the fix the body re-checks in
        // `trait_mod`'s scope, where `add-i64` resolves.
        tc.register_trait_impl_self(&impl_).unwrap_or_else(|e| {
            panic!(
                "default-method body must resolve `add-i64` in the trait's \
                 DEFINING module (`trait_mod`), not the impl writer's (`user`); \
                 got: {e:?}"
            )
        });
    }

    // =====================================================================
    // `Def.callees` completeness contract (FIXME 0470, S101 Wave 2)
    //
    // spec: tests/plan/s101-coverage-postmortem.md §2.1 — every statically-
    //   resolved user-fn reference (call-position AND value-position) must be
    //   recorded in the checked entry's `callees`; no spurious edges for
    //   shadowed names, primitives/special forms, non-UserFn Def kinds, or
    //   unrelated siblings. Consumer: the S101 R3 dependent-recompilation
    //   transaction's reverse index (design/int/session-transaction.md §3.2).
    // =====================================================================

    /// Read the `callees` list off a module entry (owned copy).
    fn callees_of(tc: &TestFixture, module: &str, name: &str) -> Vec<FQSymbol> {
        let path = ModuleFullPath::from(module);
        let guard = tc.modules.get(&path).expect("module exists");
        guard
            .get(name)
            .unwrap_or_else(|| panic!("`{name}` not found in module `{module}`"))
            .callees()
            .to_vec()
    }

    fn fq_sym(module: &str, symbol: &str) -> FQSymbol {
        FQSymbol {
            module: ModuleFullPath::from(module),
            symbol: Symbol::from(symbol),
        }
    }

    /// Parse + check `src` in the fixture's current module.
    fn check_src(tc: &mut TestFixture, src: &str) {
        let sexps = cranelisp_frontend::parse(src).expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
        tc.check_program_self(&program)
            .unwrap_or_else(|e| panic!("check failed for:\n{src}\n error: {e:?}"));
    }

    // spec: tests/plan/s101-coverage-postmortem.md §2.1 item 1(a) — a plain
    //   fully-applied direct call to a single-sig concrete user fn records the
    //   caller→callee edge (the 0470 headline gap: this was EMPTY before).
    #[test]
    fn callees_records_direct_call_to_user_fn() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn callee [:primitives/Int x] :primitives/Int x)\n\
             (defn c [:primitives/Int x] :primitives/Int (callee x))",
        );
        assert!(
            callees_of(&tc, "test", "c").contains(&fq_sym("test", "callee")),
            "direct call must record the callee edge; got {:?}",
            callees_of(&tc, "test", "c"),
        );
    }

    // TB-24 (§3.2) — a conventional (kind-`*`) trait impl over a POLY-APPLIED
    // target `(Box a)` MUST accept: the lowercase con-var `a` binds as a fresh
    // type var through the ONE shared type-expr resolver, NOT reject as
    // `unknown type a` before the §7.3.5 arity gate (the pre-fix bare-head
    // NAMED lookup). `check_src` panics on any check error, so a clean return
    // IS the assertion (the impl registers a polymorphic impl over every
    // `(Box a)`).
    #[test]
    fn conventional_impl_poly_applied_target_binds_con_var() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(deftype (Box a) (Box [:a val]))\n\
             (deftrait Disp (dp [x] :primitives/Int))\n\
             (impl Disp (Box a) (defn dp [x] 7))",
        );
    }

    // TB24b (§7.3.3 + §8.5) — an UNKNOWN trait in the impl-target constraint slot
    // (`(Box :NoSuchTrait a)`) MUST be rejected. The constraint rides
    // `impl_.type_constraints` (typecheck-reachable) but pre-fix was never routed
    // through trait resolution → silent-accept. A KNOWN trait (`:Disp`) still
    // accepts (the accept fence). `check_program_self` returns Err on the reject.
    #[test]
    fn impl_target_unknown_trait_constraint_rejected_tb24b() {
        // Known trait in the constraint slot — ACCEPTS.
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(deftype (Box a) (Box [:a val]))\n\
             (deftrait Disp (dp [x] :primitives/Int))\n\
             (impl Disp (Box :Disp a) (defn dp [x] 7))",
        );
        // Unknown trait `NoSuchTrait` in the constraint slot — REJECTS.
        let mut tc2 = tc_with_prims();
        let sexps = cranelisp_frontend::parse(
            "(deftype (Box a) (Box [:a val]))\n\
             (deftrait Disp (dp [x] :primitives/Int))\n\
             (impl Disp (Box :NoSuchTrait a) (defn dp [x] 7))",
        )
        .expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
        let result = tc2.check_program_self(&program);
        assert!(
            result.is_err(),
            "an unknown trait `:NoSuchTrait` in the impl-target constraint slot \
             MUST be rejected (TB24b), not silently accepted; got Ok"
        );
    }

    // spec: tests/plan/s101-coverage-postmortem.md §2.1 item 1(b) — a user fn
    //   passed as a HOF argument (value position) records the edge; the HOF
    //   call itself also records its (call-position) edge.
    #[test]
    fn callees_records_fn_as_value_hof_argument() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn callee [:primitives/Int x] :primitives/Int x)\n\
             (defn hof [f :primitives/Int x] :primitives/Int (f x))\n\
             (defn c [:primitives/Int x] :primitives/Int (hof callee x))",
        );
        let edges = callees_of(&tc, "test", "c");
        assert!(
            edges.contains(&fq_sym("test", "callee")),
            "fn-as-value HOF argument must record the callee edge; got {edges:?}",
        );
        assert!(
            edges.contains(&fq_sym("test", "hof")),
            "the HOF call itself must record a call-position edge; got {edges:?}",
        );
    }

    // spec: tests/plan/s101-coverage-postmortem.md §2.1 item 1(c) — a user fn
    //   returned as a bare value records the edge.
    #[test]
    fn callees_records_fn_as_value_returned() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn callee [:primitives/Int x] :primitives/Int x)\n\
             (defn c [] callee)",
        );
        assert!(
            callees_of(&tc, "test", "c").contains(&fq_sym("test", "callee")),
            "returned fn-as-value must record the callee edge; got {:?}",
            callees_of(&tc, "test", "c"),
        );
    }

    // spec: tests/plan/s101-coverage-postmortem.md §2.1 item 1(d) — a user fn
    //   stored in a container literal records the edge.
    #[test]
    fn callees_records_fn_as_value_stored_in_container() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn callee [:primitives/Int x] :primitives/Int x)\n\
             (defn c [] [callee])",
        );
        assert!(
            callees_of(&tc, "test", "c").contains(&fq_sym("test", "callee")),
            "container-stored fn-as-value must record the callee edge; got {:?}",
            callees_of(&tc, "test", "c"),
        );
    }

    // spec: tests/plan/s101-coverage-postmortem.md §2.1 item 1(e) — a curried
    //   partial application records the edge to the curried target.
    #[test]
    fn callees_records_curried_partial_application() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn callee2 [:primitives/Int a :primitives/Int b] :primitives/Int (add-i64 a b))\n\
             (defn c [:primitives/Int x] :primitives/Int ((callee2 x) x))",
        );
        assert!(
            callees_of(&tc, "test", "c").contains(&fq_sym("test", "callee2")),
            "curried partial application must record the target edge; got {:?}",
            callees_of(&tc, "test", "c"),
        );
    }

    // spec: tests/plan/s101-coverage-postmortem.md §2.1 item 1(f) — a reference
    //   inside a nested lambda attributes the edge to the ENCLOSING defn (the
    //   L-R2 carrier shape).
    #[test]
    fn callees_records_reference_inside_nested_lambda() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn callee [:primitives/Int x] :primitives/Int x)\n\
             (defn c [] (fn [x] (callee x)))",
        );
        assert!(
            callees_of(&tc, "test", "c").contains(&fq_sym("test", "callee")),
            "a nested-lambda reference must attribute the edge to the enclosing \
             defn; got {:?}",
            callees_of(&tc, "test", "c"),
        );
    }

    // spec: tests/plan/s101-coverage-postmortem.md §2.1 item 1(g) — a
    //   qualified cross-module reference records the edge with the DEFINING
    //   module's FQ identity.
    #[test]
    fn callees_records_qualified_cross_module_reference() {
        let mut tc = tc_with_prims();
        let util = ModuleFullPath::from("util");
        tc.set_current_module(util.clone());
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
        check_src(
            &mut tc,
            "(defn ucallee [:primitives/Int x] :primitives/Int x)",
        );
        tc.set_current_module(ModuleFullPath::from("test"));
        check_src(
            &mut tc,
            "(defn c [:primitives/Int x] :primitives/Int (util/ucallee x))",
        );
        assert!(
            callees_of(&tc, "test", "c").contains(&fq_sym("util", "ucallee")),
            "qualified cross-module call must record the (util, ucallee) edge; \
             got {:?}",
            callees_of(&tc, "test", "c"),
        );
    }

    // spec: tests/plan/s101-coverage-postmortem.md §2.1 item 1(g) (companion) —
    //   an IMPORTED bare-name reference chain-follows to the defining module:
    //   the edge is (util, ucallee), NOT (test, ucallee).
    #[test]
    fn callees_records_imported_bare_name_at_home_module() {
        let mut tc = tc_with_prims();
        let util = ModuleFullPath::from("util");
        tc.set_current_module(util.clone());
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
        check_src(
            &mut tc,
            "(defn ucallee [:primitives/Int x] :primitives/Int x)",
        );
        tc.set_current_module(ModuleFullPath::from("test"));
        seed_specific_import(&mut tc, &util, &["ucallee"]);
        check_src(
            &mut tc,
            "(defn c [:primitives/Int x] :primitives/Int (ucallee x))",
        );
        let edges = callees_of(&tc, "test", "c");
        assert!(
            edges.contains(&fq_sym("util", "ucallee")),
            "imported bare-name call must chain-follow to the HOME module; \
             got {edges:?}",
        );
        assert!(
            !edges.contains(&fq_sym("test", "ucallee")),
            "the edge must NOT be recorded against the importing module; \
             got {edges:?}",
        );
    }

    // spec: design/typecheck/ownership-inference.md §15.5 (FIXME 0621) — a
    //   RENAMED import `[lib [foo as bar]]` records the callees edge under the
    //   SOURCE storage key `lib/foo` (`resolved.storage_fq()`), NOT the written
    //   alias `lib/bar` (`resolved.fq`, composed from the alias spelling — no
    //   such entry exists). Same storage-key discipline the `resolved_targets`
    //   carrier already uses; both feeds now agree by the schema-20 flip.
    #[test]
    fn callees_records_renamed_import_by_storage_key() {
        let mut tc = tc_with_prims();
        // `foo` (0-arg user fn) lives in module `lib`.
        tc.set_current_module(ModuleFullPath::from("lib"));
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
        check_src(&mut tc, "(defn foo [] 0)");
        // Back in `test`: import `foo` RENAMED to `bar`, then call `(bar)`.
        tc.set_current_module(ModuleFullPath::from("test"));
        tc.symbol_table_mut().insert(
            Symbol::from("bar"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: ModuleFullPath::from("lib"),
                    symbol: Symbol::from("foo"),
                },
                visibility: Visibility::Public,
            },
        );
        check_src(&mut tc, "(defn use-bar [] (bar))");
        let edges = callees_of(&tc, "test", "use-bar");
        assert!(
            edges.contains(&fq_sym("lib", "foo")),
            "renamed-import call must record the SOURCE storage key lib/foo; got {edges:?}",
        );
        assert!(
            !edges.contains(&fq_sym("lib", "bar")) && !edges.contains(&fq_sym("test", "bar")),
            "the callees edge must NOT be the written alias `bar`; got {edges:?}",
        );
    }

    // spec: tests/plan/s101-coverage-postmortem.md §2.1 item 2(a) — a SHADOWED
    //   name (fn param, let binding) records NO edge to the same-named
    //   module-level fn.
    #[test]
    fn callees_neg_shadowed_name_records_no_edge() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn callee [:primitives/Int x] :primitives/Int x)\n\
             (defn c [callee :primitives/Int x] :primitives/Int (callee x))\n\
             (defn c2 [:primitives/Int x] :primitives/Int\n\
               (let [callee (fn [y] (add-i64 y 0))] (callee x)))",
        );
        assert!(
            !callees_of(&tc, "test", "c")
                .contains(&fq_sym("test", "callee")),
            "a param-shadowed name must record no module edge; got {:?}",
            callees_of(&tc, "test", "c"),
        );
        assert!(
            !callees_of(&tc, "test", "c2")
                .contains(&fq_sym("test", "callee")),
            "a let-shadowed name must record no module edge; got {:?}",
            callees_of(&tc, "test", "c2"),
        );
    }

    // spec: tests/plan/s101-coverage-postmortem.md §2.1 item 2(b) — primitives
    //   and special forms record NO user-fn edge (BuiltinFn deliberately
    //   skipped: always available, no codegen dependency).
    #[test]
    fn callees_neg_primitives_and_special_forms_record_no_edge() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn c [:primitives/Int x] :primitives/Int\n\
               (if (lt-i64 x 1) (add-i64 x x) x))",
        );
        assert!(
            callees_of(&tc, "test", "c").is_empty(),
            "primitive calls + special forms must record no edges; got {:?}",
            callees_of(&tc, "test", "c"),
        );
    }

    // spec: tests/plan/s101-coverage-postmortem.md §2.1 item 2(b)/(c) — a
    //   non-UserFn `Def` kind records no edge. Probed with a Constructor (the
    //   constructible case); the same `DefKind::UserFn` gate excludes
    //   `DefKind::Macro` entries — macro USES never reach typecheck (expanded
    //   upstream), so macro edges ride their own channel (save.rs macro
    //   partition), and a macro name can never enter `callees` here.
    #[test]
    fn callees_neg_constructor_reference_records_no_edge() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(deftype Box [:primitives/Int v])\n\
             (defn c [] (Box 1))",
        );
        assert!(
            !callees_of(&tc, "test", "c")
                .iter()
                .any(|e| e.symbol.as_ref() == "Box"),
            "a constructor reference must record no user-fn edge; got {:?}",
            callees_of(&tc, "test", "c"),
        );
    }

    // spec: tests/plan/s101-coverage-postmortem.md §2.1 item 2(d) — unrelated
    //   fns sharing a module record no edge to each other (the L-R3(b)
    //   exactness negative at the unit grain).
    #[test]
    fn callees_neg_unrelated_siblings_record_no_edges() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn a [:primitives/Int x] :primitives/Int x)\n\
             (defn b [:primitives/Int x] :primitives/Int (add-i64 x 1))",
        );
        assert!(
            callees_of(&tc, "test", "a").is_empty(),
            "unrelated `a` must have no edges; got {:?}",
            callees_of(&tc, "test", "a"),
        );
        assert!(
            callees_of(&tc, "test", "b").is_empty(),
            "unrelated `b` must have no edges; got {:?}",
            callees_of(&tc, "test", "b"),
        );
    }

    // spec: tests/plan/s101-coverage-postmortem.md §2.1 item 3 — uniformity:
    //   call-position and value-position references record the SAME
    //   `Vec<FQSymbol>` carrier; consumers cannot distinguish them
    //   (design/int/session-transaction.md §3.2 — sound at stage M because
    //   every ABI change is a type change, which breaks value uses too).
    #[test]
    fn callees_uniform_carrier_for_call_and_value_position() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn callee [:primitives/Int x] :primitives/Int x)\n\
             (defn call-pos [:primitives/Int x] :primitives/Int (callee x))\n\
             (defn value-pos [] callee)",
        );
        assert_eq!(
            callees_of(&tc, "test", "call-pos"),
            callees_of(&tc, "test", "value-pos"),
            "call-position and value-position edges must be indistinguishable \
             in the carrier",
        );
        assert_eq!(
            callees_of(&tc, "test", "call-pos"),
            vec![fq_sym("test", "callee")],
        );
    }

    // spec: design/arch/fixmes/0472 + tests/plan/s101-coverage-postmortem.md
    //   §2.1 (impl-method-caller row) — a trait-impl method body checked at the
    //   Pass-1 seam (`check_impl_method`, outside the Pass-2 per-form delta)
    //   must STILL record its statically-resolved user-fn references on the
    //   mangled entry. Before the cure: `Sizey.bump$Int/Def.callees = []`
    //   (the recorder fired but every Pass-2 snapshot preceded its spans).
    #[test]
    fn callees_records_impl_method_body_reference() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn helper [:primitives/Int x] :primitives/Int x)",
        );

        // (deftrait Sizey [a] (defn bump [self] Int))
        let decl = TraitDecl {
            name: TraitName::from("Sizey"),
            docstring: None,
            type_params: vec![],
            methods: vec![TraitMethodSig {
                name: Symbol::from("bump"),
                docstring: None,
                params: vec![(Symbol::from("self"), TypeExpr::SelfType)],
                ret_type: TypeExpr::Named(cranelisp_types::TypeRef::new(
                    None,
                    TypeName::from("Int"),
                )),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        tc.register_trait_decl_self(&decl).unwrap();

        // (impl Sizey Int (defn bump [a] (helper a))) — the body calls the
        // module-level user fn `helper`. Distinct spans: the recorder is
        // span-keyed, so synthetic-span collisions would mask the reference.
        let impl_ = TraitImpl {
            head_con_var: None,
            trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Sizey")),
            target: TypeExpr::Named(cranelisp_types::TypeRef::new(
                None,
                TypeName::from("Int"),
            )),
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("bump"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("a"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(
                            Symbol::from("helper"),
                            Span::new(900, 906),
                        )),
                        args: vec![Expr::var(Symbol::from("a"), Span::new(907, 908))],
                        span: Span::new(899, 909),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: Span::new(890, 910),
                }],
                visibility: Visibility::Public,
                span: Span::new(890, 910),
            }],
            span: Span::new(880, 911),
        };
        tc.register_trait_impl_self(&impl_).unwrap();

        let edges = callees_of(&tc, "test", "Sizey.bump$primitives/Int");
        assert!(
            edges.contains(&fq_sym("test", "helper")),
            "an impl-method body reference must record the edge on the \
             mangled entry (FIXME 0472); got {edges:?}",
        );
    }

    // spec: design/arch/fixmes/0472 — the DEFAULT-method seam shares the
    //   impl-method writeback; a synthesized default body (checked under the
    //   trait's DEFINING module, D1/S86) records its user-fn references on
    //   the mangled entry, with the FQ resolved in the trait-home context.
    #[test]
    fn callees_records_default_method_body_reference() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn dhelper [:primitives/Int x] :primitives/Int x)",
        );

        // (deftrait Doubly [a]
        //   (defn req [self] Self)
        //   (defn dbl [a] Int (dhelper a)))   ; default body calls dhelper
        let default_body = Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("dhelper"), Span::new(920, 927))),
            args: vec![Expr::var(Symbol::from("a"), Span::new(928, 929))],
            span: Span::new(919, 930),
            resolved_call: None,
            inferred_type: None,
        };
        let decl = TraitDecl {
            name: TraitName::from("Doubly"),
            docstring: None,
            type_params: vec![],
            methods: vec![
                TraitMethodSig {
                    name: Symbol::from("req"),
                    docstring: None,
                    params: vec![(Symbol::from("self"), TypeExpr::SelfType)],
                    ret_type: TypeExpr::SelfType,
                    span: Span::SYNTHETIC,
                    hkt_param_index: None,
                    default_body: None,
                },
                TraitMethodSig {
                    name: Symbol::from("dbl"),
                    docstring: None,
                    params: vec![(Symbol::from("a"), TypeExpr::SelfType)],
                    ret_type: TypeExpr::Named(cranelisp_types::TypeRef::new(
                        None,
                        TypeName::from("Int"),
                    )),
                    span: Span::SYNTHETIC,
                    hkt_param_index: None,
                    default_body: Some(default_body),
                },
            ],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        tc.register_trait_decl_self(&decl).unwrap();

        // (impl Doubly Int (defn req [a] a)) — omits `dbl`, forcing default
        // synthesis + body check through the same writeback seam.
        let impl_ = TraitImpl {
            head_con_var: None,
            trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Doubly")),
            target: TypeExpr::Named(cranelisp_types::TypeRef::new(
                None,
                TypeName::from("Int"),
            )),
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("req"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("a"), None)],
                    body: Expr::var(Symbol::from("a"), Span::new(940, 941)),
                    span: Span::new(935, 942),
                }],
                visibility: Visibility::Public,
                span: Span::new(935, 942),
            }],
            span: Span::new(930, 943),
        };
        tc.register_trait_impl_self(&impl_).unwrap();

        let edges = callees_of(&tc, "test", "Doubly.dbl$primitives/Int");
        assert!(
            edges.contains(&fq_sym("test", "dhelper")),
            "a default-method body reference must record the edge on the \
             mangled entry (FIXME 0472, same writeback seam); got {edges:?}",
        );
    }

    // spec: tests/plan/s101-coverage-postmortem.md §2.1 item 1(e)/(g) (F4
    //   sibling, /review S101) — a curried partial application of an IMPORTED
    //   fn records the recorder's HOME-module edge. Pins the dual-channel
    //   cover: the AutoCurry `ResolvedCall` channel stamps `current_module`
    //   (the pre-existing Step-5 approximation), so the recorder's
    //   chain-followed home edge is what makes the reverse index reach the
    //   defining module.
    #[test]
    fn callees_records_cross_module_curried_imported_fn_at_home() {
        let mut tc = tc_with_prims();
        let util = ModuleFullPath::from("util");
        tc.set_current_module(util.clone());
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
        check_src(
            &mut tc,
            "(defn ucallee2 [:primitives/Int a :primitives/Int b] :primitives/Int (add-i64 a b))",
        );
        tc.set_current_module(ModuleFullPath::from("test"));
        seed_specific_import(&mut tc, &util, &["ucallee2"]);
        check_src(
            &mut tc,
            "(defn c [:primitives/Int x] :primitives/Int ((ucallee2 x) x))",
        );
        let edges = callees_of(&tc, "test", "c");
        assert!(
            edges.contains(&fq_sym("util", "ucallee2")),
            "curried imported fn must record the recorder's home-module edge; \
             got {edges:?}",
        );
    }

    // Self-edge disposition (FIXME 0470: "may be recorded or skipped — pick
    // whichever is cheaper and document it"). SKIPPED is the structural
    // outcome and the cheap choice: `check_defn_body` binds the recursion
    // name as a LOCAL (`mono(fn_type)`), so the local-shadow gate in
    // `record_user_fn_ref` never sees a module reference — zero extra checks.
    // The transaction's SCC condensation is indifferent, and
    // `save.rs::dependency_sort` filters self-edges anyway.
    // spec: design/int/session-transaction.md §3.2
    #[test]
    fn callees_skips_recursive_self_edge() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn r [:primitives/Int x] :primitives/Int\n\
               (if (lt-i64 x 1) x (r (sub-i64 x 1))))",
        );
        assert!(
            !callees_of(&tc, "test", "r").contains(&fq_sym("test", "r")),
            "recursion records NO self-edge (documented disposition: the \
             recursion name is a local binding); got {:?}",
            callees_of(&tc, "test", "r"),
        );
    }

    // =====================================================================
    // FIXME 0488 — generic-fn missing monomorphisation (typecheck-side)
    // Unit shapes per `tests/plan/0488-isolation.md` §"Unit-test shapes".
    // =====================================================================

    /// Collect the first `SigDispatch` mangled name found on any Apply node in
    /// a body Expr tree (helper for the 0488 collection-shape tests).
    fn first_sig_dispatch(expr: &Expr) -> Option<String> {
        if let Expr::Apply { callee, args, resolved_call, .. } = expr {
            if let Some(ResolvedCall::SigDispatch { mangled_name }) = resolved_call.as_deref() {
                return Some(mangled_name.as_ref().to_string());
            }
            if let Some(m) = first_sig_dispatch(callee) {
                return Some(m);
            }
            for a in args {
                if let Some(m) = first_sig_dispatch(a) {
                    return Some(m);
                }
            }
        }
        None
    }

    /// Does any `Var` node in the tree carry the given name? (fn-value rewrite
    /// witness for signature (b)).
    fn body_has_var_named(expr: &Expr, target: &str) -> bool {
        match expr {
            Expr::Var { name, .. } => name.as_ref() == target,
            Expr::Apply { callee, args, .. } => {
                body_has_var_named(callee, target)
                    || args.iter().any(|a| body_has_var_named(a, target))
            }
            Expr::If { cond, then_branch, else_branch, .. } => {
                body_has_var_named(cond, target)
                    || body_has_var_named(then_branch, target)
                    || body_has_var_named(else_branch, target)
            }
            Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
                bindings.iter().any(|(_, b)| body_has_var_named(b, target))
                    || body_has_var_named(body, target)
            }
            Expr::Lambda { body, .. }
            | Expr::Annotate { expr: body, .. }
            | Expr::Trace { body, .. } => body_has_var_named(body, target),
            Expr::VecLit { elements, .. } => {
                elements.iter().any(|e| body_has_var_named(e, target))
            }
            _ => false,
        }
    }

    /// The stored annotated body of `name` in the fixture's current module.
    fn stored_body(tc: &TestFixture, name: &str) -> Expr {
        match tc.symbol_table().get(name) {
            Some(ModuleEntry::Def { ast: Some(variant), .. }) => variant.body.clone(),
            other => panic!("`{name}` has no stored annotated body: {other:?}"),
        }
    }

    // spec: spec/04-expressions.md §4.2.2 — a same-module qualified call to a
    //   generic fn MUST monomorphise/dispatch under the BARE mangled name,
    //   identically to the bare call. RED on HEAD (FIXME 0488 sig a, same-module
    //   sub-cause): the pass-4 local collector probes the module table with the
    //   RAW qualified key (`test/iden`) and misses, so no `iden$Int` is minted
    //   and the call node carries no SigDispatch.
    #[test]
    fn u_a1_same_module_fq_call_mints_bare_and_dispatches() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn iden [x] x)\n\
             (defn caller [] (test/iden 5))",
        );

        // `test/iden$Int` minted (home-qualified, FIXME 0519), concrete + slotted.
        match tc.symbol_table().get("test/iden$Int") {
            Some(ModuleEntry::Def { kind, scheme, .. }) => {
                assert!(
                    matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }
                    ),
                    "test/iden$Int must be a Concrete (slotted) mono instance, got {kind:?}",
                );
                assert!(scheme.ty.is_concrete(), "test/iden$Int type must be concrete");
            }
            other => panic!(
                "same-module FQ call must mint `test/iden$Int` (FIXME 0488 sig a); got {other:?}"
            ),
        }
        // The caller's Apply node carries SigDispatch{test/iden$Int}.
        assert_eq!(
            first_sig_dispatch(&stored_body(&tc, "caller")).as_deref(),
            Some("test/iden$Int"),
            "the same-module FQ call node must carry SigDispatch{{test/iden$Int}}",
        );
    }

    // spec: spec/04-expressions.md §4.2.2 — CONTROL: a same-module FQ call on a
    //   CONCRETE fn mints NO mono instance (concrete fns need no specialisation).
    #[test]
    fn u_a1_neg_same_module_fq_concrete_call_mints_nothing() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn incr [:primitives/Int x] (add-i64 x 1))\n\
             (defn caller [] (test/incr 5))",
        );
        assert!(
            tc.symbol_table().get("incr$Int").is_none(),
            "a concrete FQ callee must NOT mint a mono instance",
        );
    }

    // spec: spec/04-expressions.md §4.2.2 — a CROSS-module qualified call to an
    //   imported generic fn MUST monomorphise + dispatch. FIXME 0519: the mono
    //   name is HOME-QUALIFIED by the DEFINING module (`gen`), so the instance is
    //   `gen/iden2$Int` (NOT the home-blind bare `iden2$Int`, whose ambiguity was
    //   the 0508 silent-miscompile). The consumer registers the mono under the
    //   home-qualified key in its own table and dispatches to it.
    #[test]
    fn u_a2_cross_module_fq_call_mints_home_qualified_name() {
        let mut tc = tc_with_prims();
        // Build the fixture module `gen` with a generic `iden2`.
        tc.set_current_module(ModuleFullPath::from("gen"));
        check_src(&mut tc, "(defn iden2 [x] x)");

        // Back in `test`, import + call by FQ name.
        tc.set_current_module(ModuleFullPath::from("test"));
        seed_specific_import(&mut tc, &ModuleFullPath::from("gen"), &["iden2"]);
        check_src(&mut tc, "(defn caller [] (gen/iden2 5))");

        assert!(
            tc.symbol_table().get("gen/iden2$Int").is_some(),
            "cross-module FQ call must mint the HOME-qualified `gen/iden2$Int` in \
             the caller module (FIXME 0488 sig a + 0519 home-qualification)",
        );
        assert!(
            tc.symbol_table().get("iden2$Int").is_none(),
            "the mono must NOT be minted under the home-blind bare `iden2$Int` \
             name (the 0508 collision axis)",
        );
        assert_eq!(
            first_sig_dispatch(&stored_body(&tc, "caller")).as_deref(),
            Some("gen/iden2$Int"),
            "the cross-module FQ call node must carry SigDispatch{{gen/iden2$Int}}",
        );
    }

    // spec: spec/04-expressions.md §4.6.2 — an IMPORTED generic fn passed as a
    //   VALUE into a HOF MUST be monomorphised and the fn-value `Var` rewritten
    //   to the mangled name in the caller's stored AST. RED on HEAD (FIXME 0488
    //   sig b): `collect_parametric_fn_value_args` carries a `home ==
    //   current_module` gate excluding imported generics, and the mint call
    //   hard-codes `home: None`.
    #[test]
    fn u_b_imported_fn_value_use_mints_and_rewrites() {
        let mut tc = tc_with_prims();
        tc.set_current_module(ModuleFullPath::from("gen"));
        check_src(&mut tc, "(defn iden2 [x] x)");

        tc.set_current_module(ModuleFullPath::from("test"));
        seed_specific_import(&mut tc, &ModuleFullPath::from("gen"), &["iden2"]);
        check_src(
            &mut tc,
            "(defn call1 [f x] (f x))\n\
             (defn use1 [] (call1 iden2 5))",
        );

        assert!(
            // FIXME 0519: home-qualified by the DEFINING module `gen`.
            tc.symbol_table().get("gen/iden2$Int").is_some(),
            "imported fn-value use must mint `gen/iden2$Int` (FIXME 0488 sig b)",
        );
        // The fn-value `Var` in use1's body is rewritten to the mangled name.
        let body = stored_body(&tc, "use1");
        assert!(
            body_has_var_named(&body, "gen/iden2$Int"),
            "the imported fn-value `Var` must be rewritten to `gen/iden2$Int` in the \
             caller AST; body = {body:?}",
        );
        assert!(
            !body_has_var_named(&body, "iden2"),
            "the un-rewritten bare `iden2` fn-value `Var` must be gone; body = {body:?}",
        );
    }

    // spec: spec/04-expressions.md §4.6.2 — CONTROL / regression fence for the
    //   0374 LOCAL fn-value path: a SAME-module generic passed as a value still
    //   mints + rewrites (must stay green after the sig-(b) gate relaxation).
    #[test]
    fn u_b_neg_same_module_fn_value_use_unchanged() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn iden [x] x)\n\
             (defn call1 [f x] (f x))\n\
             (defn use1 [] (call1 iden 5))",
        );
        assert!(
            tc.symbol_table().get("test/iden$Int").is_some(),
            "same-module fn-value use must still mint `test/iden$Int` (0374 regression fence)",
        );
        assert!(
            body_has_var_named(&stored_body(&tc, "use1"), "test/iden$Int"),
            "same-module fn-value `Var` must still be rewritten to `test/iden$Int`",
        );
    }

    // spec: spec/04-expressions.md §4.6.2 + spec/03-types.md §3.11.1 — POSITION
    //   COMPLETENESS (I2 / FIXME 0585). A generic fn-value referenced in a
    //   value position that is NEITHER an `Apply` arg NOR a `Let`/`ParBind`
    //   binding value — here an `if` BRANCH — must still be monomorphised and
    //   rewritten. RED on the pre-0571.2 whitelist: `collect_parametric_fn_value_args`
    //   only visited `Apply { args }` and `Let`/`ParBind` bindings, so an
    //   if/match/vector-position fn-value was never collected and reached the
    //   backend slot-less (the codegen `undefined variable` leak). The uniform
    //   non-callee-child walk (mirroring `find_ambiguous_value_position`) closes
    //   it. This unit test FAILS on revert of that walk.
    #[test]
    fn u_b_if_branch_fn_value_position_mints_and_rewrites() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            "(defn iden [x] x)\n\
             (defn use1 [] ((if true iden iden) 5))",
        );
        assert!(
            tc.symbol_table().get("test/iden$Int").is_some(),
            "a generic fn-value in an `if`-branch value position must be \
             monomorphised (I2/0585 position-completeness — the whitelist skipped \
             if/match/vector)",
        );
        let body = stored_body(&tc, "use1");
        assert!(
            body_has_var_named(&body, "test/iden$Int"),
            "the if-branch fn-value `Var` must be rewritten to the mangled name; \
             body = {body:?}",
        );
        assert!(
            !body_has_var_named(&body, "iden"),
            "no un-rewritten bare `iden` fn-value `Var` may remain; body = {body:?}",
        );
    }

    // The signature-(c) fixture, mirroring the e2e FOLD_MODULE: a same-module
    // generic fold (`vreduce`/`vreduce-loop`) whose helper threads a polymorphic
    // accumulator, and `vconcat` — a fold-bodied generic passing the builtin
    // `vec-push` as a VALUE into the fold.
    const FOLD_SRC: &str = "\
        (defn vreduce [f init v] (vreduce-loop f init v (vec-len v) 0))\n\
        (defn vreduce-loop [f acc v :primitives/Int len :primitives/Int i]\n  \
          (if (ge-i64 i len) acc\n    \
            (vreduce-loop f (f acc (vec-get v i)) v len (add-i64 i 1))))\n\
        (defn vconcat [va vb] (vreduce vec-push va vb))";

    // spec: spec/03-types.md §3.4 — after generalization a fold-bodied generic's
    //   scheme MUST tie its result to its params: the body `(vreduce vec-push va
    //   vb)` unifies va, vb and the result with vreduce's accumulator, so
    //   `vconcat` generalizes to `(Fn [(Vec a) (Vec a)] (Vec a))`. RED on HEAD
    //   (FIXME 0488 sig c ROOT CAUSE): HEAD publishes `(Fn [a (Vec b)] c)` —
    //   result untied, first param degraded — because `vconcat`'s body is checked
    //   against a STALE (under-tied) `vreduce` scheme (the forward-reference to
    //   the later-defined `vreduce-loop` was not yet body-checked when the
    //   0344 writeback froze `vreduce`).
    #[test]
    fn u_c1_fold_bodied_scheme_ties_result_to_params() {
        let mut tc = tc_with_prims();
        check_src(&mut tc, FOLD_SRC);

        let scheme = match tc.symbol_table().get("vconcat") {
            Some(ModuleEntry::Def { scheme, .. }) => scheme.clone(),
            other => panic!("vconcat not a Def: {other:?}"),
        };
        // Exactly ONE quantified var — the element var shared across both
        // (Vec _) params and the (Vec _) result.
        assert_eq!(
            scheme.type_vars.len(),
            1,
            "vconcat must generalize over exactly ONE var, got {:?}",
            scheme,
        );
        // (Fn [(Vec x) (Vec x)] (Vec x)) — same inner var x throughout.
        let vec_var = |t: &Type| -> Option<u32> {
            match t {
                Type::ADT(name, args)
                    if name.name.as_ref() == "Vec" && args.len() == 1 =>
                {
                    match &args[0] {
                        Type::Var(id) => Some(*id),
                        _ => None,
                    }
                }
                _ => None,
            }
        };
        match &scheme.ty {
            Type::Fn(params, ret) => {
                assert_eq!(params.len(), 2, "vconcat takes (va vb)");
                let a = vec_var(&params[0]).unwrap_or_else(|| {
                    panic!("param 0 must be (Vec x), got {:?}", params[0])
                });
                let b = vec_var(&params[1]).unwrap_or_else(|| {
                    panic!("param 1 must be (Vec x), got {:?}", params[1])
                });
                let r = vec_var(ret).unwrap_or_else(|| {
                    panic!("result must be (Vec x), got {:?}", ret)
                });
                assert!(
                    a == b && b == r,
                    "vconcat's two (Vec _) params and its (Vec _) result must \
                     share ONE element var; got a={a} b={b} r={r} (FIXME 0488 sig c)",
                );
            }
            other => panic!("vconcat scheme is not a function type: {other:?}"),
        }
    }

    // spec: spec/03-types.md §3.4 / s84-concrete-types-ambiguity-ruling — a minted
    //   mono instance's REGISTERED scheme must have a fully-concrete return type
    //   (no residual `Type::Var` in a `Concrete` entry's scheme). RED on HEAD
    //   (FIXME 0488 sig c secondary): the fold-bodied template's untied result
    //   makes `register_mono_entry` capture a residual-var `concrete_ret_ty`
    //   (`(Fn [(Vec Int) (Vec Int)] tN)`). The sig-(c) template-tie fix pins the
    //   result at instantiation, so the mono scheme becomes concrete.
    #[test]
    fn u_c2_minted_mono_scheme_return_is_concrete() {
        let mut tc = tc_with_prims();
        check_src(
            &mut tc,
            &format!("{FOLD_SRC}\n(defn usec [] (vconcat [1 2] [3 4]))"),
        );

        // Find the minted vconcat mono instance.
        let st = tc.symbol_table();
        let (mono_name, scheme) = st
            .all_symbols()
            // FIXME 0519: mono name is home-qualified with a lossless sig.
            .find(|(n, _)| n.as_ref().contains("vconcat$"))
            .and_then(|(n, e)| match e {
                ModuleEntry::Def { scheme, .. } => Some((n.as_ref().to_string(), scheme.clone())),
                _ => None,
            })
            .expect("a `vconcat$..` mono instance must be minted for the concrete call");
        assert!(
            scheme.ty.is_concrete(),
            "the minted `{mono_name}` mono entry's registered scheme must be fully \
             concrete (no residual result var); got {:?} (FIXME 0488 sig c secondary)",
            scheme.ty,
        );
    }

    // ---- S113 0655 (user ruling (a)): qualified own-module self-reference is
    // another spelling of the bare local. Normalization at the ONE Var entry
    // (`normalize_self_qualified`) + the collapsed candidate-order twin
    // (`qualified_candidate_modules`). ----

    // spec: spec/08-modules.md §8.6.6 + S113 0655 — `test/x` in module `test`
    // (after §8.6.6 alias substitution) IS the bare `x`; a genuine cross-module
    // qualifier and Principle-16 literal `/`-names are left untouched. Direct
    // unit of the normalization seam.
    #[test]
    fn normalize_self_qualified_collapses_current_module_spelling() {
        let tc = tc_with_prims(); // current module = "test"
        // An alias `t -> test` so the alias-spelled current module also collapses
        // (§8.6.6 longest-prefix substitution applied BEFORE the current-module
        // comparison).
        tc.module_aliases.insert(
            ModuleFullPath::from("t"),
            cranelisp_types::ModuleAliasEntry::new(
                ModuleFullPath::from("test"),
                Visibility::Public,
                cranelisp_types::Span::SYNTHETIC,
            ),
        );
        let env = tc.env();
        // Current-module-qualified → bare local.
        assert_eq!(env.normalize_self_qualified(&tc.state, "test/qloop"), "qloop");
        // Alias-spelled current module → bare local (MC-X3c).
        assert_eq!(env.normalize_self_qualified(&tc.state, "t/qloop"), "qloop");
        // Bare name → unchanged.
        assert_eq!(env.normalize_self_qualified(&tc.state, "qloop"), "qloop");
        // Genuine cross-module qualifier → NOT normalized.
        assert_eq!(
            env.normalize_self_qualified(&tc.state, "other/qloop"),
            "other/qloop"
        );
        // A submodule-child qualifier names `test.util`, NOT the current module —
        // NOT normalized (left for the child-first qualified leg).
        assert_eq!(
            env.normalize_self_qualified(&tc.state, "util/helper"),
            "util/helper"
        );
        // Principle-16 literal `/`-names → unchanged (never a qualified form).
        assert_eq!(env.normalize_self_qualified(&tc.state, "foo/"), "foo/");
        assert_eq!(env.normalize_self_qualified(&tc.state, "/bar"), "/bar");
        assert_eq!(env.normalize_self_qualified(&tc.state, "/"), "/");
    }

    // spec: spec/08-modules.md §8.6.6 + S113 0655 — the ONE candidate-order source
    // both `lookup` and `resolve_ref_target` walk: child-of-current-module BEFORE
    // absolute (Principle 7 — the former hand-rolled `resolve_ref_target` mirror
    // is retired). Guards the twin collapse.
    #[test]
    fn qualified_candidate_modules_child_before_absolute() {
        let tc = tc_with_prims(); // current module = "test"
        let env = tc.env();
        let (name_part, [child, abs]) = env
            .qualified_candidate_modules(&tc.state, "util/helper")
            .expect("a two-part qualified name yields candidates");
        assert_eq!(name_part, "helper");
        assert_eq!(child, ModuleFullPath::from("test.util"), "child-of-current first");
        assert_eq!(abs, ModuleFullPath::from("util"), "absolute path second");
        // A bare name / Principle-16 literal has no qualified candidates.
        assert!(env.qualified_candidate_modules(&tc.state, "helper").is_none());
        assert!(env.qualified_candidate_modules(&tc.state, "foo/").is_none());
    }

    // spec: spec/04-scoping.md §4.6 + S113 0655 (ruling (a)) — a self-qualified
    // reference `test/helper` is another spelling of the bare `helper` and is
    // therefore SUBJECT to lexical shadowing: a `let`-bound local `helper`
    // shadows the module `helper`, so `test/helper` resolves to the LET-LOCAL.
    // FAILING-FIRST: without the Var-entry normalization, `test/helper` resolved
    // through the qualified leg to the MODULE `helper` (`(Fn [c] Bool)`), making
    // `caller` return `Bool`; with it, the identity let-local wins and `caller`
    // is the identity `(Fn [a] a)`.
    #[test]
    fn self_qualified_ref_let_shadow_wins_sec_4_6() {
        let mut tc = tc_with_prims();
        let src = "(defn helper [y] true)\n\
                   (defn caller [x] (let [helper (fn [z] z)] (test/helper x)))";
        let sexps = cranelisp_frontend::parse(src).expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
        tc.check_program_self(&program)
            .expect("a self-qualified ref under a let-shadow MUST type-check");
        let table = tc.symbol_table();
        let Some(ModuleEntry::Def { scheme, .. }) = table.get("caller") else {
            panic!("caller not found");
        };
        match &scheme.ty {
            Type::Fn(params, ret) => {
                assert_eq!(params.len(), 1);
                assert_eq!(
                    params[0], **ret,
                    "§4.6: the let-shadowed `test/helper` MUST resolve to the \
                     identity let-local (ret == param), NOT the module `helper` \
                     which returns Bool; got {:?}",
                    scheme.ty
                );
            }
            other => panic!("expected caller: (Fn [a] a); got {other:?}"),
        }
    }

    // spec: spec/04-scoping.md §4.6 + S113 0655 (ruling (a)) — the same §4.6
    // shadow rule for a MATCH-arm binding: a var-pattern `helper` binds the
    // scrutinee, and the self-qualified `test/helper` in the arm body resolves to
    // that binding (the whole-value pattern var), NOT the module `helper`.
    // FAILING-FIRST: without normalization `test/helper` typed as the module
    // `helper` `(Fn [c] Bool)` → `caller: (Fn [a] (Fn [c] Bool))`; with it the arm
    // binding wins → `caller: (Fn [a] a)`.
    #[test]
    fn self_qualified_ref_match_arm_shadow_wins_sec_4_6() {
        let mut tc = tc_with_prims();
        let src = "(defn helper [y] true)\n\
                   (defn caller [x] (match x [helper test/helper]))";
        let sexps = cranelisp_frontend::parse(src).expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
        tc.check_program_self(&program)
            .expect("a self-qualified ref under a match-arm shadow MUST type-check");
        let table = tc.symbol_table();
        let Some(ModuleEntry::Def { scheme, .. }) = table.get("caller") else {
            panic!("caller not found");
        };
        match &scheme.ty {
            Type::Fn(params, ret) => {
                assert_eq!(params.len(), 1);
                assert_eq!(
                    params[0], **ret,
                    "§4.6: the match-arm-bound `test/helper` MUST resolve to the \
                     whole-value pattern binding (ret == param), NOT the module \
                     `helper`; got {:?}",
                    scheme.ty
                );
            }
            other => panic!("expected caller: (Fn [a] a); got {other:?}"),
        }
    }

    // spec: spec/08-modules.md §8.6.6 + S113 0655 (ruling (a)) — an UNSHADOWED
    // self-qualified defn-body self-call `(test/qloop x)` type-checks (the
    // normalized bare `qloop` hits the recursion-local env binding), the seam the
    // §4.6 shadow cells above share with the top-level path. The CARRIER the
    // backend keys its ONE fetch on (whose mid-graph absence is the batch
    // `undefined function: user/qloop` leak, FIXME 0655) is drained from the
    // transient `method_resolutions` into the codegen_view at finalize and is
    // observed END-TO-END by the e2e cell
    // `qualified_self_reference_mc_x3::qualified_own_module_self_ref_batch_no_codegen_leak`
    // (the fixture's committed view resolves the qualified spelling the batch
    // module-graph path cannot, so the carrier drop is only an e2e-visible fault).
    #[test]
    fn self_qualified_defn_body_self_call_type_checks() {
        let mut tc = tc_with_prims();
        let src = "(defn qloop [x] 0)\n\
                   (defn qloop [x] (if true 0 (test/qloop x)))";
        let sexps = cranelisp_frontend::parse(src).expect("parse");
        let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
        tc.check_program_self(&program).expect(
            "a self-qualified defn-body self-call MUST type-check (ruling (a): \
             `test/qloop` in module `test` IS the recursion-local `qloop`)",
        );
        let table = tc.symbol_table();
        let Some(ModuleEntry::Def { scheme, .. }) = table.get("qloop") else {
            panic!("qloop not found");
        };
        // Body `(if true 0 (test/qloop x))`: the `0` branch fixes the return to
        // Int; `x` is otherwise unconstrained (passed only to the recursive
        // self-call), so the param stays a free var — `(Fn [a] Int)`. The
        // load-bearing fact is that the self-call RESOLVED (the recursion is
        // well-typed with an Int result), not that it errored on `test/qloop`.
        match &scheme.ty {
            Type::Fn(params, ret) => {
                assert_eq!(params.len(), 1);
                assert_eq!(
                    **ret,
                    Type::Int,
                    "the self-referencing `qloop` MUST return Int; got {:?}",
                    scheme.ty
                );
            }
            other => panic!("expected qloop: (Fn [a] Int); got {other:?}"),
        }
    }
