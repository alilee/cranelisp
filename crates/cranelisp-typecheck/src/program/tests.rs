    use super::*;
    use crate::checker::TestFixture;
    use cranelisp_types::{CompileContext, DefnVariant, Expr, FQSymbol, FQTypeName,
        ModuleEntry, ModuleFullPath, Symbol,
        TraitDecl, TraitImpl, TraitMethodSig, TraitName, TypeExpr, TypeName, Visibility,
    };

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

        // impl Num for Int: + → add-i64
        let impl_ = TraitImpl {
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
        TypeCheckEnv::<()>::collect_constrained_calls(&expr, &constrained, &mut calls);

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
        TypeCheckEnv::<()>::collect_constrained_calls(&expr, &constrained, &mut calls);

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
        TypeCheckEnv::<()>::collect_constrained_calls(&expr, &constrained, &mut calls);

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
        TypeCheckEnv::<()>::collect_constrained_calls(&expr, &constrained, &mut calls);

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
            mono_names.iter().any(|n| n.as_ref() == "add$Int+Int"),
            "expected add$Int+Int in mono entries, got {mono_names:?}"
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
            mono_names.iter().any(|n| n.as_ref() == "add$Int+Int"),
            "expected add$Int+Int in mono entries, got {mono_names:?}"
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
            type_params: vec![Symbol::from("a")],
            methods: vec![TraitMethodSig {
                name: Symbol::from("eq"),
                docstring: None,
                params: vec![
                    (Symbol::from("lhs"), TypeExpr::TypeVar(Symbol::from("a"))),
                    (Symbol::from("rhs"), TypeExpr::TypeVar(Symbol::from("a"))),
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
            type_params: vec![Symbol::from("a")],
            methods: vec![TraitMethodSig {
                name: Symbol::from("show"),
                docstring: None,
                params: vec![(Symbol::from("x"), TypeExpr::TypeVar(Symbol::from("a")))],
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
            type_params: vec![Symbol::from("a")],
            methods: vec![TraitMethodSig {
                name: Symbol::from("eq"),
                docstring: None,
                params: vec![
                    (Symbol::from("a"), TypeExpr::TypeVar(Symbol::from("a"))),
                    (Symbol::from("b"), TypeExpr::TypeVar(Symbol::from("a"))),
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
            result.default_method_defns.iter().any(|d| d.name.as_ref().contains("Eq.eq$Int")),
            "should contain Eq.eq$Int mangled defn"
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
            type_params: vec![Symbol::from("a")],
            methods: vec![TraitMethodSig {
                name: Symbol::from("eq"),
                docstring: None,
                params: vec![
                    (Symbol::from("a"), TypeExpr::TypeVar(Symbol::from("a"))),
                    (Symbol::from("b"), TypeExpr::TypeVar(Symbol::from("a"))),
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
            type_params: vec![Symbol::from("a")],
            methods: vec![TraitMethodSig {
                name: Symbol::from("double"),
                docstring: None,
                params: vec![(Symbol::from("x"), TypeExpr::TypeVar(Symbol::from("a")))],
                ret_type: TypeExpr::TypeVar(Symbol::from("a")),
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

        // The register pass should produce the mangled defn
        let mangled_name = Symbol::from("Double.double$Int");
        assert!(
            !accumulator.default_method_defns.is_empty(),
            "register should produce default_method_defns"
        );
        assert!(
            accumulator.default_method_defns.iter().any(|d| d.name == mangled_name),
            "should contain Double.double$Int"
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

        // (defn idf [x] x) — unconstrained → Concrete, slot allocated at the
        // determination point.
        let idf = |s: u32| TopLevel::Defn(make_defn(
            "idf",
            vec![Symbol::from("x")],
            vec![None],
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

        // constrained → concrete redef: redefine cadd as `(defn cadd [x y] x)`
        // (no constraint). Nothing to reuse (the template was slot-less), so a
        // FRESH slot is allocated and the entry becomes Concrete.
        let cadd_concrete = TopLevel::Defn(make_defn(
            "cadd",
            vec![Symbol::from("x"), Symbol::from("y")],
            vec![None, None],
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
            .filter(|(name, _)| name.as_ref().starts_with("reduce$"))
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
            type_params: vec![Symbol::from("a")],
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

    // spec: design/typecheck/ast-annotation.md §10.2.3 — CheckResult has only
    // { warnings, display }. Structural guard: if a retired field
    // (method_resolutions / mono_defns / default_method_defns /
    // constrained_fn_names / expr_types) is reintroduced, this won't compile.
    #[test]
    fn check_result_slim_shape() {
        use crate::result::CheckResult;
        // Only the two surviving fields are nameable; constructing with exactly
        // them (and reading them back) pins the slim shape.
        let r = CheckResult {
            warnings: Vec::new(),
            display: None,
        };
        let _ = &r.warnings;
        let _ = &r.display;
        assert_eq!(r.warnings.len(), 0);
        assert!(r.display.is_none());
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
            DefKind::UserFn { fn_state: UserFnState::Concrete { got_slot: 7 } },
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
