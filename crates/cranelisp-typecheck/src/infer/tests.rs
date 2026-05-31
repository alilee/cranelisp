    use super::*;
    use crate::checker::TestFixture;
    use cranelisp_types::{ConstructorDef, FQSymbol, FQTypeName, ModuleEntry, ModuleFullPath, Span, Symbol, TypeName, Visibility};

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

    /// Test helper: create an FQTypeName in the "test" module (used for types registered via
    /// register_type_def_self in tc() which has current_module = "test").
    fn test_fqtn(name: &str) -> FQTypeName {
        FQTypeName::new(ModuleFullPath::from("test"), TypeName::from(name))
    }

    /// Test helper: create an FQTypeName in the "primitives" module.
    fn prims_fqtn(name: &str) -> FQTypeName {
        FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from(name))
    }

    fn span(start: u32, end: u32) -> Span {
        Span::new(start, end)
    }

    /// Create a TypeChecker with builtins for testing.
    /// Uses set_current_module to create a "test" module seeded with primitives.
    fn tc() -> TestFixture {
        let mut tc = TestFixture::new();
        tc.set_current_module(ModuleFullPath::from("test"));
        // Import primitives so bare names (add-i64 etc.) resolve.
        seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
        tc
    }

    /// Register a simple enum type for testing.
    fn register_color(tc: &mut TestFixture) {
        tc.register_type_def_self(
            &TypeName::from("Color"),
            &None,
            &[],
            &[
                ConstructorDef {
                    name: Symbol::from("Red"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
                ConstructorDef {
                    name: Symbol::from("Green"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
                ConstructorDef {
                    name: Symbol::from("Blue"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
            ],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();
    }

    // --- Literal tests ---

    // spec: 03-types §3.5.3 — integer literal infers to Int
    #[test]
    fn test_infer_int_lit() {
        let mut tc = tc();
        let mut expr = Expr::IntLit {
            value: 42,
            span: span(0, 2),
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // spec: 03-types §3.5.3 — float literal infers to Float
    #[test]
    fn test_infer_float_lit() {
        let mut tc = tc();
        let mut expr = Expr::FloatLit {
            value: 2.72,
            span: span(0, 4),
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Float);
    }

    // spec: 03-types §3.5.3 — boolean literal infers to Bool
    #[test]
    fn test_infer_bool_lit() {
        let mut tc = tc();
        let mut expr = Expr::BoolLit {
            value: true,
            span: span(0, 4),
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Bool);
    }

    // --- Var tests ---

    // spec: 03-types §3.5.3 — variable reference looks up and instantiates scheme
    #[test]
    fn test_infer_var_defined() {
        let mut tc = tc();
        tc.bind_local_self(Symbol::from("x"), mono(Type::Int));
        let mut expr = Expr::Var {
            name: Symbol::from("x"),
            span: span(0, 1),
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // spec: 03-types §3.5.3 — undefined variable reference is a type error
    #[test]
    fn test_infer_var_undefined() {
        let mut tc = tc();
        let mut expr = Expr::Var {
            name: Symbol::from("x"),
            span: span(0, 1),
            inferred_type: None,
        };
        assert!(tc.infer_expr_for_test(&mut expr).is_err());
    }

    // --- Let tests ---

    // spec: 03-types §3.5.3 — let binding infers value type and propagates to body
    #[test]
    fn test_infer_let_simple() {
        let mut tc = tc();
        // (let [x 42] x)
        let mut expr = Expr::Let {
            bindings: vec![(
                Symbol::from("x"),
                Expr::IntLit {
                    value: 42,
                    span: span(6, 8),
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::Var {
                name: Symbol::from("x"),
                span: span(10, 11),
                inferred_type: None,
            }),
            span: span(0, 12),
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // spec: 03-types §3.5.3 — let sequential bindings: later bindings see earlier ones
    #[test]
    fn test_infer_let_sequential_bindings() {
        let mut tc = tc();
        // (let [x 42 y x] y)
        let mut expr = Expr::Let {
            bindings: vec![
                (
                    Symbol::from("x"),
                    Expr::IntLit {
                        value: 42,
                        span: span(6, 8),
                        inferred_type: None,
                    },
                ),
                (
                    Symbol::from("y"),
                    Expr::Var {
                        name: Symbol::from("x"),
                        span: span(11, 12),
                        inferred_type: None,
                    },
                ),
            ],
            body: Box::new(Expr::Var {
                name: Symbol::from("y"),
                span: span(14, 15),
                inferred_type: None,
            }),
            span: span(0, 16),
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // --- If tests ---

    // spec: 03-types §3.5.3 — if expression: branches unify, result is branch type
    #[test]
    fn test_infer_if_ok() {
        let mut tc = tc();
        // (if true 1 2)
        let mut expr = Expr::If {
            cond: Box::new(Expr::BoolLit {
                value: true,
                span: span(4, 8),
                inferred_type: None,
            }),
            then_branch: Box::new(Expr::IntLit {
                value: 1,
                span: span(9, 10),
                inferred_type: None,
            }),
            else_branch: Box::new(Expr::IntLit {
                value: 2,
                span: span(11, 12),
                inferred_type: None,
            }),
            span: span(0, 13),
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // spec: 03-types §3.5.3 — if condition must unify with Bool
    #[test]
    fn test_infer_if_non_bool_condition() {
        let mut tc = tc();
        // (if 42 1 2) -- condition must be Bool
        let mut expr = Expr::If {
            cond: Box::new(Expr::IntLit {
                value: 42,
                span: span(4, 6),
                inferred_type: None,
            }),
            then_branch: Box::new(Expr::IntLit {
                value: 1,
                span: span(7, 8),
                inferred_type: None,
            }),
            else_branch: Box::new(Expr::IntLit {
                value: 2,
                span: span(9, 10),
                inferred_type: None,
            }),
            span: span(0, 11),
            inferred_type: None,
        };
        let err = tc.infer_expr_for_test(&mut expr).unwrap_err();
        assert!(err.message().contains("type mismatch"));
    }

    // spec: 03-types §3.5.3 — if branches must unify with each other
    #[test]
    fn test_infer_if_branch_mismatch() {
        let mut tc = tc();
        // (if true 1 true) -- branches must agree
        let mut expr = Expr::If {
            cond: Box::new(Expr::BoolLit {
                value: true,
                span: span(4, 8),
                inferred_type: None,
            }),
            then_branch: Box::new(Expr::IntLit {
                value: 1,
                span: span(9, 10),
                inferred_type: None,
            }),
            else_branch: Box::new(Expr::BoolLit {
                value: true,
                span: span(11, 15),
                inferred_type: None,
            }),
            span: span(0, 16),
            inferred_type: None,
        };
        assert!(tc.infer_expr_for_test(&mut expr).is_err());
    }

    // --- Lambda tests ---

    // spec: 03-types §3.5.3 — lambda: params get fresh vars, result is Fn type
    #[test]
    fn test_infer_lambda_identity() {
        let mut tc = tc();
        // (fn [x] x)
        let mut expr = Expr::Lambda {
            params: vec![(Symbol::from("x"), None)],
            body: Box::new(Expr::Var {
                name: Symbol::from("x"),
                span: span(8, 9),
                inferred_type: None,
            }),
            span: span(0, 10),
            inferred_type: None,
        };
        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        // Should be Fn([tN], tN) for some N
        match ty {
            Type::Fn(params, ret) => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0], *ret);
            }
            _ => panic!("expected Fn type, got {ty:?}"),
        }
    }

    // spec: 03-types §3.9.1 — concrete type annotation constrains param type
    #[test]
    fn test_infer_lambda_annotated() {
        let mut tc = tc();
        // (fn [:Int x] x)
        let mut expr = Expr::Lambda {
            params: vec![(Symbol::from("x"), Some(TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int")))))],
            body: Box::new(Expr::Var {
                name: Symbol::from("x"),
                span: span(13, 14),
                inferred_type: None,
            }),
            span: span(0, 15),
            inferred_type: None,
        };
        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(ty, Type::Fn(vec![Type::Int], Box::new(Type::Int)));
    }

    // --- Apply tests ---

    // spec: 03-types §3.5.3 — function application unifies callee with arg types
    #[test]
    fn test_infer_apply_lambda() {
        let mut tc = tc();
        // ((fn [x] x) 42)
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Lambda {
                params: vec![(Symbol::from("x"), None)],
                body: Box::new(Expr::Var {
                    name: Symbol::from("x"),
                    span: span(8, 9),
                    inferred_type: None,
                }),
                span: span(1, 10),
                inferred_type: None,
            }),
            args: vec![Expr::IntLit {
                value: 42,
                span: span(11, 13),
                inferred_type: None,
            }],
            span: span(0, 14),
            resolved_call: None,
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // spec: 03-types §3.5.3 — apply primitive add-i64 records BuiltinFn resolution
    #[test]
    fn test_infer_apply_int_add() {
        let mut tc = tc();
        // (add-i64 1 2) -> Int
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-i64"),
                span: span(1, 8),
                inferred_type: None,
            }),
            args: vec![
                Expr::IntLit {
                    value: 1,
                    span: span(9, 10),
                    inferred_type: None,
                },
                Expr::IntLit {
                    value: 2,
                    span: span(11, 12),
                    inferred_type: None,
                },
            ],
            span: span(0, 13),
            resolved_call: None,
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);

        // Check that a BuiltinFn resolution was recorded
        let resolution = tc.state.method_resolutions.resolved_calls.get(&span(0, 13)).unwrap();
        match resolution {
            ResolvedCall::BuiltinFn { name } => {
                assert_eq!(name.as_ref(), "add-i64");
            }
            _ => panic!("expected BuiltinFn resolution"),
        }
    }

    // spec: 03-types §3.5.3 — apply primitive add-f64 infers Float return
    #[test]
    fn test_infer_apply_float_add() {
        let mut tc = tc();
        // (add-f64 1.0 2.0) -> Float
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-f64"),
                span: span(1, 8),
                inferred_type: None,
            }),
            args: vec![
                Expr::FloatLit {
                    value: 1.0,
                    span: span(9, 12),
                    inferred_type: None,
                },
                Expr::FloatLit {
                    value: 2.0,
                    span: span(13, 16),
                    inferred_type: None,
                },
            ],
            span: span(0, 17),
            resolved_call: None,
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Float);

        let resolution = tc.state.method_resolutions.resolved_calls.get(&span(0, 17)).unwrap();
        match resolution {
            ResolvedCall::BuiltinFn { name } => {
                assert_eq!(name.as_ref(), "add-f64");
            }
            _ => panic!("expected BuiltinFn resolution"),
        }
    }

    // spec: 03-types §3.5.3 — apply comparison primitive returns Bool
    #[test]
    fn test_infer_apply_int_eq() {
        let mut tc = tc();
        // (eq-i64 1 2) -> Bool
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("eq-i64"),
                span: span(1, 7),
                inferred_type: None,
            }),
            args: vec![
                Expr::IntLit {
                    value: 1,
                    span: span(8, 9),
                    inferred_type: None,
                },
                Expr::IntLit {
                    value: 2,
                    span: span(10, 11),
                    inferred_type: None,
                },
            ],
            span: span(0, 12),
            resolved_call: None,
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Bool);
    }

    // spec: appendix-a-builtins §A.3 — not primitive: Bool -> Bool
    #[test]
    fn test_infer_apply_not() {
        let mut tc = tc();
        // (not true) -> Bool
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("not"),
                span: span(1, 4),
                inferred_type: None,
            }),
            args: vec![Expr::BoolLit {
                value: true,
                span: span(5, 9),
                inferred_type: None,
            }],
            span: span(0, 10),
            resolved_call: None,
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Bool);

        let resolution = tc.state.method_resolutions.resolved_calls.get(&span(0, 10)).unwrap();
        match resolution {
            ResolvedCall::BuiltinFn { name } => {
                assert_eq!(name.as_ref(), "not");
            }
            _ => panic!("expected BuiltinFn resolution"),
        }
    }

    // spec: 03-types §3.8.6 — type mismatch: float args to int primitive fails
    #[test]
    fn test_infer_apply_type_mismatch_int_add_float() {
        let mut tc = tc();
        // (add-i64 1.0 2.0) -- type error: float args to int primitive
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-i64"),
                span: span(1, 8),
                inferred_type: None,
            }),
            args: vec![
                Expr::FloatLit {
                    value: 1.0,
                    span: span(9, 12),
                    inferred_type: None,
                },
                Expr::FloatLit {
                    value: 2.0,
                    span: span(13, 16),
                    inferred_type: None,
                },
            ],
            span: span(0, 17),
            resolved_call: None,
            inferred_type: None,
        };
        assert!(tc.infer_expr_for_test(&mut expr).is_err(), "add-i64 with float args should fail");
    }

    // spec: 04-expressions §4.6.3 — too few args triggers auto-curry
    #[test]
    fn test_infer_apply_auto_curry() {
        let mut tc = tc();
        // (add-i64 1) -- too few args, auto-curry returns Fn([Int], Int)
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-i64"),
                span: span(1, 8),
                inferred_type: None,
            }),
            args: vec![Expr::IntLit {
                value: 1,
                span: span(9, 10),
                inferred_type: None,
            }],
            span: span(0, 11),
            resolved_call: None,
            inferred_type: None,
        };
        let ty = tc.infer_expr_for_test(&mut expr).expect("auto-curry should succeed");
        let resolved = tc.apply_subst_self(&ty);
        match resolved {
            Type::Fn(params, ret) => {
                assert_eq!(params.len(), 1, "curried fn should take 1 remaining arg");
                assert_eq!(params[0], Type::Int);
                assert_eq!(*ret, Type::Int);
            }
            other => panic!("expected Fn type, got {:?}", other),
        }
    }

    // spec: 03-types §3.8.3 — too many args is still an arity error
    #[test]
    fn test_infer_apply_too_many_args() {
        let mut tc = tc();
        // (add-i64 1 2 3) -- too many args
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-i64"),
                span: span(1, 8),
                inferred_type: None,
            }),
            args: vec![
                Expr::IntLit { value: 1, span: span(9, 10), inferred_type: None, },
                Expr::IntLit { value: 2, span: span(11, 12), inferred_type: None, },
                Expr::IntLit { value: 3, span: span(13, 14), inferred_type: None, },
            ],
            span: span(0, 15),
            resolved_call: None,
            inferred_type: None,
        };
        assert!(tc.infer_expr_for_test(&mut expr).is_err());
    }

    // --- Match tests ---

    // spec: 06-pattern-matching §6.1 — match enum with all constructors covered
    #[test]
    fn test_infer_match_enum() {
        let mut tc = tc();
        register_color(&mut tc);

        // (match Red [Red 1 Green 2 Blue 3])
        let mut expr = Expr::Match {
            scrutinee: Box::new(Expr::Var {
                name: Symbol::from("Red"),
                span: span(7, 10),
                inferred_type: None,
            }),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: cranelisp_types::SymbolRef::new(None, Symbol::from("Red")),
                        bindings: vec![],
                        span: span(12, 15),
                    },
                    body: Expr::IntLit {
                        value: 1,
                        span: span(16, 17),
                        inferred_type: None,
                    },
                    span: span(12, 17),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: cranelisp_types::SymbolRef::new(None, Symbol::from("Green")),
                        bindings: vec![],
                        span: span(18, 23),
                    },
                    body: Expr::IntLit {
                        value: 2,
                        span: span(24, 25),
                        inferred_type: None,
                    },
                    span: span(18, 25),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: cranelisp_types::SymbolRef::new(None, Symbol::from("Blue")),
                        bindings: vec![],
                        span: span(26, 30),
                    },
                    body: Expr::IntLit {
                        value: 3,
                        span: span(31, 32),
                        inferred_type: None,
                    },
                    span: span(26, 32),
                },
            ],
            span: span(0, 33),
            compiler_generated: false,
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // spec: 06-pattern-matching §6.5.1 — non-exhaustive match on ADT is compile error
    #[test]
    fn test_infer_match_non_exhaustive() {
        let mut tc = tc();
        register_color(&mut tc);

        // Match with only Red -- missing Green, Blue
        let mut expr = Expr::Match {
            scrutinee: Box::new(Expr::Var {
                name: Symbol::from("Red"),
                span: span(7, 10),
                inferred_type: None,
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: cranelisp_types::SymbolRef::new(None, Symbol::from("Red")),
                    bindings: vec![],
                    span: span(12, 15),
                },
                body: Expr::IntLit {
                    value: 1,
                    span: span(16, 17),
                    inferred_type: None,
                },
                span: span(12, 17),
            }],
            span: span(0, 18),
            compiler_generated: false,
            inferred_type: None,
        };
        let err = tc.infer_expr_for_test(&mut expr).unwrap_err();
        assert!(err.message().contains("non-exhaustive"));
    }

    // spec: 06-pattern-matching §6.2.3 — wildcard pattern covers remaining cases
    #[test]
    fn test_infer_match_wildcard() {
        let mut tc = tc();
        register_color(&mut tc);

        // (match Red [Red 1 _ 0])
        let mut expr = Expr::Match {
            scrutinee: Box::new(Expr::Var {
                name: Symbol::from("Red"),
                span: span(7, 10),
                inferred_type: None,
            }),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: cranelisp_types::SymbolRef::new(None, Symbol::from("Red")),
                        bindings: vec![],
                        span: span(12, 15),
                    },
                    body: Expr::IntLit {
                        value: 1,
                        span: span(16, 17),
                        inferred_type: None,
                    },
                    span: span(12, 17),
                },
                MatchArm {
                    pattern: Pattern::Wildcard {
                        span: span(18, 19),
                    },
                    body: Expr::IntLit {
                        value: 0,
                        span: span(20, 21),
                        inferred_type: None,
                    },
                    span: span(18, 21),
                },
            ],
            span: span(0, 22),
            compiler_generated: false,
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // spec: 06-pattern-matching §6.2.4 — variable pattern binds scrutinee value
    #[test]
    fn test_infer_match_var_pattern() {
        let mut tc = tc();
        register_color(&mut tc);

        // (match Red [x 1]) -- var pattern binds scrutinee
        let mut expr = Expr::Match {
            scrutinee: Box::new(Expr::Var {
                name: Symbol::from("Red"),
                span: span(7, 10),
                inferred_type: None,
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Var {
                    name: Symbol::from("x"),
                    span: span(12, 13),
                },
                body: Expr::IntLit {
                    value: 1,
                    span: span(14, 15),
                    inferred_type: None,
                },
                span: span(12, 15),
            }],
            span: span(0, 16),
            compiler_generated: false,
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // --- Annotate tests ---

    // spec: 03-types §3.9.1 — annotation matching inferred type succeeds
    #[test]
    fn test_infer_annotate_matching() {
        let mut tc = tc();
        // (:Int 42) -- annotation matches
        let mut expr = Expr::Annotate {
            annotation: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int"))),
            expr: Box::new(Expr::IntLit {
                value: 42,
                span: span(5, 7),
                inferred_type: None,
            }),
            span: span(0, 8),
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // spec: 03-types §3.9.1 — annotation mismatching inferred type fails
    #[test]
    fn test_infer_annotate_mismatch() {
        let mut tc = tc();
        // (:Bool 42) -- annotation doesn't match
        let mut expr = Expr::Annotate {
            annotation: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Bool"))),
            expr: Box::new(Expr::IntLit {
                value: 42,
                span: span(6, 8),
                inferred_type: None,
            }),
            span: span(0, 9),
            inferred_type: None,
        };
        assert!(tc.infer_expr_for_test(&mut expr).is_err());
    }

    // --- expr_types recording tests ---

    // spec: 03-types §3.5.1 — expr_types map records inferred type per span
    #[test]
    fn test_expr_types_recorded() {
        let mut tc = tc();
        let s = span(0, 2);
        let mut expr = Expr::IntLit { value: 42, span: s, inferred_type: None, };
        tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(tc.state.expr_types.get(&s), Some(&Type::Int));
    }

    // --- Nested expression tests ---

    // spec: 03-types §3.5.3 — nested function application infers correctly
    #[test]
    fn test_infer_nested_arithmetic() {
        let mut tc = tc();
        // (add-i64 (add-i64 1 2) 3)
        let inner = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-i64"),
                span: span(9, 16),
                inferred_type: None,
            }),
            args: vec![
                Expr::IntLit {
                    value: 1,
                    span: span(17, 18),
                    inferred_type: None,
                },
                Expr::IntLit {
                    value: 2,
                    span: span(19, 20),
                    inferred_type: None,
                },
            ],
            span: span(8, 21),
            resolved_call: None,
            inferred_type: None,
        };
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-i64"),
                span: span(1, 8),
                inferred_type: None,
            }),
            args: vec![
                inner,
                Expr::IntLit {
                    value: 3,
                    span: span(23, 24),
                    inferred_type: None,
                },
            ],
            span: span(0, 25),
            resolved_call: None,
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // --- String literal tests (Ring 1) ---

    // spec: 03-types §3.5.3 — string literal infers to String
    #[test]
    fn test_infer_string_lit() {
        let mut tc = tc();
        let mut expr = Expr::StringLit {
            value: "hello".to_string(),
            span: span(0, 7),
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::String);
    }

    // spec: 03-types §3.5.1 — string literal records String in expr_types
    #[test]
    fn test_string_lit_expr_types_recorded() {
        let mut tc = tc();
        let s = span(0, 7);
        let mut expr = Expr::StringLit {
            value: "hello".to_string(),
            span: s,
            inferred_type: None,
        };
        tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(tc.state.expr_types.get(&s), Some(&Type::String));
    }

    // --- Data constructor pattern tests (Ring 1) ---

    /// Register (Option a) with None and Some[:a val].
    fn register_option(tc: &mut TestFixture) {
        tc.register_type_def_self(
            &TypeName::from("Option"),
            &None,
            &[Symbol::from("a")],
            &[
                ConstructorDef {
                    name: Symbol::from("None"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
                ConstructorDef {
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

    // spec: 06-pattern-matching §6.4.1 — data constructor pattern binds field types
    #[test]
    fn test_infer_match_data_constructor_pattern() {
        let mut tc = tc();
        register_option(&mut tc);

        // (match (Some 42) [(Some x) x (None 0)])
        let mut expr = Expr::Match {
            scrutinee: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Some"),
                    span: span(8, 12),
                    inferred_type: None,
                }),
                args: vec![Expr::IntLit {
                    value: 42,
                    span: span(13, 15),
                    inferred_type: None,
                }],
                span: span(7, 16),
                resolved_call: None,
                inferred_type: None,
            }),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: cranelisp_types::SymbolRef::new(None, Symbol::from("Some")),
                        bindings: vec![Symbol::from("x")],
                        span: span(18, 24),
                    },
                    body: Expr::Var {
                        name: Symbol::from("x"),
                        span: span(26, 27),
                        inferred_type: None,
                    },
                    span: span(18, 27),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: cranelisp_types::SymbolRef::new(None, Symbol::from("None")),
                        bindings: vec![],
                        span: span(29, 33),
                    },
                    body: Expr::IntLit {
                        value: 0,
                        span: span(34, 35),
                        inferred_type: None,
                    },
                    span: span(29, 35),
                },
            ],
            span: span(0, 36),
            compiler_generated: false,
            inferred_type: None,
        };

        // Should infer result type Int (x : Int from Some pattern, 0 : Int)
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // spec: 06-pattern-matching §6.2.1 — wrong binding count in constructor pattern is error
    #[test]
    fn test_infer_match_data_constructor_wrong_binding_count() {
        let mut tc = tc();
        register_option(&mut tc);

        // (match (Some 42) [(Some x y) x]) -- too many bindings
        let mut expr = Expr::Match {
            scrutinee: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Some"),
                    span: span(108, 112),
                    inferred_type: None,
                }),
                args: vec![Expr::IntLit {
                    value: 42,
                    span: span(113, 115),
                    inferred_type: None,
                }],
                span: span(107, 116),
                resolved_call: None,
                inferred_type: None,
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: cranelisp_types::SymbolRef::new(None, Symbol::from("Some")),
                    bindings: vec![Symbol::from("x"), Symbol::from("y")],
                    span: span(118, 128),
                },
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: span(130, 131),
                    inferred_type: None,
                },
                span: span(118, 131),
            }],
            span: span(100, 132),
            compiler_generated: false,
            inferred_type: None,
        };

        let err = tc.infer_expr_for_test(&mut expr).unwrap_err();
        assert!(err.message().contains("expects 1 field"));
    }

    // spec: 06-pattern-matching §6.2.2 — nullary constructor with bindings is error
    #[test]
    fn test_infer_match_nullary_with_bindings_errors() {
        let mut tc = tc();
        register_option(&mut tc);

        // (match (Some 1) [(None x) x]) -- None is nullary, no bindings allowed
        let mut expr = Expr::Match {
            scrutinee: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Some"),
                    span: span(208, 212),
                    inferred_type: None,
                }),
                args: vec![Expr::IntLit {
                    value: 1,
                    span: span(213, 214),
                    inferred_type: None,
                }],
                span: span(207, 215),
                resolved_call: None,
                inferred_type: None,
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: cranelisp_types::SymbolRef::new(None, Symbol::from("None")),
                    bindings: vec![Symbol::from("x")],
                    span: span(217, 224),
                },
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: span(226, 227),
                    inferred_type: None,
                },
                span: span(217, 227),
            }],
            span: span(200, 228),
            compiler_generated: false,
            inferred_type: None,
        };

        let err = tc.infer_expr_for_test(&mut expr).unwrap_err();
        assert!(err.message().contains("takes no arguments"));
    }

    // spec: 06-pattern-matching §6.5.1 — non-exhaustive match on Option (missing None)
    #[test]
    fn test_infer_match_option_non_exhaustive() {
        let mut tc = tc();
        register_option(&mut tc);

        // Match only Some, missing None
        let mut expr = Expr::Match {
            scrutinee: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Some"),
                    span: span(308, 312),
                    inferred_type: None,
                }),
                args: vec![Expr::IntLit {
                    value: 1,
                    span: span(313, 314),
                    inferred_type: None,
                }],
                span: span(307, 315),
                resolved_call: None,
                inferred_type: None,
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: cranelisp_types::SymbolRef::new(None, Symbol::from("Some")),
                    bindings: vec![Symbol::from("x")],
                    span: span(317, 324),
                },
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: span(326, 327),
                    inferred_type: None,
                },
                span: span(317, 327),
            }],
            span: span(300, 328),
            compiler_generated: false,
            inferred_type: None,
        };

        let err = tc.infer_expr_for_test(&mut expr).unwrap_err();
        assert!(err.message().contains("None"));
    }

    // --- Lambda expr_types completeness (Ring 1 validation) ---

    // spec: 03-types §3.5.3 — lambda records Fn type in expr_types
    #[test]
    fn test_lambda_expr_types_recorded() {
        let mut tc = tc();
        let s = span(0, 10);
        let mut expr = Expr::Lambda {
            params: vec![(Symbol::from("x"), Some(TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int")))))],
            body: Box::new(Expr::Var {
                name: Symbol::from("x"),
                span: span(13, 14),
                inferred_type: None,
            }),
            span: s,
            inferred_type: None,
        };
        tc.infer_expr_for_test(&mut expr).unwrap();

        // Lambda should record a Fn type in expr_types
        let recorded = tc.state.expr_types.get(&s).unwrap();
        assert!(matches!(recorded, Type::Fn(_, _)));
    }

    // --- Annotate with Applied type (Ring 1) ---

    // spec: 03-types §3.9.1 — annotate with applied type :(Option Int)
    #[test]
    fn test_annotate_with_applied_type() {
        let mut tc = tc();
        register_option(&mut tc);

        // :(Option Int) (Some 42) -- annotate with applied type
        let mut annotate_expr = Expr::Annotate {
            annotation: TypeExpr::Applied(cranelisp_types::TypeRef::new(None, TypeName::from("Option")),
                vec![TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int")))],
            ),
            expr: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Some"),
                    span: span(418, 422),
                    inferred_type: None,
                }),
                args: vec![Expr::IntLit {
                    value: 42,
                    span: span(423, 425),
                    inferred_type: None,
                }],
                span: span(417, 426),
                resolved_call: None,
                inferred_type: None,
            }),
            span: span(400, 427),
            inferred_type: None,
        };

        let ty = tc.infer_expr_for_test(&mut annotate_expr).unwrap();
        assert_eq!(
            ty,
            Type::ADT(test_fqtn("Option"), vec![Type::Int])
        );
    }

    // --- Product type match tests ---

    // spec: 06-pattern-matching §6.4.1 — product type destructuring in match
    #[test]
    fn test_infer_match_product_type() {
        let mut tc = tc();
        // (deftype Point [:Int x :Int y])
        tc.register_type_def_self(
            &TypeName::from("Point"),
            &None,
            &[],
            &[ConstructorDef {
                name: Symbol::from("Point"),
                docstring: None,
                fields: vec![
                    cranelisp_types::FieldDef {
                        name: Symbol::from("x"),
                        type_expr: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int"))),
                        span: Span::SYNTHETIC,
                    },
                    cranelisp_types::FieldDef {
                        name: Symbol::from("y"),
                        type_expr: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int"))),
                        span: Span::SYNTHETIC,
                    },
                ],
                span: Span::SYNTHETIC,
            }],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // (match (Point 1 2) [(Point a b) (add-i64 a b)])
        let mut expr = Expr::Match {
            scrutinee: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Point"),
                    span: span(508, 513),
                    inferred_type: None,
                }),
                args: vec![
                    Expr::IntLit {
                        value: 1,
                        span: span(514, 515),
                        inferred_type: None,
                    },
                    Expr::IntLit {
                        value: 2,
                        span: span(516, 517),
                        inferred_type: None,
                    },
                ],
                span: span(507, 518),
                resolved_call: None,
                inferred_type: None,
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: cranelisp_types::SymbolRef::new(None, Symbol::from("Point")),
                    bindings: vec![Symbol::from("a"), Symbol::from("b")],
                    span: span(520, 530),
                },
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("add-i64"),
                        span: span(532, 539),
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::Var {
                            name: Symbol::from("a"),
                            span: span(540, 541),
                            inferred_type: None,
                        },
                        Expr::Var {
                            name: Symbol::from("b"),
                            span: span(542, 543),
                            inferred_type: None,
                        },
                    ],
                    span: span(531, 544),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(520, 544),
            }],
            span: span(500, 545),
            compiler_generated: false,
            inferred_type: None,
        };

        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // spec: 05-definitions §5.2.7 — data constructor applied as function
    #[test]
    fn test_infer_constructor_as_function() {
        let mut tc = tc();
        register_option(&mut tc);

        // (Some 42) -- constructor applied to argument
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("Some"),
                span: span(601, 605),
                inferred_type: None,
            }),
            args: vec![Expr::IntLit {
                value: 42,
                span: span(606, 608),
                inferred_type: None,
            }],
            span: span(600, 609),
            resolved_call: None,
            inferred_type: None,
        };

        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(
            ty,
            Type::ADT(test_fqtn("Option"), vec![Type::Int])
        );
    }

    // spec: 05-definitions §5.2.7 — nullary constructor is polymorphic value
    #[test]
    fn test_infer_none_has_polymorphic_type() {
        let mut tc = tc();
        register_option(&mut tc);

        // None on its own should be (Option tN) for some N
        let mut expr = Expr::Var {
            name: Symbol::from("None"),
            span: span(700, 704),
            inferred_type: None,
        };

        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        match &ty {
            Type::ADT(name, args) => {
                assert_eq!(name.name.as_ref(), "Option");
                assert_eq!(args.len(), 1);
                // The arg should be a fresh var
                assert!(matches!(args[0], Type::Var(_)));
            }
            _ => panic!("None should have ADT type, got {ty:?}"),
        }
    }

    // spec: 03-types §3.5.3 — if branches with String type unify
    #[test]
    fn test_infer_string_in_if_branches() {
        let mut tc = tc();
        // (if true "hello" "world")
        let mut expr = Expr::If {
            cond: Box::new(Expr::BoolLit {
                value: true,
                span: span(804, 808),
                inferred_type: None,
            }),
            then_branch: Box::new(Expr::StringLit {
                value: "hello".to_string(),
                span: span(809, 816),
                inferred_type: None,
            }),
            else_branch: Box::new(Expr::StringLit {
                value: "world".to_string(),
                span: span(817, 824),
                inferred_type: None,
            }),
            span: span(800, 825),
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::String);
    }

    // spec: 03-types §3.5.3 — let binding with String value
    #[test]
    fn test_infer_string_in_let() {
        let mut tc = tc();
        // (let [s "hello"] s)
        let mut expr = Expr::Let {
            bindings: vec![(
                Symbol::from("s"),
                Expr::StringLit {
                    value: "hello".to_string(),
                    span: span(906, 913),
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::Var {
                name: Symbol::from("s"),
                span: span(915, 916),
                inferred_type: None,
            }),
            span: span(900, 917),
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::String);
    }

    // --- Vec literal tests (Sprint 3) ---

    // spec: 03-types §3.5.3 — Vec literal with Int elements infers (Vec Int)
    #[test]
    fn test_infer_vec_lit_ints() {
        let mut tc = tc();
        // [1 2 3]
        let mut expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 1, span: span(1001, 1002), inferred_type: None, },
                Expr::IntLit { value: 2, span: span(1003, 1004), inferred_type: None, },
                Expr::IntLit { value: 3, span: span(1005, 1006), inferred_type: None, },
            ],
            span: span(1000, 1007),
            inferred_type: None,
        };
        assert_eq!(
            tc.infer_expr_for_test(&mut expr).unwrap(),
            Type::ADT(prims_fqtn("Vec"), vec![Type::Int])
        );
    }

    // spec: 03-types §3.5.3 — Vec literal with String elements infers (Vec String)
    #[test]
    fn test_infer_vec_lit_strings() {
        let mut tc = tc();
        // ["a" "b"]
        let mut expr = Expr::VecLit {
            elements: vec![
                Expr::StringLit { value: "a".into(), span: span(1101, 1104), inferred_type: None, },
                Expr::StringLit { value: "b".into(), span: span(1105, 1108), inferred_type: None, },
            ],
            span: span(1100, 1109),
            inferred_type: None,
        };
        assert_eq!(
            tc.infer_expr_for_test(&mut expr).unwrap(),
            Type::ADT(prims_fqtn("Vec"), vec![Type::String])
        );
    }

    // spec: 03-types §3.5.3 — empty Vec literal is polymorphic (Vec a)
    #[test]
    fn test_infer_vec_lit_empty_is_polymorphic() {
        let mut tc = tc();
        // []
        let mut expr = Expr::VecLit {
            elements: vec![],
            span: span(1200, 1202),
            inferred_type: None,
        };
        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        match &ty {
            Type::ADT(name, args) => {
                assert_eq!(name.name.as_ref(), "Vec");
                assert_eq!(args.len(), 1);
                // Element type should be a fresh type variable
                assert!(matches!(args[0], Type::Var(_)));
            }
            _ => panic!("empty vec should be ADT(Vec, [Var]), got {ty:?}"),
        }
    }

    // spec: 03-types §3.5.3 — Vec literal elements must have same type
    #[test]
    fn test_infer_vec_lit_type_mismatch() {
        let mut tc = tc();
        // [1 "hello"] -- Int vs String
        let mut expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 1, span: span(1301, 1302), inferred_type: None, },
                Expr::StringLit { value: "hello".into(), span: span(1303, 1310), inferred_type: None, },
            ],
            span: span(1300, 1311),
            inferred_type: None,
        };
        let err = tc.infer_expr_for_test(&mut expr).unwrap_err();
        assert!(err.message().contains("mismatch"), "expected type mismatch error, got: {}", err.message());
    }

    // spec: 03-types §3.5.3 — Vec literal with Bool elements infers (Vec Bool)
    #[test]
    fn test_infer_vec_lit_booleans() {
        let mut tc = tc();
        // [true false]
        let mut expr = Expr::VecLit {
            elements: vec![
                Expr::BoolLit { value: true, span: span(1401, 1405), inferred_type: None, },
                Expr::BoolLit { value: false, span: span(1406, 1411), inferred_type: None, },
            ],
            span: span(1400, 1412),
            inferred_type: None,
        };
        assert_eq!(
            tc.infer_expr_for_test(&mut expr).unwrap(),
            Type::ADT(prims_fqtn("Vec"), vec![Type::Bool])
        );
    }

    // spec: 03-types §3.5.3 — Vec literal in let binding propagates element type
    #[test]
    fn test_infer_vec_lit_in_let_binding() {
        let mut tc = tc();
        // (let [xs [1 2 3]] xs)
        let mut expr = Expr::Let {
            bindings: vec![(
                Symbol::from("xs"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 1, span: span(1508, 1509), inferred_type: None, },
                        Expr::IntLit { value: 2, span: span(1510, 1511), inferred_type: None, },
                        Expr::IntLit { value: 3, span: span(1512, 1513), inferred_type: None, },
                    ],
                    span: span(1507, 1514),
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::Var {
                name: Symbol::from("xs"),
                span: span(1516, 1518),
                inferred_type: None,
            }),
            span: span(1500, 1519),
            inferred_type: None,
        };
        assert_eq!(
            tc.infer_expr_for_test(&mut expr).unwrap(),
            Type::ADT(prims_fqtn("Vec"), vec![Type::Int])
        );
    }

    // spec: 03-types §3.5.3 — Vec literal as function argument unifies element type
    #[test]
    fn test_infer_vec_lit_as_function_arg() {
        let mut tc = tc();
        // Define a function that takes (Vec Int) -> Int
        tc.bind_local_self(
            Symbol::from("vec-len"),
            mono(Type::Fn(
                vec![Type::ADT(prims_fqtn("Vec"), vec![Type::Int])],
                Box::new(Type::Int),
            )),
        );
        // (vec-len [1 2 3])
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: span(1601, 1608),
                inferred_type: None,
            }),
            args: vec![Expr::VecLit {
                elements: vec![
                    Expr::IntLit { value: 1, span: span(1610, 1611), inferred_type: None, },
                    Expr::IntLit { value: 2, span: span(1612, 1613), inferred_type: None, },
                    Expr::IntLit { value: 3, span: span(1614, 1615), inferred_type: None, },
                ],
                span: span(1609, 1616),
                inferred_type: None,
            }],
            span: span(1600, 1617),
            resolved_call: None,
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // spec: 03-types §3.5.3 — lambda returning Vec infers (Fn [Int] (Vec Int))
    #[test]
    fn test_infer_vec_lit_as_function_return() {
        let mut tc = tc();
        // (fn [x] [x]) -- returns Vec of the param type
        let mut expr = Expr::Lambda {
            params: vec![(Symbol::from("x"), Some(TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int")))))],
            body: Box::new(Expr::VecLit {
                elements: vec![Expr::Var {
                    name: Symbol::from("x"),
                    span: span(1710, 1711),
                    inferred_type: None,
                }],
                span: span(1709, 1712),
                inferred_type: None,
            }),
            span: span(1700, 1713),
            inferred_type: None,
        };
        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(
            ty,
            Type::Fn(
                vec![Type::Int],
                Box::new(Type::ADT(prims_fqtn("Vec"), vec![Type::Int]))
            )
        );
    }

    // spec: 03-types §3.5.3 — single-element Vec literal infers element type
    #[test]
    fn test_infer_vec_lit_single_element() {
        let mut tc = tc();
        // [42]
        let mut expr = Expr::VecLit {
            elements: vec![Expr::IntLit { value: 42, span: span(1801, 1803), inferred_type: None, }],
            span: span(1800, 1804),
            inferred_type: None,
        };
        assert_eq!(
            tc.infer_expr_for_test(&mut expr).unwrap(),
            Type::ADT(prims_fqtn("Vec"), vec![Type::Int])
        );
    }

    // spec: 03-types §3.5.1 — Vec literal records type in expr_types map
    #[test]
    fn test_infer_vec_lit_expr_type_recorded() {
        let mut tc = tc();
        let s = span(1900, 1907);
        let mut expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 1, span: span(1901, 1902), inferred_type: None, },
                Expr::IntLit { value: 2, span: span(1903, 1904), inferred_type: None, },
            ],
            span: s,
            inferred_type: None,
        };
        tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(
            tc.state.expr_types.get(&s),
            Some(&Type::ADT(prims_fqtn("Vec"), vec![Type::Int]))
        );
    }

    // spec: 03-types §3.5.3 — Vec literal with Float elements infers (Vec Float)
    #[test]
    fn test_infer_vec_lit_floats() {
        let mut tc = tc();
        // [1.0 2.0 3.0]
        let mut expr = Expr::VecLit {
            elements: vec![
                Expr::FloatLit { value: 1.0, span: span(2001, 2004), inferred_type: None, },
                Expr::FloatLit { value: 2.0, span: span(2005, 2008), inferred_type: None, },
                Expr::FloatLit { value: 3.0, span: span(2009, 2012), inferred_type: None, },
            ],
            span: span(2000, 2013),
            inferred_type: None,
        };
        assert_eq!(
            tc.infer_expr_for_test(&mut expr).unwrap(),
            Type::ADT(prims_fqtn("Vec"), vec![Type::Float])
        );
    }

    // -----------------------------------------------------------------------
    // resolve_primitive_jit_name tests (pipeline-orchestration §3)
    // -----------------------------------------------------------------------

    // spec: pipeline-orchestration §3 — unqualified primitive resolves to bare name
    #[test]
    fn test_resolve_primitive_unqualified() {
        let tc = tc();
        let result = tc.resolve_primitive_jit_name_self("add-i64");
        assert_eq!(result.as_deref(), Some("add-i64"));
    }

    // spec: pipeline-orchestration §3 — non-primitive returns None
    #[test]
    fn test_resolve_primitive_non_primitive() {
        let tc = tc();
        let result = tc.resolve_primitive_jit_name_self("if");
        // "if" is a SpecialForm, not a Primitive
        assert!(result.is_none(), "special forms should not resolve as primitives");
    }

    // spec: pipeline-orchestration §3 — unknown name returns None
    #[test]
    fn test_resolve_primitive_unknown() {
        let tc = tc();
        let result = tc.resolve_primitive_jit_name_self("nonexistent");
        assert!(result.is_none());
    }

    // spec: pipeline-orchestration §3 — qualified macros/sconcat resolves to bare "sconcat"
    #[test]
    fn test_resolve_primitive_qualified_sconcat() {
        let tc = tc();
        let result = tc.resolve_primitive_jit_name_self("macros/sconcat");
        assert_eq!(
            result.as_deref(),
            Some("sconcat"),
            "macros/sconcat should resolve to bare name 'sconcat'"
        );
    }

    // spec: pipeline-orchestration §3 — qualified name for non-primitive returns None
    #[test]
    fn test_resolve_primitive_qualified_non_primitive() {
        let tc = tc();
        // macros/SNil is a Constructor, not a Primitive
        let result = tc.resolve_primitive_jit_name_self("macros/SNil");
        assert!(result.is_none(), "constructors should not resolve as primitives");
    }

    // spec: pipeline-orchestration §3 — qualified name in unknown module returns None
    #[test]
    fn test_resolve_primitive_qualified_unknown_module() {
        let tc = tc();
        let result = tc.resolve_primitive_jit_name_self("unknown/foo");
        assert!(result.is_none());
    }

    // spec: pipeline-orchestration §3 — extern primitives resolve (str-concat)
    #[test]
    fn test_resolve_primitive_extern() {
        let tc = tc();
        let result = tc.resolve_primitive_jit_name_self("str-concat");
        assert_eq!(result.as_deref(), Some("str-concat"));
    }

    // spec: pipeline-orchestration §3 — quote-sexp resolves as primitive
    #[test]
    fn test_resolve_primitive_quote_sexp() {
        let tc = tc();
        let result = tc.resolve_primitive_jit_name_self("quote-sexp");
        assert_eq!(result.as_deref(), Some("quote-sexp"));
    }

    // -----------------------------------------------------------------------
    // B2: in_call_position scoping — args must NOT be in call position
    // -----------------------------------------------------------------------

    /// Register a constrained function "cfn" in the current module for testing.
    fn register_constrained_fn(tc: &mut TestFixture) {
        use cranelisp_types::{ConstrainedFn, DefnVariant};

        let a_var = tc.fresh_var();
        let a_id = match &a_var { Type::Var(id) => *id, _ => unreachable!() };
        let fn_ty = Type::Fn(vec![a_var.clone(), a_var.clone()], Box::new(a_var));
        let scheme = Scheme {
            type_vars: vec![a_id],
            constraints: {
                let mut c = HashMap::new();
                c.insert(a_id, vec![cranelisp_types::FQTraitName::new(
                    cranelisp_types::ModuleFullPath::from("test"),
                    cranelisp_types::TraitName::from("Num"),
                )]);
                c
            },
            ty: fn_ty,
        };

        // Bind in scope so infer_var finds it
        tc.bind_local_self(Symbol::from("cfn"), scheme.clone());

        // Register in module so the constrained_fn check finds it
        tc.symbol_table_mut().insert(
            Symbol::from("cfn"),
            ModuleEntry::def(
                scheme.clone(),
                cranelisp_types::DefKind::UserFn {
                    constrained_fn: Some(Box::new(ConstrainedFn {
                        variant: DefnVariant {
                            params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                            body: Expr::IntLit { value: 0, span: Span::SYNTHETIC, inferred_type: None, },
                            span: Span::SYNTHETIC,
                        },
                        scheme: scheme.clone(),
                    })),
                },
            )
            .param_names(vec![Symbol::from("x"), Symbol::from("y")])
            .build(),
        );
    }

    // spec: 03-types §3.6.6 — constrained fn as argument in nested apply is rejected
    #[test]
    fn test_constrained_fn_rejected_as_arg_in_nested_apply() {
        let mut tc = tc();
        register_constrained_fn(&mut tc);

        // Set up: (fn [f] f) as an identity function
        tc.bind_local_self(
            Symbol::from("id"),
            Scheme {
                type_vars: vec![],
                ty: Type::Fn(
                    vec![Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int))],
                    Box::new(Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int))),
                ),
                constraints: HashMap::new(),
            },
        );

        // (id cfn) — cfn is an argument, NOT in call position → should error
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("id"),
                span: span(3000, 3002),
                inferred_type: None,
            }),
            args: vec![Expr::Var {
                name: Symbol::from("cfn"),
                span: span(3003, 3006),
                inferred_type: None,
            }],
            span: span(2999, 3007),
            resolved_call: None,
            inferred_type: None,
        };

        let err = tc.infer_expr_for_test(&mut expr).unwrap_err();
        assert!(
            err.message().contains("constrained function"),
            "should reject constrained fn as argument, got: {}",
            err.message()
        );
    }

    // spec: 03-types §3.6.6 — constrained fn in call position of nested apply is allowed
    #[test]
    fn test_constrained_fn_allowed_in_call_position() {
        let mut tc = tc();
        register_constrained_fn(&mut tc);

        // (cfn 1 2) — cfn is in call position → should succeed
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("cfn"),
                span: span(3100, 3103),
                inferred_type: None,
            }),
            args: vec![
                Expr::IntLit { value: 1, span: span(3104, 3105), inferred_type: None, },
                Expr::IntLit { value: 2, span: span(3106, 3107), inferred_type: None, },
            ],
            span: span(3099, 3108),
            resolved_call: None,
            inferred_type: None,
        };

        // Should succeed (constrained fn in call position is allowed)
        assert!(tc.infer_expr_for_test(&mut expr).is_ok());
    }

    // -----------------------------------------------------------------------
    // Trait constraint eagerness: trait methods with wrong types error at call site
    // -----------------------------------------------------------------------

    /// Set up Num trait with + method (impl for Int, Float only)
    /// and Ord trait with < method (impl for Int, Float only).
    fn register_num_and_ord_traits(tc: &mut TestFixture) {
        use cranelisp_types::{DefnVariant, TraitDecl, TraitImpl, TraitMethodSig, TraitName, TypeExpr, Defn};

        // Num trait: + :: (Fn [a a] a)
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

        // impl Num for Int
        let int_impl = TraitImpl {
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
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: Span::SYNTHETIC,
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: Span::SYNTHETIC, inferred_type: None, },
                            Expr::Var { name: Symbol::from("y"), span: Span::SYNTHETIC, inferred_type: None, },
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
        tc.register_trait_impl_self(&int_impl).unwrap();

        // impl Num for Float
        let float_impl = TraitImpl {
            trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Num")),
            target: cranelisp_types::TypeExpr::Named(
                cranelisp_types::TypeRef::new(None, TypeName::from("Float")),
            ),
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("+"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-f64"),
                            span: Span::SYNTHETIC,
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: Span::SYNTHETIC, inferred_type: None, },
                            Expr::Var { name: Symbol::from("y"), span: Span::SYNTHETIC, inferred_type: None, },
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
        tc.register_trait_impl_self(&float_impl).unwrap();

        // Ord trait: < :: (Fn [a a] Bool)
        let ord_decl = TraitDecl {
            name: TraitName::from("Ord"),
            docstring: None,
            type_params: vec![Symbol::from("a")],
            methods: vec![TraitMethodSig {
                name: Symbol::from("<"),
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
        tc.register_trait_decl_self(&ord_decl).unwrap();

        // impl Ord for Int
        let int_ord_impl = TraitImpl {
            trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Ord")),
            target: cranelisp_types::TypeExpr::Named(
                cranelisp_types::TypeRef::new(None, TypeName::from("Int")),
            ),
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("<"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("lt-i64"),
                            span: Span::SYNTHETIC,
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: Span::SYNTHETIC, inferred_type: None, },
                            Expr::Var { name: Symbol::from("y"), span: Span::SYNTHETIC, inferred_type: None, },
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
        tc.register_trait_impl_self(&int_ord_impl).unwrap();

        tc.clear_transient_state();
    }

    // spec: 07-traits §7.4.3 — (+ true true) errors: Bool has no Num impl
    #[test]
    fn test_trait_method_plus_bool_error() {
        let mut tc = tc();
        register_num_and_ord_traits(&mut tc);

        // (+ true true)
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("+"),
                span: span(4001, 4002),
                inferred_type: None,
            }),
            args: vec![
                Expr::BoolLit { value: true, span: span(4003, 4007), inferred_type: None, },
                Expr::BoolLit { value: true, span: span(4008, 4012), inferred_type: None, },
            ],
            span: span(4000, 4013),
            resolved_call: None,
            inferred_type: None,
        };

        let err = tc.infer_expr_for_test(&mut expr).unwrap_err();
        assert!(
            err.message().contains("no impl of trait Num for type Bool"),
            "expected Num/Bool error, got: {}",
            err.message()
        );
    }

    // spec: 07-traits §7.4.3 — (+ "a" "b") errors: String has no Num impl
    #[test]
    fn test_trait_method_plus_string_error() {
        let mut tc = tc();
        register_num_and_ord_traits(&mut tc);

        // (+ "a" "b")
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("+"),
                span: span(4101, 4102),
                inferred_type: None,
            }),
            args: vec![
                Expr::StringLit { value: "a".to_string(), span: span(4103, 4106), inferred_type: None, },
                Expr::StringLit { value: "b".to_string(), span: span(4107, 4110), inferred_type: None, },
            ],
            span: span(4100, 4111),
            resolved_call: None,
            inferred_type: None,
        };

        let err = tc.infer_expr_for_test(&mut expr).unwrap_err();
        assert!(
            err.message().contains("no impl of trait Num for type String"),
            "expected Num/String error, got: {}",
            err.message()
        );
    }

    // spec: 07-traits §7.4.3 — (< true false) errors: Bool has no Ord impl
    #[test]
    fn test_trait_method_lt_bool_error() {
        let mut tc = tc();
        register_num_and_ord_traits(&mut tc);

        // (< true false)
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("<"),
                span: span(4201, 4202),
                inferred_type: None,
            }),
            args: vec![
                Expr::BoolLit { value: true, span: span(4203, 4207), inferred_type: None, },
                Expr::BoolLit { value: false, span: span(4208, 4213), inferred_type: None, },
            ],
            span: span(4200, 4214),
            resolved_call: None,
            inferred_type: None,
        };

        let err = tc.infer_expr_for_test(&mut expr).unwrap_err();
        assert!(
            err.message().contains("no impl of trait Ord for type Bool"),
            "expected Ord/Bool error, got: {}",
            err.message()
        );
    }

    // spec: 07-traits §7.4.3 — (< "a" "b") errors: String has no Ord impl
    #[test]
    fn test_trait_method_lt_string_error() {
        let mut tc = tc();
        register_num_and_ord_traits(&mut tc);

        // (< "a" "b")
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("<"),
                span: span(4301, 4302),
                inferred_type: None,
            }),
            args: vec![
                Expr::StringLit { value: "a".to_string(), span: span(4303, 4306), inferred_type: None, },
                Expr::StringLit { value: "b".to_string(), span: span(4307, 4310), inferred_type: None, },
            ],
            span: span(4300, 4311),
            resolved_call: None,
            inferred_type: None,
        };

        let err = tc.infer_expr_for_test(&mut expr).unwrap_err();
        assert!(
            err.message().contains("no impl of trait Ord for type String"),
            "expected Ord/String error, got: {}",
            err.message()
        );
    }

    // spec: 07-traits §7.4.3 — (+ 1 true) errors: type mismatch (Int vs Bool)
    #[test]
    fn test_trait_method_mixed_types_error() {
        let mut tc = tc();
        register_num_and_ord_traits(&mut tc);

        // (+ 1 true) — first arg is Int, second is Bool → unification error
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("+"),
                span: span(4401, 4402),
                inferred_type: None,
            }),
            args: vec![
                Expr::IntLit { value: 1, span: span(4403, 4404), inferred_type: None, },
                Expr::BoolLit { value: true, span: span(4405, 4409), inferred_type: None, },
            ],
            span: span(4400, 4410),
            resolved_call: None,
            inferred_type: None,
        };

        // Should error: either unification fails (Int vs Bool) or constraint fails
        assert!(tc.infer_expr_for_test(&mut expr).is_err());
    }

    // spec: 07-traits §7.4.1 — (+ 1 2) succeeds: Int has Num impl
    #[test]
    fn test_trait_method_plus_int_succeeds() {
        let mut tc = tc();
        register_num_and_ord_traits(&mut tc);

        // (+ 1 2) -> Int
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("+"),
                span: span(4501, 4502),
                inferred_type: None,
            }),
            args: vec![
                Expr::IntLit { value: 1, span: span(4503, 4504), inferred_type: None, },
                Expr::IntLit { value: 2, span: span(4505, 4506), inferred_type: None, },
            ],
            span: span(4500, 4507),
            resolved_call: None,
            inferred_type: None,
        };

        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(ty, Type::Int);

        // Check resolution was recorded — FIXME 0185: primitive trait-method
        // resolution short-circuits to ResolvedCall::BuiltinFn instead of
        // TraitMethod, so backend can inline the primitive without paying the
        // impl-body call frame. (Num, +, Int) → add-i64.
        let resolution = tc.state.method_resolutions.resolved_calls.get(&span(4500, 4507)).unwrap();
        match resolution {
            ResolvedCall::BuiltinFn { name } => {
                assert_eq!(name.as_ref(), "add-i64");
            }
            _ => panic!("expected BuiltinFn resolution (primitive trait-method short-circuit per FIXME 0185), got {resolution:?}"),
        }
    }

    // spec: 07-traits §7.4.1 — (+ 1.0 2.0) succeeds: Float has Num impl
    #[test]
    fn test_trait_method_plus_float_succeeds() {
        let mut tc = tc();
        register_num_and_ord_traits(&mut tc);

        // (+ 1.0 2.0) -> Float
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("+"),
                span: span(4601, 4602),
                inferred_type: None,
            }),
            args: vec![
                Expr::FloatLit { value: 1.0, span: span(4603, 4606), inferred_type: None, },
                Expr::FloatLit { value: 2.0, span: span(4607, 4610), inferred_type: None, },
            ],
            span: span(4600, 4611),
            resolved_call: None,
            inferred_type: None,
        };

        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(ty, Type::Float);
    }
