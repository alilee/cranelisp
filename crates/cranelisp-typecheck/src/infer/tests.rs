    use super::*;
    use std::collections::HashMap;
    use crate::checker::TestFixture;
    use cranelisp_types::{ConstructorDef, FQSymbol, FQTypeName, ModuleEntry, ModuleFullPath, Scheme, Span, Symbol, TypeName, Visibility};

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
    ///
    /// Narrowed (FIXME 0243) from `TestFixture::new()` (= `full()`) to the
    /// content the inference tests in this file actually consume: builtin type
    /// names + the Ring 0/1/3 primitive `Def`s (`add-i64` etc.) + the synthetic
    /// `macros` module (`macros/sconcat` resolution). The inference tests do
    /// not consult the IO ADT or special-form symbol-table entries (special
    /// forms are handled at the AST level, not via name lookup), so `with_io()`
    /// and `with_special_forms()` are dropped. Bootstrap order: primitives and
    /// macros both require `with_builtin_type_names()` first.
    fn tc() -> TestFixture {
        let mut tc = TestFixture::with_content(
            crate::builtins::FixtureBuilder::new()
                .with_builtin_type_names()
                .with_primitives()
                .with_macros_sexp(),
        );
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
        let mut expr = Expr::var(Symbol::from("x"), span(0, 1));
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // spec: 03-types §3.5.3 — undefined variable reference is a type error
    #[test]
    fn test_infer_var_undefined() {
        let mut tc = tc();
        let mut expr = Expr::var(Symbol::from("x"), span(0, 1));
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
            body: Box::new(Expr::var(Symbol::from("x"), span(10, 11))),
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
                    Expr::var(Symbol::from("x"), span(11, 12)),
                ),
            ],
            body: Box::new(Expr::var(Symbol::from("y"), span(14, 15))),
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
            body: Box::new(Expr::var(Symbol::from("x"), span(8, 9))),
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

    // RU (FIXME 0595 item 2): `infer_lambda`'s per-body inference state is torn
    // down symmetrically on BOTH the Ok and Err paths — a body-inference error
    // must NOT leave the shared `written_var_scope` as `None` (the pre-existing `?`
    // exit skipped the re-install) nor leak the pushed env frame. Pin: seed the
    // shared scope, run a lambda whose body references an undefined variable (the
    // body infer errors), and assert the scope survives + the frame is popped.
    #[test]
    fn infer_lambda_teardown_is_symmetric_on_body_error() {
        let mut tc = tc();
        let mut scope = std::collections::HashMap::new();
        scope.insert(Symbol::from("a"), 999u32);
        tc.state.written_var_scope = Some(scope.clone());
        let frames_before = tc.state.env.top_frame_index();

        // (fn [y] undefined-name) — the body Var errors at infer time.
        let mut expr = Expr::Lambda {
            params: vec![(Symbol::from("y"), None)],
            body: Box::new(Expr::var(Symbol::from("undefined-name"), span(8, 22))),
            span: span(0, 23),
            inferred_type: None,
        };
        let result = tc.infer_expr_for_test(&mut expr);
        assert!(result.is_err(), "an undefined body var must make infer_lambda error");

        // The shared scope is re-installed (never None) on the error path.
        assert_eq!(
            tc.state.written_var_scope, Some(scope),
            "infer_lambda must restore the shared written_var_scope on the error path"
        );
        // The pushed env frame is popped on the error path.
        assert_eq!(
            tc.state.env.top_frame_index(),
            frames_before,
            "infer_lambda must pop its pushed env frame on the error path"
        );
    }

    // spec: 03-types §3.9.1 — concrete type annotation constrains param type
    #[test]
    fn test_infer_lambda_annotated() {
        let mut tc = tc();
        // (fn [:Int x] x)
        let mut expr = Expr::Lambda {
            params: vec![(Symbol::from("x"), Some(TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int")))))],
            body: Box::new(Expr::var(Symbol::from("x"), span(13, 14))),
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
                body: Box::new(Expr::var(Symbol::from("x"), span(8, 9))),
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
            callee: Box::new(Expr::var(Symbol::from("add-i64"), span(1, 8))),
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
            callee: Box::new(Expr::var(Symbol::from("add-f64"), span(1, 8))),
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
            callee: Box::new(Expr::var(Symbol::from("eq-i64"), span(1, 7))),
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
            callee: Box::new(Expr::var(Symbol::from("not"), span(1, 4))),
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
            callee: Box::new(Expr::var(Symbol::from("add-i64"), span(1, 8))),
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
            callee: Box::new(Expr::var(Symbol::from("add-i64"), span(1, 8))),
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

    // spec: 05-definitions §5.2.7 — an under-applied ADT constructor is an
    // ARITY ERROR, not an auto-curry. With the S79 product-ctor dual facet a
    // single-ctor product (`Point`) is an ordinary got-slotted ctor `Def` whose
    // function-type scheme is curry-shaped; without the ctor guard in
    // `try_auto_curry` it would silently curry into `Fn([Int], Point)`. The
    // constructor must reject the partial application instead.
    #[test]
    fn test_infer_product_ctor_under_application_is_arity_error() {
        let mut tc = tc();
        // (deftype Point [:Int x :Int y]) — single-ctor product (dual facet).
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
                        type_expr: TypeExpr::Named(cranelisp_types::TypeRef::new(
                            None,
                            TypeName::from("Int"),
                        )),
                        span: Span::SYNTHETIC,
                    },
                    cranelisp_types::FieldDef {
                        name: Symbol::from("y"),
                        type_expr: TypeExpr::Named(cranelisp_types::TypeRef::new(
                            None,
                            TypeName::from("Int"),
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

        // (Point 1) — one arg for a two-field ctor. MUST be an arity error,
        // NOT a curried closure.
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("Point"), span(1, 6))),
            args: vec![Expr::IntLit {
                value: 1,
                span: span(7, 8),
                inferred_type: None,
            }],
            span: span(0, 9),
            resolved_call: None,
            inferred_type: None,
        };
        let err = tc
            .infer_expr_for_test(&mut expr)
            .expect_err("under-applied product ctor must be an arity error, not a curry");
        let msg = err.message();
        assert!(
            msg.contains("Point") && (msg.contains("expects") || msg.contains("argument")),
            "expected a constructor arity diagnostic naming Point; got: {msg}"
        );
    }

    // spec: 03-types §3.8.3 — too many args is still an arity error
    #[test]
    fn test_infer_apply_too_many_args() {
        let mut tc = tc();
        // (add-i64 1 2 3) -- too many args
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("add-i64"), span(1, 8))),
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
            scrutinee: Box::new(Expr::var(Symbol::from("Red"), span(7, 10))),
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
            scrutinee: Box::new(Expr::var(Symbol::from("Red"), span(7, 10))),
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
            scrutinee: Box::new(Expr::var(Symbol::from("Red"), span(7, 10))),
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
            scrutinee: Box::new(Expr::var(Symbol::from("Red"), span(7, 10))),
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
            callee: Box::new(Expr::var(Symbol::from("add-i64"), span(9, 16))),
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
            callee: Box::new(Expr::var(Symbol::from("add-i64"), span(1, 8))),
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
                callee: Box::new(Expr::var(Symbol::from("Some"), span(8, 12))),
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
                    body: Expr::var(Symbol::from("x"), span(26, 27)),
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
                callee: Box::new(Expr::var(Symbol::from("Some"), span(108, 112))),
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
                body: Expr::var(Symbol::from("x"), span(130, 131)),
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
                callee: Box::new(Expr::var(Symbol::from("Some"), span(208, 212))),
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
                body: Expr::var(Symbol::from("x"), span(226, 227)),
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
                callee: Box::new(Expr::var(Symbol::from("Some"), span(308, 312))),
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
                body: Expr::var(Symbol::from("x"), span(326, 327)),
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
            body: Box::new(Expr::var(Symbol::from("x"), span(13, 14))),
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
                callee: Box::new(Expr::var(Symbol::from("Some"), span(418, 422))),
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
                callee: Box::new(Expr::var(Symbol::from("Point"), span(508, 513))),
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
                    callee: Box::new(Expr::var(Symbol::from("add-i64"), span(532, 539))),
                    args: vec![
                        Expr::var(Symbol::from("a"), span(540, 541)),
                        Expr::var(Symbol::from("b"), span(542, 543)),
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
            callee: Box::new(Expr::var(Symbol::from("Some"), span(601, 605))),
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
        let mut expr = Expr::var(Symbol::from("None"), span(700, 704));

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
            body: Box::new(Expr::var(Symbol::from("s"), span(915, 916))),
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
            body: Box::new(Expr::var(Symbol::from("xs"), span(1516, 1518))),
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
            callee: Box::new(Expr::var(Symbol::from("vec-len"), span(1601, 1608))),
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
                elements: vec![Expr::var(Symbol::from("x"), span(1710, 1711))],
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

    // spec: design/arch/fixmes/0360 (ruled S83 /arch, Path 1) — a slot-less
    // `DefKind::PrimitiveExtern` callee MUST classify as a builtin (resolve to
    // its bare JIT name) just like a GOT-slotted `DefKind::Primitive`. This is
    // the guard the classifier's missing arm lacked: pre-fix
    // `resolve_primitive_jit_name` matched only `Primitive { .. }`, silently
    // dropping `PrimitiveExtern` callees (`bind`/`sconcat`/`quote-sexp`/trace
    // accessors) so they never lowered. Both arms are exercised:
    //   - `quote-sexp` (unqualified) + `macros/sconcat` (qualified) are seeded
    //     `PrimitiveExtern` (by-name dispatch)
    //   - `add-i64` is seeded `Primitive { got_slot }`
    // and BOTH must classify as builtins.
    #[test]
    fn test_resolve_primitive_extern_classifies_as_builtin() {
        use cranelisp_types::{DefKind, ModuleEntry, ModuleFullPath};

        let tc = tc();

        // Precondition: confirm the fixture seeds these in the representation
        // the production path uses — `quote-sexp` slot-less `PrimitiveExtern`,
        // `add-i64` GOT-slotted `Primitive`. If a future fixture change flips
        // these the guard below would test the wrong shape.
        let prims = tc.modules.get(&ModuleFullPath::from("primitives")).unwrap();
        assert!(
            matches!(
                prims.get("quote-sexp"),
                Some(ModuleEntry::Def { kind, .. }) if matches!(kind.as_ref(), DefKind::PrimitiveExtern)
            ),
            "fixture precondition: quote-sexp must be slot-less PrimitiveExtern"
        );
        assert!(
            matches!(
                prims.get("add-i64"),
                Some(ModuleEntry::Def { kind, .. }) if matches!(kind.as_ref(), DefKind::Primitive { .. })
            ),
            "fixture precondition: add-i64 must be GOT-slotted Primitive"
        );
        drop(prims);

        // The fix: a PrimitiveExtern callee classifies as a builtin (resolves
        // to its bare JIT name) — both via the qualified `module/name` arm and
        // the unqualified arm.
        assert_eq!(
            tc.resolve_primitive_jit_name_self("quote-sexp").as_deref(),
            Some("quote-sexp"),
            "PrimitiveExtern `quote-sexp` must classify as a builtin (unqualified arm)"
        );
        assert_eq!(
            tc.resolve_primitive_jit_name_self("macros/sconcat").as_deref(),
            Some("sconcat"),
            "PrimitiveExtern `macros/sconcat` must classify as a builtin (qualified arm)"
        );

        // And a genuine GOT-slotted Primitive still classifies — the fix is
        // additive, not a replacement.
        assert_eq!(
            tc.resolve_primitive_jit_name_self("add-i64").as_deref(),
            Some("add-i64"),
            "GOT-slotted Primitive `add-i64` must still classify as a builtin"
        );
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

        // Register in module so the constrained_fn check finds it. NOTE (S114
        // PS-SH1): `cfn` is registered ONLY in the module, NOT bound in local
        // scope — a top-level constrained fn is resolved via the module fallback
        // (`self.lookup` env-miss → `lookup_in_current_module`), with
        // `env.lookup("cfn") == None`. Binding it into LOCAL scope would model it
        // as a §4.6 lexical local (a plain value the value-position gate must NOT
        // reject — the PS-SH1 local-scope-first discipline); the reject fires on
        // the MODULE-resolved constrained base, which is what these tests intend.
        tc.symbol_table_mut().insert(
            Symbol::from("cfn"),
            ModuleEntry::def(
                scheme.clone(),
                cranelisp_types::DefKind::UserFn {
                    fn_state: cranelisp_types::UserFnState::Constrained(Box::new(ConstrainedFn {
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
            callee: Box::new(Expr::var(Symbol::from("id"), span(3000, 3002))),
            args: vec![Expr::var(Symbol::from("cfn"), span(3003, 3006))],
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
            callee: Box::new(Expr::var(Symbol::from("cfn"), span(3100, 3103))),
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

        // impl Num for Int
        let int_impl = TraitImpl {
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
        tc.register_trait_impl_self(&int_impl).unwrap();

        // impl Num for Float
        let float_impl = TraitImpl {
            head_con_var: None,
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
                        callee: Box::new(Expr::var(Symbol::from("add-f64"), Span::SYNTHETIC)),
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
        tc.register_trait_impl_self(&float_impl).unwrap();

        // Ord trait: < :: (Fn [a a] Bool)
        let ord_decl = TraitDecl {
            name: TraitName::from("Ord"),
            docstring: None,
            type_params: vec![],
            methods: vec![TraitMethodSig {
                name: Symbol::from("<"),
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
        tc.register_trait_decl_self(&ord_decl).unwrap();

        // impl Ord for Int
        let int_ord_impl = TraitImpl {
            head_con_var: None,
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
                        callee: Box::new(Expr::var(Symbol::from("lt-i64"), Span::SYNTHETIC)),
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
            callee: Box::new(Expr::var(Symbol::from("+"), span(4001, 4002))),
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
            err.message().contains("no impl of trait test/Num for type primitives/Bool"),
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
            callee: Box::new(Expr::var(Symbol::from("+"), span(4101, 4102))),
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
            err.message().contains("no impl of trait test/Num for type primitives/String"),
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
            callee: Box::new(Expr::var(Symbol::from("<"), span(4201, 4202))),
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
            err.message().contains("no impl of trait test/Ord for type primitives/Bool"),
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
            callee: Box::new(Expr::var(Symbol::from("<"), span(4301, 4302))),
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
            err.message().contains("no impl of trait test/Ord for type primitives/String"),
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
            callee: Box::new(Expr::var(Symbol::from("+"), span(4401, 4402))),
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
            callee: Box::new(Expr::var(Symbol::from("+"), span(4501, 4502))),
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

    // spec: 04-expressions §4.6 / §11.8.8 — the Ruling-5 carrier discriminator
    // (W3-review Important-3 extraction: the ONE predicate the five resolution
    // seams consult). An unbound name resolves to its TABLE/carrier identity
    // (trait/overload/primitive dispatch); a `let`/`fn`/param binding that shadows
    // it is a §4.6 LOCAL that must resolve to the local binding — the mechanism
    // that makes `(let [+ (fn [a b] 0)] (+ 1 2))` call the closure (0), not the
    // `Num.+` trait method (3). Pins the extraction at its seam.
    #[test]
    fn resolves_to_carrier_identity_discriminates_local_shadow() {
        let mut tc = tc();
        // Unbound `+` → carrier identity (dispatch is legitimate).
        assert!(
            tc.state.resolves_to_carrier_identity("+"),
            "an unbound name must resolve to its carrier identity"
        );
        // Shadow `+` with a `let`-style local binding.
        tc.state.env.push_scope(span(0, 1));
        tc.state.env.bind(Symbol::from("+"), crate::scheme::mono(Type::Int));
        assert!(
            !tc.state.resolves_to_carrier_identity("+"),
            "a local shadow must NOT resolve to the carrier identity (§4.6) — this \
             is what stops the trait-method mis-dispatch"
        );
        // The shadow only masks within its scope.
        tc.state.env.pop_scope();
        assert!(
            tc.state.resolves_to_carrier_identity("+"),
            "after the shadowing scope pops, the name resolves to its carrier again"
        );
    }

    // spec: 07-traits §7.4.1 — (+ 1.0 2.0) succeeds: Float has Num impl
    #[test]
    fn test_trait_method_plus_float_succeeds() {
        let mut tc = tc();
        register_num_and_ord_traits(&mut tc);

        // (+ 1.0 2.0) -> Float
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("+"), span(4601, 4602))),
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

    // -----------------------------------------------------------------------
    // §7.6 — trait method as a first-class value (value-position resolution).
    // FIXME 0300. The trait method appears as a bare Expr::Var bound in a
    // `let` (escaping the call site as a value); the value-position pass must
    // resolve it to the correct impl for the operand types read from the Var's
    // inferred function type. Symptom-B regressions: String `=` and Float `+`.
    // -----------------------------------------------------------------------

    /// Register Eq (Int + String impls) and Display (Int impl) so the
    /// value-position §7.6 tests can resolve `=` / `show` as values.
    fn register_eq_and_display_traits(tc: &mut TestFixture) {
        use cranelisp_types::{DefnVariant, TraitDecl, TraitImpl, TraitMethodSig, TraitName, TypeExpr, Defn};

        // Eq trait: = :: (Fn [a a] Bool)
        let eq_decl = TraitDecl {
            name: TraitName::from("Eq"),
            docstring: None,
            type_params: vec![],
            methods: vec![TraitMethodSig {
                name: Symbol::from("="),
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
        tc.register_trait_decl_self(&eq_decl).unwrap();

        // = impl bodies dispatch to a primitive (eq-i64 / str-eq); the actual
        // body is irrelevant for resolution (primitive_for_trait_method short-
        // circuits to BuiltinFn), but a valid Defn must be registered.
        let mk_eq_impl = |target: &str, prim: &str| TraitImpl {
            head_con_var: None,
            trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Eq")),
            target: cranelisp_types::TypeExpr::Named(
                cranelisp_types::TypeRef::new(None, TypeName::from(target)),
            ),
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("="),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from(prim), Span::SYNTHETIC)),
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
        tc.register_trait_impl_self(&mk_eq_impl("Int", "eq-i64")).unwrap();
        tc.register_trait_impl_self(&mk_eq_impl("String", "str-eq")).unwrap();

        // Display trait: show :: (Fn [a] String)
        let display_decl = TraitDecl {
            name: TraitName::from("Display"),
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
        tc.register_trait_decl_self(&display_decl).unwrap();
        let show_int_impl = TraitImpl {
            head_con_var: None,
            trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Display")),
            target: cranelisp_types::TypeExpr::Named(
                cranelisp_types::TypeRef::new(None, TypeName::from("Int")),
            ),
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("show"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("x"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("int-to-string"), Span::SYNTHETIC)),
                        args: vec![Expr::var(Symbol::from("x"), Span::SYNTHETIC)],
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
        tc.register_trait_impl_self(&show_int_impl).unwrap();

        tc.clear_transient_state();
    }

    /// Build `(let [f <method>] (f <args...>))` where `<method>` is a bare
    /// trait-method Var bound in value position. Returns the expr plus the
    /// span of the value-position `<method>` Var (the one the value-position
    /// pass must resolve).
    fn let_bound_method_call(method: &str, binding_span: Span, args: Vec<Expr>) -> (Expr, Span) {
        let f_call = Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("f"), Span::new(9000, 9001))),
            args,
            span: Span::new(9002, 9100),
            resolved_call: None,
            inferred_type: None,
        };
        let let_expr = Expr::Let {
            bindings: vec![(Symbol::from("f"), Expr::var(Symbol::from(method), binding_span))],
            body: Box::new(f_call),
            span: Span::new(8000, 9200),
            inferred_type: None,
        };
        (let_expr, binding_span)
    }

    // spec: 07-traits §7.6 — `=` bound as a value resolves to the String impl
    // when applied to String operands (Symptom B: must NOT pick the Int impl).
    #[test]
    fn value_position_eq_string_resolves_to_str_eq() {
        let mut tc = tc();
        register_eq_and_display_traits(&mut tc);

        // (let [f =] (f "a" "b"))
        let bspan = span(8100, 8101);
        let (mut expr, value_span) = let_bound_method_call(
            "=",
            bspan,
            vec![
                Expr::StringLit { value: "a".into(), span: span(9010, 9013), inferred_type: None },
                Expr::StringLit { value: "b".into(), span: span(9014, 9017), inferred_type: None },
            ],
        );

        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(ty, Type::Bool);

        tc.resolve_value_position_trait_methods_for_test(&expr);

        let resolution = tc.state.method_resolutions.resolved_calls.get(&value_span)
            .expect("value-position `=` Var must be resolved (§7.6)");
        match resolution {
            ResolvedCall::BuiltinFn { name } => assert_eq!(name.as_ref(), "str-eq",
                "String `=` must dispatch to str-eq, not the Int impl"),
            other => panic!("expected BuiltinFn str-eq, got {other:?}"),
        }
    }

    // spec: 07-traits §7.6 — `+` bound as a value resolves to the Float impl
    // when applied to Float operands (Symptom B: must NOT pick the Int impl).
    #[test]
    fn value_position_plus_float_resolves_to_add_f64() {
        let mut tc = tc();
        register_num_and_ord_traits(&mut tc);

        // (let [f +] (f 1.0 2.0))
        let bspan = span(8200, 8201);
        let (mut expr, value_span) = let_bound_method_call(
            "+",
            bspan,
            vec![
                Expr::FloatLit { value: 1.0, span: span(9010, 9013), inferred_type: None },
                Expr::FloatLit { value: 2.0, span: span(9014, 9017), inferred_type: None },
            ],
        );

        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(ty, Type::Float);

        tc.resolve_value_position_trait_methods_for_test(&expr);

        let resolution = tc.state.method_resolutions.resolved_calls.get(&value_span)
            .expect("value-position `+` Var must be resolved (§7.6)");
        match resolution {
            ResolvedCall::BuiltinFn { name } => assert_eq!(name.as_ref(), "add-f64",
                "Float `+` must dispatch to add-f64, not the Int impl"),
            other => panic!("expected BuiltinFn add-f64, got {other:?}"),
        }
    }

    // spec: 07-traits §7.6 — `show` bound as a value resolves to the Int impl
    // when applied to an Int operand (Symptom A: was `undefined variable: show`).
    #[test]
    fn value_position_show_int_resolves_to_int_to_string() {
        let mut tc = tc();
        register_eq_and_display_traits(&mut tc);

        // (let [f show] (f 42))
        let bspan = span(8300, 8301);
        let (mut expr, value_span) = let_bound_method_call(
            "show",
            bspan,
            vec![Expr::IntLit { value: 42, span: span(9010, 9012), inferred_type: None }],
        );

        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(ty, Type::String);

        tc.resolve_value_position_trait_methods_for_test(&expr);

        let resolution = tc.state.method_resolutions.resolved_calls.get(&value_span)
            .expect("value-position `show` Var must be resolved (§7.6)");
        match resolution {
            ResolvedCall::BuiltinFn { name } => assert_eq!(name.as_ref(), "int-to-string",
                "Int `show` must dispatch to int-to-string"),
            other => panic!("expected BuiltinFn int-to-string, got {other:?}"),
        }
    }

    // spec: 07-traits §7.6 — `=` bound as a value resolves to the Int impl
    // when applied to Int operands (the Int happy-path that previously worked
    // only because Int was the hard-coded backend default).
    #[test]
    fn value_position_eq_int_resolves_to_eq_i64() {
        let mut tc = tc();
        register_eq_and_display_traits(&mut tc);

        // (let [f =] (f 1 1))
        let bspan = span(8400, 8401);
        let (mut expr, value_span) = let_bound_method_call(
            "=",
            bspan,
            vec![
                Expr::IntLit { value: 1, span: span(9010, 9011), inferred_type: None },
                Expr::IntLit { value: 1, span: span(9012, 9013), inferred_type: None },
            ],
        );

        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(ty, Type::Bool);

        tc.resolve_value_position_trait_methods_for_test(&expr);

        let resolution = tc.state.method_resolutions.resolved_calls.get(&value_span)
            .expect("value-position `=` Var must be resolved (§7.6)");
        match resolution {
            ResolvedCall::BuiltinFn { name } => assert_eq!(name.as_ref(), "eq-i64"),
            other => panic!("expected BuiltinFn eq-i64, got {other:?}"),
        }
    }

    // spec: 07-traits §7.6 — an ordinary local (non-trait-method) Var bound in
    // value position must NOT be touched by the pass (resolved_call stays None).
    #[test]
    fn value_position_ordinary_local_is_not_resolved() {
        let mut tc = tc();
        register_eq_and_display_traits(&mut tc);

        // (let [g 7] (let [f g] (f)))  — `f` here is a local, not a trait
        // method. Simpler: (let [f 7] f) — the inner `f` Var is a local value.
        // Build `(let [f 7] f)` and assert the body `f` Var is untouched.
        let body_span = span(8501, 8502);
        let mut expr = Expr::Let {
            bindings: vec![(Symbol::from("f"), Expr::IntLit { value: 7, span: span(8503, 8504), inferred_type: None })],
            body: Box::new(Expr::var(Symbol::from("f"), body_span)),
            span: span(8500, 8510),
            inferred_type: None,
        };

        let _ = tc.infer_expr_for_test(&mut expr).unwrap();
        tc.resolve_value_position_trait_methods_for_test(&expr);

        assert!(
            !tc.state.method_resolutions.resolved_calls.contains_key(&body_span),
            "ordinary local Var must NOT receive a trait-method resolution"
        );
    }

    // spec: 08-modules §8.6.1 — locals-first lookup; a local binding shadows a
    // trait-method name of the same spelling. FIXME 0306 (option b): the
    // value-position pass's predicate (`is_trait_method_with_state`) consults the
    // MODULE symbol table only, not local scope (which is unwound by the time the
    // post-inference pass runs), so the shadowing local Var MAY receive a bogus
    // trait-method `resolved_call`. This is NOT a live miscompile: backend
    // `compile_var` checks `self.variables.get(name)` BEFORE the `resolved_call`
    // branch, so the local value wins (the shadow returns the local fn's result,
    // not a trait dispatch). This test pins the adversarial shadow shape so the
    // masking guarantee is a regression guard — if a future backend refactor
    // reorders the locals check, option (a) (predicate gated on local-binding
    // visibility) must replace this reliance.
    #[test]
    fn value_position_local_shadow_of_trait_method_does_not_miscompile() {
        let mut tc = tc();
        register_eq_and_display_traits(&mut tc);

        // (let [show (fn [x] (int-to-string x))] (let [g show] (g 42)))
        //
        // `show` is locally bound to a fn, shadowing the `Display::show` trait
        // method (locals-first, §8.6.1). `g` binds to that local `show`. The
        // value-position `show` Var (in `[g show]`) is the adversarial site.
        let show_value_span = span(8601, 8605); // the `show` reference bound to `g`
        let g_callee_span = span(8700, 8701);
        let inner_g_call = Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("g"), g_callee_span)),
            args: vec![Expr::IntLit { value: 42, span: span(8702, 8704), inferred_type: None }],
            span: span(8700, 8710),
            resolved_call: None,
            inferred_type: None,
        };
        let inner_let = Expr::Let {
            bindings: vec![(Symbol::from("g"), Expr::var(Symbol::from("show"), show_value_span))],
            body: Box::new(inner_g_call),
            span: span(8600, 8800),
            inferred_type: None,
        };
        let show_fn = Expr::Lambda {
            params: vec![(Symbol::from("x"), None)],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("int-to-string"), span(8520, 8533))),
                args: vec![Expr::var(Symbol::from("x"), span(8534, 8535))],
                span: span(8519, 8536),
                resolved_call: None,
                inferred_type: None,
            }),
            span: span(8510, 8540),
            inferred_type: None,
        };
        let mut expr = Expr::Let {
            bindings: vec![(Symbol::from("show"), show_fn)],
            body: Box::new(inner_let),
            span: span(8500, 8810),
            inferred_type: None,
        };

        // Inference must succeed using the LOCAL `show` fn (Int -> String), NOT a
        // trait dispatch: the whole expression types as String.
        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(
            ty,
            Type::String,
            "the local `show` fn (Int -> String) must drive inference, not the trait method"
        );

        tc.resolve_value_position_trait_methods_for_test(&expr);

        // Option (b) acceptance: the pass may attach a trait-method resolution to
        // the shadowing local Var (the predicate is module-table-only). Whether or
        // not it does, the local value is what the backend dispatches (locals-first
        // in `compile_var`), so the shadow is correctly evaluated as the local fn.
        // We assert the masking invariant: IF a resolution was attached to the
        // shadow Var, it is the (harmless) `show`/int-to-string trait-method
        // annotation that backend ordering overrides — never a resolution that
        // would change the local's value semantics.
        if let Some(resolution) =
            tc.state.method_resolutions.resolved_calls.get(&show_value_span)
        {
            match resolution {
                ResolvedCall::BuiltinFn { name } => assert_eq!(
                    name.as_ref(),
                    "int-to-string",
                    "any annotation on the shadow Var must be the (masked) Display::show \
                     trait-method dispatch, not an unrelated resolution"
                ),
                other => panic!(
                    "unexpected non-primitive trait-method annotation on a local shadow: {other:?}"
                ),
            }
        }
    }

    // =========================================================================
    // (trace expr) — inference rule (harvested from tests/legacy/
    // ring4_trace_taxonomy.rs per FIXME 0130, typecheck portion).
    //
    // The typecheck-internal contract for the `trace` special form is the
    // `infer_trace` rule: `(trace expr)` ALWAYS infers as
    // `Type::ADT(primitives/Trace, [])`, regardless of the body's type, while
    // still inferring the body for constraint propagation / error detection.
    // Per Decision 0040 the Trace ADT, `TraceCall` constructor, and the field
    // accessors (`name`/`params`/`result`/`nanos`/`children`) relocated in
    // FULL to the `int` binary crate (seeded in `src/bootstrap.rs`); they are
    // NOT a typecheck preset and NOT resolvable from the typecheck fixture, so
    // the field-accessor return-type and `TraceCall`-pattern-match assertions
    // from the legacy file are no longer typecheck-internal and are not
    // harvested here (they belong to the int/runtime cluster). What remains
    // typecheck-internal is the trace-form's own inferred shape, exercised
    // here through the frontend parser + AST builder.
    // =========================================================================

    /// Helper: parse a single expression to an `Expr` AST via the frontend,
    /// mirroring `tests/CLAUDE.md §"Isolating Cross-Crate Failures"` (do not
    /// hand-construct `Expr` trees).
    fn build_expr_from_source(src: &str) -> cranelisp_types::Expr {
        let sexps = cranelisp_frontend::parse(src).expect("parse must succeed");
        assert_eq!(sexps.len(), 1, "expected a single expression");
        cranelisp_frontend::build_expr(&sexps[0]).expect("build_expr must succeed")
    }

    /// The canonical Trace type the `infer_trace` rule synthesises.
    fn trace_type() -> Type {
        Type::ADT(prims_fqtn("Trace"), vec![])
    }

    // spec: spec/04-expressions.md §4.12.1 — (trace ...) infers as Trace for an
    // Int-bodied call.
    #[test]
    fn trace_returns_trace_type_int_body() {
        let mut tc = tc();
        // (defn fact [n] ...) bound locally so the call has a concrete type.
        tc.bind_local_self(
            Symbol::from("fact"),
            mono(Type::Fn(vec![Type::Int], Box::new(Type::Int))),
        );
        let mut expr = build_expr_from_source("(trace (fact 5))");
        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(ty, trace_type(), "trace of an Int-bodied call must infer as Trace");
    }

    // spec: spec/04-expressions.md §4.12.1 — (trace ...) infers as Trace
    // regardless of the body's type (here a Bool-returning call).
    #[test]
    fn trace_returns_trace_type_regardless_of_body() {
        let mut tc = tc();
        tc.bind_local_self(
            Symbol::from("always-true"),
            mono(Type::Fn(vec![], Box::new(Type::Bool))),
        );
        let mut expr = build_expr_from_source("(trace (always-true))");
        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(
            ty,
            trace_type(),
            "trace must infer as Trace even for a Bool-bodied expression"
        );
    }

    // spec: spec/04-expressions.md §4.12.2 — (trace ...) over inline primitives
    // (no user calls) still infers as Trace.
    #[test]
    fn trace_inline_primitive_no_calls() {
        let mut tc = tc();
        let mut expr = build_expr_from_source("(trace (add-i64 1 2))");
        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(
            ty,
            trace_type(),
            "trace of an inline primitive must still infer as Trace"
        );
    }

    // spec: spec/04-expressions.md §4.12.5 — lexically nested trace still infers
    // as a single Trace at the type level (the nested-trace RUNTIME error is an
    // int/runtime concern, covered e2e in tests/trace.rs).
    #[test]
    fn trace_nested_single_trace() {
        let mut tc = tc();
        tc.bind_local_self(
            Symbol::from("fact"),
            mono(Type::Fn(vec![Type::Int], Box::new(Type::Int))),
        );
        let mut expr = build_expr_from_source("(trace (trace (fact 3)))");
        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(ty, trace_type(), "nested trace must still infer as Trace");
    }

    // spec: spec/04-expressions.md §4.12.7 — a trace value is an ordinary value:
    // let-binding it preserves the Trace type.
    #[test]
    fn trace_composability_let_binding() {
        let mut tc = tc();
        tc.bind_local_self(
            Symbol::from("fact"),
            mono(Type::Fn(vec![Type::Int], Box::new(Type::Int))),
        );
        let mut expr = build_expr_from_source("(let [t (trace (fact 3))] t)");
        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(
            ty,
            trace_type(),
            "a let-bound trace value must retain the Trace type"
        );
    }

    // spec: spec/04-expressions.md §4.12.7 — a trace value is an ordinary value
    // and can be passed as a function argument. The legacy harvest source
    // (`tests/legacy/ring4_trace_taxonomy.rs::trace_composability_pass_to_function`)
    // asserted `Type::String` via the `name` accessor, but that accessor's
    // return-type scheme is seeded in the `int` binary (`src/bootstrap.rs`),
    // not a typecheck preset — so the String result is an int/runtime fact, not
    // typecheck-internal. The typecheck-internal fact harvested here is the
    // unification angle: when a trace value flows into a polymorphic
    // identity-shaped function parameter, that parameter unifies to Trace and
    // the call result is Trace. This pins the trace-form's own type as an
    // ordinary, passable value at the inference seam (the field-accessor
    // return-type GAPs from the legacy file belong to the int/runtime cluster,
    // per the block comment above).
    #[test]
    fn trace_composability_pass_to_function() {
        let mut tc = tc();
        tc.bind_local_self(
            Symbol::from("fact"),
            mono(Type::Fn(vec![Type::Int], Box::new(Type::Int))),
        );
        // An identity-shaped fn over a single param: forall a. (Fn [a] a).
        let a_var = tc.fresh_var();
        let a_id = match &a_var {
            Type::Var(id) => *id,
            _ => unreachable!("fresh_var returns Type::Var"),
        };
        tc.bind_local_self(
            Symbol::from("id-trace"),
            Scheme {
                type_vars: vec![a_id],
                constraints: HashMap::new(),
                ty: Type::Fn(vec![a_var.clone()], Box::new(a_var)),
            },
        );
        let mut expr = build_expr_from_source("(id-trace (trace (fact 3)))");
        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(
            ty,
            trace_type(),
            "passing a trace value through an identity-shaped fn must yield Trace"
        );
    }

    // --- ParBind tests (FIXME 0400, spec/10-io.md §10.12 transparency) ---

    /// The `(IO inner)` ADT type — what a `ParBind` binding value carries and
    /// what its body / result are.
    fn io_type(inner: Type) -> Type {
        Type::ADT(prims_fqtn("IO"), vec![inner])
    }

    /// Build a `ParBind` node by hand. `ParBind` has no surface syntax (it is
    /// synthesised by S85 auto-IO scheduling from a `bind` chain), so it cannot
    /// go through `build_expr_from_source`.
    fn par_bind(bindings: Vec<(Symbol, Expr)>, body: Expr) -> Expr {
        Expr::ParBind {
            bindings,
            body: Box::new(body),
            span: span(0, 80),
            inferred_type: None,
        }
    }

    // spec: 10-io §10.12 — a ParBind unwraps each binding's `IO aᵢ` and binds
    // the name to the inner type `aᵢ` (NOT `IO aᵢ`), exactly as the sequential
    // bind chain would; the body is `IO U` and the ParBind result is `IO U`.
    #[test]
    fn par_bind_unwraps_io_bindings_body_uses_names_unwrapped() {
        let mut tc = tc();
        // Two binding values typed `IO Int` (the actions the bind chain wraps).
        tc.bind_local_self(Symbol::from("act1"), mono(io_type(Type::Int)));
        tc.bind_local_self(Symbol::from("act2"), mono(io_type(Type::Int)));
        // A continuation-shaped helper `(Fn [Int] (IO Int))` so the body is
        // itself an `IO` action that consumes the (unwrapped) names at Int.
        tc.bind_local_self(
            Symbol::from("mk-io"),
            mono(Type::Fn(vec![Type::Int], Box::new(io_type(Type::Int)))),
        );

        // ParBind { a <- act1, b <- act2 } in (mk-io (add-i64 a b))
        // — `a` and `b` are used at Int via add-i64; the body is `IO Int`.
        let body = build_expr_from_source("(mk-io (add-i64 a b))");
        let mut expr = par_bind(
            vec![
                (Symbol::from("a"), Expr::var(Symbol::from("act1"), span(10, 14))),
                (Symbol::from("b"), Expr::var(Symbol::from("act2"), span(15, 19))),
            ],
            body,
        );
        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(
            ty,
            io_type(Type::Int),
            "ParBind over two `IO Int` bindings whose body is `IO Int` must infer `IO Int`"
        );
    }

    // spec: 10-io §10.12 — a body that misuses a bound name as `IO Int` (not the
    // unwrapped `Int`) is a type error: the ParBind rule binds the name to the
    // UNWRAPPED inner type, so feeding it where an `IO Int` is expected fails.
    #[test]
    fn par_bind_body_misusing_name_as_io_is_type_error() {
        let mut tc = tc();
        tc.bind_local_self(Symbol::from("act1"), mono(io_type(Type::Int)));
        // `consume-io` expects an `(IO Int)`, not an `Int`.
        tc.bind_local_self(
            Symbol::from("consume-io"),
            mono(Type::Fn(vec![io_type(Type::Int)], Box::new(io_type(Type::Int)))),
        );

        // ParBind { a <- act1 } in (consume-io a)
        // — `a` is bound to `Int` (unwrapped), but used where `(IO Int)` is
        // expected → unification failure.
        let body = build_expr_from_source("(consume-io a)");
        let mut expr = par_bind(
            vec![(Symbol::from("a"), Expr::var(Symbol::from("act1"), span(10, 14)))],
            body,
        );
        assert!(
            tc.infer_expr_for_test(&mut expr).is_err(),
            "using a ParBind-bound name as `IO Int` (not unwrapped `Int`) must be a type error"
        );
    }

    // --- LaunchContinue tests (S96 Chunk B, spec/10-io.md §10.12.7) -----------

    /// Build a `LaunchContinue` node by hand (no surface syntax — synthesised by
    /// the bind-chain independence analysis at the §10.12.7 launch shape).
    fn launch_continue(launched: Expr, continuation: Expr) -> Expr {
        Expr::LaunchContinue {
            launched: Box::new(launched),
            continuation: Box::new(continuation),
            span: span(0, 80),
            inferred_type: None,
        }
    }

    // spec: 10-io.md §10.12.7 — a `LaunchContinue` types as its CONTINUATION; the
    // launched effect's result is discarded. The launched arm still typechecks
    // (it's a real `IO a` effect run as a detached strand).
    #[test]
    fn launch_continue_types_as_its_continuation() {
        let mut tc = tc();
        // launched effect typed `IO Int` (its result discarded); continuation an
        // `IO Bool` action (its type IS this node's type).
        tc.bind_local_self(Symbol::from("eff"), mono(io_type(Type::Int)));
        tc.bind_local_self(Symbol::from("cont"), mono(io_type(Type::Bool)));
        let mut expr = launch_continue(
            Expr::var(Symbol::from("eff"), span(10, 14)),
            Expr::var(Symbol::from("cont"), span(15, 19)),
        );
        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(
            ty,
            io_type(Type::Bool),
            "LaunchContinue types as its continuation (IO Bool); the launched \
             effect's result (IO Int) is discarded"
        );
    }

    // spec: 10-io.md §10.12.7 — the launched arm MUST typecheck as a real `IO a`
    // effect: a non-IO launched value is a type error (it is unified against
    // `IO ?a`, exactly as the sequential `bind` would).
    #[test]
    fn launch_continue_non_io_launched_is_type_error() {
        let mut tc = tc();
        tc.bind_local_self(Symbol::from("plain"), mono(Type::Int)); // NOT an IO action
        tc.bind_local_self(Symbol::from("cont"), mono(io_type(Type::Bool)));
        let mut expr = launch_continue(
            Expr::var(Symbol::from("plain"), span(10, 15)),
            Expr::var(Symbol::from("cont"), span(16, 20)),
        );
        assert!(
            tc.infer_expr_for_test(&mut expr).is_err(),
            "a launched arm that is not an `IO a` effect must be a type error"
        );
    }
