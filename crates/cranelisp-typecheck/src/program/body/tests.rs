//! Per-submodule tests for `program/body.rs` — Pass-2 body checking: infer each
//! defn body against its registered signature, harvest resolutions/edges, and
//! populate the per-form `FormCheckResult`. Split from the pooled
//! `program/tests.rs` (FIXME 0722); the AST-annotation writeback and the
//! two-pass `check_form` body arms are the sub-topics in sibling files.

use super::*;

use crate::program::test_support::*;

mod annotation;

mod check_form_arms;



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
