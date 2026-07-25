//! `program/body.rs` sub-topic — the AST-annotation writeback: every checked
//! node carries its resolved `inferred_type` and `resolved_call`
//! (`design/typecheck/ast-annotation.md`).

use super::*;

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
    if let ModuleEntry::Def {
        ast: Some(defn), ..
    } = entry
    {
        let body = &defn.body;

        // All inferred_types should be concrete (no Var)
        let mut types = Vec::new();
        collect_inferred_types(body, &mut types);
        for (s, ty) in &types {
            let ty = ty
                .as_ref()
                .unwrap_or_else(|| panic!("no inferred_type at span {:?}", s));
            assert!(
                !ty.contains_var(),
                "inferred_type at span {:?} contains Var: {:?}",
                s,
                ty
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
        assert!(
            rc.is_some(),
            "Apply (add-i64 x x) should have resolved_call"
        );
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
                args: vec![Expr::IntLit {
                    value: 5,
                    span: span(228, 229),
                    inferred_type: None,
                }],
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
    if let ModuleEntry::Def {
        ast: Some(defn), ..
    } = entry
    {
        let body = &defn.body;
        let rc = find_resolved_call(body, plus_span);
        assert!(
            rc.is_some(),
            "Apply (+ x x) should have resolved_call on AST node"
        );
        match rc.unwrap() {
            ResolvedCall::BuiltinFn { name } => {
                assert_eq!(name.as_ref(), "add-i64");
            }
            other => panic!(
                "expected BuiltinFn (primitive trait-method short-circuit per FIXME 0185), got {:?}",
                other
            ),
        }

        // All types should be concrete
        let mut types = Vec::new();
        collect_inferred_types(body, &mut types);
        for (s, ty) in &types {
            let ty = ty
                .as_ref()
                .unwrap_or_else(|| panic!("no inferred_type at span {:?}", s));
            assert!(
                !ty.contains_var(),
                "inferred_type at span {:?} contains Var: {:?}",
                s,
                ty
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
                        Expr::IntLit {
                            value: 1,
                            span: span(319, 320),
                            inferred_type: None,
                        },
                        Expr::IntLit {
                            value: 2,
                            span: span(321, 322),
                            inferred_type: None,
                        },
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
    if let ModuleEntry::Def {
        ast: Some(defn), ..
    } = entry
    {
        let body = &defn.body;

        // All inferred_types should be concrete
        let mut types = Vec::new();
        collect_inferred_types(body, &mut types);
        for (s, ty) in &types {
            let ty = ty
                .as_ref()
                .unwrap_or_else(|| panic!("no inferred_type at span {:?}", s));
            assert!(
                !ty.contains_var(),
                "inferred_type at span {:?} contains Var: {:?}",
                s,
                ty
            );
        }

        // The Let expression should have type Int
        assert_eq!(body.inferred_type().unwrap(), &Type::Int);

        // The binding expression (add-i64 1 2) should have resolved_call
        let rc = find_resolved_call(body, add_span);
        assert!(
            rc.is_some(),
            "Apply (add-i64 1 2) should have resolved_call"
        );
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
                    Expr::IntLit {
                        value: 0,
                        span: span(420, 421),
                        inferred_type: None,
                    },
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
                            Expr::IntLit {
                                value: 1,
                                span: span(451, 452),
                                inferred_type: None,
                            },
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
    if let ModuleEntry::Def {
        ast: Some(defn), ..
    } = entry
    {
        let body = &defn.body;

        // All inferred_types should be concrete
        let mut types = Vec::new();
        collect_inferred_types(body, &mut types);
        for (s, ty) in &types {
            let ty = ty
                .as_ref()
                .unwrap_or_else(|| panic!("no inferred_type at span {:?}", s));
            assert!(
                !ty.contains_var(),
                "inferred_type at span {:?} contains Var: {:?}",
                s,
                ty
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
        assert!(
            fact_rc.is_none(),
            "recursive fact call should have resolved_call = None (plain user fn)"
        );
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
                    Expr::IntLit {
                        value: 1,
                        span: span(525, 526),
                        inferred_type: None,
                    },
                    Expr::IntLit {
                        value: 2,
                        span: span(527, 528),
                        inferred_type: None,
                    },
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
    if let ModuleEntry::Def {
        ast: Some(defn), ..
    } = entry
    {
        let body = &defn.body;

        // All inferred_types should be concrete (Int, no Var)
        let mut types = Vec::new();
        collect_inferred_types(body, &mut types);
        for (s, ty) in &types {
            let ty = ty
                .as_ref()
                .unwrap_or_else(|| panic!("no inferred_type at span {:?}", s));
            assert!(
                !ty.contains_var(),
                "inferred_type at span {:?} contains Var: {:?}",
                s,
                ty
            );
        }

        // The + call should have resolved_call set (resolved via
        // deferred trait call resolution after the call site pins types).
        // FIXME 0185: (Num, +, Int) short-circuits to BuiltinFn so backend
        // emits the primitive inline without paying the impl-body call frame.
        let rc = find_resolved_call(body, plus_span);
        assert!(
            rc.is_some(),
            "Apply (+ x x) should have resolved_call on AST node"
        );
        match rc.unwrap() {
            ResolvedCall::BuiltinFn { name } => {
                assert_eq!(name.as_ref(), "add-i64");
            }
            other => panic!(
                "expected BuiltinFn (primitive trait-method short-circuit per FIXME 0185), got {:?}",
                other
            ),
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

    let sexps =
        cranelisp_frontend::parse("(defn concat-nils [] (macros/sconcat macros/SNil macros/SNil))")
            .unwrap();
    let program = cranelisp_frontend::build_program(&sexps).unwrap();

    let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

    let st = tc.symbol_table();
    let entry = st
        .get("concat-nils")
        .expect("concat-nils should be in symbol table");
    if let ModuleEntry::Def {
        ast: Some(defn), ..
    } = entry
    {
        let body = &defn.body;

        // Find the Apply node (there's only one)
        fn find_any_apply(expr: &Expr) -> Option<&Expr> {
            if matches!(expr, Expr::Apply { .. }) {
                return Some(expr);
            }
            match expr {
                Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
                    for (_, e) in bindings {
                        if let Some(a) = find_any_apply(e) {
                            return Some(a);
                        }
                    }
                    find_any_apply(body)
                }
                Expr::If {
                    cond,
                    then_branch,
                    else_branch,
                    ..
                } => find_any_apply(cond)
                    .or_else(|| find_any_apply(then_branch))
                    .or_else(|| find_any_apply(else_branch)),
                Expr::Lambda { body, .. }
                | Expr::Annotate { expr: body, .. }
                | Expr::Trace { body, .. } => find_any_apply(body),
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

        let ty = body
            .inferred_type()
            .expect("Apply should have inferred_type");
        assert!(
            !ty.contains_var(),
            "inferred_type should be concrete, got {:?}",
            ty
        );
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
    let double_decl =
        crate::traits::test_helpers::parse_trait_decl("(deftrait Double (double [x] self))");
    let decl_form = TopLevel::TraitDecl(double_decl);
    let result = tc
        .check_form(&module, &decl_form, CheckPass::Register, &mut accumulator)
        .unwrap();
    tc.merge_form_result(&module, &mut accumulator, result);

    // Impl Double for Int: (defn double [x] (+ x x))
    let impl_ = TraitImpl {
        head_con_var: None,
        trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Double")),
        target: cranelisp_types::TypeExpr::Named(cranelisp_types::TypeRef::new(
            None,
            TypeName::from("Int"),
        )),
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
    let result = tc
        .check_form(&module, &impl_form, CheckPass::Register, &mut accumulator)
        .unwrap();
    tc.merge_form_result(&module, &mut accumulator, result);

    // The register pass should produce the mangled defn (S102 FQ `$Type`
    // suffix: `primitives/Int`, lock-step with the dispatch site).
    let mangled_name = Symbol::from("Double.double$primitives/Int");
    assert!(
        !accumulator.default_method_defns.is_empty(),
        "register should produce default_method_defns"
    );
    assert!(
        accumulator
            .default_method_defns
            .iter()
            .any(|d| d.name == mangled_name),
        "should contain Double.double$primitives/Int"
    );

    // Step: Run register for the mangled defn (like register_default_methods does)
    let defaults = std::mem::take(&mut accumulator.default_method_defns);
    for defn in &defaults {
        let form = TopLevel::Defn(defn.clone());
        let result = tc
            .check_form(&module, &form, CheckPass::Register, &mut accumulator)
            .unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);
    }
    accumulator.default_method_defns = defaults;

    // Step: Run CheckBody for the mangled defn (like finalize_module does)
    let defaults_for_body = accumulator.default_method_defns.clone();
    for defn in &defaults_for_body {
        let form = TopLevel::Defn(defn.clone());
        let result = tc
            .check_form(&module, &form, CheckPass::CheckBody, &mut accumulator)
            .unwrap();
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
                    mangled_name,
                    scheme.ty
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
        panic!(
            "mangled method '{}' not found in symbol table",
            mangled_name
        );
    }

    // Verify AST annotations are concrete (no Var(N))
    if let Some(ModuleEntry::Def {
        ast: Some(annotated),
        ..
    }) = table.get(mangled_name.as_ref())
    {
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
    let entry = st
        .get("trivial")
        .expect("'trivial' must be registered after check");
    match entry {
        ModuleEntry::Def { ast, .. } => {
            assert!(
                ast.is_some(),
                "ModuleEntry::Def.ast must be Some(_) after Phase-1 AST annotation"
            );
            // The annotated body must carry a resolved (var-free) type.
            let defn = ast.as_ref().unwrap();
            let body = &defn.body;
            let ty = body
                .inferred_type()
                .expect("annotated body must carry inferred_type");
            assert!(
                !ty.contains_var(),
                "inferred_type must be concrete, got {ty:?}"
            );
        }
        other => panic!("expected Def entry for 'trivial', got {other:?}"),
    }
}
