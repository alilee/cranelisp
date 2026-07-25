//! `program/body.rs` sub-topic — the per-form `check_form(CheckBody)` arms and
//! their two-pass interaction with Pass-1 registration (forward/mutual
//! reference, shared substitution across forms, accumulated warnings, error
//! propagation) — `design/typecheck/check-form-api.md`.

use super::*;

// spec: design/typecheck/check-form-api.md §check_form — single defn CheckBody pass
#[test]
fn test_check_form_single_defn_check_body() {
    let mut tc = tc_with_prims();
    let module = ModuleFullPath::from("test");
    let mut accumulator = ModuleCheckAccumulator::new();

    let defn = make_inc_defn();
    let form = TopLevel::Defn(defn);

    // Must register first
    let reg_result = tc
        .check_form(&module, &form, CheckPass::Register, &mut accumulator)
        .unwrap();
    tc.merge_form_result(&module, &mut accumulator, reg_result);

    // Now check body
    let body_result = tc
        .check_form(&module, &form, CheckPass::CheckBody, &mut accumulator)
        .unwrap();

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

// spec: design/typecheck/check-form-api.md §check_form — TypeDef CheckBody is no-op
#[test]
fn test_check_form_typedef_check_body_noop() {
    let mut tc = tc_with_prims();
    let module = ModuleFullPath::from("test");
    let mut accumulator = ModuleCheckAccumulator::new();

    let form = make_color_typedef();
    // Register first
    let _ = tc
        .check_form(&module, &form, CheckPass::Register, &mut accumulator)
        .unwrap();

    // CheckBody on TypeDef should be a no-op
    let result = tc
        .check_form(&module, &form, CheckPass::CheckBody, &mut accumulator)
        .unwrap();
    assert!(result.method_resolutions.is_empty());
    assert!(result.expr_types.is_empty());
    assert!(result.constrained_fn.is_none());
    assert!(result.mono_defns.is_empty());
}

// spec: design/typecheck/check-form-api.md §check_form — TraitDecl CheckBody is no-op
#[test]
fn test_check_form_trait_decl_check_body_noop() {
    let mut tc = tc_with_prims();
    let module = ModuleFullPath::from("test");
    let mut accumulator = ModuleCheckAccumulator::new();

    let decl = crate::traits::test_helpers::parse_trait_decl("(deftrait Show (show [x] String))");
    let form = TopLevel::TraitDecl(decl);

    // Register first
    let _ = tc
        .check_form(&module, &form, CheckPass::Register, &mut accumulator)
        .unwrap();

    // CheckBody should be no-op
    let result = tc
        .check_form(&module, &form, CheckPass::CheckBody, &mut accumulator)
        .unwrap();
    assert!(result.method_resolutions.is_empty());
    assert!(result.expr_types.is_empty());
}

// spec: design/typecheck/check-form-api.md §check_form — Expr wrapped as __expr
#[test]
fn test_check_form_expr_register_and_check() {
    let mut tc = tc_with_prims();
    let module = ModuleFullPath::from("test");
    let mut accumulator = ModuleCheckAccumulator::new();

    // Wrap expr as synthetic defn (matching what check() does internally)
    let expr = Expr::IntLit {
        value: 42,
        span: span(700, 702),
        inferred_type: None,
    };
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
    let reg_result = tc
        .check_form(&module, &form, CheckPass::Register, &mut accumulator)
        .unwrap();
    tc.merge_form_result(&module, &mut accumulator, reg_result);

    assert!(
        accumulator
            .defn_type_vars
            .contains_key(&Symbol::from("__expr"))
    );

    // CheckBody pass
    let body_result = tc
        .check_form(&module, &form, CheckPass::CheckBody, &mut accumulator)
        .unwrap();

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
        let result = tc
            .check_form(&module, form, CheckPass::Register, &mut accumulator)
            .unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);
    }

    // Both signatures should be registered
    assert!(
        accumulator
            .defn_type_vars
            .contains_key(&Symbol::from("double"))
    );
    assert!(
        accumulator
            .defn_type_vars
            .contains_key(&Symbol::from("add-self"))
    );

    // Pass 2: Check bodies of both
    for form in &program {
        let result = tc
            .check_form(&module, form, CheckPass::CheckBody, &mut accumulator)
            .unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);
    }

    // Both should have produced expr_types
    assert!(
        !accumulator.expr_types.is_empty(),
        "accumulated expr_types should be non-empty"
    );

    // Finalize to get final types
    let _result = tc
        .finalize_check_result(&module, &mut accumulator, &program, ModuleStrategy::Replace)
        .unwrap();

    // After finalization, all expr_types should be resolved on annotated ASTs.
    for name in ["double", "add-self"] {
        if let Some(ModuleEntry::Def {
            ast: Some(defn), ..
        }) = tc.symbol_table().get(name)
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

// spec: design/typecheck/check-form-api.md §Invariant 2 — TraitDecl before TraitImpl
#[test]
fn test_check_form_trait_decl_before_impl() {
    let mut tc = tc_with_prims();
    let module = ModuleFullPath::from("test");
    let mut accumulator = ModuleCheckAccumulator::new();

    // Register TraitDecl(Eq) first
    let decl = crate::traits::test_helpers::parse_trait_decl("(deftrait Eq (eq [a b] Bool))");
    let decl_form = TopLevel::TraitDecl(decl);
    let result = tc
        .check_form(&module, &decl_form, CheckPass::Register, &mut accumulator)
        .unwrap();
    tc.merge_form_result(&module, &mut accumulator, result);

    // Then register TraitImpl(Eq for Int) — should succeed because decl was registered first
    let impl_ = TraitImpl {
        head_con_var: None,
        trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Eq")),
        target: cranelisp_types::TypeExpr::Named(cranelisp_types::TypeRef::new(
            None,
            TypeName::from("Int"),
        )),
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
            args: vec![Expr::var(Symbol::from("z"), span(862, 863))],
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
        let result = tc
            .check_form(&module, form, CheckPass::Register, &mut accumulator)
            .unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);
    }

    // Pass 2: Check all bodies
    for form in &program {
        let result = tc
            .check_form(&module, form, CheckPass::CheckBody, &mut accumulator)
            .unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);
    }

    // Finalize
    let _result = tc
        .finalize_check_result(&module, &mut accumulator, &program, ModuleStrategy::Replace)
        .unwrap();

    // All three should be monomorphic Int via shared substitution
    for name in &["f", "g", "h"] {
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get(*name) {
            assert!(
                scheme.type_vars.is_empty(),
                "{} should be monomorphic (pinned to Int via shared substitution)",
                name
            );
        } else {
            panic!("{} not found in symbol table", name);
        }
    }
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
                        Expr::IntLit {
                            value: 1,
                            span: span(1244, 1245),
                            inferred_type: None,
                        },
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
        if let ModuleEntry::Def {
            ast: Some(defn),
            scheme,
            ..
        } = entry
        {
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
                Expr::BoolLit {
                    value: true,
                    span: span(1326, 1330),
                    inferred_type: None,
                },
            ],
            span: span(1315, 1331),
            resolved_call: None,
            inferred_type: None,
        },
        Visibility::Public,
        span(1300, 1332),
    ));

    // Register should succeed
    let reg = tc
        .check_form(&module, &bad_defn, CheckPass::Register, &mut accumulator)
        .unwrap();
    tc.merge_form_result(&module, &mut accumulator, reg);

    // CheckBody should produce an error
    let result = tc.check_form(&module, &bad_defn, CheckPass::CheckBody, &mut accumulator);
    assert!(
        result.is_err(),
        "type error in body should propagate as Err"
    );
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
        target: cranelisp_types::TypeExpr::Named(cranelisp_types::TypeRef::new(
            None,
            TypeName::from("Int"),
        )),
        type_constraints: vec![],
        methods: vec![],
        span: Span::SYNTHETIC,
    };
    let form = TopLevel::TraitImpl(impl_);
    let result = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator);

    assert!(
        result.is_err(),
        "TraitImpl for undeclared trait should error"
    );
}

// ---- AST Annotation Tests (Step 1b) ----
