//! Per-submodule tests for `program/finalize.rs` — merge + finalize: accumulate
//! per-form results, run the cross-defn post-passes (regeneralize, resettle,
//! deferred re-resolve, the settlement-harvest windows), and drain the
//! accumulator into `CheckResult`. Split from the pooled `program/tests.rs`
//! (FIXME 0722).

use super::*;

use crate::program::test_support::*;

// spec: 07-traits §7.3 — finalization refreshes the exact settled method name
// minted by qualified impl registration, never a source-derived remangle.
#[test]
fn qualified_impl_finalize_refreshes_canonical_settled_entry() {
    let mut tc = tc_with_prims();
    let fmt = ModuleFullPath::from("fmt");
    let user = ModuleFullPath::from("test");
    let body_span = span(310, 311);

    tc.set_current_module(fmt.clone());
    tc.register_trait_decl_self(&crate::traits::test_helpers::parse_trait_decl(
        "(deftrait Display (shw [self] Int))",
    ))
    .unwrap();
    tc.set_current_module(user.clone());

    let impl_ = TraitImpl {
        head_con_var: None,
        trait_name: cranelisp_types::TraitRef::new(Some(fmt), TraitName::from("Display")),
        target: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int"))),
        type_constraints: vec![],
        methods: vec![Defn {
            name: Symbol::from("shw"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("self"), None)],
                body: Expr::IntLit {
                    value: 7,
                    span: body_span,
                    inferred_type: None,
                },
                span: span(300, 320),
            }],
            visibility: Visibility::Public,
            span: span(300, 320),
        }],
        span: span(290, 330),
    };
    let program = vec![TopLevel::TraitImpl(impl_)];
    let mut accumulator = ModuleCheckAccumulator::new();
    let registered = tc
        .check_form(&user, &program[0], CheckPass::Register, &mut accumulator)
        .unwrap();
    tc.merge_form_result(&user, &mut accumulator, registered);

    let canonical = Symbol::from("Display.shw$primitives/Int");
    assert!(
        accumulator
            .default_method_defns
            .iter()
            .any(|defn| defn.name == canonical),
        "registration must carry the settled canonical method name"
    );

    // Make the final refresh observable: erase the body annotation on the
    // canonical entry, then provide the settled span fact finalization owns.
    {
        let mut table = tc.symbol_table_mut();
        let Some(ModuleEntry::Def { ast: Some(ast), .. }) = table.symbols.get_mut(&canonical)
        else {
            panic!("qualified impl must publish its canonical method entry");
        };
        let Expr::IntLit { inferred_type, .. } = &mut ast.body else {
            panic!("expected literal impl body");
        };
        *inferred_type = None;
    }
    accumulator.expr_types.insert(body_span, Type::Int);

    tc.finalize_check_result(&user, &mut accumulator, &program, ModuleStrategy::Additive)
        .unwrap();

    let table = tc.symbol_table();
    let Some(ModuleEntry::Def { ast: Some(ast), .. }) = table.get(&canonical) else {
        panic!("canonical method entry must survive finalization");
    };
    let Expr::IntLit { inferred_type, .. } = &ast.body else {
        panic!("expected literal impl body");
    };
    assert_eq!(
        inferred_type.as_deref(),
        Some(&Type::Int),
        "production finalization must refresh the canonical settled entry"
    );
    assert!(
        table.get("fmt/Display.shw$Int").is_none(),
        "syntax-derived qualified/bare-target decoy must not be minted"
    );
}

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
    assert!(
        m.contains("2-arg"),
        "names the offending clause by arity: {m}"
    );
    assert!(m.contains("clause"), "says 'clause': {m}");
    assert!(m.contains("rot"), "names the unpinned param: {m}");
    assert!(
        m.contains("§3.11"),
        "cites the §3.11 standalone-equivalence rule: {m}"
    );
    assert!(
        !m.contains("independently"),
        "MS-8: drops the retired 'each arity clause is type-checked \
         independently' framing: {m}"
    );
    assert!(
        !m.contains("__"),
        "never leaks a synthetic binder (0568): {m}"
    );

    // Single-sig (no clause arity) + no bound param → the plain fn-level
    // message, still `__`-free.
    let plain = AmbiguousForm {
        name: Symbol::from("main"),
        span: sp,
        clause_arity: None,
        param: None,
    }
    .message();
    assert!(
        plain.contains("main") && plain.contains("ambiguous type"),
        "{plain}"
    );
    assert!(
        !plain.contains("clause"),
        "single-sig keeps the plain message: {plain}"
    );
    assert!(!plain.contains("__"), "no synthetic binder leak: {plain}");
}

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
    if let Some(ModuleEntry::Def {
        ast: Some(defn), ..
    }) = tc.symbol_table().get("inc")
    {
        walk_inferred_types(&defn.body, &mut any_typed, &mut all_resolved);
    }
    assert!(any_typed, "expr_types should be populated on annotated AST");
    assert!(
        all_resolved,
        "all expr_types should be resolved (no Var types)"
    );

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
    let program = vec![make_color_typedef(), TopLevel::Defn(make_is_red_defn())];

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
    if let Some(ModuleEntry::Def {
        ast: Some(defn), ..
    }) = tc.symbol_table().get("is-red")
    {
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
        assert_eq!(scheme.ty, Type::Fn(vec![Type::Int], Box::new(Type::Int)),);
    } else {
        panic!("double not found");
    }

    if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("add-self") {
        assert_eq!(scheme.ty, Type::Fn(vec![Type::Int], Box::new(Type::Int)),);
    } else {
        panic!("add-self not found");
    }

    // expr_types should be populated on annotated AST (post-slim).
    let mut any_typed = false;
    let mut _all_resolved = true;
    if let Some(ModuleEntry::Def {
        ast: Some(defn), ..
    }) = tc.symbol_table().get("add-self")
    {
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
    if let Some(ModuleEntry::Def {
        ast: Some(defn), ..
    }) = tc.symbol_table().get("__expr")
    {
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
                        Expr::IntLit {
                            value: 1,
                            span: span(620, 621),
                            inferred_type: None,
                        },
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
    if let Some(ModuleEntry::Def {
        ast: Some(defn), ..
    }) = tc.symbol_table().get("add$Int+Int")
    {
        walk_inferred_types(&defn.body, &mut any_typed, &mut _all_resolved);
    }
    assert!(any_typed);
}

// ---- Category 2: Per-Form Basics ----

// spec: design/typecheck/check-form-api.md — accumulator merge grows with each form
#[test]
fn test_check_form_accumulator_merge() {
    let mut tc = tc_with_prims();
    let module = ModuleFullPath::from("test");
    let mut accumulator = ModuleCheckAccumulator::new();

    let program = make_forward_ref_program();

    // Pass 1: Register all
    for form in &program {
        let result = tc
            .check_form(&module, form, CheckPass::Register, &mut accumulator)
            .unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);
    }

    // Pass 2: Check bodies and verify accumulator grows
    let et_before_first = accumulator.expr_types.len();
    let form0_result = tc
        .check_form(&module, &program[0], CheckPass::CheckBody, &mut accumulator)
        .unwrap();
    let form0_et = form0_result.expr_types.len();
    tc.merge_form_result(&module, &mut accumulator, form0_result);
    let et_after_first = accumulator.expr_types.len();

    assert!(
        et_after_first > et_before_first,
        "accumulator should grow after first form's CheckBody"
    );

    let form1_result = tc
        .check_form(&module, &program[1], CheckPass::CheckBody, &mut accumulator)
        .unwrap();
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
        let result = tc
            .check_form(&module, form, CheckPass::Register, &mut accumulator)
            .unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);
    }
    for form in &program {
        let result = tc
            .check_form(&module, form, CheckPass::CheckBody, &mut accumulator)
            .unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);
    }

    let _result = tc
        .finalize_check_result(&module, &mut accumulator, &program, ModuleStrategy::Replace)
        .unwrap();

    // finalize should produce complete annotated ASTs + method resolutions.
    // Post-slim (Wave 2 step 4): resolutions live on annotated AST nodes;
    // expr_types live on `Expr::inferred_type`.
    let mut any_typed = false;
    let mut all_resolved = true;
    if let Some(ModuleEntry::Def {
        ast: Some(defn), ..
    }) = tc.symbol_table().get("inc")
    {
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
    let reg = tc
        .check_form(&module, &defn_form, CheckPass::Register, &mut accumulator)
        .unwrap();
    tc.merge_form_result(&module, &mut accumulator, reg);

    // Check body
    let body = tc
        .check_form(&module, &defn_form, CheckPass::CheckBody, &mut accumulator)
        .unwrap();

    // Should detect constrained fn
    assert!(
        body.constrained_fn.is_some(),
        "add should be detected as constrained"
    );
    assert_eq!(body.constrained_fn.as_ref().unwrap().as_ref(), "add",);
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
        tc.symbol_table()
            .get(name)
            .and_then(|e| e.callable_got_slot())
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
    let idf = |s: u32| {
        TopLevel::Defn(make_defn(
            "idf",
            vec![Symbol::from("x")],
            vec![Some(cranelisp_types::TypeExpr::Named(
                cranelisp_types::TypeRef::new(None, TypeName::from("Int")),
            ))],
            Expr::var(Symbol::from("x"), span(s, s + 1)),
            Visibility::Public,
            span(s, s + 2),
        ))
    };
    tc.check(&[idf(10)], &ctx, ModuleStrategy::Additive)
        .unwrap();
    let slot_n = slot_of(&tc, "idf").expect("concrete idf must carry a slot");

    // Redefine idf with the SAME (concrete) shape — the determination point
    // must REUSE slot N, not allocate N+1.
    tc.check(&[idf(20)], &ctx, ModuleStrategy::Additive)
        .unwrap();
    let slot_after = slot_of(&tc, "idf").expect("redefined concrete idf must carry a slot");
    assert_eq!(
        slot_after, slot_n,
        "concrete→concrete redefinition MUST reuse the existing GOT slot \
         (use-after-free guard); got {slot_after} expected {slot_n}",
    );

    // (defn cadd [x y] (+ x y)) — `+` is the Num trait method, so the
    // inferred scheme carries a Num constraint → Constrained template,
    // slot-less by construction.
    let cadd = || {
        TopLevel::Defn(make_defn(
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
        ))
    };
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
    let int_ann = || {
        Some(cranelisp_types::TypeExpr::Named(
            cranelisp_types::TypeRef::new(None, TypeName::from("Int")),
        ))
    };
    let cadd_concrete = TopLevel::Defn(make_defn(
        "cadd",
        vec![Symbol::from("x"), Symbol::from("y")],
        vec![int_ann(), int_ann()],
        Expr::var(Symbol::from("x"), span(40, 41)),
        Visibility::Public,
        span(39, 42),
    ));
    tc.check(&[cadd_concrete], &ctx, ModuleStrategy::Additive)
        .unwrap();
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
                    DefKind::UserFn {
                        fn_state: UserFnState::Polymorphic(_)
                    }
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
        tc.symbol_table()
            .get("id")
            .and_then(|e| e.callable_got_slot()),
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
                DefKind::UserFn {
                    fn_state: UserFnState::Concrete { got_slot, .. },
                } => Some(*got_slot),
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
        DefKind::UserFn {
            fn_state: UserFnState::Concrete {
                got_slot: 7,
                mode_summary: None,
            },
        },
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
        DefKind::UserFn {
            fn_state: UserFnState::Constrained(Box::new(cf)),
        },
    )
    .build();
    assert!(template.is_constrained_template());
    assert_eq!(template.callable_got_slot(), None);
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
        Expr::VecLit {
            elements: vec![],
            span: span(10, 12),
            inferred_type: None,
        },
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
    tc.check(
        &[h, caller],
        &test_ctx(),
        cranelisp_types::ModuleStrategy::Additive,
    )
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
                    DefKind::UserFn {
                        fn_state: UserFnState::Concrete { .. }
                    }
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
        args: vec![Expr::IntLit {
            value: 7,
            span: span(43, 44),
            inferred_type: None,
        }],
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
    tc.check(&[h, caller], &test_ctx(), ModuleStrategy::Additive)
        .expect(
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
                    DefKind::UserFn {
                        fn_state: UserFnState::Concrete { .. }
                    }
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
