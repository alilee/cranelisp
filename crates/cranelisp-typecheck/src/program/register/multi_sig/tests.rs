//! Per-submodule tests for `program/register/multi_sig.rs` — the multi-signature
//! overload family: arity/type-discriminated clause registration, duplicate-sig
//! rejection, the mangled variant entries and their annotated ASTs, and
//! call-site variant selection (`spec/05-definitions.md` §5.1.2).

use super::*;

use crate::program::test_support::*;
use cranelisp_types::ConcreteType;



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

// ============ §11.8.11 the deferred-dispatch callee retype (S115 W4, 0719) ====

// spec: spec/05-definitions.md §5.1.2 — a multi-sig defn type-checks identically
// to the equivalent two-function form. The WRAPPER-indirection shape
// (`(defn run-elim [idx] (vec-len (peers idx)))` over a multi-sig `peers`) is the
// S115 0719 face. Inside the minted instance of the `$Var` template clause the
// overloaded base is no longer the enclosing defn, so the sibling call drains as
// an EXTERNAL call to the concrete clause — and the DEFERRED arm, unlike the
// inline arm in `infer_apply`, left the callee `Var` carrying the base's
// PRE-DISPATCH instantiation. Its element var never settled, so `from_expr`
// rejected the instance:
//   `ambiguous type … monomorphised in \`user/peers$Var$Int\``.
// The drain now records the callee's type from the settled dispatch DECISION
// (P26). `check_src` panics on any check error, so a clean return IS the
// assertion — this cell goes RED the moment the retype is reverted (verified by
// revert, S115 W4), and its e2e twin is
// `tests/mc_x4_consume_at_distance_0719::multi_sig_return_through_wrapper_indirection_infers`.
#[test]
fn wrapper_indirected_multi_sig_return_monomorphises_from_settled_state() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn peers\n\
         \x20 ([idx]     (peers idx []))\n\
         \x20 ([idx acc] (if (eq-i64 idx 0) acc (peers (add-i64 idx -1) (vec-push acc idx)))))\n\
         (defn run-elim [idx] (vec-len (peers idx)))\n\
         (defn top [] (run-elim 3))",
    );
    // The template clause's instance exists and carries a concrete-boundary view
    // — a view cannot be built while any node retains a residual `Var`, so its
    // presence IS the settled-state evidence.
    let minted = symbol_names_containing(&tc, "peers$");
    assert!(
        minted.iter().any(|n| n.contains("$Int")),
        "the wrapper-indirected multi-sig call MUST mint a concrete instance; \
         got {minted:?}"
    );
    let _view = mono_instance_view_containing(&tc, "peers$Var$");
}

// spec: spec/05-definitions.md §5.1.2 — a multi-sig defn type-checks identically
// to the equivalent two-function form, and every node of the checked body
// carries its own type. The SELF-CALL face of FIXME 0719/0774: a cross-clause
// self-call is drained in pass 1 (`is_self_call`), and until S115 W4b that arm
// carried a 21-line comment describing a callee retype it did not perform — the
// callee `Var` kept the PRE-DISPATCH instantiation of the overloaded base, which
// the drain's own back-flow unify had by then bound to the call's RESULT var. The
// observable symptom is sharp and needs no program shape to provoke: the callee
// of an application is typed `Int` instead of `Fn([Int, Int], Int)` — a node type
// no consumer can act on. This cell asserts the callee node's type is a function
// type in BOTH clauses of a self-recursive multi-sig, so the arm cannot regress
// to comment-only again (verified by revert, S115 W4b: both assertions go RED,
// each reporting `Int`).
#[test]
fn self_call_drain_retypes_the_callee_node_from_settled_state() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn cnt\n\
         \x20 ([n]   (cnt n 0))\n\
         \x20 ([n a] (if (eq-i64 n 0) a (cnt (add-i64 n -1) (add-i64 a 1)))))\n\
         (defn top [] (cnt 3))",
    );
    // Both clauses self-call `cnt`; both drained through the pass-1 self-call arm.
    for variant in ["cnt$Int", "cnt$Int+Int"] {
        let view = main_codegen_view_of(&tc, variant);
        let mut callees = Vec::new();
        collect_callee_types_named(&view.body, "cnt", &mut callees);
        assert!(
            !callees.is_empty(),
            "{variant} must contain a self-call to `cnt`"
        );
        for ty in &callees {
            assert!(
                matches!(ty, ConcreteType::Fn(..)),
                "{variant}: the self-call callee node must be typed from the settled \
                 dispatch decision (a Fn type), got {ty:?}"
            );
        }
    }
}

/// Collect the `ty` of every `Var` in CALLEE position whose name is `name`.
fn collect_callee_types_named(e: &MonoExpr, name: &str, out: &mut Vec<ConcreteType>) {
    if let MonoExpr::Apply { callee, .. } = e
        && let MonoExpr::Var { name: n, ty, .. } = callee.as_ref()
        && n.as_ref() == name
    {
        out.push(ty.clone());
    }
    match e {
        MonoExpr::Apply { callee, args, .. } => {
            collect_callee_types_named(callee, name, out);
            for a in args {
                collect_callee_types_named(a, name, out);
            }
        }
        MonoExpr::If { cond, then_branch, else_branch, .. } => {
            collect_callee_types_named(cond, name, out);
            collect_callee_types_named(then_branch, name, out);
            collect_callee_types_named(else_branch, name, out);
        }
        MonoExpr::Let { bindings, body, .. } => {
            for (_, rhs) in bindings {
                collect_callee_types_named(rhs, name, out);
            }
            collect_callee_types_named(body, name, out);
        }
        MonoExpr::Match { scrutinee, arms, .. } => {
            collect_callee_types_named(scrutinee, name, out);
            for arm in arms {
                collect_callee_types_named(&arm.body, name, out);
            }
        }
        _ => {}
    }
}

// spec: spec/05-definitions.md §5.1.2 — the TEMPLATE-clause face of FIXME 0719
// (the third arm, unpinned until S115 W4b). An EXTERNAL call to a
// genuinely-polymorphic multi-sig clause monomorphises the clause at this call's
// args and dispatches to the MINTED INSTANCE; the callee node must be retyped to
// that instance's signature for the same reason the concrete arm is — otherwise
// it keeps the overloaded base's pre-dispatch instantiation. Pinned by asserting
// the caller's callee node is a `Fn` over the call's concrete args (verified by
// revert, S115 W4b: RED, reporting the bare result type).
#[test]
fn template_clause_external_call_retypes_the_callee_node_to_the_instance() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn idpoly ([x] x) ([x y] (add-i64 x y)))\n\
         (defn top [] (idpoly 3))",
    );
    let view = main_codegen_view_of(&tc, "top");
    let mut callees = Vec::new();
    collect_callee_types_named(&view.body, "idpoly", &mut callees);
    assert_eq!(callees.len(), 1, "top must contain one call to `idpoly`");
    assert!(
        matches!(&callees[0], ConcreteType::Fn(p, r)
            if p.as_slice() == [ConcreteType::Int] && **r == ConcreteType::Int),
        "the template-clause call's callee node must carry the minted instance's \
         signature Fn([Int], Int), got {:?}",
        callees[0]
    );
}
