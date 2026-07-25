//! `program/mono_collect.rs` sub-topic — the typed dispatch carriers
//! (`VarRef`/`ApplyRef`, `design/typecheck/typed-resolution-carrier.md`): what
//! identity each resolved reference records, and the shadowing carve-outs that
//! must record none.

use super::*;

#[test]
fn builtin_qualified_extern_keeps_abi_name_and_exact_storage_home() {
    let mut tc = tc_with_prims();
    check_src(
        &mut tc,
        "(defn main [] (macros/sconcat macros/SNil macros/SNil))",
    );

    let view = main_codegen_view_of(&tc, "main");
    let mut targets = Vec::new();
    collect_resolved_targets(&view.body, &mut targets);
    assert!(
        targets.iter().any(|(label, fq)| {
            label == "@apply"
                && fq.as_ref()
                    == Some(&FQSymbol {
                        module: ModuleFullPath::from("macros"),
                        symbol: Symbol::from("sconcat"),
                    })
        }),
        "qualified builtin Apply must carry macros/sconcat; collected: {targets:?}"
    );
    let resolved_call = match &view.body {
        cranelisp_types::MonoExpr::Apply { resolved_call, .. } => resolved_call.as_deref(),
        other => panic!("expected Apply body, got {other:?}"),
    };
    assert!(matches!(
        resolved_call,
        Some(ResolvedCall::BuiltinFn { name }) if name.as_ref() == "sconcat"
    ));
}

#[test]
fn builtin_renamed_import_uses_terminal_abi_name_and_storage_home() {
    let mut tc = tc_with_prims();
    tc.symbol_table_mut().insert(
        Symbol::from("sum"),
        ModuleEntry::Import {
            source: FQSymbol {
                module: ModuleFullPath::from("primitives"),
                symbol: Symbol::from("add-i64"),
            },
            visibility: Visibility::Public,
        },
    );
    check_src(&mut tc, "(defn main [] (sum 1 2))");

    let view = main_codegen_view_of(&tc, "main");
    let mut targets = Vec::new();
    collect_resolved_targets(&view.body, &mut targets);
    assert!(targets.iter().any(|(label, fq)| {
        label == "@apply"
            && fq.as_ref()
                == Some(&FQSymbol {
                    module: ModuleFullPath::from("primitives"),
                    symbol: Symbol::from("add-i64"),
                })
    }));
    let resolved_call = match &view.body {
        cranelisp_types::MonoExpr::Apply { resolved_call, .. } => resolved_call.as_deref(),
        other => panic!("expected Apply body, got {other:?}"),
    };
    assert!(matches!(
        resolved_call,
        Some(ResolvedCall::BuiltinFn { name }) if name.as_ref() == "add-i64"
    ));
}

#[test]
fn builtin_immediate_autocurry_keeps_exact_storage_home() {
    let mut tc = tc_with_prims();
    check_src(&mut tc, "(defn main [] (macros/sconcat macros/SNil))");

    let view = main_codegen_view_of(&tc, "main");
    let mut targets = Vec::new();
    collect_resolved_targets(&view.body, &mut targets);
    assert!(
        targets.iter().any(|(label, fq)| {
            label == "@apply"
                && fq.as_ref()
                    == Some(&FQSymbol {
                        module: ModuleFullPath::from("macros"),
                        symbol: Symbol::from("sconcat"),
                    })
        }),
        "immediate builtin auto-curry must retain macros/sconcat; collected: {targets:?}"
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
                Expr::IntLit {
                    value: 1,
                    span: span(12, 13),
                    inferred_type: None,
                },
                Expr::IntLit {
                    value: 2,
                    span: span(14, 15),
                    inferred_type: None,
                },
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
        x_span,
        Span::SYNTHETIC,
        "the defn-param binding-form span must be real, not SYNTHETIC"
    );
    assert_ne!(
        y_span,
        Span::SYNTHETIC,
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
                args: vec![Expr::IntLit {
                    value: 3,
                    span: span(91, 92),
                    inferred_type: None,
                }],
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
    let bare_fq = targets
        .iter()
        .find(|(l, _)| l == "Some")
        .and_then(|(_, fq)| fq.clone());
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
    let accessor_fq = targets
        .iter()
        .find(|(l, _)| l == "v")
        .and_then(|(_, fq)| fq.clone());
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
    let bar_fq = targets
        .iter()
        .find(|(l, _)| l == "bar")
        .and_then(|(_, fq)| fq.clone());
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

// A trait short-circuit carries its builtin identity as one correlated product.
// A same-named USER fn in caller scope therefore cannot capture the storage key:
// there is no bare-name re-resolution after the short-circuit selection.
// spec: design/arch/backend-keyed-consumer.md §1.1.1 (BuiltinFn leg)
#[test]
fn resolved_target_builtin_fq_ignores_shadowing_user_fn() {
    let mut tc = tc_with_prims();
    // `+` dispatches to the Int impl (short-circuit → jit name add-i64).
    register_num_trait_inline(&mut tc);
    // Model the prelude-suppressed shadow: a local UserFn named `add-i64`
    // installed over the primitives import. The already-selected builtin
    // product must remain authoritative.
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
    tc.symbol_table_mut()
        .insert(Symbol::from("add-i64"), local_add);
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
        "the selected builtin product must retain primitives/add-i64, not capture \
         the caller's test/add-i64; collected: {targets:?}"
    );
}

#[test]
fn builtin_settled_autocurry_retry_keeps_renamed_nonprimitive_home() {
    let mut tc = tc_with_prims();
    tc.symbol_table_mut().insert(
        Symbol::from("cat"),
        ModuleEntry::Import {
            source: FQSymbol {
                module: ModuleFullPath::from("macros"),
                symbol: Symbol::from("sconcat"),
            },
            visibility: Visibility::Public,
        },
    );
    let callee_ty = tc.lookup("cat").expect("renamed builtin scheme").ty;
    let call_span = span(700, 710);
    let callee_span = span(701, 704);
    tc.state.method_resolutions.var_refs.insert(
        callee_span,
        cranelisp_types::VarRef::Global(FQSymbol {
            module: ModuleFullPath::from("macros"),
            symbol: Symbol::from("sconcat"),
        }),
    );
    tc.state.pending_auto_curry.push((
        call_span,
        Symbol::from("cat"),
        1,
        2,
        callee_ty,
        None,
        Some(callee_span),
    ));

    let env = TypeCheckEnv::new(
        &tc.modules,
        &tc.next_id,
        &tc.module_aliases,
        &tc.prelude_fallback,
    );
    env.resolve_auto_curry(&mut tc.state, AutoCurryDrain::Final);

    assert_eq!(
        tc.state.method_resolutions.apply_refs.get(&call_span),
        Some(&cranelisp_types::ApplyRef::Dispatch(FQSymbol {
            module: ModuleFullPath::from("macros"),
            symbol: Symbol::from("sconcat"),
        })),
        "settled retry must preserve the renamed builtin's terminal macros home"
    );
    assert!(matches!(
        tc.state.method_resolutions.resolved_calls.get(&call_span),
        Some(ResolvedCall::AutoCurry {
            trait_resolution: Some(inner),
            ..
        }) if matches!(inner.as_ref(), ResolvedCall::BuiltinFn { name } if name.as_ref() == "sconcat")
    ));
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
        Some(ModuleEntry::Def {
            codegen_view: Some(v),
            ..
        }) => v.clone(),
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
         (deftype Color Red Green)\n\
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
                    DefKind::UserFn {
                        fn_state: UserFnState::Concrete { .. }
                    }
                ),
                "test/iden$Int must be a Concrete (slotted) mono instance, got {kind:?}",
            );
            assert!(
                scheme.ty.is_concrete(),
                "test/iden$Int type must be concrete"
            );
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
