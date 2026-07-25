//! Per-submodule tests for `program/mono_collect.rs` — the Pass-4 collection
//! concern: walk bodies for constrained/parametric call sites, dedup, drive
//! `monomorphise_call`, drain the auto-curry. Split from the pooled
//! `program/tests.rs` (FIXME 0722); the batch/REPL drivers, the dispatch
//! carriers and the multi-sig dispatch legs are sub-topics in sibling files.

use super::*;

use crate::program::test_support::*;

mod batch;

mod carriers;

mod multi_sig;

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
    TypeCheckEnv::<()>::collect_constrained_calls(
        &expr,
        &constrained,
        &all_var_carriers(&expr),
        &mut calls,
    );

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
    TypeCheckEnv::<()>::collect_constrained_calls(
        &expr,
        &constrained,
        &all_var_carriers(&expr),
        &mut calls,
    );

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
    TypeCheckEnv::<()>::collect_constrained_calls(
        &expr,
        &constrained,
        &all_var_carriers(&expr),
        &mut calls,
    );

    assert_eq!(calls.len(), 1);
    assert_eq!(calls[0].0.as_ref(), "add");
}

// spec: 03-types §3.6 — collect_constrained_calls recurses into if branches
#[test]
fn test_collect_constrained_calls_recurses_into_if() {
    let constrained = HashSet::from([Symbol::from("add")]);
    // (if true (add 1 2) (add 3 4))
    let expr = Expr::If {
        cond: Box::new(Expr::BoolLit {
            value: true,
            span: span(4, 8),
            inferred_type: None,
        }),
        then_branch: Box::new(Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("add"), span(10, 13))),
            args: vec![
                Expr::IntLit {
                    value: 1,
                    span: span(14, 15),
                    inferred_type: None,
                },
                Expr::IntLit {
                    value: 2,
                    span: span(16, 17),
                    inferred_type: None,
                },
            ],
            span: span(9, 18),
            resolved_call: None,
            inferred_type: None,
        }),
        else_branch: Box::new(Expr::Apply {
            callee: Box::new(Expr::var(Symbol::from("add"), span(20, 23))),
            args: vec![
                Expr::IntLit {
                    value: 3,
                    span: span(24, 25),
                    inferred_type: None,
                },
                Expr::IntLit {
                    value: 4,
                    span: span(26, 27),
                    inferred_type: None,
                },
            ],
            span: span(19, 28),
            resolved_call: None,
            inferred_type: None,
        }),
        span: span(0, 29),
        inferred_type: None,
    };

    let mut calls = Vec::new();
    TypeCheckEnv::<()>::collect_constrained_calls(
        &expr,
        &constrained,
        &all_var_carriers(&expr),
        &mut calls,
    );

    assert_eq!(calls.len(), 2, "should find calls in both branches");
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
            Expr::IntLit {
                value: 3,
                span: span(104, 105),
                inferred_type: None,
            },
            Expr::IntLit {
                value: 4,
                span: span(106, 107),
                inferred_type: None,
            },
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
                args: vec![Expr::IntLit {
                    value: 7,
                    span: span(43, 44),
                    inferred_type: None,
                }],
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
        Some(ModuleEntry::Def {
            codegen_view: Some(v),
            ..
        }) => v.clone(),
        other => panic!("main has no codegen_view: {other:?}"),
    };

    fn collect_sig_dispatch(e: &MonoExpr, out: &mut Vec<String>) {
        let rc = match e {
            MonoExpr::Apply {
                callee,
                args,
                resolved_call,
                ..
            } => {
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
            MonoExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
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
                    DefKind::UserFn {
                        fn_state: UserFnState::Concrete { .. }
                    }
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
// carrier (`var_refs → VarRef::Global(mk$Int)`; S114 carrier flip — was
// `resolved_targets → mk$Int`) is written UNCONDITIONALLY. Only the
// belt-and-braces AST `Var`-rename skips (its target `st.symbols.get_mut(base)`
// is the `Overloaded` base entry with `ast: None` — the clause bodies live
// under the MANGLED variant entries). That skip is benign: the mangled
// variant's `codegen_view` is rebuilt from `var_refs`, so the backend
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
                DefKind::UserFn {
                    fn_state: UserFnState::Constrained(_)
                }
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
        monos
            .iter()
            .find(|(n, _)| n == "helper/cmp$Int")
            .map(|(_, c)| *c)
            .unwrap_or(false),
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
                        DefKind::UserFn {
                            fn_state: UserFnState::Concrete { .. }
                        }
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
            Type::ADT(name, args) if name.name.as_ref() == "Vec" && args.len() == 1 => {
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
            let a = vec_var(&params[0])
                .unwrap_or_else(|| panic!("param 0 must be (Vec x), got {:?}", params[0]));
            let b = vec_var(&params[1])
                .unwrap_or_else(|| panic!("param 1 must be (Vec x), got {:?}", params[1]));
            let r = vec_var(ret).unwrap_or_else(|| panic!("result must be (Vec x), got {:?}", ret));
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

#[test]
fn find_trait_method_decl_home_hop_finds_self_returning_method_d2() {
    let mut tc = tc_with_prims();
    let zlib = ModuleFullPath::from("zlib");
    tc.set_current_module(zlib.clone());
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    // Trait `Zero` with a nullary Self-returning method `z` (`(z [] self)`).
    let decl = crate::traits::test_helpers::parse_trait_decl("(deftrait Zero (z [] self))");
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

// =============== §1.3 the fn-as-value `'='` producer boundary (S115 W4) ======

/// The `ApplyRef` recorded at the FIRST `Apply` in a `codegen_view` body whose
/// resolved call is an `AutoCurry` — the carrier the backend's wrapper emitter
/// reads (`control_flow/fn_as_value.rs::emit_wrapper_call`).
fn autocurry_dispatch_in(view: &MonoDefnVariant) -> cranelisp_types::ApplyRef {
    fn find(e: &MonoExpr) -> Option<cranelisp_types::ApplyRef> {
        if let MonoExpr::Apply {
            dispatch,
            resolved_call,
            args,
            callee,
            ..
        } = e
        {
            if matches!(
                resolved_call.as_deref(),
                Some(cranelisp_types::ResolvedCall::AutoCurry { .. })
            ) {
                return Some(dispatch.clone());
            }
            if let Some(r) = find(callee) {
                return Some(r);
            }
            for a in args {
                if let Some(r) = find(a) {
                    return Some(r);
                }
            }
        }
        None
    }
    find(&view.body).expect("the body carries an AutoCurry Apply")
}

// spec: design/backend/s115-carrier-and-rc-sweep.md §1.3 — the producer BOUNDARY:
// a trait-method DECLARATION FQ is a dispatch-table key with NO GOT slot, so it
// must NEVER be transported as an `ApplyRef::Dispatch` carrier. Partially applying
// a trait operator inside a body whose operand type is only pinned by a LATER form
// (`(defn g [x] (+ x))` … `(g 3)`) left `try_resolve_trait_method` with a free var
// at the per-form drain, and the else-branch shipped the callee `Var`'s
// `VarRef::Global(<trait-home>/+)` — the decl — straight to the wrapper emitter,
// which died at the GOT terminal. The deferrable drain now holds the entry for the
// SETTLED finalize window, where the operand IS concrete and the operator resolves
// to its impl. This is the gate's detection proof: reverting the boundary check
// makes this cell RED (the carrier reverts to the decl FQ).
#[test]
fn autocurry_over_trait_operator_never_carries_the_decl_fq() {
    let mut tc = tc_with_prims();
    register_num_trait_inline(&mut tc);
    check_src(
        &mut tc,
        "(defn g [x] (+ x))\n\
         (defn h [] ((g 3) 4))",
    );
    let view = main_codegen_view_of(&tc, "g");
    match autocurry_dispatch_in(&view) {
        cranelisp_types::ApplyRef::Dispatch(fq) => {
            assert_eq!(
                fq,
                FQSymbol {
                    module: ModuleFullPath::from("primitives"),
                    symbol: Symbol::from("add-i64"),
                },
                "the settled operator curry must retain the exact builtin storage \
                 identity, never the trait declaration or a reconstructed name"
            );
        }
        other => panic!(
            "expected a slotted dispatch carrier for the settled operator curry; got {other:?}"
        ),
    }
}

// spec: design/backend/s115-carrier-and-rc-sweep.md §1.3 — the boundary PREDICATE
// itself, both polarities. `fq_is_trait_method_decl` is carrier-keyed (Principle
// 24): it asks the question of the FQ that would be transported, not of the raw
// source name, so a plain user fn of the same shape is unaffected.
#[test]
fn fq_is_trait_method_decl_discriminates_decl_from_callable() {
    let mut tc = tc_with_prims();
    register_num_trait_inline(&mut tc);
    check_src(
        &mut tc,
        "(defn plus2 [:primitives/Int x] :primitives/Int x)",
    );
    let module = tc.state.current_module.clone();
    assert!(
        tc.env().fq_is_trait_method_decl(&FQSymbol {
            module: module.clone(),
            symbol: Symbol::from("+"),
        }),
        "the `deftrait Num` method entry `+` IS a declaration (it carries \
         `trait_origin`) — unslotted, never a dispatch carrier"
    );
    assert!(
        !tc.env().fq_is_trait_method_decl(&FQSymbol {
            module,
            symbol: Symbol::from("plus2"),
        }),
        "a plain user fn is a callable, NOT a trait-method declaration — the \
         boundary must not over-reach and strand ordinary plain-fn curries"
    );
}

// spec: design/backend/s115-carrier-and-rc-sweep.md §1.3 — the MULTI-SIG
// per-variant TWIN of `autocurry_over_trait_operator_never_carries_the_decl_fq`
// (FIXME 0775; the standing "coverage by definition variants" lens — one
// invariant, both def forms, SAME assertion). A trait operator partially applied
// inside a multi-sig CLAUSE must not transport the trait-method declaration FQ
// as its dispatch carrier, exactly as in the single-sig form.
//
// DETECTION, stated honestly (METHOD §2.2 — an instrument is unverified until it
// is proven to detect). This cell pins the CONTRACT for the multi-sig form; it
// does NOT detect a discipline flip at the per-variant drain seam
// (`program/body.rs:441` `Deferrable`→`Final` leaves it GREEN, measured S115
// W4b). The reason is structural: the 1-arity clause here stays a `$Var`
// template, so the observable carrier is minted by the mono-body RECHECK — a
// `Final` seam — which re-derives it from settled state regardless of what the
// per-variant drain concluded. Five of the six drain seams have no unit-tier
// detection today; that gap is FIXME 0779 (`target: /qa`), not something this
// cell can close.
#[test]
fn autocurry_in_a_multi_sig_clause_never_carries_the_decl_fq() {
    let mut tc = tc_with_prims();
    register_num_trait_inline(&mut tc);
    check_src(
        &mut tc,
        "(defn g ([x] (+ x)) ([x y] (+ x y)))\n\
         (defn h [] ((g 3) 4))",
    );
    // The 1-arity clause is a `$Var` template; `(g 3)` mints its instance.
    let view = mono_instance_view_containing(&tc, "g$");
    match autocurry_dispatch_in(&view) {
        cranelisp_types::ApplyRef::Dispatch(fq) => {
            assert!(
                !tc.env().fq_is_trait_method_decl(&fq),
                "the multi-sig clause's auto-curry carrier MUST NOT be the \
                 trait-method DECLARATION `{fq}` — the per-variant drain seam is \
                 pre-settlement exactly like the single-sig one"
            );
        }
        other => panic!(
            "expected a slotted dispatch carrier for the settled operator curry; got {other:?}"
        ),
    }
}
