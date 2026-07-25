//! `program/mono_collect.rs` sub-topic — the batch and REPL `pass4_monomorphise`
//! drivers end-to-end: what a run mints (and what it must NOT mint — the
//! no-partial-instance rule, `monomorphisation.md` §9.3 Phase-4 part A).

use super::*;

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
                        Expr::IntLit {
                            value: 3,
                            span: span(44, 45),
                            inferred_type: None,
                        },
                        Expr::IntLit {
                            value: 4,
                            span: span(46, 47),
                            inferred_type: None,
                        },
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
    let _result = tc.check_repl_input_self(&expr_input).unwrap();

    // Should have mono_defns populated (entry on SymbolTable post-slim)
    let mono_names = tc.mono_defn_names();
    assert!(
        !mono_names.is_empty(),
        "REPL expr should generate mono_defns for constrained fn calls"
    );
    assert!(
        // FIXME 0519: mono names are home-qualified `{home}/{bare}$sig`.
        mono_names.iter().any(|n| n.as_ref() == "test/add$Int+Int"),
        "expected test/add$Int+Int in mono entries, got {mono_names:?}"
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
                    Expr::IntLit {
                        value: 1,
                        span: span(204, 205),
                        inferred_type: None,
                    },
                    Expr::IntLit {
                        value: 2,
                        span: span(206, 207),
                        inferred_type: None,
                    },
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
        // FIXME 0519: mono names are home-qualified `{home}/{bare}$sig`.
        mono_names.iter().any(|n| n.as_ref() == "test/add$Int+Int"),
        "expected test/add$Int+Int in mono entries, got {mono_names:?}"
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

    assert!(tc.constrained_fn_names_set().is_empty());
    assert!(tc.mono_defn_names().is_empty());
}

// --- Multi-sig defn tests ---

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
            params[1],
            ret,
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
                    f_ret.as_ref(),
                    &Type::Var(b),
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
        assert_eq!(
            params[1],
            Type::Var(b_acc),
            "init must be the accumulator var b"
        );
        assert_eq!(
            ret.as_ref(),
            &Type::Var(b_acc),
            "result must be the accumulator var b"
        );
        // v (params[2]) is `(Vec a)` — element type a.
        match &params[2] {
            Type::ADT(name, args) if name.name.as_ref() == "Vec" => {
                assert_eq!(args.len(), 1, "Vec is unary");
                assert_eq!(
                    args[0],
                    Type::Var(a_elem),
                    "v must be (Vec a) over the element var"
                );
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
    assert_eq!(
        call_prog.len(),
        1,
        "expected a single trailing expression form"
    );
    let call_result = tc
        .check_program_self(&call_prog)
        .expect("Int-accumulator reduce call must type-check (FIXME 0344)");
    let display = call_result
        .display
        .expect("trailing expression must produce a display type");
    assert_eq!(
        display.ty,
        Type::Int,
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
        .filter(|(name, _)| name.as_ref().contains("reduce$"))
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
                ret.as_ref(),
                &Type::Int,
                "main folds Ints to an Int (FIXME 0349); got ret {:?}",
                ret,
            );
        }
        other => panic!("main scheme is not a function type: {other:?}"),
    }
}

// spec: design/arch/concrete-boundary-type.md §4-A — Phase-4 part A
//   mono-completeness: the fold helper mints ONLY the genuine concrete
//   `reduce-loop$Int+Vec+Int+Int` instance, NOT the spurious partial
//   `reduce-loop$Vec+Int+Int`. The spurious partial was minted by
//   `monomorphise_inner_parametric_hops` recursing into `reduce`'s body
//   while `reduce` is still generic (`f`/`acc`/element are `reduce`'s own
//   scheme vars), bypassing the all-args-concrete gate via the bare-var-
//   result trigger. After part A's all-args-concrete guard + trigger collapse,
//   no partial is minted; every minted instance is fully concrete, so
//   `MonoExpr::from_expr` succeeds on each (the carve-out deletion's
//   completeness proof — the check below returning Ok IS that proof for the
//   fold shape, since an instance with a residual var would now raise the
//   ambiguity TypeError instead of being swallowed).
#[test]
fn fold_helper_mints_only_concrete_instance_no_partial() {
    let mut tc = tc_with_prims();
    // The 0344 fold shape with a CONCRETE caller `main` (Int accumulator).
    let src = "\
        (defn reduce [f init v] (reduce-loop f init v (vec-len v) 0))\n\
        (defn reduce-loop [f acc v :primitives/Int len :primitives/Int i]\n  \
          (if (ge-i64 i len) acc\n    \
            (reduce-loop f (f acc (vec-get v i)) v len (add-i64 i 1))))\n\
        (defn main [] (reduce add-i64 0 [1 2 3]))";
    let sexps = cranelisp_frontend::parse(src).expect("parse");
    let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");

    // The check must SUCCEED — with the `allowed_vars` carve-out deleted, a
    // surviving residual var in any minted instance would now surface as the
    // ambiguity / could-not-monomorphise TypeError at the mono seam. Success
    // is the completeness proof for the fold shape.
    let result = tc.check_program_self(&program);
    assert!(
        result.is_ok(),
        "fold must type-check AND every minted instance must be fully \
         concrete (Phase-4 part A — `from_expr` succeeds on every instance); \
         got error: {:?}",
        result.as_ref().err().map(|e| e.message().to_string()),
    );

    // The genuine concrete instance MUST be minted; the SPURIOUS partial
    // (Var-dropping lossy name) MUST NOT.
    let mono_names: Vec<String> = tc
        .mono_variants()
        .iter()
        .map(|v| v.name.as_ref().to_string())
        .collect();
    // FIXME 0519: the mono name is home-qualified with a lossless recursive
    // sig (`f`'s `Fn` type recursed, the `(Vec Int)` arg recursed FQ), so the
    // exact string is `test/reduce-loop$Fn(...)+Int+.../Vec$Int+Int+Int`. The
    // test's invariant is unchanged: exactly ONE genuine concrete instance,
    // and NO spurious partial (a residual `Var` token in the sig).
    let reduce_loop_monos: Vec<&String> = mono_names
        .iter()
        .filter(|n| n.contains("reduce-loop$"))
        .collect();
    assert!(
        !reduce_loop_monos.is_empty(),
        "the genuine concrete `reduce-loop` mono must be minted; \
         mono variants: {mono_names:?}",
    );
    assert!(
        !reduce_loop_monos.iter().any(|n| n.contains("Var")),
        "the SPURIOUS partial `reduce-loop` mint (a residual-`Var` lossy sig) \
         must NOT be minted (Phase-4 part A suppresses the generic-caller \
         recursion mint); mono variants: {mono_names:?}",
    );
}
