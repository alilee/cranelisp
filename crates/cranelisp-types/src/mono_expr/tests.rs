use super::*;
use crate::{MatchArm, ModuleFullPath, Type, TypeExpr, TypeName, TypeRef};
use std::collections::HashMap;

/// NOTE: `Span::new(0, 0)` == [`Span::SYNTHETIC`]. Tests that exercise
/// TYPE-side behaviour (concreteness, erasure) deliberately use this synthetic
/// span so their `Var`/`Apply` nodes take the all-local carve-out and need no
/// sidecar entries; tests that exercise the RESOLUTION gate use real spans and
/// explicit typed-map entries.
fn span() -> Span {
    Span::new(0, 0)
}

fn int_ty() -> Option<Box<Type>> {
    Some(Box::new(Type::Int))
}

fn int_lit(v: i64) -> Expr {
    Expr::IntLit {
        value: v,
        span: span(),
        inferred_type: int_ty(),
    }
}

fn no_pc() -> HashMap<Span, FQSymbol> {
    HashMap::new()
}

fn no_vr() -> HashMap<Span, VarRef> {
    HashMap::new()
}

fn no_ar() -> HashMap<Span, ApplyRef> {
    HashMap::new()
}

fn typed_var(name: &str, sp: Span, ty: Type) -> Expr {
    Expr::Var {
        name: Symbol::from(name),
        span: sp,
        resolved_call: None,
        inferred_type: Some(Box::new(ty)),
    }
}

// S109 W1.2 §10.2 (BU-3, population→transport seam): a `Pattern::Constructor`
// arm's `resolved_ctor` is populated from the `pattern_ctors` sidecar keyed by
// the CONSTRUCTOR PATTERN's OWN span (not the arm span); a `Wildcard` arm stays
// `None`; an empty sidecar leaves the ctor arm `None` (the loud-miss precondition
// the backend keys on).
#[test]
fn match_arm_carries_resolved_ctor_from_sidecar_keyed_by_pattern_span() {
    use crate::{FQSymbol, FQTypeName, Pattern, SymbolRef};
    let pat_span = Span::new(10, 20);
    let fq = FQSymbol {
        module: ModuleFullPath::from("m"),
        symbol: Symbol::from("Maybe.Some"),
    };
    let scrut = typed_var(
        "s",
        span(),
        Type::ADT(
            FQTypeName::new(ModuleFullPath::from("m"), TypeName::from("Maybe")),
            vec![],
        ),
    );
    let match_expr = Expr::Match {
        scrutinee: Box::new(scrut),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: SymbolRef::new(None, Symbol::from("Some")),
                    bindings: vec![Symbol::from("x")],
                    span: pat_span,
                },
                body: int_lit(1),
                span: Span::new(5, 30),
            },
            MatchArm {
                pattern: Pattern::Wildcard {
                    span: Span::new(40, 41),
                },
                body: int_lit(0),
                span: Span::new(50, 60),
            },
        ],
        span: span(),
        compiler_generated: false,
        inferred_type: int_ty(),
    };
    let mut pc = no_pc();
    pc.insert(pat_span, fq.clone());

    let MonoExpr::Match { arms, .. } =
        MonoExpr::from_expr(&match_expr, &pc, &no_vr(), &no_ar()).expect("concrete")
    else {
        panic!("expected a Match node");
    };
    assert_eq!(
        arms[0].resolved_ctor.as_ref(),
        Some(&fq),
        "the ctor arm carries the sidecar FQSymbol keyed by the pattern span"
    );
    assert_eq!(
        arms[1].resolved_ctor, None,
        "a wildcard arm has no resolved_ctor"
    );

    // Empty sidecar ⇒ the ctor arm is None (the population gap the backend
    // detects — it is never silently filled by the transport layer).
    let MonoExpr::Match { arms: arms2, .. } =
        MonoExpr::from_expr(&match_expr, &no_pc(), &no_vr(), &no_ar()).expect("concrete")
    else {
        panic!("expected a Match node");
    };
    assert_eq!(
        arms2[0].resolved_ctor, None,
        "an empty sidecar leaves the ctor arm None"
    );
}

// S114 carrier flip (typed-resolution-carrier.md §4): `from_expr` populates the
// NON-OPTIONAL `MonoExpr::Var.resolution` / `MonoExpr::Apply.dispatch` from the
// typed `var_refs`/`apply_refs` sidecars keyed by the referencing node's span.
#[test]
fn var_and_apply_carry_typed_verdicts_from_sidecars_keyed_by_span() {
    use crate::FQSymbol;
    let var_span = Span::new(10, 20);
    let apply_span = Span::new(30, 40);
    let fq_fn = FQSymbol {
        module: ModuleFullPath::from("m"),
        symbol: Symbol::from("f"),
    };
    let fq_dispatch = FQSymbol {
        module: ModuleFullPath::from("m"),
        symbol: Symbol::from("g$Int"),
    };

    // `(f)` — the callee Var carries its Global verdict; the Apply carries the
    // dispatch-leg verdict.
    let callee = typed_var("f", var_span, Type::Fn(vec![], Box::new(Type::Int)));
    let apply = Expr::Apply {
        callee: Box::new(callee),
        args: vec![],
        span: apply_span,
        resolved_call: None,
        inferred_type: int_ty(),
    };
    let mut vr = no_vr();
    vr.insert(var_span, VarRef::Global(fq_fn.clone()));
    let mut ar = no_ar();
    ar.insert(apply_span, ApplyRef::Dispatch(fq_dispatch.clone()));

    let MonoExpr::Apply {
        callee, dispatch, ..
    } = MonoExpr::from_expr(&apply, &no_pc(), &vr, &ar).expect("concrete")
    else {
        panic!("expected an Apply node");
    };
    assert_eq!(
        dispatch,
        ApplyRef::Dispatch(fq_dispatch),
        "Apply carries the dispatch-leg verdict"
    );
    let MonoExpr::Var { resolution, .. } = *callee else {
        panic!("expected a Var callee");
    };
    assert_eq!(
        resolution,
        VarRef::Global(fq_fn),
        "the callee Var carries its Global verdict"
    );
}

// The view-build gate (typed-resolution-carrier.md §3.2): a real-span `Var`
// with no `var_refs` entry is the LOCATED `Unresolved` typecheck-phase error —
// never a silent local, never a codegen-time miss.
#[test]
fn from_expr_real_span_var_miss_errors_unresolved() {
    let var_span = Span::new(7, 13);
    let e = typed_var("mystery", var_span, Type::Int);
    assert_eq!(
        MonoExpr::from_expr(&e, &no_pc(), &no_vr(), &no_ar()).unwrap_err(),
        ViewBuildError::Unresolved {
            span: var_span,
            name: Symbol::from("mystery")
        }
    );
}

// The Apply sibling: a real-span `Apply` with no `apply_refs` entry errors
// `Unresolved` at the APPLY span, naming the callee head.
#[test]
fn from_expr_real_span_apply_miss_errors_unresolved_naming_callee_head() {
    let var_span = Span::new(7, 13);
    let apply_span = Span::new(5, 20);
    let callee = typed_var("f", var_span, Type::Fn(vec![], Box::new(Type::Int)));
    let apply = Expr::Apply {
        callee: Box::new(callee),
        args: vec![],
        span: apply_span,
        resolved_call: None,
        inferred_type: int_ty(),
    };
    // The callee Var HAS a verdict; only the Apply's is missing — isolates the
    // Apply-side gate.
    let mut vr = no_vr();
    vr.insert(
        var_span,
        VarRef::Global(FQSymbol {
            module: ModuleFullPath::from("m"),
            symbol: Symbol::from("f"),
        }),
    );
    assert_eq!(
        MonoExpr::from_expr(&apply, &no_pc(), &vr, &no_ar()).unwrap_err(),
        ViewBuildError::Unresolved {
            span: apply_span,
            name: Symbol::from("f")
        }
    );
}

// Gate precedence: a node that is BOTH unresolved and non-concrete reports
// `Unresolved` — were `NotConcrete` to win, the caller's lenient fallback
// would re-walk the same miss and panic (a seam assert where a located error
// was designed). The verdict is read before the node type.
#[test]
fn unresolved_gate_takes_precedence_over_not_concrete_at_the_same_node() {
    let var_span = Span::new(3, 9);
    let e = typed_var("x", var_span, Type::Var(7));
    assert_eq!(
        MonoExpr::from_expr(&e, &no_pc(), &no_vr(), &no_ar()).unwrap_err(),
        ViewBuildError::Unresolved {
            span: var_span,
            name: Symbol::from("x")
        },
        "resolution gate fires before the concreteness gate"
    );
}

// The SYNTHETIC carve-out (typed-resolution-carrier.md §3.4): synthetic nodes
// are structurally outside span-keyed transport, so a Span::SYNTHETIC miss
// takes the all-local verdict in BOTH walks — Local for a Var, ViaCallee for
// an Apply.
#[test]
fn synthetic_span_miss_takes_all_local_verdict() {
    let syn = Span::SYNTHETIC;
    let callee = typed_var("p", syn, Type::Fn(vec![], Box::new(Type::Int)));
    let apply = Expr::Apply {
        callee: Box::new(callee),
        args: vec![],
        span: syn,
        resolved_call: None,
        inferred_type: int_ty(),
    };
    let MonoExpr::Apply {
        callee, dispatch, ..
    } = MonoExpr::from_expr(&apply, &no_pc(), &no_vr(), &no_ar()).expect("concrete")
    else {
        panic!("expected an Apply node");
    };
    assert_eq!(dispatch, ApplyRef::ViaCallee);
    let MonoExpr::Var { resolution, .. } = *callee else {
        panic!("expected Var callee")
    };
    assert_eq!(
        resolution,
        VarRef::Local {
            binder: Symbol::from("p"),
            binding_span: syn
        }
    );
}

// The lenient walk's tolerance is for TYPES only: a real-span resolution miss
// is an in-process producer bug and fires the always-on tier-3 seam assert
// (safety-invariants.md §2) — never a silently manufactured `Local`.
#[test]
#[should_panic(expected = "no VarRef verdict")]
fn lenient_real_span_var_miss_panics_seam_assert() {
    let e = typed_var("table-ref", Span::new(3, 12), Type::Int);
    let _ = MonoExpr::lenient_from_expr(&e, &no_pc(), &no_vr(), &no_ar());
}

#[test]
#[should_panic(expected = "no ApplyRef verdict")]
fn lenient_real_span_apply_miss_panics_seam_assert() {
    let var_span = Span::new(3, 12);
    let apply = Expr::Apply {
        callee: Box::new(typed_var(
            "f",
            var_span,
            Type::Fn(vec![], Box::new(Type::Int)),
        )),
        args: vec![],
        span: Span::new(1, 20),
        resolved_call: None,
        inferred_type: int_ty(),
    };
    let mut vr = no_vr();
    vr.insert(
        var_span,
        VarRef::Global(FQSymbol {
            module: ModuleFullPath::from("m"),
            symbol: Symbol::from("f"),
        }),
    );
    let _ = MonoExpr::lenient_from_expr(&apply, &no_pc(), &vr, &no_ar());
}

// The lenient walk transports the same typed carriers as the strict walk
// (byte-identical on a fully-concrete, fully-resolved body).
#[test]
fn lenient_carries_typed_verdicts_and_matches_strict() {
    let var_span = Span::new(10, 20);
    let apply_span = Span::new(5, 25);
    let fq_fn = FQSymbol {
        module: ModuleFullPath::from("m"),
        symbol: Symbol::from("f"),
    };
    let apply = Expr::Apply {
        callee: Box::new(typed_var(
            "f",
            var_span,
            Type::Fn(vec![], Box::new(Type::Int)),
        )),
        args: vec![],
        span: apply_span,
        resolved_call: None,
        inferred_type: int_ty(),
    };
    let mut vr = no_vr();
    vr.insert(var_span, VarRef::Global(fq_fn));
    let mut ar = no_ar();
    ar.insert(apply_span, ApplyRef::ViaCallee);

    let strict = MonoExpr::from_expr(&apply, &no_pc(), &vr, &ar).expect("concrete");
    let lenient = MonoExpr::lenient_from_expr(&apply, &no_pc(), &vr, &ar);
    assert_eq!(
        format!("{strict:?}"),
        format!("{lenient:?}"),
        "lenient is byte-identical to strict on a concrete, resolved body"
    );
    let MonoExpr::Apply { dispatch, .. } = lenient else {
        panic!("expected Apply")
    };
    assert_eq!(dispatch, ApplyRef::ViaCallee);
}

// Absence is unrepresentable (no `#[serde(default)]` on the flipped fields): a
// persisted `Var` node missing `resolution` is schema-invalid — deserialization
// FAILS rather than conservatively defaulting (the Option-conflation cannot
// re-enter through the cache).
#[test]
fn var_resolution_field_absence_is_unrepresentable_in_serde() {
    let node = MonoExpr::Var {
        name: Symbol::from("x"),
        span: Span::new(1, 2),
        resolved_call: None,
        resolution: VarRef::Local {
            binder: Symbol::from("x"),
            binding_span: Span::new(0, 5),
        },
        ty: ConcreteType::Int,
    };
    let mut v = serde_json::to_value(&node).expect("serialize");
    // Round-trips intact...
    let back: MonoExpr = serde_json::from_value(v.clone()).expect("round-trip");
    let MonoExpr::Var { resolution, .. } = back else {
        panic!("expected Var")
    };
    assert_eq!(
        resolution,
        VarRef::Local {
            binder: Symbol::from("x"),
            binding_span: Span::new(0, 5)
        }
    );
    // ...and refuses the field's absence.
    v.as_object_mut()
        .unwrap()
        .get_mut("Var")
        .unwrap()
        .as_object_mut()
        .unwrap()
        .remove("resolution");
    assert!(
        serde_json::from_value::<MonoExpr>(v).is_err(),
        "a Var without `resolution` must fail deserialization, not default"
    );
}

// S114 FIXME 0685 (design/arch/typed-resolution-carrier.md §3.4): the sanctioned
// all-local builder for SYNTHETIC synthesis bodies (adt.rs ctor + accessor) —
// the all-local MODE of the ONE shared lenient walk: every Var takes
// `VarRef::Local { binding_span: SYNTHETIC }`, every Apply `ViaCallee`;
// pattern-ctor identities still transported through the `pattern_ctors`
// sidecar keyed by the synthetic pattern span.
#[test]
fn synthetic_local_builder_is_all_local_mode_and_carries_pattern_ctor() {
    use crate::{FQSymbol, Pattern, SymbolRef};
    // Accessor-shaped synthesis body: (match self [(Box v) v]) — every node
    // Span::SYNTHETIC, every inferred_type None (the lenient placeholder path).
    let syn = Span::SYNTHETIC;
    let fq_ctor = FQSymbol {
        module: ModuleFullPath::from("m"),
        symbol: Symbol::from("Box"),
    };
    let body = Expr::Match {
        scrutinee: Box::new(Expr::var(Symbol::from("self$accessor"), syn)),
        arms: vec![MatchArm {
            pattern: Pattern::Constructor {
                name: SymbolRef::new(None, Symbol::from("Box")),
                bindings: vec![Symbol::from("v")],
                span: syn,
            },
            body: Expr::var(Symbol::from("v"), syn),
            span: syn,
        }],
        span: syn,
        compiler_generated: true,
        inferred_type: None,
    };
    let mut pc = no_pc();
    pc.insert(syn, fq_ctor.clone());

    let via_synthetic = MonoExpr::synthetic_local_from_expr(&body, &pc);
    let via_lenient = MonoExpr::lenient_from_expr(&body, &pc, &no_vr(), &no_ar());
    assert_eq!(
        format!("{via_synthetic:?}"),
        format!("{via_lenient:?}"),
        "the all-local builder IS the shared lenient walk over an all-synthetic body"
    );
    let MonoExpr::Match {
        scrutinee, arms, ..
    } = via_synthetic
    else {
        panic!("expected a Match node");
    };
    assert_eq!(
        arms[0].resolved_ctor.as_ref(),
        Some(&fq_ctor),
        "a synthesis-held ctor identity still rides the pattern_ctors sidecar"
    );
    // Every Var in the synthesis body takes the POSITIVE all-local verdict.
    let MonoExpr::Var { resolution, .. } = *scrutinee else {
        panic!("expected Var scrutinee")
    };
    assert_eq!(
        resolution,
        VarRef::Local {
            binder: Symbol::from("self$accessor"),
            binding_span: syn
        }
    );
    let MonoExpr::Var {
        resolution: arm_res,
        ..
    } = &arms[0].body
    else {
        panic!("expected Var arm body")
    };
    assert_eq!(
        *arm_res,
        VarRef::Local {
            binder: Symbol::from("v"),
            binding_span: syn
        }
    );
}

// The license bound, face 1: a real-span VAR reaching the all-local builder is
// refused by the shared walk's seam assert BEFORE the span assert — it can
// never receive a silent local verdict.
#[test]
#[should_panic(expected = "no VarRef verdict")]
fn synthetic_local_builder_rejects_real_span_var_bodies() {
    let real = Expr::var(Symbol::from("table-ref"), Span::new(3, 12));
    let _ = MonoExpr::synthetic_local_from_expr(&real, &no_pc());
}

// The license bound, face 2: a real-span NON-reference node (nothing for the
// walk's verdict rule to refuse) still trips the whole-body synthetic-span
// assert — the license is machine-bounded for every node kind.
#[test]
#[should_panic(expected = "synthetic_local_from_expr")]
fn synthetic_local_builder_rejects_real_span_non_reference_bodies() {
    let real = Expr::IntLit {
        value: 1,
        span: Span::new(3, 12),
        inferred_type: int_ty(),
    };
    let _ = MonoExpr::synthetic_local_from_expr(&real, &no_pc());
}

#[test]
fn concrete_int_lit_round_trips() {
    let e = int_lit(42);
    let m = MonoExpr::from_expr(&e, &no_pc(), &no_vr(), &no_ar()).expect("concrete");
    assert!(matches!(m, MonoExpr::IntLit { value: 42, ref ty, .. } if *ty == ConcreteType::Int));
    assert_eq!(m.ty(), &ConcreteType::Int);
}

#[test]
fn unannotated_node_fails() {
    // inferred_type == None — representation-undetermined.
    let e = Expr::IntLit {
        value: 1,
        span: span(),
        inferred_type: None,
    };
    assert_eq!(
        MonoExpr::from_expr(&e, &no_pc(), &no_vr(), &no_ar()).unwrap_err(),
        ViewBuildError::NotConcrete(NotConcrete::Var(0))
    );
}

#[test]
fn residual_var_node_fails_at_that_node() {
    // A concrete `If` whose then-branch carries a residual `Var` — the failure
    // is reported from that node. (The Var sits at the synthetic span, taking
    // the all-local carve-out, so the RESOLUTION gate passes and the
    // CONCRETENESS gate is what fires — the real-span sibling is
    // `unresolved_gate_takes_precedence_over_not_concrete_at_the_same_node`.)
    let then = typed_var("x", span(), Type::Var(7));
    let e = Expr::If {
        cond: Box::new(Expr::BoolLit {
            value: true,
            span: span(),
            inferred_type: Some(Box::new(Type::Bool)),
        }),
        then_branch: Box::new(then),
        else_branch: Box::new(int_lit(0)),
        span: span(),
        inferred_type: int_ty(),
    };
    assert_eq!(
        MonoExpr::from_expr(&e, &no_pc(), &no_vr(), &no_ar()).unwrap_err(),
        ViewBuildError::NotConcrete(NotConcrete::Var(7))
    );
}

#[test]
fn annotate_is_erased() {
    // (Annotate :Int 5) — the `Annotate` collapses to its inner IntLit.
    let inner = int_lit(5);
    let e = Expr::Annotate {
        annotation: TypeExpr::Named(TypeRef::new(None, TypeName::from("Int"))),
        expr: Box::new(inner),
        span: span(),
        inferred_type: int_ty(),
    };
    let m = MonoExpr::from_expr(&e, &no_pc(), &no_vr(), &no_ar()).expect("concrete");
    // The result is the inner IntLit, NOT a wrapper node.
    assert!(matches!(m, MonoExpr::IntLit { value: 5, .. }));
}

#[test]
fn nested_annotate_erases_to_inner() {
    // (Annotate :Int (Annotate :Int 9)) erases both layers.
    let core = int_lit(9);
    let one = Expr::Annotate {
        annotation: TypeExpr::Named(TypeRef::new(None, TypeName::from("Int"))),
        expr: Box::new(core),
        span: span(),
        inferred_type: int_ty(),
    };
    let two = Expr::Annotate {
        annotation: TypeExpr::Named(TypeRef::new(None, TypeName::from("Int"))),
        expr: Box::new(one),
        span: span(),
        inferred_type: int_ty(),
    };
    let m = MonoExpr::from_expr(&two, &no_pc(), &no_vr(), &no_ar()).expect("concrete");
    assert!(matches!(m, MonoExpr::IntLit { value: 9, .. }));
}

#[test]
fn lambda_param_type_exprs_are_erased() {
    // (fn [:Int x] x) — the param `:Int` TypeExpr is erased; only the name
    // survives. The lambda's `ty` carries the concrete Fn type.
    let body = typed_var("x", span(), Type::Int);
    let lam_ty = Type::Fn(vec![Type::Int], Box::new(Type::Int));
    let e = Expr::Lambda {
        params: vec![(
            Symbol::from("x"),
            Some(TypeExpr::Named(TypeRef::new(None, TypeName::from("Int")))),
        )],
        body: Box::new(body),
        span: span(),
        inferred_type: Some(Box::new(lam_ty)),
    };
    let m = MonoExpr::from_expr(&e, &no_pc(), &no_vr(), &no_ar()).expect("concrete");
    match m {
        MonoExpr::Lambda { params, ty, .. } => {
            assert_eq!(params, vec![Symbol::from("x")]);
            assert_eq!(
                ty,
                ConcreteType::Fn(vec![ConcreteType::Int], Box::new(ConcreteType::Int))
            );
        }
        _ => panic!("expected Lambda, got {m:?}"),
    }
}

#[test]
fn apply_carries_resolved_call_and_concrete_args() {
    // (f 1) where f : Int -> Int and the call carries a BuiltinFn resolution.
    // Both nodes sit at the synthetic span (all-local carve-out) — the Apply's
    // `dispatch` takes the ViaCallee verdict; `resolved_call` rides verbatim.
    let callee = typed_var("f", span(), Type::Fn(vec![Type::Int], Box::new(Type::Int)));
    let rc = ResolvedCall::BuiltinFn {
        name: Symbol::from("add-i64"),
    };
    let e = Expr::Apply {
        callee: Box::new(callee),
        args: vec![int_lit(1)],
        span: span(),
        resolved_call: Some(Box::new(rc)),
        inferred_type: int_ty(),
    };
    let m = MonoExpr::from_expr(&e, &no_pc(), &no_vr(), &no_ar()).expect("concrete");
    match m {
        MonoExpr::Apply {
            resolved_call,
            dispatch,
            args,
            ty,
            ..
        } => {
            assert!(resolved_call.is_some());
            assert_eq!(dispatch, ApplyRef::ViaCallee);
            assert_eq!(args.len(), 1);
            assert_eq!(ty, ConcreteType::Int);
        }
        _ => panic!("expected Apply, got {m:?}"),
    }
}

#[test]
fn concrete_adt_node_round_trips() {
    // (Some 1) : (Option Int) — a fully-concrete ConstrADT.
    let opt_int = Type::adt(
        ModuleFullPath::from("primitives"),
        TypeName::from("Option"),
        vec![Type::Int],
    );
    let e = Expr::ConstrADT {
        type_name: FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Option")),
        tag: 1,
        fields: vec![int_lit(1)],
        span: span(),
        inferred_type: Some(Box::new(opt_int)),
    };
    let m = MonoExpr::from_expr(&e, &no_pc(), &no_vr(), &no_ar()).expect("concrete");
    match m {
        MonoExpr::ConstrADT {
            tag, fields, ty, ..
        } => {
            assert_eq!(tag, 1);
            assert_eq!(fields.len(), 1);
            assert!(matches!(ty, ConcreteType::ADT(_, ref a) if a == &vec![ConcreteType::Int]));
        }
        _ => panic!("expected ConstrADT, got {m:?}"),
    }
}

#[test]
fn match_arm_pattern_survives_body_converts() {
    // (match s ((Some x) 1) (_ 0)) — patterns reused verbatim, bodies convert.
    let e = Expr::Match {
        scrutinee: Box::new(Expr::var(Symbol::from("s"), span())),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard { span: span() },
            body: int_lit(0),
            span: span(),
        }],
        span: span(),
        compiler_generated: false,
        inferred_type: int_ty(),
    };
    // scrutinee must be concretely typed.
    let e = match e {
        Expr::Match {
            mut scrutinee,
            arms,
            span,
            compiler_generated,
            inferred_type,
        } => {
            scrutinee.set_inferred_type(Some(Box::new(Type::Bool)));
            Expr::Match {
                scrutinee,
                arms,
                span,
                compiler_generated,
                inferred_type,
            }
        }
        _ => unreachable!(),
    };
    let m = MonoExpr::from_expr(&e, &no_pc(), &no_vr(), &no_ar()).expect("concrete");
    match m {
        MonoExpr::Match { arms, ty, .. } => {
            assert_eq!(arms.len(), 1);
            assert!(matches!(arms[0].pattern, Pattern::Wildcard { .. }));
            assert_eq!(ty, ConcreteType::Int);
        }
        _ => panic!("expected Match, got {m:?}"),
    }
}

#[test]
fn deeply_nested_var_in_let_binding_is_caught() {
    // (let [y <var>] 0) — the binding value carries a residual Var (at the
    // synthetic span, so the concreteness gate is the one under test).
    let bad = typed_var("z", span(), Type::Var(3));
    let e = Expr::Let {
        bindings: vec![(Symbol::from("y"), bad)],
        body: Box::new(int_lit(0)),
        span: span(),
        inferred_type: int_ty(),
    };
    assert_eq!(
        MonoExpr::from_expr(&e, &no_pc(), &no_vr(), &no_ar()).unwrap_err(),
        ViewBuildError::NotConcrete(NotConcrete::Var(3))
    );
}

// --- FIXME-0689 fence: `is_strict_type_concrete`, the single-sourced pure-TYPE
// half of the `from_expr` gate, consumed by the ownership fixpoint's W0.b
// universe pin (`cranelisp-typecheck::ownership::fixpoint::collect_universe`).
// The three universe populations are pinned at the representative-body level —
// the exact body shapes typecheck synthesizes/produces per population
// (`backend-keyed-consumer.md` §4 W0.b: ctor/accessor/lenient-fallback
// excluded; mono instances + genuine concrete defns retained) — plus the
// Annotate-erasure rule and the equivalence contract with `from_expr` under
// total resolution maps (here: all-synthetic-span bodies, whose all-local
// carve-out makes the empty maps total).

#[test]
fn strict_type_concrete_retains_genuine_concrete_and_mono_bodies() {
    // Retained populations: a fully-typed body — the genuine-concrete-defn and
    // mono-instance shapes (both are fully-annotated bodies at pin time).
    let body = Expr::Let {
        bindings: vec![(Symbol::from("x"), int_lit(1))],
        body: Box::new(Expr::Apply {
            callee: Box::new(typed_var(
                "f",
                span(),
                Type::Fn(vec![Type::Int], Box::new(Type::Int)),
            )),
            args: vec![typed_var("x", span(), Type::Int)],
            span: span(),
            resolved_call: None,
            inferred_type: int_ty(),
        }),
        span: span(),
        inferred_type: int_ty(),
    };
    assert!(is_strict_type_concrete(&body));
    // Equivalence contract: strict build succeeds exactly where the predicate
    // holds (total-maps precondition met via the synthetic-span carve-out).
    assert!(MonoExpr::from_expr(&body, &no_pc(), &no_vr(), &no_ar()).is_ok());
}

#[test]
fn strict_type_concrete_excludes_ctor_synthesis_bodies() {
    // Excluded population 1 (ctors): adt.rs synthesizes `ConstrADT` bodies
    // with NO `inferred_type` — they must stay out of the ownership universe.
    let body = Expr::ConstrADT {
        type_name: FQTypeName::new(ModuleFullPath::from("m"), TypeName::from("Maybe")),
        tag: 0,
        fields: vec![],
        span: span(),
        inferred_type: None,
    };
    assert!(!is_strict_type_concrete(&body));
    // Equivalence: `from_expr` refuses the same body (NotConcrete).
    assert!(matches!(
        MonoExpr::from_expr(&body, &no_pc(), &no_vr(), &no_ar()),
        Err(ViewBuildError::NotConcrete(_))
    ));
}

#[test]
fn strict_type_concrete_excludes_accessor_synthesis_bodies() {
    // Excluded population 2 (accessors): the `(match self …)` synthesis body
    // with un-typed nodes.
    let body = Expr::Match {
        scrutinee: Box::new(Expr::Var {
            name: Symbol::from("self"),
            span: span(),
            resolved_call: None,
            inferred_type: None,
        }),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard { span: span() },
            body: int_lit(0),
            span: span(),
        }],
        span: span(),
        compiler_generated: true,
        inferred_type: None,
    };
    assert!(!is_strict_type_concrete(&body));
    assert!(matches!(
        MonoExpr::from_expr(&body, &no_pc(), &no_vr(), &no_ar()),
        Err(ViewBuildError::NotConcrete(_))
    ));
}

#[test]
fn strict_type_concrete_excludes_lenient_fallback_bodies() {
    // Excluded population 3 (lenient-fallback concrete defns): a genuine
    // `Type::Var` residual deep in an otherwise-typed body (the `f$Var`
    // multi-sig-variant shape) — `from_expr` fails it, the lenient walk
    // carries it, and the universe pin must exclude it.
    let body = Expr::If {
        cond: Box::new(Expr::BoolLit {
            value: true,
            span: span(),
            inferred_type: Some(Box::new(Type::Bool)),
        }),
        then_branch: Box::new(typed_var("x", span(), Type::Var(9))),
        else_branch: Box::new(int_lit(0)),
        span: span(),
        inferred_type: int_ty(),
    };
    assert!(!is_strict_type_concrete(&body));
    assert!(matches!(
        MonoExpr::from_expr(&body, &no_pc(), &no_vr(), &no_ar()),
        Err(ViewBuildError::NotConcrete(_))
    ));
}

#[test]
fn strict_type_concrete_erases_annotate_like_from_expr() {
    // The `Annotate` node's own (here: absent) type is never examined — the
    // predicate erases it to the inner node, exactly the `from_expr` arm.
    let e = Expr::Annotate {
        annotation: TypeExpr::Named(TypeRef::new(None, TypeName::from("Int"))),
        expr: Box::new(int_lit(5)),
        span: span(),
        inferred_type: None,
    };
    assert!(is_strict_type_concrete(&e));
    assert!(MonoExpr::from_expr(&e, &no_pc(), &no_vr(), &no_ar()).is_ok());
}
