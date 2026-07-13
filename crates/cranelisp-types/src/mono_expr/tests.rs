use super::*;
use crate::{MatchArm, ModuleFullPath, Type, TypeExpr, TypeName, TypeRef};

fn span() -> Span {
    Span::new(0, 0)
}

fn int_ty() -> Option<Box<Type>> {
    Some(Box::new(Type::Int))
}

fn int_lit(v: i64) -> Expr {
    Expr::IntLit { value: v, span: span(), inferred_type: int_ty() }
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
    let scrut = Expr::Var {
        name: Symbol::from("s"),
        span: span(),
        resolved_call: None,
        inferred_type: Some(Box::new(Type::ADT(
            FQTypeName::new(ModuleFullPath::from("m"), TypeName::from("Maybe")),
            vec![],
        ))),
    };
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
                pattern: Pattern::Wildcard { span: Span::new(40, 41) },
                body: int_lit(0),
                span: Span::new(50, 60),
            },
        ],
        span: span(),
        compiler_generated: false,
        inferred_type: int_ty(),
    };
    let mut pc = std::collections::HashMap::new();
    pc.insert(pat_span, fq.clone());

    let MonoExpr::Match { arms, .. } =
        MonoExpr::from_expr(&match_expr, &pc).expect("concrete")
    else {
        panic!("expected a Match node");
    };
    assert_eq!(
        arms[0].resolved_ctor.as_ref(),
        Some(&fq),
        "the ctor arm carries the sidecar FQSymbol keyed by the pattern span"
    );
    assert_eq!(arms[1].resolved_ctor, None, "a wildcard arm has no resolved_ctor");

    // Empty sidecar ⇒ the ctor arm is None (the population gap the backend
    // detects — it is never silently filled by the transport layer).
    let MonoExpr::Match { arms: arms2, .. } =
        MonoExpr::from_expr(&match_expr, &std::collections::HashMap::new()).expect("concrete")
    else {
        panic!("expected a Match node");
    };
    assert_eq!(arms2[0].resolved_ctor, None, "an empty sidecar leaves the ctor arm None");
}

#[test]
fn concrete_int_lit_round_trips() {
    let e = int_lit(42);
    let m = MonoExpr::from_expr(&e, &std::collections::HashMap::new()).expect("concrete");
    assert!(matches!(m, MonoExpr::IntLit { value: 42, ref ty, .. } if *ty == ConcreteType::Int));
    assert_eq!(m.ty(), &ConcreteType::Int);
}

#[test]
fn unannotated_node_fails() {
    // inferred_type == None — representation-undetermined.
    let e = Expr::IntLit { value: 1, span: span(), inferred_type: None };
    assert_eq!(MonoExpr::from_expr(&e, &std::collections::HashMap::new()).unwrap_err(), NotConcrete::Var(0));
}

#[test]
fn residual_var_node_fails_at_that_node() {
    // A concrete `If` whose then-branch carries a residual `Var` — the failure
    // is reported from that node.
    let then = Expr::Var {
        name: Symbol::from("x"),
        span: span(),
        resolved_call: None,
        inferred_type: Some(Box::new(Type::Var(7))),
    };
    let e = Expr::If {
        cond: Box::new(Expr::BoolLit { value: true, span: span(), inferred_type: Some(Box::new(Type::Bool)) }),
        then_branch: Box::new(then),
        else_branch: Box::new(int_lit(0)),
        span: span(),
        inferred_type: int_ty(),
    };
    assert_eq!(MonoExpr::from_expr(&e, &std::collections::HashMap::new()).unwrap_err(), NotConcrete::Var(7));
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
    let m = MonoExpr::from_expr(&e, &std::collections::HashMap::new()).expect("concrete");
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
    let m = MonoExpr::from_expr(&two, &std::collections::HashMap::new()).expect("concrete");
    assert!(matches!(m, MonoExpr::IntLit { value: 9, .. }));
}

#[test]
fn lambda_param_type_exprs_are_erased() {
    // (fn [:Int x] x) — the param `:Int` TypeExpr is erased; only the name
    // survives. The lambda's `ty` carries the concrete Fn type.
    let body = Expr::var(Symbol::from("x"), span());
    // body must carry a concrete inferred_type for from_expr to succeed.
    let body = match body {
        Expr::Var { name, span, resolved_call, .. } => {
            Expr::Var { name, span, resolved_call, inferred_type: int_ty() }
        }
        _ => unreachable!(),
    };
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
    let m = MonoExpr::from_expr(&e, &std::collections::HashMap::new()).expect("concrete");
    match m {
        MonoExpr::Lambda { params, ty, .. } => {
            assert_eq!(params, vec![Symbol::from("x")]);
            assert_eq!(ty, ConcreteType::Fn(vec![ConcreteType::Int], Box::new(ConcreteType::Int)));
        }
        _ => panic!("expected Lambda, got {m:?}"),
    }
}

#[test]
fn apply_carries_resolved_call_and_concrete_args() {
    // (f 1) where f : Int -> Int and the call carries a SigDispatch resolution.
    let callee = Expr::Var {
        name: Symbol::from("f"),
        span: span(),
        resolved_call: None,
        inferred_type: Some(Box::new(Type::Fn(vec![Type::Int], Box::new(Type::Int)))),
    };
    let rc = ResolvedCall::BuiltinFn { name: Symbol::from("add-i64") };
    let e = Expr::Apply {
        callee: Box::new(callee),
        args: vec![int_lit(1)],
        span: span(),
        resolved_call: Some(Box::new(rc)),
        inferred_type: int_ty(),
    };
    let m = MonoExpr::from_expr(&e, &std::collections::HashMap::new()).expect("concrete");
    match m {
        MonoExpr::Apply { resolved_call, args, ty, .. } => {
            assert!(resolved_call.is_some());
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
    let m = MonoExpr::from_expr(&e, &std::collections::HashMap::new()).expect("concrete");
    match m {
        MonoExpr::ConstrADT { tag, fields, ty, .. } => {
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
        arms: vec![
            MatchArm {
                pattern: Pattern::Wildcard { span: span() },
                body: int_lit(0),
                span: span(),
            },
        ],
        span: span(),
        compiler_generated: false,
        inferred_type: int_ty(),
    };
    // scrutinee must be concretely typed.
    let e = match e {
        Expr::Match { mut scrutinee, arms, span, compiler_generated, inferred_type } => {
            scrutinee.set_inferred_type(Some(Box::new(Type::Bool)));
            Expr::Match { scrutinee, arms, span, compiler_generated, inferred_type }
        }
        _ => unreachable!(),
    };
    let m = MonoExpr::from_expr(&e, &std::collections::HashMap::new()).expect("concrete");
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
    // (let [y <var>] 0) — the binding value carries a residual Var.
    let bad = Expr::Var {
        name: Symbol::from("z"),
        span: span(),
        resolved_call: None,
        inferred_type: Some(Box::new(Type::Var(3))),
    };
    let e = Expr::Let {
        bindings: vec![(Symbol::from("y"), bad)],
        body: Box::new(int_lit(0)),
        span: span(),
        inferred_type: int_ty(),
    };
    assert_eq!(MonoExpr::from_expr(&e, &std::collections::HashMap::new()).unwrap_err(), NotConcrete::Var(3));
}
