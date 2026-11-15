//! The ownership plan's decisions and the linearity check's detection proof
//! (`design/backend/uniform-counting.md` §2, §3; S123 evidence U-6).

use cranelisp_types::{
    ApplyRef, ConcreteType, FQSymbol, ModuleFullPath, MonoExpr, MonoMatchArm, Pattern, Span,
    Symbol, SymbolRef, VarRef,
};

use super::{BinderId, Intro, Occurrence, OwnershipPlan, Use, node_key};

fn sym(name: &str) -> Symbol {
    Symbol::from(name)
}

fn vec_ty() -> ConcreteType {
    ConcreteType::ADT(
        cranelisp_types::FQTypeName::new(
            ModuleFullPath::from("primitives"),
            cranelisp_types::TypeName::from("Vec"),
        ),
        vec![ConcreteType::Int],
    )
}

fn local(name: &str) -> MonoExpr {
    MonoExpr::Var {
        name: sym(name),
        span: Span::SYNTHETIC,
        resolved_call: None,
        resolution: VarRef::Local {
            binder: sym(name),
            binding_span: Span::SYNTHETIC,
        },
        ty: vec_ty(),
    }
}

fn global(name: &str) -> MonoExpr {
    MonoExpr::Var {
        name: sym(name),
        span: Span::SYNTHETIC,
        resolved_call: None,
        resolution: VarRef::Global(FQSymbol {
            module: ModuleFullPath::from("user"),
            symbol: sym(name),
        }),
        ty: ConcreteType::Int,
    }
}

/// `(f args…)` for a table function `f`.
fn call(f: &str, args: Vec<MonoExpr>) -> MonoExpr {
    MonoExpr::Apply {
        callee: Box::new(global(f)),
        args,
        span: Span::SYNTHETIC,
        resolved_call: None,
        dispatch: ApplyRef::ViaCallee,
        ty: vec_ty(),
        escapes: None,
        confined: None,
        unique_static: None,
        provenance: None,
    }
}

fn if_(cond: MonoExpr, then_branch: MonoExpr, else_branch: MonoExpr) -> MonoExpr {
    MonoExpr::If {
        cond: Box::new(cond),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
        span: Span::SYNTHETIC,
        ty: vec_ty(),
    }
}

fn let_(bindings: Vec<(&str, MonoExpr)>, body: MonoExpr) -> MonoExpr {
    MonoExpr::Let {
        bindings: bindings
            .into_iter()
            .map(|(name, init)| (sym(name), init))
            .collect(),
        body: Box::new(body),
        span: Span::SYNTHETIC,
        ty: vec_ty(),
    }
}

fn lambda(params: &[&str], body: MonoExpr) -> MonoExpr {
    MonoExpr::Lambda {
        params: params.iter().map(|p| sym(p)).collect(),
        body: Box::new(body),
        span: Span::SYNTHETIC,
        ty: ConcreteType::Fn(vec![], Box::new(vec_ty())),
        escapes: None,
        confined: None,
        unique_static: None,
    }
}

fn ctor_arm(ctor: &str, bindings: &[&str], body: MonoExpr) -> MonoMatchArm {
    MonoMatchArm {
        pattern: Pattern::Constructor {
            name: SymbolRef::new(None, sym(ctor)),
            bindings: bindings.iter().map(|b| sym(b)).collect(),
            span: Span::SYNTHETIC,
        },
        body,
        span: Span::SYNTHETIC,
        provenance: None,
        resolved_ctor: None,
    }
}

fn match_(scrutinee: MonoExpr, arms: Vec<MonoMatchArm>) -> MonoExpr {
    MonoExpr::Match {
        scrutinee: Box::new(scrutinee),
        arms,
        span: Span::SYNTHETIC,
        compiler_generated: false,
        ty: vec_ty(),
    }
}

fn args(node: &MonoExpr) -> &[MonoExpr] {
    match node {
        MonoExpr::Apply { args, .. } => args,
        _ => panic!("not an application"),
    }
}

fn plan(body: &MonoExpr, params: &[&str]) -> OwnershipPlan {
    let params: Vec<Symbol> = params.iter().map(|p| sym(p)).collect();
    OwnershipPlan::build(body, &params, &[], false)
}

fn param(plan: &OwnershipPlan, i: usize) -> BinderId {
    plan.binder_at(Intro::Param(i)).expect("param planned")
}

fn owned(binder: BinderId, use_: Use) -> Option<Occurrence> {
    Some(Occurrence::Owned { binder, use_ })
}

fn check(plan: &OwnershipPlan, body: &MonoExpr, params: usize) -> Result<(), String> {
    plan.check_linearity(body, params).map_err(|v| v.0)
}

// spec: design/backend/uniform-counting.md §1 — the last use moves; every
// earlier use, in evaluation order, duplicates.
#[test]
fn the_last_use_moves_and_an_earlier_use_duplicates() {
    let body = call("f", vec![local("v"), local("v")]);
    let p = plan(&body, &["v"]);
    let v = param(&p, 0);
    assert_eq!(p.occurrence(&args(&body)[0]), owned(v, Use::Duplicate));
    assert_eq!(p.occurrence(&args(&body)[1]), owned(v, Use::Move));
    assert!(!p.dead_at_intro(v));
}

// spec: design/backend/uniform-counting.md §1 — a binder with no use is dead at
// its introduction; a binder used on one branch only is dropped on entry to the
// other.
#[test]
fn unused_binders_die_at_introduction_and_at_branch_entry() {
    let body = if_(local("c"), local("v"), local("w"));
    let p = plan(&body, &["c", "v", "w", "unused"]);
    let (v, w) = (param(&p, 1), param(&p, 2));
    let key = node_key(&body);
    assert_eq!(p.entry_drops(key, 0), &[w], "the then-branch drops w");
    assert_eq!(p.entry_drops(key, 1), &[v], "the else-branch drops v");
    assert!(p.dead_at_intro(param(&p, 3)));
    for i in 0..3 {
        assert!(!p.dead_at_intro(param(&p, i)), "param {i} is used");
    }
}

// spec: design/backend/uniform-counting.md §3 — binder identity is resolved
// once by the plan, so a shadowing `let` binder is a second binder with its own
// obligation, and its initializer sees the preceding one.
#[test]
fn a_shadowing_binder_is_a_distinct_binder() {
    let init = call("g", vec![local("v")]);
    let body = let_(vec![("v", init)], local("v"));
    let p = plan(&body, &["v"]);
    let outer = param(&p, 0);
    let inner = p
        .binder_at(Intro::Let {
            node: node_key(&body),
            index: 0,
        })
        .expect("let binder planned");
    assert_ne!(outer, inner);
    let MonoExpr::Let {
        bindings,
        body: let_body,
        ..
    } = &body
    else {
        unreachable!()
    };
    assert_eq!(
        p.occurrence(&args(&bindings[0].1)[0]),
        owned(outer, Use::Move)
    );
    assert_eq!(p.occurrence(let_body), owned(inner, Use::Move));
}

// spec: design/backend/uniform-counting.md §4 — a constructor arm owns only
// the fields it binds and uses; an unused field binder is dead at entry.
#[test]
fn an_unused_pattern_field_is_dead_at_its_introduction() {
    let body = match_(local("s"), vec![ctor_arm("Pair", &["a", "b"], local("a"))]);
    let p = plan(&body, &["s"]);
    let key = node_key(&body);
    let slot = |slot| {
        p.binder_at(Intro::Arm {
            node: key,
            arm: 0,
            slot,
        })
        .expect("field planned")
    };
    assert!(!p.dead_at_intro(slot(0)));
    assert!(p.dead_at_intro(slot(1)));
}

// spec: design/backend/uniform-counting.md §3 — a closure creation is one
// capture occurrence per captured binder, classified like any other use.
#[test]
fn a_capture_at_its_last_use_moves_into_the_closure() {
    let closure = lambda(&["x"], call("f", vec![local("v"), local("x")]));
    let body = call("h", vec![local("v"), closure]);
    let p = plan(&body, &["v"]);
    let v = param(&p, 0);
    assert_eq!(p.occurrence(&args(&body)[0]), owned(v, Use::Duplicate));
    let captures = p.captures(&args(&body)[1]).expect("captures planned");
    assert_eq!(captures.len(), 1, "only v is free in the lambda body");
    assert_eq!(
        captures[0].occurrence,
        Occurrence::Owned {
            binder: v,
            use_: Use::Move
        }
    );
}

// spec: design/backend/uniform-counting.md §3 — a capture of the planned body
// is its environment's: every use duplicates and nothing drops it.
#[test]
fn a_capture_of_the_body_always_duplicates() {
    let body = call("f", vec![local("k")]);
    let p = OwnershipPlan::build(&body, &[], &[sym("k")], false);
    assert_eq!(p.occurrence(&args(&body)[0]), Some(Occurrence::Capture));
    assert!(check(&p, &body, 0).is_ok());
}

// spec: design/backend/uniform-counting.md §2 — moves off is U1's uniform
// reference: every use duplicates, and the binder is dropped once the
// consuming position has run.
#[test]
fn moves_off_duplicates_every_use_and_drops_after_the_consumer() {
    let body = call("f", vec![local("v"), local("v")]);
    let p = OwnershipPlan::build(&body, &[sym("v")], &[], true);
    let v = param(&p, 0);
    for arg in args(&body) {
        assert_eq!(p.occurrence(arg), owned(v, Use::Duplicate));
    }
    assert_eq!(p.post_drops(&body), &[v], "dropped after the call");
    assert!(check(&p, &body, 1).is_ok());
}

// spec: design/backend/uniform-counting.md §3 — a lenient spark's frame drops
// what the sequential subtree would have consumed, and nothing it introduced.
#[test]
fn consumed_within_names_the_outer_binders_a_subtree_consumes() {
    let inner = let_(vec![("t", call("g", vec![local("v")]))], local("t"));
    let body = call("f", vec![local("w"), inner]);
    let p = plan(&body, &["v", "w"]);
    assert_eq!(p.consumed_within(&args(&body)[1]), vec![param(&p, 0)]);
    assert_eq!(p.consumed_within(&args(&body)[0]), vec![param(&p, 1)]);
}

/// A body exercising duplicates, moves, branch-entry drops, introduction
/// drops, a match and a capture.
fn varied_body() -> MonoExpr {
    let then_branch = let_(
        vec![
            ("dead", call("mk", vec![])),
            ("t", call("f", vec![local("v"), local("v")])),
        ],
        match_(local("t"), vec![ctor_arm("Pair", &["a", "b"], local("a"))]),
    );
    let else_branch = call("h", vec![lambda(&[], local("w"))]);
    if_(local("c"), then_branch, else_branch)
}

// spec: design/backend/uniform-counting.md §2 — U-6: the linearity check is
// silent on an unplanted plan, in both polarities.
#[test]
fn linearity_check_is_silent_on_unplanted_plans() {
    let body = varied_body();
    for moves_off in [false, true] {
        let params = [sym("c"), sym("v"), sym("w")];
        let p = OwnershipPlan::build(&body, &params, &[], moves_off);
        assert_eq!(check(&p, &body, 3), Ok(()), "moves_off = {moves_off}");
    }
}

// spec: design/backend/uniform-counting.md §2 — U-6 detection proof: a
// planted missing drop fires.
#[test]
fn linearity_check_detects_a_planted_missing_drop() {
    let body = varied_body();
    let mut p = plan(&body, &["c", "v", "w"]);
    assert!(p.plant_missing_drop(), "the body has a drop to remove");
    let err = check(&p, &body, 3).expect_err("a missing drop must fire");
    assert!(
        err.contains("disagree") || err.contains("still held"),
        "unexpected violation: {err}"
    );
}

// spec: design/backend/uniform-counting.md §2 — U-6 detection proof: a
// planted extra move fires (a use after the reference has gone).
#[test]
fn linearity_check_detects_a_planted_extra_move() {
    let body = varied_body();
    let mut p = plan(&body, &["c", "v", "w"]);
    assert!(p.plant_extra_move(), "the body has a duplicate to turn");
    let err = check(&p, &body, 3).expect_err("an extra move must fire");
    assert!(
        err.contains("holds no reference"),
        "unexpected violation: {err}"
    );
}

// spec: design/backend/uniform-counting.md §2 — the missing-drop plant also
// fires when the only drop is a binder's death at its introduction.
#[test]
fn linearity_check_detects_a_missing_introduction_drop() {
    let body = call("f", vec![]);
    let mut p = plan(&body, &["unused"]);
    assert!(p.dead_at_intro(param(&p, 0)));
    assert!(p.plant_missing_drop());
    let err = check(&p, &body, 1).expect_err("the parameter is never consumed");
    assert!(err.contains("still held"), "unexpected violation: {err}");
}

// spec: design/backend/uniform-counting.md §3.2 — the one operand-order
// definition: an evaluated callee precedes the arguments, which run left to
// right; an unevaluated callee is no operand; a continuation's capture point
// follows its node's operand expressions; branching and binding nodes are
// outside the sequence.
#[test]
fn the_operand_sequence_is_callee_then_operands_left_to_right() {
    let body = call("f", vec![local("a"), local("b")]);
    let keys = |sequence: &super::OperandSequence<'_>| -> Vec<usize> {
        sequence.in_order().map(|(_, e)| node_key(e)).collect()
    };
    let MonoExpr::Apply { callee, args, .. } = &body else {
        unreachable!()
    };
    let evaluated = super::operand_sequence(&body, true).expect("an application");
    assert_eq!(
        keys(&evaluated),
        vec![node_key(callee), node_key(&args[0]), node_key(&args[1])]
    );
    assert!(!evaluated.continuation);
    let table = super::operand_sequence(&body, false).expect("an application");
    assert_eq!(keys(&table), vec![node_key(&args[0]), node_key(&args[1])]);

    let par = MonoExpr::ParBind {
        bindings: vec![(sym("x"), local("a")), (sym("y"), local("b"))],
        body: Box::new(local("x")),
        span: Span::SYNTHETIC,
        ty: vec_ty(),
    };
    let MonoExpr::ParBind { bindings, .. } = &par else {
        unreachable!()
    };
    let sequence = super::operand_sequence(&par, false).expect("a par-bind");
    assert_eq!(
        keys(&sequence),
        vec![node_key(&bindings[0].1), node_key(&bindings[1].1)]
    );
    assert!(
        sequence.continuation,
        "the continuation's captures come last"
    );

    for outside in [
        if_(local("c"), local("a"), local("b")),
        let_(vec![("a", local("b"))], local("a")),
        lambda(&[], local("a")),
    ] {
        assert!(super::operand_sequence(&outside, false).is_none());
    }
}
