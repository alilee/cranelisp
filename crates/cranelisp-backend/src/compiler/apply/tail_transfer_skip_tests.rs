//! F1 (Wave 11 B3.1a-R) — the TCO-flush skip-predicate seam.
//!
//! `tail_transfer_skip` must exclude from the tail-jump flush ONLY the bindings
//! that MOVE into a tail argument as a bare top-level `Var` (no consuming inc).
//! A binding aliased into a tail argument *through a control-flow form* (`if` /
//! `match`) must NOT be in the skip set — those are protected by an explicit
//! per-branch inc (`maybe_protect_tail_arg_alias`) and flushed uniformly.
//! Skipping them here was the use-after-free: the flush kept them un-dec'd only
//! for the literal-`Var` case, so the control-flow-aliased binding was freed
//! while the next iteration still owned it.

use super::tail_transfer_skip;
use cranelisp_types::{ConcreteType, MonoExpr, Span, Symbol};

// `tail_transfer_skip` matches only on `Var`-ness, so the node type is
// irrelevant to the skip decision — use a scalar for construction simplicity.
fn var(name: &str) -> MonoExpr {
    MonoExpr::Var {
        resolution: cranelisp_types::VarRef::Local { binder: Symbol::from(name), binding_span: Span::SYNTHETIC },
        name: Symbol::from(name),
        span: Span::SYNTHETIC,
        resolved_call: None,
        ty: ConcreteType::Int,
    }
}

fn if_(cond: MonoExpr, then_b: MonoExpr, else_b: MonoExpr) -> MonoExpr {
    MonoExpr::If {
        cond: Box::new(cond),
        then_branch: Box::new(then_b),
        else_branch: Box::new(else_b),
        span: Span::SYNTHETIC,
        ty: ConcreteType::Int,
    }
}

// spec: spec/12-runtime.md §12.3.1 — a bare top-level `Var` tail argument MOVES
// its single reference into the loop param (no inc), so the flush MUST skip it.
#[test]
fn bare_var_top_level_arg_is_skipped() {
    let skip = tail_transfer_skip(&[var("v")]);
    assert!(
        skip.contains(&Symbol::from("v")),
        "a bare top-level Var tail arg moves and must be excluded from the flush"
    );
}

// spec: spec/12-runtime.md §12.3.1 — a binding aliased into a tail arg through
// `if` reaches the arg value with NO owning inc; it is NOT a move and MUST be
// flushed (then balanced by the branch-tail protective inc). This is the F1 UAF:
// on HEAD such a binding was silently retained-then-freed.
#[test]
fn control_flow_aliased_binding_is_not_skipped() {
    // `(recur (if c a a))` — `a` is aliased via `if`, never a top-level Var.
    let arg = if_(var("c"), var("a"), var("a"));
    let skip = tail_transfer_skip(&[arg]);
    assert!(
        !skip.contains(&Symbol::from("a")),
        "a control-flow-aliased binding must NOT be in transfer_skip — the flush \
         must dec it (balanced by the protective inc); skipping it is the UAF"
    );
}

// spec: spec/12-runtime.md §12.3.1 — distinct per-branch bindings: neither is a
// top-level move, so both are flushed; whichever branch runs, its binding is
// protected+moved and the dead one is freed. A single static skip could not do
// "skip lo XOR skip hi".
#[test]
fn distinct_branch_bindings_are_both_flushed() {
    let arg = if_(var("c"), var("lo"), var("hi"));
    let skip = tail_transfer_skip(&[arg]);
    assert!(!skip.contains(&Symbol::from("lo")));
    assert!(!skip.contains(&Symbol::from("hi")));
}

// spec: spec/12-runtime.md §12.3.1 — a binding that appears BOTH as a bare
// top-level move (`arg0 = v`) and inside a control-flow arg is skipped (the move
// governs) so the flush leaves it; the control-flow arg's protective inc adds
// the second owner. Mixed positions net correctly.
#[test]
fn binding_moved_at_top_level_and_aliased_elsewhere_is_skipped() {
    let skip = tail_transfer_skip(&[var("v"), if_(var("c"), var("v"), var("v"))]);
    assert!(
        skip.contains(&Symbol::from("v")),
        "the top-level move of `v` governs the skip decision"
    );
}
