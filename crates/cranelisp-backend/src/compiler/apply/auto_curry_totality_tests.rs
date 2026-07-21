//! FIXME 0705 (S115 W3 change-set 3) — the auto-curry emission seam is TOTAL
//! over the closed carrier sums (`design/backend/s115-carrier-and-rc-sweep.md`
//! §3; `tests/plan/s115-test-plan.md` §6.5; Principle 24 corollary prong 3 /
//! Principle 20 exhaustiveness).
//!
//! After the S114 typed-resolution flip `ApplyRef ∈ {Dispatch(FQ), ViaCallee}`
//! and `VarRef ∈ {Global(FQ), Local{..}}` are CLOSED. Every legal
//! `(ApplyRef, VarRef)` pair must have an emission arm, and the one illegal
//! pair must be a LOCATED PRODUCER ERROR — never a `_ =>` fallthrough and never
//! a name-resolver re-derivation (Rev-2). These cells are that table.
//!
//! Before this change-set the `ViaCallee` + `VarRef::Local` state had NO arm: it
//! exhausted `func_ids` (a local closure is not a compiled unit fn), the ctor
//! probe, and the inline-primitive probe, and hit the GOT terminal with
//! `target_fq = None` — the 0705 defect, with typecheck complete and correct.

use cranelisp_types::{
    ConcreteType, FQSymbol, JitSymbol, ModuleFullPath, MonoExpr, ResolvedCall, Span, Symbol,
    VarRef,
};

use super::{classify_auto_curry_target, AutoCurryTarget};

fn fq(module: &str, symbol: &str) -> FQSymbol {
    FQSymbol { module: ModuleFullPath::from(module), symbol: Symbol::from(symbol) }
}

fn local_callee(name: &str) -> MonoExpr {
    MonoExpr::Var {
        resolution: VarRef::Local {
            binder: Symbol::from(name),
            binding_span: Span::SYNTHETIC,
        },
        name: Symbol::from(name),
        span: Span::SYNTHETIC,
        resolved_call: None,
        ty: ConcreteType::Int,
    }
}

fn global_callee(module: &str, name: &str) -> MonoExpr {
    MonoExpr::Var {
        resolution: VarRef::Global(fq(module, name)),
        name: Symbol::from(name),
        span: Span::SYNTHETIC,
        resolved_call: None,
        ty: ConcreteType::Int,
    }
}

/// A computed (non-`Var`) callee — the other state `ApplyRef::ViaCallee`
/// explicitly admits ("a computed closure value").
fn computed_callee() -> MonoExpr {
    MonoExpr::Apply {
        callee: Box::new(global_callee("user", "mk")),
        args: vec![],
        span: Span::SYNTHETIC,
        resolved_call: None,
        dispatch: cranelisp_types::ApplyRef::ViaCallee,
        ty: ConcreteType::Int,
        escapes: None,
        confined: None,
        unique_static: None,
        provenance: None,
    }
}

fn builtin_resolution() -> ResolvedCall {
    ResolvedCall::BuiltinFn { name: Symbol::from("eq-i64") }
}

fn sig_resolution() -> ResolvedCall {
    ResolvedCall::SigDispatch { mangled_name: JitSymbol::from("user/f$Int") }
}

// spec: design/backend/s115-carrier-and-rc-sweep.md §3 row 1–3 — a Dispatch
// carrier is a table symbol, whichever callee shape accompanies it.
#[test]
fn dispatch_carrier_takes_the_table_symbol_arms() {
    let target = fq("user", "f");
    for callee in [local_callee("g"), global_callee("user", "f"), computed_callee()] {
        assert_eq!(
            classify_auto_curry_target(Some(&target), None, &callee),
            AutoCurryTarget::Dispatch
        );
    }
    // A Dispatch carrier WITH an inner resolution is still Dispatch — the
    // carrier is the more specific fact and the landed arms consume it.
    assert_eq!(
        classify_auto_curry_target(Some(&target), Some(&builtin_resolution()), &local_callee("g")),
        AutoCurryTarget::Dispatch
    );
}

// spec: §3 row 4 — an inner TraitMethod/BuiltinFn resolution self-derives its
// impl carrier; this is the LANDED arm and must NOT be diverted to the new one.
#[test]
fn inner_resolution_keeps_the_self_derived_impl_arm() {
    assert_eq!(
        classify_auto_curry_target(None, Some(&builtin_resolution()), &local_callee("g")),
        AutoCurryTarget::InnerResolution
    );
    assert_eq!(
        classify_auto_curry_target(None, Some(&sig_resolution()), &global_callee("user", "f")),
        AutoCurryTarget::InnerResolution
    );
}

// spec: §3 row 5 (THE 0705 arm) — `ViaCallee` + `VarRef::Local` is a LEGAL
// carrier state: a `let`-bound closure has no GOT slot, so recording no dispatch
// FQ is the correct, complete producer output. The seam curries the closure
// VALUE. Repro: `(defn f [] (let [g (fn [a b] 0)] ((g 1) 2)))`.
#[test]
fn via_callee_over_a_local_closure_curries_the_closure_value() {
    assert_eq!(
        classify_auto_curry_target(None, None, &local_callee("g")),
        AutoCurryTarget::ClosureValue
    );
}

// spec: §3 — `ViaCallee` over a COMPUTED callee is the same arm (the identity
// rides the callee expression, per the `ApplyRef::ViaCallee` contract).
#[test]
fn via_callee_over_a_computed_callee_is_the_same_closure_value_arm() {
    assert_eq!(
        classify_auto_curry_target(None, None, &computed_callee()),
        AutoCurryTarget::ClosureValue
    );
}

// spec: §3 last row (NEGATIVE — the honest floor) — `ViaCallee` + `Global` with
// no inner resolution is the ONE illegal pairing: the producer transports a
// Global plain-fn callee as `ApplyRef::Dispatch`, so this state is a producer
// contradiction. It must be a LOCATED error carrying the offending FQ, never a
// silent fallback to a name-keyed lookup (Rev-2, backend-keyed-consumer §1.2).
#[test]
fn via_callee_over_a_global_callee_is_a_located_producer_contradiction_neg() {
    let verdict = classify_auto_curry_target(None, None, &global_callee("prelude", "="));
    assert_eq!(verdict, AutoCurryTarget::ProducerContradiction(fq("prelude", "=")));
    // The FQ is carried so the diagnostic NAMES the seam and the offending key
    // — the attribution evidence the 0705/`'='` split turned on.
    match verdict {
        AutoCurryTarget::ProducerContradiction(f) => {
            assert_eq!(f.module.as_ref(), "prelude");
            assert_eq!(f.symbol.as_ref(), "=");
        }
        other => panic!("expected a producer contradiction, got {other:?}"),
    }
}
