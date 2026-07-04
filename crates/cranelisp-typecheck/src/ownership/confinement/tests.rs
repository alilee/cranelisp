//! CS-3 Principle-23 matrices for `confinement.rs`
//! (`design/typecheck/ownership-inference.md` §13.7 `confinement.rs` block):
//! strand-context, join, propagation, and the increment-I negatives.

use std::collections::HashMap;

use cranelisp_types::{
    ConcreteType, FQSymbol, JitSymbol, Mode, ModeSummary, ModuleFullPath, MonoExpr, ParamFlow,
    ResultMode, Span, Symbol,
};

use super::super::classify::TerminalKind;
use super::super::transfer::TransferEnv;
use super::*;

#[derive(Default)]
struct TestEnv {
    summaries: HashMap<Symbol, ModeSummary>,
}
impl TestEnv {
    fn summary(mut self, name: &str, s: ModeSummary) -> Self {
        self.summaries.insert(Symbol::from(name), s);
        self
    }
}
impl TransferEnv for TestEnv {
    fn terminal_kind(&self, _name: &Symbol) -> Option<TerminalKind> {
        None
    }
    fn summary_of(&self, name: &Symbol) -> Option<(FQSymbol, ModeSummary)> {
        self.summaries.get(name).map(|s| {
            (FQSymbol { module: ModuleFullPath::from("user"), symbol: name.clone() }, s.clone())
        })
    }
}

fn s() -> Span {
    Span::SYNTHETIC
}
fn var(n: &str) -> MonoExpr {
    MonoExpr::Var { name: Symbol::from(n), span: s(), resolved_call: None, ty: ConcreteType::String }
}
fn call(name: &str, args: Vec<MonoExpr>) -> MonoExpr {
    MonoExpr::Apply {
        callee: Box::new(var(name)),
        args,
        span: s(),
        resolved_call: Some(Box::new(cranelisp_types::ResolvedCall::SigDispatch {
            mangled_name: JitSymbol::from(name),
        })),
        ty: ConcreteType::String,
        escapes: None,
        confined: None,
        unique_static: None,
        provenance: None,
    }
}
fn sm(param_modes: Vec<Mode>, spark_ops: Vec<bool>) -> ModeSummary {
    let n = param_modes.len();
    ModeSummary {
        param_modes,
        result: ResultMode::Fresh,
        param_flow: vec![ParamFlow::Consumed; n],
        spark_ops,
        result_unique: false,
    }
}
fn owned_p() -> Vec<(Symbol, Mode)> {
    vec![(Symbol::from("p"), Mode::Owned)]
}

#[test]
fn parent_strand_owned_op_is_confined() {
    // spec: §5.2/§5.3 — an Owned param consumed only on the parent strand ⇒
    // spark_ops clear (Confined).
    let env = TestEnv::default().summary("consume", sm(vec![Mode::Owned], vec![false]));
    let r = confine(&owned_p(), &call("consume", vec![var("p")]), &env);
    assert!(!r.spark_ops[0]);
}

#[test]
fn parbind_owned_op_is_crossing() {
    // spec: §5.2 — an Owned consuming op inside a ParBind (spark) ⇒ spark_ops set.
    let env = TestEnv::default().summary("consume", sm(vec![Mode::Owned], vec![false]));
    let body = MonoExpr::ParBind {
        bindings: vec![(Symbol::from("r"), call("consume", vec![var("p")]))],
        body: Box::new(var("r")),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = confine(&owned_p(), &body, &env);
    assert!(r.spark_ops[0]);
}

#[test]
fn borrowed_spark_read_zero_ops_is_confined() {
    // spec: §5.3 (the F2 shape) — a Borrowed param read inside a spark has zero
    // surviving ops ⇒ spark_ops clear even though it crosses a strand.
    let env = TestEnv::default().summary("readonly", sm(vec![Mode::Borrowed], vec![false]));
    let body = MonoExpr::ParBind {
        bindings: vec![(Symbol::from("r"), call("readonly", vec![var("p")]))],
        body: Box::new(var("r")),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = confine(&[(Symbol::from("p"), Mode::Borrowed)], &body, &env);
    assert!(!r.spark_ops[0]);
}

#[test]
fn callee_spark_op_propagates_transitively() {
    // spec: §5.3 — a callee whose spark_op is set makes the caller's param
    // crossing, on any strand (even parent).
    let env = TestEnv::default().summary("inner", sm(vec![Mode::Owned], vec![true]));
    let r = confine(&owned_p(), &call("inner", vec![var("p")]), &env);
    assert!(r.spark_ops[0]);
}

#[test]
fn launch_continue_deferred_op_is_crossing() {
    // spec: §5.2 — a consuming op inside LaunchContinue.launched (deferred) crosses.
    let env = TestEnv::default().summary("consume", sm(vec![Mode::Owned], vec![false]));
    let body = MonoExpr::LaunchContinue {
        launched: Box::new(call("consume", vec![var("p")])),
        continuation: Box::new(MonoExpr::IntLit { value: 0, span: s(), ty: ConcreteType::Int }),
        span: s(),
        ty: ConcreteType::Int,
    };
    let r = confine(&owned_p(), &body, &env);
    assert!(r.spark_ops[0]);
}

#[test]
fn copy_param_never_crosses() {
    // spec: §5 (negative) — a Copy param carries no RC ops; spark_ops stays clear.
    let env = TestEnv::default().summary("consume", sm(vec![Mode::Owned], vec![false]));
    let body = MonoExpr::ParBind {
        bindings: vec![(Symbol::from("r"), call("consume", vec![var("n")]))],
        body: Box::new(var("r")),
        span: s(),
        ty: ConcreteType::Int,
    };
    let r = confine(&[(Symbol::from("n"), Mode::Copy)], &body, &env);
    assert!(!r.spark_ops[0]);
}

#[test]
fn shadowed_param_name_does_not_false_match_in_spark() {
    // spec: §13.6(i) (F4, confinement precision) — an inner `let` binding that
    // shadows param `p` must NOT make a spark-side consume of the SHADOWED `p`
    // spuriously set `spark_ops` for the real param. Without the confiner's
    // scope discipline the `param_idx` lookup matches the param name and
    // over-widens toward Crossing (sound, but imprecise). `(let [p (readonly p)]
    // (par [_r (consume p)] _r))`.
    let env = TestEnv::default()
        .summary("readonly", sm(vec![Mode::Borrowed], vec![false]))
        .summary("consume", sm(vec![Mode::Owned], vec![false]));
    let spark = MonoExpr::ParBind {
        bindings: vec![(Symbol::from("_r"), call("consume", vec![var("p")]))],
        body: Box::new(var("_r")),
        span: s(),
        ty: ConcreteType::String,
    };
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("p"), call("readonly", vec![var("p")]))],
        body: Box::new(spark),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = confine(&owned_p(), &body, &env);
    // The consumed `p` inside the spark is the inner (shadowing) binding, not the
    // param ⇒ the param's spark_ops stays clear.
    assert!(!r.spark_ops[0], "shadowed inner p must not false-match the param");
}

#[test]
fn confined_facts_true_on_parent_false_in_spark() {
    // spec: §5.3 — allocation sites record confined=true parent-strand,
    // false (Crossing) inside a spark. Transferred is never emitted (§5.4).
    let env = TestEnv::default().summary("consume", sm(vec![Mode::Owned], vec![false]));
    // (let [_a (consume p)]  -- lenient RHS = potential fork
    //   "lit")               -- parent-strand string literal
    let lit = MonoExpr::StringLit {
        value: "x".into(),
        span: Span::new(100, 101),
        ty: ConcreteType::String,
        escapes: None,
        confined: None,
        unique_static: None,
    };
    let inner = MonoExpr::ConstrADT {
        type_name: cranelisp_types::FQTypeName::new(ModuleFullPath::from("user"), cranelisp_types::TypeName::from("Box")),
        tag: 0,
        fields: vec![],
        span: Span::new(200, 201),
        ty: ConcreteType::String,
        escapes: None,
        confined: None,
        unique_static: None,
    };
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("_a"), inner)],
        body: Box::new(lit),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = confine(&owned_p(), &body, &env);
    // The parent-strand literal is Confined; the let-RHS ADT is in a
    // potential-fork ⇒ Crossing.
    assert_eq!(r.confined.get(&Span::new(100, 101)), Some(&true));
    assert_eq!(r.confined.get(&Span::new(200, 201)), Some(&false));
}

// ============ ConfineFrame scope-stack matrix (S102 /qa audit) ============
//
// The confinement mirror of the transfer scope-stack matrix (§13.6(i)).
// `shadowed_param_name_does_not_false_match_in_spark` above is the seed
// (restore-basic: an inner shadow does not false-match the param). These fill
// the restore-REINSTATES arm + nesting + multi-arm same-name.
//
// NOTE on soundness direction: the confiner's `param_idx.remove(n)` on a
// name-colliding binding is a PRECISION move (avoid a false Crossing on the
// shadow). The paired `restore_frame` is soundness-preserving GIVEN the remove:
// without the reinstate, a genuine later spark-consume of the REAL param would
// miss `param_idx` and leave `spark_ops` clear — an UNDER-approximation (false
// when truth is Crossing) that would pick non-atomic RC for an off-strand value.
// So these reinstate cells guard a real soundness edge of the remove+restore
// PAIR, and each asserts `spark_ops[0] == true` (the param IS consumed
// off-strand after its shadow scope closes).

#[test]
fn confine_sequential_shadow_restores_param_reinstates() {
    // spec: §13.6(i) (F4, confinement restore-REINSTATES). An inner `let` shadows
    // param `p` inside an outer binding's RHS; after that scope closes, a spark
    // `(consume p)` means the PARAM and must set `spark_ops[0]`. The frame must
    // reinstate `p` in `param_idx`.
    // `(let [x (let [p (readonly p)] p)] (par [_r (consume p)] _r))`.
    let env = TestEnv::default()
        .summary("readonly", sm(vec![Mode::Borrowed], vec![false]))
        .summary("consume", sm(vec![Mode::Owned], vec![false]));
    let inner_let = MonoExpr::Let {
        bindings: vec![(Symbol::from("p"), call("readonly", vec![var("p")]))],
        body: Box::new(var("p")),
        span: s(),
        ty: ConcreteType::String,
    };
    let spark = MonoExpr::ParBind {
        bindings: vec![(Symbol::from("_r"), call("consume", vec![var("p")]))],
        body: Box::new(var("_r")),
        span: s(),
        ty: ConcreteType::String,
    };
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("x"), inner_let)],
        body: Box::new(spark),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = confine(&owned_p(), &body, &env);
    assert!(
        r.spark_ops[0],
        "param p must be reinstated after the inner shadow scope closes; the spark consume sets spark_ops"
    );
}

#[test]
fn confine_triple_nested_shadow_restores_param() {
    // spec: §13.6(i) (F4, confinement nesting ≥3). Three nested `let` scopes each
    // shadow param `p`; after all unwind, a spark `(consume p)` means the PARAM.
    // Every level's frame must reinstate on exit or the param is lost from
    // `param_idx` ⇒ missed Crossing.
    // `(let [x (let [p (readonly p)] (let [p (readonly p)] (let [p (readonly p)] p)))]
    //    (par [_r (consume p)] _r))`.
    let env = TestEnv::default()
        .summary("readonly", sm(vec![Mode::Borrowed], vec![false]))
        .summary("consume", sm(vec![Mode::Owned], vec![false]));
    let mk_let = |inner: MonoExpr| MonoExpr::Let {
        bindings: vec![(Symbol::from("p"), call("readonly", vec![var("p")]))],
        body: Box::new(inner),
        span: s(),
        ty: ConcreteType::String,
    };
    let nest = mk_let(mk_let(mk_let(var("p"))));
    let spark = MonoExpr::ParBind {
        bindings: vec![(Symbol::from("_r"), call("consume", vec![var("p")]))],
        body: Box::new(var("_r")),
        span: s(),
        ty: ConcreteType::String,
    };
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("x"), nest)],
        body: Box::new(spark),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = confine(&owned_p(), &body, &env);
    assert!(
        r.spark_ops[0],
        "param p must be reinstated after 3-deep shadow unwinds; the spark consume sets spark_ops"
    );
}

#[test]
fn confine_two_match_arms_same_name_param_restored() {
    // spec: §13.6(i) (F4, confinement multi-arm same-name). Both match arms bind
    // field `p` (shadowing param `p`), each in its own frame; after the match a
    // spark `(consume p)` means the PARAM. If an arm frame leaked, the param would
    // stay shadowed out of `param_idx` and the spark consume would miss it.
    // `(let [x (match h [(Box p) p] [(Cell p) p])] (par [_r (consume p)] _r))`.
    let env = TestEnv::default().summary("consume", sm(vec![Mode::Owned], vec![false]));
    let arm1 = cranelisp_types::MonoMatchArm {
        pattern: cranelisp_types::Pattern::Constructor {
            name: cranelisp_types::SymbolRef { module: None, name: Symbol::from("Box") },
            bindings: vec![Symbol::from("p")],
            span: s(),
        },
        body: var("p"),
        span: Span::new(70, 71),
        provenance: None,
    };
    let arm2 = cranelisp_types::MonoMatchArm {
        pattern: cranelisp_types::Pattern::Constructor {
            name: cranelisp_types::SymbolRef { module: None, name: Symbol::from("Cell") },
            bindings: vec![Symbol::from("p")],
            span: s(),
        },
        body: var("p"),
        span: Span::new(72, 73),
        provenance: None,
    };
    let m = MonoExpr::Match {
        scrutinee: Box::new(var("h")),
        arms: vec![arm1, arm2],
        span: s(),
        compiler_generated: false,
        ty: ConcreteType::String,
    };
    let spark = MonoExpr::ParBind {
        bindings: vec![(Symbol::from("_r"), call("consume", vec![var("p")]))],
        body: Box::new(var("_r")),
        span: s(),
        ty: ConcreteType::String,
    };
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("x"), m)],
        body: Box::new(spark),
        span: s(),
        ty: ConcreteType::String,
    };
    // params: p (Owned, index 0) + h (scrutinee, Owned) so param_idx has both.
    let params = vec![(Symbol::from("p"), Mode::Owned), (Symbol::from("h"), Mode::Owned)];
    let r = confine(&params, &body, &env);
    assert!(
        r.spark_ops[0],
        "param p must survive two same-name arms (each its own frame); the spark consume sets spark_ops"
    );
}
