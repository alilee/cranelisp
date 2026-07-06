//! CS-II-1/CS-II-2 Principle-23 matrices for `uniqueness.rs`
//! (`design/typecheck/ownership-inference.md` §14.2, §14.6).
//!
//! Pure — every scenario is a hand-built [`MonoExpr`] body over a stub
//! [`UniqEnv`]. Matrices: `result_unique` from return shape + chaining;
//! `unique_static` single-use positives + the load-bearing multi-use /
//! conditional / layout negatives; the projection-read-is-not-a-consume rule;
//! the stash soundness fence.

use std::collections::HashMap;

use cranelisp_types::{
    ConcreteType, FQTypeName, JitSymbol, Mode, ModeSummary, ModuleFullPath, MonoExpr, ParamFlow,
    ResultMode, Span, Symbol, TypeName,
};

use super::super::classify::TerminalKind;
use super::*;

// --- test harness ---

#[derive(Default)]
struct TestEnv {
    kinds: HashMap<Symbol, TerminalKind>,
    summaries: HashMap<Symbol, ModeSummary>,
    unique: HashMap<Symbol, bool>,
}

impl TestEnv {
    /// Register a callee as a summarised UserFn with the given param modes +
    /// result_unique bit (for chaining reads).
    fn callee(mut self, name: &str, param_modes: Vec<Mode>, result_unique: bool) -> Self {
        self.kinds.insert(Symbol::from(name), TerminalKind::UserFnConcrete);
        let n = param_modes.len();
        self.summaries.insert(
            Symbol::from(name),
            ModeSummary {
                param_modes,
                result: ResultMode::Fresh,
                param_flow: vec![ParamFlow::Consumed; n],
                spark_ops: vec![false; n],
                result_unique,
            },
        );
        self.unique.insert(Symbol::from(name), result_unique);
        self
    }
}

impl UniqEnv for TestEnv {
    fn terminal_kind(&self, name: &Symbol) -> Option<TerminalKind> {
        self.kinds.get(name).copied()
    }
    fn summary_of(&self, name: &Symbol) -> Option<ModeSummary> {
        self.summaries.get(name).cloned()
    }
    fn result_unique_of(&self, name: &Symbol) -> bool {
        self.unique.get(name).copied().unwrap_or(false)
    }
    fn layout_eligible(&self, ty: &ConcreteType) -> bool {
        // Heap ADT / String / Vec: reuse-eligible. Scalars: not.
        matches!(ty, ConcreteType::String | ConcreteType::ADT(..))
    }
}

fn sp(n: u32) -> Span {
    Span::new(n, n + 1)
}
fn adt_ty() -> ConcreteType {
    ConcreteType::ADT(FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Box")), vec![])
}
fn var(n: &str) -> MonoExpr {
    MonoExpr::Var { name: Symbol::from(n), span: sp(900), resolved_call: None, ty: adt_ty() }
}
/// A fresh `(Box fields...)` allocation with an explicit span + type.
fn boxed(span: Span, ty: ConcreteType, fields: Vec<MonoExpr>) -> MonoExpr {
    MonoExpr::ConstrADT {
        type_name: FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Box")),
        tag: 0,
        fields,
        span,
        ty,
        escapes: None,
        confined: None,
        unique_static: None,
    }
}
fn fresh(span: Span) -> MonoExpr {
    boxed(span, adt_ty(), vec![])
}
/// A statically-resolved `(name args…)` call (Summarised) with explicit span + type.
fn call(span: Span, name: &str, ty: ConcreteType, args: Vec<MonoExpr>) -> MonoExpr {
    MonoExpr::Apply {
        callee: Box::new(var(name)),
        args,
        span,
        resolved_call: Some(Box::new(cranelisp_types::ResolvedCall::SigDispatch {
            mangled_name: JitSymbol::from(name),
        })),
        ty,
        escapes: None,
        confined: None,
        unique_static: None,
        provenance: None,
    }
}
fn let_(bindings: Vec<(&str, MonoExpr)>, body: MonoExpr) -> MonoExpr {
    MonoExpr::Let {
        bindings: bindings.into_iter().map(|(n, e)| (Symbol::from(n), e)).collect(),
        body: Box::new(body),
        span: sp(800),
        ty: adt_ty(),
    }
}
fn if_(then_branch: MonoExpr, else_branch: MonoExpr) -> MonoExpr {
    MonoExpr::If {
        cond: Box::new(MonoExpr::BoolLit { value: true, span: sp(700), ty: ConcreteType::Bool }),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
        span: sp(701),
        ty: adt_ty(),
    }
}
fn param(n: &str) -> (Symbol, ConcreteType) {
    (Symbol::from(n), adt_ty())
}
fn analyze(params: &[(Symbol, ConcreteType)], body: MonoExpr, env: &TestEnv) -> UniquenessResult {
    analyze_uniqueness(params, &body, env)
}

// =================== result_unique — return shape ===================

#[test]
fn result_unique_fresh_return_is_true() {
    // spec: §14.2 clause 3 — a body returning a fresh allocation is result_unique.
    let r = analyze(&[], fresh(sp(1)), &TestEnv::default());
    assert!(r.result_unique);
}

#[test]
fn result_unique_aliased_param_return_is_false() {
    // spec: §14.2 (negative) — returning a param aliases it ⇒ not a fresh unique
    // root ⇒ result_unique false.
    let r = analyze(&[param("x")], var("x"), &TestEnv::default());
    assert!(!r.result_unique);
}

#[test]
fn result_unique_projected_call_return_is_false() {
    // spec: §14.2 (negative) — a call whose callee is NOT result_unique yields no
    // fresh unique root (the sound chaining read is the bit, never result==Fresh).
    let env = TestEnv::default().callee("proj", vec![Mode::Borrowed], /*unique*/ false);
    let r = analyze(&[param("x")], call(sp(2), "proj", adt_ty(), vec![var("x")]), &env);
    assert!(!r.result_unique);
}

#[test]
fn result_unique_chains_through_unique_call() {
    // spec: §14.2 clause 3 — returning the result of a call whose callee IS
    // result_unique chains the proof through (bool read).
    let env = TestEnv::default().callee("mk", vec![], /*unique*/ true);
    let r = analyze(&[], call(sp(3), "mk", adt_ty(), vec![]), &env);
    assert!(r.result_unique, "chained through mk.result_unique");
}

#[test]
fn result_unique_let_bound_fresh_single_use_return_is_true() {
    // spec: §14.2 clause 2 — `(let [v (fresh)] v)`: v is a fresh single-use
    // binding returned once ⇒ result_unique.
    let body = let_(vec![("v", fresh(sp(4)))], var("v"));
    let r = analyze(&[], body, &TestEnv::default());
    assert!(r.result_unique);
}

#[test]
fn result_unique_stashed_then_returned_is_false_soundness() {
    // spec: §14.2 clause 2 (SOUNDNESS FENCE) — `(let [v (fresh)] (let [_ (stash
    // v)] v))`: v is stashed (a second consuming use) AND returned. `result ==
    // Fresh` would (wrongly) hold; the single-consuming-use gate makes
    // result_unique FALSE — the caller cannot see the callee-side stash, so
    // relying on result==Fresh would be unsound. `stash` is a Decision-24 site
    // (consumes v Owned).
    let stash = call(sp(5), "stash", adt_ty(), vec![var("v")]);
    let env = TestEnv::default().callee("stash", vec![Mode::Owned], false);
    let inner = let_(vec![("_", stash)], var("v"));
    let body = let_(vec![("v", fresh(sp(6)))], inner);
    let r = analyze(&[], body, &env);
    assert!(!r.result_unique, "a stashed-then-returned fresh value is NOT unique");
}

// =================== unique_static — site facts (§14.2) ===================

#[test]
fn unique_static_fresh_single_use_is_some_true() {
    // spec: §14.2 (positive) — `(let [v (fresh@10)] (consume v))`: v used once in
    // a consuming (Owned) position ⇒ the fresh alloc @10 is a proven unique root.
    let env = TestEnv::default().callee("consume", vec![Mode::Owned], false);
    let body = let_(
        vec![("v", fresh(sp(10)))],
        call(sp(11), "consume", adt_ty(), vec![var("v")]),
    );
    let r = analyze(&[], body, &env);
    assert_eq!(r.unique_sites.get(&sp(10)), Some(&true), "single-use fresh ⇒ Some(true)");
}

#[test]
fn unique_static_multi_use_is_none() {
    // spec: §14.2 clause 2 (load-bearing NEGATIVE) — `(let [v (fresh@12)] (pair v
    // v))`: v consumed twice (both ConstrADT fields) ⇒ NOT unique ⇒ no fact.
    let body = let_(
        vec![("v", fresh(sp(12)))],
        boxed(sp(13), adt_ty(), vec![var("v"), var("v")]),
    );
    let r = analyze(&[], body, &TestEnv::default());
    assert!(r.unique_sites.get(&sp(12)).is_none(), "multi-use ⇒ None");
}

#[test]
fn unique_static_conditional_consume_is_none() {
    // spec: §14.2 clause 2 (NEGATIVE) — `(let [v (fresh@14)] (if c (consume v)
    // v))`: v consumed on one path, returned on another ⇒ two consuming uses ⇒
    // not provably single-use ⇒ None.
    let env = TestEnv::default().callee("consume", vec![Mode::Owned], false);
    let body = let_(
        vec![("v", fresh(sp(14)))],
        if_(call(sp(15), "consume", adt_ty(), vec![var("v")]), var("v")),
    );
    let r = analyze(&[], body, &env);
    assert!(r.unique_sites.get(&sp(14)).is_none(), "conditional-consume ⇒ None");
}

#[test]
fn unique_static_projection_read_is_not_a_consume() {
    // spec: §14.2 clause 2 — a Borrowed (projection/read) use does NOT count as a
    // consuming use. `(let [v (fresh@16)] (pair (readonly v) v))`: `readonly`
    // takes v Borrowed (not counted); the bare `v` field is the ONE consuming use
    // ⇒ still Some(true).
    let env = TestEnv::default().callee("readonly", vec![Mode::Borrowed], false);
    let body = let_(
        vec![("v", fresh(sp(16)))],
        boxed(
            sp(17),
            adt_ty(),
            vec![call(sp(18), "readonly", adt_ty(), vec![var("v")]), var("v")],
        ),
    );
    let r = analyze(&[], body, &env);
    assert_eq!(
        r.unique_sites.get(&sp(16)),
        Some(&true),
        "a borrowed read is not a consuming use ⇒ single-use still holds"
    );
}

#[test]
fn unique_static_cow_copy_is_some_true() {
    // spec: §14.2 clause 1(ii) — a freshly-COW'd copy (a call whose callee is
    // result_unique) consumed once ⇒ Some(true) on the COW call node.
    let env = TestEnv::default()
        .callee("cow", vec![Mode::Owned], /*unique*/ true)
        .callee("consume", vec![Mode::Owned], false);
    let body = let_(
        vec![("g", call(sp(20), "cow", adt_ty(), vec![var("grid")]))],
        call(sp(21), "consume", adt_ty(), vec![var("g")]),
    );
    let r = analyze(&[param("grid")], body, &env);
    assert_eq!(r.unique_sites.get(&sp(20)), Some(&true), "COW copy single-use ⇒ Some(true)");
}

#[test]
fn unique_static_layout_ineligible_is_none() {
    // spec: §14.2 clause 3 (NEGATIVE) — a fresh unique single-use value whose
    // TYPE is layout-ineligible (a scalar, no reusable heap slot) gets NO fact.
    // `mk-int` returns Int and is result_unique; consumed once — but Int is not
    // reuse-eligible.
    let env = TestEnv::default()
        .callee("mk-int", vec![], /*unique*/ true)
        .callee("consume-int", vec![Mode::Owned], false);
    let body = let_(
        vec![("n", call(sp(22), "mk-int", ConcreteType::Int, vec![]))],
        call(sp(23), "consume-int", adt_ty(), vec![var("n")]),
    );
    let r = analyze(&[], body, &env);
    assert!(r.unique_sites.get(&sp(22)).is_none(), "layout-ineligible (Int) ⇒ None");
}

#[test]
fn unique_static_inline_returned_fresh_is_some_true() {
    // spec: §14.2 — a fresh allocation in the RETURN position (single-use by
    // construction) is a proven unique root.
    let r = analyze(&[], fresh(sp(24)), &TestEnv::default());
    assert_eq!(r.unique_sites.get(&sp(24)), Some(&true));
}
