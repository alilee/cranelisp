//! CS-2 Principle-23 matrices for `transfer.rs`
//! (`design/typecheck/ownership-inference.md` §13.7 `transfer.rs` block).
//!
//! Pure — every scenario is a hand-built [`MonoExpr`] body over a
//! `HashMap`-backed [`TransferEnv`]. Matrices: mode/flow join, escape edge,
//! projection depth, and the increment-I negatives.

use std::collections::HashMap;

use cranelisp_types::{
    ConcreteType, FQSymbol, FQTypeName, JitSymbol, Mode, ModeSummary, ModuleFullPath, MonoExpr,
    MonoMatchArm, ParamFlow, Pattern, ResultMode, Span, Symbol, TypeName,
};

use super::super::classify::TerminalKind;
use super::*;

// --- test harness ---

#[derive(Default)]
struct TestEnv {
    kinds: HashMap<Symbol, TerminalKind>,
    summaries: HashMap<Symbol, ModeSummary>,
}

impl TestEnv {
    fn summary(mut self, name: &str, s: ModeSummary) -> Self {
        self.summaries.insert(Symbol::from(name), s);
        self
    }
}

impl TransferEnv for TestEnv {
    fn terminal_kind(&self, name: &Symbol) -> Option<TerminalKind> {
        self.kinds.get(name).copied()
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
    MonoExpr::Var { name: Symbol::from(n), span: s(), resolved_call: None, ty: ConcreteType::String, resolution: cranelisp_types::VarRef::Local { binder: Symbol::from(n), binding_span: cranelisp_types::Span::SYNTHETIC } }
}
/// A statically-resolved call `(name args...)` via SigDispatch (classifies
/// Summarised(name), consulting the summary registered under `name`).
fn call(name: &str, args: Vec<MonoExpr>) -> MonoExpr {
    MonoExpr::Apply {
        dispatch: cranelisp_types::ApplyRef::ViaCallee,
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
/// A call with no resolved_call (the None+Var classifier row).
fn bare_call(name: &str, args: Vec<MonoExpr>) -> MonoExpr {
    MonoExpr::Apply {
        dispatch: cranelisp_types::ApplyRef::ViaCallee,
        callee: Box::new(var(name)),
        args,
        span: s(),
        resolved_call: None,
        ty: ConcreteType::String,
        escapes: None,
        confined: None,
        unique_static: None,
        provenance: None,
    }
}
fn adt(fields: Vec<MonoExpr>) -> MonoExpr {
    adt_sp(s(), fields)
}
/// A `ConstrADT` with an explicit span (distinct spans needed when a test
/// inspects per-node escape facts — `s()` alone collides all nodes on SYNTHETIC).
fn adt_sp(span: Span, fields: Vec<MonoExpr>) -> MonoExpr {
    MonoExpr::ConstrADT {
        type_name: FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Box")),
        tag: 0,
        fields,
        span,
        ty: ConcreteType::ADT(FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Box")), vec![]),
        escapes: None,
        confined: None,
        unique_static: None,
    }
}
/// A `SigDispatch` call with an explicit span.
fn call_sp(span: Span, name: &str, args: Vec<MonoExpr>) -> MonoExpr {
    MonoExpr::Apply {
        dispatch: cranelisp_types::ApplyRef::ViaCallee,
        callee: Box::new(var(name)),
        args,
        span,
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
fn sm(param_modes: Vec<Mode>, result: ResultMode, param_flow: Vec<ParamFlow>) -> ModeSummary {
    let n = param_modes.len();
    ModeSummary { param_modes, result, param_flow, spark_ops: vec![false; n], result_unique: false }
}
fn strparam(n: &str) -> (Symbol, ConcreteType) {
    (Symbol::from(n), ConcreteType::String)
}
fn intparam(n: &str) -> (Symbol, ConcreteType) {
    (Symbol::from(n), ConcreteType::Int)
}
fn run(params: &[(Symbol, ConcreteType)], body: MonoExpr, env: TestEnv) -> TransferResult {
    transfer(params, &body, &env, &CopyClassifier::scalars_only())
}

// =================== Mode/flow join matrix ===================

#[test]
fn borrowed_handoff_is_non_widening() {
    // spec: §2.2 rule (load-bearing negative) — a Borrowed handoff does not widen.
    let env = TestEnv::default().summary("readonly", sm(vec![Mode::Borrowed], ResultMode::Fresh, vec![ParamFlow::Consumed]));
    let r = run(&[strparam("p")], call("readonly", vec![var("p")]), env);
    assert_eq!(r.summary.param_mode(0), Mode::Borrowed);
}

#[test]
fn owned_handoff_widens_and_applies_flow() {
    // spec: §2.2 — an Owned handoff widens to Owned and applies the callee flow.
    let env = TestEnv::default().summary("consume", sm(vec![Mode::Owned], ResultMode::Fresh, vec![ParamFlow::Consumed]));
    let r = run(&[strparam("p")], call("consume", vec![var("p")]), env);
    assert_eq!(r.summary.param_mode(0), Mode::Owned);
    assert_eq!(r.summary.param_flow(0), ParamFlow::Consumed);
}

#[test]
fn decision24_site_widens_owned_retained() {
    // spec: §2.2 rule 5 — a closure-valued (Decision-24) call site widens + Retained.
    // `f` is a param binding used as a callee ⇒ closure value ⇒ Decision-24.
    let env = TestEnv::default();
    let r = run(&[(Symbol::from("f"), ConcreteType::Fn(vec![], Box::new(ConcreteType::String))), strparam("p")],
        bare_call("f", vec![var("p")]), env);
    assert_eq!(r.summary.param_mode(1), Mode::Owned);
    assert_eq!(r.summary.param_flow(1), ParamFlow::Retained);
}

#[test]
fn constructor_field_store_into_returned_is_into_result() {
    // spec: §2.2 — `(defn keep [x] (Box x))` ⇒ x: Owned / IntoResult.
    let r = run(&[strparam("x")], adt(vec![var("x")]), TestEnv::default());
    assert_eq!(r.summary.param_mode(0), Mode::Owned);
    assert_eq!(r.summary.param_flow(0), ParamFlow::IntoResult);
}

#[test]
fn declared_borrowed_leaf_does_not_widen_or_escape() {
    // spec: §9.2 — a declared-Borrowed leaf stops rule 5 (no widen, no escape).
    let env = TestEnv::default().summary("vec-len", sm(vec![Mode::Borrowed], ResultMode::Fresh, vec![ParamFlow::Consumed]));
    let r = run(&[strparam("p")], call("vec-len", vec![var("p")]), env);
    assert_eq!(r.summary.param_mode(0), Mode::Borrowed);
}

#[test]
fn absent_fact_leaf_widens_and_escapes() {
    // spec: §2.2 rule 5 — an absent-fact callee reads ⊤ ⇒ widen + Retained.
    let env = TestEnv::default(); // no summary for `mystery`
    let r = run(&[strparam("p")], call("mystery", vec![var("p")]), env);
    assert_eq!(r.summary.param_mode(0), Mode::Owned);
    assert_eq!(r.summary.param_flow(0), ParamFlow::Retained);
}

#[test]
fn multi_site_join_borrowed_then_owned_is_owned() {
    // spec: §13.7 — Borrowed ⊔ Owned = Owned (multi-site join).
    let env = TestEnv::default()
        .summary("readonly", sm(vec![Mode::Borrowed], ResultMode::Fresh, vec![ParamFlow::Consumed]))
        .summary("consume", sm(vec![Mode::Owned], ResultMode::Fresh, vec![ParamFlow::Consumed]));
    // (let [_a (readonly p)] (consume p))
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("_a"), call("readonly", vec![var("p")]))],
        body: Box::new(call("consume", vec![var("p")])),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("p")], body, env);
    assert_eq!(r.summary.param_mode(0), Mode::Owned);
}

#[test]
fn scalar_param_is_copy_never_widened() {
    // spec: §2.2 — an Int param is Copy and never widens even under Decision-24.
    let env = TestEnv::default();
    let r = run(&[(Symbol::from("f"), ConcreteType::Fn(vec![], Box::new(ConcreteType::Int))), intparam("n")],
        bare_call("f", vec![var("n")]), env);
    assert_eq!(r.summary.param_mode(1), Mode::Copy);
}

// =================== Escape-edge matrix ===================

#[test]
fn return_direct_param_is_alias() {
    // spec: §3.3 — returning param i directly ⇒ AliasOf(i), Owned/IntoResult.
    let r = run(&[strparam("p")], var("p"), TestEnv::default());
    assert_eq!(r.summary.result, ResultMode::AliasOf(0));
    assert_eq!(r.summary.param_mode(0), Mode::Owned);
}

#[test]
fn return_embedded_in_constr_escapes_and_result_conditional() {
    // spec: §16.2 row 5 (0641 I-2) — a returned ADT carrying a param is the JOIN of
    // its element origins (`Conditional{rep:x}`), NOT unconditional `Fresh`: the
    // param's reference escapes INSIDE the container, so the result publishes the
    // conservative `MayAliasOf(0)` (keeps the consumer's protect on the aliased
    // element path). Pre-§16 this returned `Fresh` — the I-2 anti-monotone rule
    // ("a fresh container whose escaping element is a COW alias" laundered to Fresh).
    let r = run(&[strparam("x")], adt(vec![var("x")]), TestEnv::default());
    assert_eq!(r.summary.result, ResultMode::MayAliasOf(0));
    // Escape site fact on the ConstrADT is true (it is returned).
    assert!(r.facts.escapes.values().any(|v| *v));
    // x is folded into the returned aggregate ⇒ IntoResult (unchanged).
    assert_eq!(r.summary.param_flow(0), ParamFlow::IntoResult);
}

#[test]
fn parbind_joined_is_non_escape() {
    // spec: §4.3 — a ParBind binding is a joined spark, non-escape.
    let env = TestEnv::default().summary("readonly", sm(vec![Mode::Borrowed], ResultMode::Fresh, vec![ParamFlow::Consumed]));
    let body = MonoExpr::ParBind {
        bindings: vec![(Symbol::from("r"), call("readonly", vec![var("p")]))],
        body: Box::new(var("r")),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("p")], body, env);
    // p only read borrowed inside the joined spark ⇒ stays Borrowed.
    assert_eq!(r.summary.param_mode(0), Mode::Borrowed);
}

#[test]
fn launch_continue_launched_is_escape_edge() {
    // spec: R6 — a value used in LaunchContinue.launched escapes (suspension).
    let body = MonoExpr::LaunchContinue {
        launched: Box::new(bare_call("f", vec![var("p")])), // f is a closure value
        continuation: Box::new(MonoExpr::IntLit { value: 0, span: s(), ty: ConcreteType::Int }),
        span: s(),
        ty: ConcreteType::Int,
    };
    let r = run(&[(Symbol::from("f"), ConcreteType::Fn(vec![], Box::new(ConcreteType::String))), strparam("p")], body, TestEnv::default());
    assert_eq!(r.summary.param_mode(1), Mode::Owned);
    assert_eq!(r.summary.param_flow(1), ParamFlow::Retained);
}

#[test]
fn binding_mediated_escape_widens_flow_and_escape() {
    // spec: §13.6 (blocker 1) — a returned let-bound Fresh aggregate that
    // consumed a param marks that param IntoResult and flips the aggregate's
    // escape fact. `(defn keep [x] (let [box (Some x)] box))`.
    // The DIRECT shape `(Some x)` is covered by
    // `constructor_field_store_into_returned_is_into_result`; this is the
    // binding-indirected shape that was the narrowing.
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("box"), adt(vec![var("x")]))],
        body: Box::new(var("box")),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("x")], body, TestEnv::default());
    // Mode stays Owned (constructor field-store; no ABI change either way).
    assert_eq!(r.summary.param_mode(0), Mode::Owned);
    // Flow widens Consumed → IntoResult (the returned aggregate carries x out).
    assert_eq!(r.summary.param_flow(0), ParamFlow::IntoResult);
    // The aggregate escapes (returned via the binding).
    assert!(r.facts.escapes.values().any(|v| *v), "aggregate must escape");
}

#[test]
fn binding_local_fresh_aggregate_does_not_escape() {
    // spec: §13.6 (blocker 1, precision twin) — a let-bound Fresh aggregate that
    // never escapes keeps escapes=false / Consumed (the fix must not over-widen
    // purely-local aggregates). `(defn f [x] (let [box (Some x)] 0))`.
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("box"), adt(vec![var("x")]))],
        body: Box::new(MonoExpr::IntLit { value: 0, span: s(), ty: ConcreteType::Int }),
        span: s(),
        ty: ConcreteType::Int,
    };
    let r = run(&[strparam("x")], body, TestEnv::default());
    assert_eq!(r.summary.param_flow(0), ParamFlow::Consumed);
    assert!(r.facts.escapes.values().all(|v| !*v), "local aggregate must not escape");
}

#[test]
fn binding_mediated_escape_flat_fold_chain_widens_all() {
    // spec: §13.6(g) (F1) — a FLAT multi-binding let fold-chain re-propagates to
    // FIXPOINT, not one level. `(defn f [x] (let [a (Some x) b (Some a)] b))`:
    // b returned ⇒ a escapes ⇒ x escapes. The single-level drain left a's RHS
    // never re-walked ⇒ x=Consumed / a's aggregate escapes=false (the F1 bug).
    let a_span = Span::new(10, 11);
    let b_span = Span::new(20, 21);
    let body = MonoExpr::Let {
        bindings: vec![
            (Symbol::from("a"), adt_sp(a_span, vec![var("x")])),
            (Symbol::from("b"), adt_sp(b_span, vec![var("a")])),
        ],
        body: Box::new(var("b")),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("x")], body, TestEnv::default());
    assert_eq!(r.summary.param_flow(0), ParamFlow::IntoResult, "x flows out through the fold-chain");
    assert_eq!(r.facts.escapes.get(&a_span), Some(&true), "a's aggregate escapes (embedded in returned b)");
    assert_eq!(r.facts.escapes.get(&b_span), Some(&true), "b's aggregate escapes (returned)");
}

#[test]
fn parbind_returned_binding_escapes_folded_param() {
    // spec: §13.6(g) (F1) — a joined-spark binding that is RETURNED escapes its
    // folded param; `ParBind` previously bound Fresh names but never drained.
    // `(par [r (Some x)] r)`. The §4.3 non-escape property is a STRAND fact, not
    // a frame-escape fact.
    let r_span = Span::new(30, 31);
    let body = MonoExpr::ParBind {
        bindings: vec![(Symbol::from("r"), adt_sp(r_span, vec![var("x")]))],
        body: Box::new(var("r")),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("x")], body, TestEnv::default());
    assert_eq!(r.summary.param_flow(0), ParamFlow::IntoResult);
    assert_eq!(r.facts.escapes.get(&r_span), Some(&true), "returned spark aggregate escapes");
}

#[test]
fn self_aliasing_shadow_binding_terminates() {
    // spec: §13.6(g)/(i) — the `case`/`cond` macro shape `(let [a a] …)` rebinds a
    // name to itself. The drain MUST terminate (dedup on (name,ctx)): before the
    // dedup, re-walking `a`'s RHS `var("a")` resolved the name to the
    // just-inserted INNER `a` (itself, unscoped bindings §13.6(i)) and re-pushed
    // forever — the observed stdlib `case`-macro compile hang.
    // (defn f [x] (let [a (Some x)] (let [a a] a)))
    let inner = MonoExpr::Let {
        bindings: vec![(Symbol::from("a"), var("a"))],
        body: Box::new(var("a")),
        span: s(),
        ty: ConcreteType::String,
    };
    let outer = MonoExpr::Let {
        bindings: vec![(Symbol::from("a"), adt(vec![var("x")]))],
        body: Box::new(inner),
        span: s(),
        ty: ConcreteType::String,
    };
    // Completing at all proves termination. Mode is Owned (constructor store, set
    // in the forward walk). Full IntoResult propagation through the self-alias is
    // blocked by the unscoped-bindings limitation (§13.6(i)), not the drain.
    let r = run(&[strparam("x")], outer, TestEnv::default());
    assert_eq!(r.summary.param_mode(0), Mode::Owned);
}

#[test]
fn match_arm_shadow_drops_ambiguous_provenance() {
    // spec: §13.6(d) (F2 mirror) — a MATCH arm binding shadowing a live
    // provenance root (not the scrutinee root) drops that stale provenance —
    // the same guard as the Let seam, single-sourced. Previously unfixed at the
    // match seam. `(defn f [g h] (let [x (gcells g)] (match h [(Box g) x])))`.
    let arm = MonoMatchArm {
        pattern: Pattern::Constructor {
            name: cranelisp_types::SymbolRef { module: None, name: Symbol::from("Box") },
            bindings: vec![Symbol::from("g")],
            span: s(),
        },
        body: var("x"),
        span: Span::new(40, 41),
        provenance: None,
        resolved_ctor: None,
    };
    let m = MonoExpr::Match {
        scrutinee: Box::new(var("h")),
        arms: vec![arm],
        span: s(),
        compiler_generated: false,
        ty: ConcreteType::String,
    };
    let outer = MonoExpr::Let {
        bindings: vec![(Symbol::from("x"), call_sp(Span::new(50, 51), "gcells", vec![var("g")]))],
        body: Box::new(m),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("g"), strparam("h")], outer, accessor_env());
    assert!(
        r.facts.provenance.values().all(|root| root.as_ref() != "g"),
        "match-arm shadow of g must drop the stale gcells provenance"
    );
}

#[test]
fn match_arm_no_shadow_keeps_provenance() {
    // spec: §13.6(d) (F2 precision twin) — an arm binding NOT shadowing any live
    // root keeps the pre-existing projection provenance.
    // `(defn f [g h] (let [x (gcells g)] (match h [(Box k) x])))`.
    let arm = MonoMatchArm {
        pattern: Pattern::Constructor {
            name: cranelisp_types::SymbolRef { module: None, name: Symbol::from("Box") },
            bindings: vec![Symbol::from("k")],
            span: s(),
        },
        body: var("x"),
        span: Span::new(40, 41),
        provenance: None,
        resolved_ctor: None,
    };
    let m = MonoExpr::Match {
        scrutinee: Box::new(var("h")),
        arms: vec![arm],
        span: s(),
        compiler_generated: false,
        ty: ConcreteType::String,
    };
    let outer = MonoExpr::Let {
        bindings: vec![(Symbol::from("x"), call_sp(Span::new(50, 51), "gcells", vec![var("g")]))],
        body: Box::new(m),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("g"), strparam("h")], outer, accessor_env());
    assert!(
        r.facts.provenance.values().any(|root| root.as_ref() == "g"),
        "unshadowed gcells provenance must survive"
    );
}

#[test]
fn match_whole_var_pattern_returning_scrutinee_records_scrutinee_escape() {
    // spec: §16 row 3 (0641 B-2) — the ESCAPE half of the whole-value
    // `Pattern::Var` match-var seam (S114 §9 item 5 unit pin). A scrutinee that
    // is a fresh allocation bound WHOLE by a var-pattern and flowed outward
    // escapes its frame: `(defn f [v] (match (vec-set v) [r r]))`. The scrutinee
    // is walked `Neutral` first (escape=false), then — because the var-pattern
    // `r` returns it in the escaping body ctx — RE-WALKED escaping so its
    // allocation-site escape fact is TRUE. A stale `Some(false)` here defeats the
    // backend P25 absent-default and produces the COW-var-pattern UAF the fix
    // cures (`design/typecheck/typed-resolution-carrier.md` §6). This pins the
    // transfer.rs recording seam directly — it FAILS on revert of the §16 row-3
    // scrutinee re-walk.
    let scrut_span = Span::new(10, 20);
    let arm = MonoMatchArm {
        pattern: Pattern::Var { name: Symbol::from("r"), span: s() },
        body: var("r"),
        span: Span::new(30, 31),
        provenance: None,
        resolved_ctor: None,
    };
    let m = MonoExpr::Match {
        // `vec-set` is a Fresh-result COW allocation over its first arg.
        scrutinee: Box::new(call_sp(scrut_span, "vec-set", vec![var("v")])),
        arms: vec![arm],
        span: s(),
        compiler_generated: false,
        ty: ConcreteType::String,
    };
    let env = TestEnv::default().summary(
        "vec-set",
        sm(vec![Mode::Owned], ResultMode::Fresh, vec![ParamFlow::Consumed]),
    );
    let r = run(&[strparam("v")], m, env);
    assert_eq!(
        r.facts.escapes.get(&scrut_span),
        Some(&true),
        "the whole-value var-pattern returns the scrutinee ⇒ its allocation escapes"
    );
}

#[test]
fn match_whole_var_pattern_scrutinee_not_returned_does_not_escape() {
    // spec: §16 row 3 (0641 B-2 precision twin) — the fix must NOT over-widen: a
    // var-pattern binding that is NOT flowed outward (the arm returns a fresh
    // constant, not `r`) keeps the scrutinee's escape fact FALSE.
    // `(defn f [v] (match (vec-set v) [r (other)]))`.
    let scrut_span = Span::new(10, 20);
    let arm = MonoMatchArm {
        pattern: Pattern::Var { name: Symbol::from("r"), span: s() },
        body: call("other", vec![]),
        span: Span::new(30, 31),
        provenance: None,
        resolved_ctor: None,
    };
    let m = MonoExpr::Match {
        scrutinee: Box::new(call_sp(scrut_span, "vec-set", vec![var("v")])),
        arms: vec![arm],
        span: s(),
        compiler_generated: false,
        ty: ConcreteType::String,
    };
    let env = TestEnv::default()
        .summary("vec-set", sm(vec![Mode::Owned], ResultMode::Fresh, vec![ParamFlow::Consumed]))
        .summary("other", sm(vec![], ResultMode::Fresh, vec![]));
    let r = run(&[strparam("v")], m, env);
    assert_eq!(
        r.facts.escapes.get(&scrut_span),
        Some(&false),
        "the var-pattern binding is not returned ⇒ the scrutinee does not escape"
    );
}

#[test]
fn let_shadow_drops_ambiguous_provenance() {
    // spec: §13.6(d) (blocker 3) — a let binding shadowing a live provenance
    // root makes that projection's root ambiguous ⇒ provenance None (backend
    // materializes at Decision-24). `(defn f [g] (let [x (gcells g)] (let [g (other)] x)))`.
    let env = accessor_env().summary("other", sm(vec![], ResultMode::Fresh, vec![]));
    let inner = MonoExpr::Let {
        bindings: vec![(Symbol::from("g"), call("other", vec![]))],
        body: Box::new(var("x")),
        span: s(),
        ty: ConcreteType::String,
    };
    let outer = MonoExpr::Let {
        bindings: vec![(Symbol::from("x"), call("gcells", vec![var("g")]))],
        body: Box::new(inner),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("g")], outer, env);
    // The gcells projection's provenance (root g) is dropped by the inner shadow.
    assert!(
        r.facts.provenance.values().all(|root| root.as_ref() != "g"),
        "shadowed root g must not survive as provenance"
    );
}

#[test]
fn unshadowed_projection_keeps_provenance() {
    // spec: §13.6(d) (blocker 3, precision twin) — with NO shadowing, the
    // projection provenance survives. `(defn f [g] (let [x (gcells g)] x))`.
    let outer = MonoExpr::Let {
        bindings: vec![(Symbol::from("x"), call("gcells", vec![var("g")]))],
        body: Box::new(var("x")),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("g")], outer, accessor_env());
    assert!(
        r.facts.provenance.values().any(|root| root.as_ref() == "g"),
        "unshadowed projection root g must survive"
    );
}

// =================== Projection-depth matrix ===================

/// An accessor call `(acc x)` with a ProjectionOf(0) summary.
fn accessor_env() -> TestEnv {
    TestEnv::default().summary("gcells", sm(vec![Mode::Borrowed], ResultMode::ProjectionOf(0), vec![ParamFlow::Consumed]))
}

#[test]
fn accessor_result_is_projection_rooted_in_param() {
    // spec: §4.4 — a ProjectionOf accessor result roots in the arg's root; the
    // param stays Borrowed (rc-free read path).
    let r = run(&[strparam("g")], call("gcells", vec![var("g")]), accessor_env());
    assert_eq!(r.summary.param_mode(0), Mode::Borrowed);
    assert_eq!(r.summary.result, ResultMode::ProjectionOf(0));
    // Provenance fact recorded on the accessor Apply with root `g`.
    assert!(r.facts.provenance.values().any(|v| v.as_ref() == "g"));
}

#[test]
fn chained_projection_collapses_to_one_root() {
    // spec: §4.2 rule 1 — a chained projection collapses to the single root `g`.
    // (get (gcells g))  where get: [Borrowed] -> ProjectionOf(0)
    let env = accessor_env().summary("get", sm(vec![Mode::Borrowed], ResultMode::ProjectionOf(0), vec![ParamFlow::Consumed]));
    let body = call("get", vec![call("gcells", vec![var("g")])]);
    let r = run(&[strparam("g")], body, env);
    assert_eq!(r.summary.param_mode(0), Mode::Borrowed);
    assert_eq!(r.summary.result, ResultMode::ProjectionOf(0));
}

#[test]
fn match_arm_binding_is_projection_of_scrutinee() {
    // spec: §4.2 rule 1 — a match-arm field binding is a borrowed projection
    // rooted in the scrutinee; the scrutinee param stays Borrowed.
    let arm = MonoMatchArm {
        pattern: Pattern::Constructor {
            name: cranelisp_types::SymbolRef { module: None, name: Symbol::from("Box") },
            bindings: vec![Symbol::from("inner")],
            span: s(),
        },
        body: var("inner"),
        span: s(),
        provenance: None,
        resolved_ctor: None,
    };
    let body = MonoExpr::Match {
        scrutinee: Box::new(var("p")),
        arms: vec![arm],
        span: s(),
        compiler_generated: false,
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("p")], body, TestEnv::default());
    assert_eq!(r.summary.param_mode(0), Mode::Borrowed);
    // Provenance recorded for the arm rooted in `p`.
    assert!(r.facts.provenance.values().any(|v| v.as_ref() == "p"));
}

// ===== §16 monotone provenance frame — the 0641 rule-table corrections =====

#[test]
fn row5_container_carries_element_reach_not_fresh() {
    // §16.2 row 5 (0641 B-1/I-2) — a container `[v]` (here a ConstrADT holding the
    // param `v`) has the JOIN of its element origins = `Conditional{rep:v}`, NOT
    // unconditional `Fresh`. The direct return publishes the conservative
    // `MayAliasOf(0)` (v's reference escapes inside the container). Pre-§16 this
    // laundered to `Fresh` (the anti-monotone rule).
    let r = run(&[strparam("v")], adt(vec![var("v")]), TestEnv::default());
    assert_eq!(r.summary.result, ResultMode::MayAliasOf(0));
}

#[test]
fn row5_row6_projection_out_of_container_inherits_reach() {
    // §16.2 rows 5+6 (0641 B-1) — `(vec-get [v] 0)`: the container `[v]` carries
    // v's reach (row 5, `Conditional{v}`); the projection-out (a `ProjectionOf(0)`
    // callee over that container) inherits it as a conditional projection → the
    // result is `MayAliasOf(0)`, NOT `Fresh`. Pre-§16 the container was `Fresh` so
    // the projection laundered v → `Fresh` (the freed-COW-read B-1 defect).
    let env = TestEnv::default().summary(
        "vec-get",
        sm(vec![Mode::Borrowed, Mode::Copy], ResultMode::ProjectionOf(0), vec![ParamFlow::Consumed, ParamFlow::Consumed]),
    );
    let getv = call(
        "vec-get",
        vec![adt(vec![var("v")]), MonoExpr::IntLit { value: 0, span: s(), ty: ConcreteType::Int }],
    );
    let r = run(&[strparam("v")], getv, env);
    assert_eq!(
        r.summary.result,
        ResultMode::MayAliasOf(0),
        "a projection-out of a param-carrying container inherits the reach (rows 5+6)"
    );
}

#[test]
fn row3_conditional_scrutinee_whole_var_binds_conditional_no_hard_claim() {
    // §16.2 row 3 (0641 B-2 provenance half) — `(match (cow v) [r r])` where `cow`
    // returns a COW `MayAliasOf(0)` scrutinee: the whole-value var-pattern `r`
    // binds the scrutinee's origin VERBATIM (`Conditional{v}`), so the arm body
    // `r` publishes `MayAliasOf(0)` — NEVER an unconditional hard `AliasOf`/
    // `ProjectionOf`. And NO arm provenance fact is emitted for a conditional
    // scrutinee. Pre-§16 the arm bound a hard `Projection(v)` (the narrowing).
    let env = TestEnv::default().summary(
        "cow",
        sm(vec![Mode::Borrowed], ResultMode::MayAliasOf(0), vec![ParamFlow::Consumed]),
    );
    let arm = MonoMatchArm {
        pattern: Pattern::Var { name: Symbol::from("r"), span: s() },
        body: var("r"),
        span: s(),
        provenance: None,
        resolved_ctor: None,
    };
    let body = MonoExpr::Match {
        scrutinee: Box::new(call("cow", vec![var("v")])),
        arms: vec![arm],
        span: s(),
        compiler_generated: false,
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("v")], body, env);
    assert_eq!(
        r.summary.result,
        ResultMode::MayAliasOf(0),
        "a whole-var arm on a conditional scrutinee stays conditional (no hard claim)"
    );
    assert!(
        r.facts.provenance.is_empty(),
        "a conditional (COW) scrutinee emits NO arm provenance fact (row 3)"
    );
}

#[test]
fn row7_captured_let_bound_param_alias_retains_param() {
    // §16.2 row 7 (0641 I-1) — `(let [r v] (fn [] (readonly r)))`: `r` is an
    // unconditional ALIAS of param `v` (`Unconditional{v}`), captured by an
    // escaping closure and used inside. The capture roots THROUGH the alias to v,
    // so v is retained past the enclosing frame (Owned/Retained) — NOT laundered as
    // a fresh local (the freed-heap read I-1).
    let env = TestEnv::default().summary(
        "readonly",
        sm(vec![Mode::Borrowed], ResultMode::Fresh, vec![ParamFlow::Consumed]),
    );
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("r"), var("v"))],
        body: Box::new(lambda_sp(Span::new(300, 301), vec![], call("readonly", vec![var("r")]))),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("v")], body, env);
    assert_eq!(r.summary.param_mode(0), Mode::Owned, "captured param alias retains v (I-1)");
    assert_eq!(r.summary.param_flow(0), ParamFlow::Retained, "v escapes via the capture");
}

// A COW call `(cow v)` with an explicit span (a `MayAliasOf(0)` result) — the
// scrutinee whose per-node escape fact the row-3 escape-half tests inspect.
fn cow_sp(span: Span) -> MonoExpr {
    MonoExpr::Apply {
        dispatch: cranelisp_types::ApplyRef::ViaCallee,
        callee: Box::new(var("cow")),
        args: vec![var("v")],
        span,
        resolved_call: Some(Box::new(cranelisp_types::ResolvedCall::SigDispatch {
            mangled_name: JitSymbol::from("cow"),
        })),
        ty: ConcreteType::String,
        escapes: None,
        confined: None,
        unique_static: None,
        provenance: None,
    }
}

#[test]
fn row3_escape_whole_var_arm_records_scrutinee_escape() {
    // ESCAPE half of §16 row 3 (0641 B-2) — `(match (cow v) [r r])` in tail: the
    // whole-value `r` binds the COW scrutinee and RETURNS it, so the scrutinee's
    // Apply node MUST record escapes=true. Pre-fix it stayed `Some(false)` (walked
    // `Neutral`) → the backend's ruled gate declined the inc → the match decs the
    // scrutinee while `r` returns it → UAF.
    let env = TestEnv::default().summary(
        "cow",
        sm(vec![Mode::Borrowed], ResultMode::MayAliasOf(0), vec![ParamFlow::Consumed]),
    );
    let cow_span = Span::new(500, 501);
    let arm = MonoMatchArm {
        pattern: Pattern::Var { name: Symbol::from("r"), span: s() },
        body: var("r"),
        span: s(),
        provenance: None,
        resolved_ctor: None,
    };
    let body = MonoExpr::Match {
        scrutinee: Box::new(cow_sp(cow_span)),
        arms: vec![arm],
        span: s(),
        compiler_generated: false,
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("v")], body, env);
    assert_eq!(
        r.facts.escapes.get(&cow_span),
        Some(&true),
        "the COW scrutinee escapes via the returned whole-value binding (B-2 escape half)"
    );
}

#[test]
fn row3_escape_whole_var_arm_scrutinee_stays_non_escaping_when_consumed_in_frame() {
    // The precision twin (loop/recur cells MUST NOT regress) — when the arm result
    // does NOT flow the binding outward (`r` unused, result consumed in-frame), the
    // scrutinee stays NON-escaping. Only a binding that actually escapes triggers
    // the scrutinee re-walk.
    let env = TestEnv::default().summary(
        "cow",
        sm(vec![Mode::Borrowed], ResultMode::MayAliasOf(0), vec![ParamFlow::Consumed]),
    );
    let cow_span = Span::new(510, 511);
    let arm = MonoMatchArm {
        pattern: Pattern::Var { name: Symbol::from("r"), span: s() },
        body: MonoExpr::IntLit { value: 0, span: s(), ty: ConcreteType::Int },
        span: s(),
        provenance: None,
        resolved_ctor: None,
    };
    let body = MonoExpr::Match {
        scrutinee: Box::new(cow_sp(cow_span)),
        arms: vec![arm],
        span: s(),
        compiler_generated: false,
        ty: ConcreteType::Int,
    };
    let r = run(&[strparam("v")], body, env);
    assert_eq!(
        r.facts.escapes.get(&cow_span),
        Some(&false),
        "the scrutinee stays non-escaping when the binding is consumed in-frame \
         (loop/recur must not regress)"
    );
}

#[test]
fn shadowed_root_emits_no_provenance() {
    // spec: §13.6(d) — a pattern binding shadowing the scrutinee root ⇒ None.
    // scrutinee is `p`; arm binds a field also named `p`.
    let arm = MonoMatchArm {
        pattern: Pattern::Constructor {
            name: cranelisp_types::SymbolRef { module: None, name: Symbol::from("Box") },
            bindings: vec![Symbol::from("p")],
            span: s(),
        },
        body: var("p"),
        span: s(),
        provenance: None,
        resolved_ctor: None,
    };
    let body = MonoExpr::Match {
        scrutinee: Box::new(var("p")),
        arms: vec![arm],
        span: s(),
        compiler_generated: false,
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("p")], body, TestEnv::default());
    // No provenance fact for the shadowed arm.
    assert!(r.facts.provenance.is_empty());
}

// ============ Result-mode partial-param-return matrix (FIXME 0520) ============
//
// The ABI-half soundness cure: a param returned through a PARTIAL control-flow
// path (some but not all return arms yield the param) must NOT collapse to
// `Fresh` (which permits the borrow-elision consumer to drop a needed RC op and
// free the returned param → UAF). `Fresh` is reserved for
// provably-no-param-reaches-result. Each cell asserts the exact `ResultMode`,
// and the regression pins guard against OVER-widening a genuinely-fresh result
// (which would keep an unneeded inc → leak). See §4.2 / §13.6(c) as-corrected.

/// An `if` with a `BoolLit` cond over the two given branches.
fn if_(then_branch: MonoExpr, else_branch: MonoExpr) -> MonoExpr {
    MonoExpr::If {
        cond: Box::new(MonoExpr::BoolLit { value: true, span: s(), ty: ConcreteType::Bool }),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
        span: s(),
        ty: ConcreteType::String,
    }
}

#[test]
fn partial_if_one_arm_param_other_fresh_is_alias_not_fresh() {
    // spec: §4.2/§13.6(c) (FIXME 0520) — THE bug. `(if c p (other))` returns
    // param p in the then-arm, a fresh value in the else-arm. Pre-cure this
    // collapsed to `Fresh` (UNSOUND: p may be returned yet the consumer elides
    // its protect). Truth: may-alias param 0 ⇒ MayAliasOf(0), not Fresh (S111
    // §3.7/§15.3 — a may-origin publishes MayAliasOf; AliasOf is reserved for
    // provable UNCONDITIONAL claims).
    let env = TestEnv::default().summary("other", sm(vec![], ResultMode::Fresh, vec![]));
    let body = if_(var("p"), call("other", vec![]));
    let r = run(&[strparam("p")], body, env);
    assert_eq!(r.summary.result, ResultMode::MayAliasOf(0), "partial param-return must be MayAliasOf(0), not Fresh");
}

#[test]
fn nested_partial_if_param_reaches_is_alias_not_fresh() {
    // spec: §4.2 (FIXME 0520, nested-control-flow sibling) —
    // `(if c1 (if c2 p (other)) (other))`. The param reaches through a nested
    // branch; every join level must preserve the may-alias, never collapse Fresh.
    let env = TestEnv::default().summary("other", sm(vec![], ResultMode::Fresh, vec![]));
    let inner = if_(var("p"), call("other", vec![]));
    let body = if_(inner, call("other", vec![]));
    let r = run(&[strparam("p")], body, env);
    assert_eq!(r.summary.result, ResultMode::MayAliasOf(0), "param reaching through nested if must be MayAliasOf(0)");
}

#[test]
fn let_bound_alias_returned_partially_is_alias_not_fresh() {
    // spec: §4.2 (FIXME 0520, let-alias sibling) —
    // `(let [w p] (if c w (other)))`. `w` aliases param p; returning it on one
    // arm must yield AliasOf(0) — provenance carries through the let alias.
    let env = TestEnv::default().summary("other", sm(vec![], ResultMode::Fresh, vec![]));
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("w"), var("p"))],
        body: Box::new(if_(var("w"), call("other", vec![]))),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("p")], body, env);
    assert_eq!(r.summary.result, ResultMode::MayAliasOf(0), "let-aliased partial param-return must be MayAliasOf(0)");
}

#[test]
fn partial_match_some_arms_param_others_fresh_is_alias_not_fresh() {
    // spec: §4.2 (FIXME 0520, match sibling) — one arm returns the scrutinee
    // param `p`, the other returns fresh ⇒ may-alias param 0, not Fresh.
    // `(match p [(Box _k) (other)] [_ p])` — arm 1 fresh, arm 2 returns p.
    let env = TestEnv::default().summary("other", sm(vec![], ResultMode::Fresh, vec![]));
    let arm1 = MonoMatchArm {
        pattern: Pattern::Constructor {
            name: cranelisp_types::SymbolRef { module: None, name: Symbol::from("Box") },
            bindings: vec![Symbol::from("k")],
            span: s(),
        },
        body: call("other", vec![]),
        span: Span::new(90, 91),
        provenance: None,
        resolved_ctor: None,
    };
    let arm2 = MonoMatchArm {
        pattern: Pattern::Wildcard { span: s() },
        body: var("p"),
        span: Span::new(92, 93),
        provenance: None,
        resolved_ctor: None,
    };
    let body = MonoExpr::Match {
        scrutinee: Box::new(var("p")),
        arms: vec![arm1, arm2],
        span: s(),
        compiler_generated: false,
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("p")], body, env);
    assert_eq!(r.summary.result, ResultMode::MayAliasOf(0), "match with one param-returning arm must be MayAliasOf(0)");
}

#[test]
fn partial_if_projection_arm_is_projection_not_fresh() {
    // spec: §4.2 (FIXME 0520, projection sibling) —
    // `(if c (gcells p) (other))`. One arm is a borrowed VIEW of param p
    // (ProjectionOf), the other fresh ⇒ may-projection. Per S111 §15.3 BOTH
    // may-arms (projection:false AND projection:true) publish MayAliasOf — a
    // conditional claim, keeping protect, never the unconditional ProjectionOf
    // (a Fresh here would dec the borrowed field as a temp → double-free).
    let env = accessor_env().summary("other", sm(vec![], ResultMode::Fresh, vec![]));
    let body = if_(call("gcells", vec![var("p")]), call("other", vec![]));
    let r = run(&[strparam("p")], body, env);
    assert_eq!(r.summary.result, ResultMode::MayAliasOf(0), "partial projection-return is a conditional claim ⇒ MayAliasOf(0)");
}

#[test]
fn multi_distinct_param_return_is_not_fresh() {
    // spec: §4.2 (FIXME 0520, multi-param sibling) — `(if c v w)` may return
    // EITHER param. The existing lattice cannot name "may alias 0 or 1"; the
    // sound conservative choice is a may-alias on the lowest reaching index
    // (MayAliasOf(0)) — any not-`Fresh` value keeps the consumer's protect
    // (binary read). Strictly more sound than the pre-cure `Fresh` (which elided
    // protect on a returned param).
    let body = if_(var("v"), var("w"));
    let r = run(&[strparam("v"), strparam("w")], body, TestEnv::default());
    assert_ne!(r.summary.result, ResultMode::Fresh, "multi-distinct-param return must not be Fresh");
    assert_eq!(r.summary.result, ResultMode::MayAliasOf(0), "conservative representative is the lowest reaching index");
}

// ---- regression pins: the definite cases must stay precise (no OVER-widen) ----

#[test]
fn full_if_both_arms_same_param_is_alias() {
    // spec: §4.2 (0520 regression pin) — `(if c v v)`: both arms return the SAME
    // param ⇒ the DEFINITE AliasOf, unchanged by the cure (v is param 1 here).
    let body = if_(var("v"), var("v"));
    let r = run(&[strparam("b"), strparam("v")], body, TestEnv::default());
    assert_eq!(r.summary.result, ResultMode::AliasOf(1), "full-if same-param stays the precise AliasOf(1)");
}

#[test]
fn both_arms_fresh_stays_fresh_no_over_widen() {
    // spec: §4.2 (0520 OVER-widen guard) — `(if c (other) (other))`: NEITHER arm
    // carries a param ⇒ the result is genuinely `Fresh`. The cure must NOT widen
    // a provably-fresh result to not-`Fresh` (that would keep an unneeded inc →
    // leak). `Fresh` is reserved for provably-no-param-reaches-result.
    let env = TestEnv::default().summary("other", sm(vec![], ResultMode::Fresh, vec![]));
    let body = if_(call("other", vec![]), call("other", vec![]));
    let r = run(&[strparam("p")], body, env);
    assert_eq!(r.summary.result, ResultMode::Fresh, "both-fresh must stay Fresh (no over-widen)");
}

#[test]
fn direct_apply_alias_composition_unchanged() {
    // spec: §4.2 (0520 regression pin) — `(idv v)` where idv: AliasOf(0). A
    // direct Apply body composes the callee result: v (param) flows through ⇒
    // AliasOf(0). The cure preserves this (the fixpoint composes Apply results).
    let env = TestEnv::default().summary("idv", sm(vec![Mode::Owned], ResultMode::AliasOf(0), vec![ParamFlow::IntoResult]));
    let r = run(&[strparam("v")], call("idv", vec![var("v")]), env);
    assert_eq!(r.summary.result, ResultMode::AliasOf(0), "direct-Apply AliasOf composition stays AliasOf(0)");
}

#[test]
fn apply_alias_of_fresh_arg_stays_fresh_no_over_widen() {
    // spec: §4.2 (0520 OVER-widen guard, composition) — `(idv (other))`: idv
    // returns AliasOf(0) but the arg is a FRESH value ⇒ the result is genuinely
    // fresh. Carrying the arg origin through must keep `Fresh` (a not-Fresh here
    // would keep an unneeded inc on a fresh temporary → leak, and move codegen).
    let env = TestEnv::default()
        .summary("idv", sm(vec![Mode::Owned], ResultMode::AliasOf(0), vec![ParamFlow::IntoResult]))
        .summary("other", sm(vec![], ResultMode::Fresh, vec![]));
    let r = run(&[strparam("p")], call("idv", vec![call("other", vec![])]), env);
    assert_eq!(r.summary.result, ResultMode::Fresh, "AliasOf of a fresh arg stays Fresh (no over-widen)");
}

// spec: design/arch/ownership-inference.md §3.7/§15.4 — the MayAliasOf CONSUMER
// arm (the compiler-forced exhaustive match). `(defn f [v x] (vec-set v 0 x))`
// where vec-set is summarised MayAliasOf(0): the result is EITHER fresh OR
// param 0's vec, decided at runtime. Composing through the Apply must keep the
// result NOT-Fresh (join Fresh with the param-reaching arg's origin ⇒ MayParam
// ⇒ MayAliasOf(0)) — so an enclosing fn returning it keeps its protect (the
// vec-assoc COW-return-through-an-Apply-body soundness cure).
#[test]
fn apply_may_alias_of_param_arg_is_may_alias_not_fresh() {
    let env = TestEnv::default().summary(
        "vec-set",
        sm(vec![Mode::Owned, Mode::Copy, Mode::Owned], ResultMode::MayAliasOf(0),
           vec![ParamFlow::Consumed, ParamFlow::Consumed, ParamFlow::IntoResult]),
    );
    let body = call("vec-set", vec![var("v"), var("i"), var("x")]);
    let r = run(&[strparam("v"), intparam("i"), strparam("x")], body, env);
    assert_eq!(
        r.summary.result,
        ResultMode::MayAliasOf(0),
        "MayAliasOf result of a param-reaching arg composes to MayAliasOf(0), never Fresh"
    );
}

// spec: §3.7/§15.4 — the MayAliasOf consumer arm with a FRESH arg. `(vec-set
// (fresh) 0 x)`: param 0 is a fresh temporary, so the result cannot reach any
// of THIS body's params ⇒ genuinely Fresh (join Fresh with a Fresh arg ⇒ Fresh).
// The may-alias never over-widens a fresh source.
#[test]
fn apply_may_alias_of_fresh_arg_stays_fresh() {
    let env = TestEnv::default()
        .summary("vec-set", sm(vec![Mode::Owned, Mode::Copy, Mode::Owned], ResultMode::MayAliasOf(0),
            vec![ParamFlow::Consumed, ParamFlow::Consumed, ParamFlow::IntoResult]))
        .summary("fresh", sm(vec![], ResultMode::Fresh, vec![]));
    let body = call("vec-set", vec![call("fresh", vec![]), var("i"), var("x")]);
    let r = run(&[intparam("i"), strparam("x")], body, env);
    assert_eq!(r.summary.result, ResultMode::Fresh, "MayAliasOf of a fresh source stays Fresh (no over-widen)");
}

// =================== Lexical-scope discipline (F4) ===================

#[test]
fn branch_sibling_shadow_does_not_narrow_param_shadow_first() {
    // spec: §13.6(i) (F4) — the load-bearing ABI-soundness cell. A param `a`
    // shadowed by an inner `let` in the THEN branch (walked first) must NOT leak
    // its inner `BindState` into the ELSE branch, where the bare `(consume a)`
    // means the PARAM. Without scope discipline the walker reads the stale inner
    // `Projection(g)` state, `param_root(a)` misses param 0, and `param_modes[0]`
    // narrows Owned→Borrowed (the UNSOUND direction on the ABI-bearing half).
    // `(defn f [a g] (if c (let [a (gcells g)] a) (consume a)))`.
    let env = accessor_env()
        .summary("consume", sm(vec![Mode::Owned], ResultMode::Fresh, vec![ParamFlow::Consumed]));
    let then_branch = MonoExpr::Let {
        bindings: vec![(Symbol::from("a"), call("gcells", vec![var("g")]))],
        body: Box::new(var("a")),
        span: s(),
        ty: ConcreteType::String,
    };
    let body = MonoExpr::If {
        cond: Box::new(MonoExpr::BoolLit { value: true, span: s(), ty: ConcreteType::Bool }),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(call("consume", vec![var("a")])),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("a"), strparam("g")], body, env);
    // The param `a` is consumed (Owned) in the else branch — truth is Owned.
    assert_eq!(r.summary.param_mode(0), Mode::Owned, "param a must widen to Owned in the sibling branch");
}

#[test]
fn branch_sibling_shadow_does_not_narrow_param_use_first() {
    // spec: §13.6(i) (F4) — the both-orderings twin. Shadow in the ELSE branch,
    // param use in the THEN branch (walked first). The cure must fix BOTH
    // orderings; this ordering happens to widen under the pre-cure walker (use
    // precedes shadow), so it is a regression guard the scope discipline must
    // not break. `(defn f [a g] (if c (consume a) (let [a (gcells g)] a)))`.
    let env = accessor_env()
        .summary("consume", sm(vec![Mode::Owned], ResultMode::Fresh, vec![ParamFlow::Consumed]));
    let else_branch = MonoExpr::Let {
        bindings: vec![(Symbol::from("a"), call("gcells", vec![var("g")]))],
        body: Box::new(var("a")),
        span: s(),
        ty: ConcreteType::String,
    };
    let body = MonoExpr::If {
        cond: Box::new(MonoExpr::BoolLit { value: true, span: s(), ty: ConcreteType::Bool }),
        then_branch: Box::new(call("consume", vec![var("a")])),
        else_branch: Box::new(else_branch),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("a"), strparam("g")], body, env);
    assert_eq!(r.summary.param_mode(0), Mode::Owned, "param a must stay Owned regardless of branch order");
}

#[test]
fn match_arm_binding_does_not_leak_past_arm() {
    // spec: §13.6(i) (F4, match-arm-leak half) — a pattern binding shadowing a
    // param must NOT leak into a sibling arm. Arm 1 binds field `a` (a borrowed
    // projection of scrutinee `h`); arm 2's `(consume a)` means the PARAM `a`.
    // Without a per-arm scope frame the leaked arm-1 `Projection(h)` state makes
    // `param_root(a)` miss param 0 ⇒ `param_modes[0]` narrows below truth.
    // `(defn f [a h] (match h [(Box a) a] [_ (consume a)]))`.
    let env = TestEnv::default()
        .summary("consume", sm(vec![Mode::Owned], ResultMode::Fresh, vec![ParamFlow::Consumed]));
    let arm1 = MonoMatchArm {
        pattern: Pattern::Constructor {
            name: cranelisp_types::SymbolRef { module: None, name: Symbol::from("Box") },
            bindings: vec![Symbol::from("a")],
            span: s(),
        },
        body: var("a"),
        span: Span::new(60, 61),
        provenance: None,
        resolved_ctor: None,
    };
    let arm2 = MonoMatchArm {
        pattern: Pattern::Wildcard { span: s() },
        body: call("consume", vec![var("a")]),
        span: Span::new(62, 63),
        provenance: None,
        resolved_ctor: None,
    };
    let body = MonoExpr::Match {
        scrutinee: Box::new(var("h")),
        arms: vec![arm1, arm2],
        span: s(),
        compiler_generated: false,
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("a"), strparam("h")], body, env);
    assert_eq!(r.summary.param_mode(0), Mode::Owned, "param a must widen to Owned in the sibling arm");
}

// =================== Negatives ===================

// ============ Closure / spark capture as an escape edge (FIXME 0523) ============
//
// R6: capture (closure capture, suspension capture) IS an escape edge. A value
// captured by a closure that escapes the frame escapes — INDEPENDENT of how the
// value is used inside the closure body. The pre-cure walker propagated escape
// through the closure body's OUTER context only; a capture used as a Borrowed
// argument (or any non-escaping sub-position) inside the escaping closure lost
// its escape edge (a hard UAF at the B3.4 stack-alloc consumer). Each cell pins
// the SPECIFIC escape site fact / param mode; the over-widen twins pin that a
// genuinely-non-escaping capture stays Some(false).

/// A lambda `(fn params body)` with an explicit span.
fn lambda_sp(span: Span, params: Vec<&str>, body: MonoExpr) -> MonoExpr {
    MonoExpr::Lambda {
        params: params.into_iter().map(Symbol::from).collect(),
        body: Box::new(body),
        span,
        ty: ConcreteType::Fn(vec![], Box::new(ConcreteType::String)),
        escapes: None,
        confined: None,
        unique_static: None,
    }
}

#[test]
fn intra_direct_closure_capture_of_local_escapes() {
    // spec: R6 — `(defn f [x] (let [r (Box x)] (fn [] r)))`. The local `r`
    // (a fresh aggregate) is captured by the RETURNED closure ⇒ escapes. The
    // Box construction's escape site fact must be true.
    let box_span = Span::new(100, 101);
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("r"), adt_sp(box_span, vec![var("x")]))],
        body: Box::new(lambda_sp(Span::new(102, 103), vec![], var("r"))),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("x")], body, TestEnv::default());
    assert_eq!(r.facts.escapes.get(&box_span), Some(&true), "captured local aggregate escapes");
    // x is folded into the escaping aggregate ⇒ Owned/Retained.
    assert_eq!(r.summary.param_mode(0), Mode::Owned);
    assert_eq!(r.summary.param_flow(0), ParamFlow::Retained);
}

#[test]
fn intra_closure_capture_through_borrow_arg_escapes() {
    // spec: R6 (THE gap) — `(defn f [x] (let [r (Box x)] (fn [] (readonly r))))`.
    // The captured local `r` is used as a BORROWED argument inside the escaping
    // closure. The pre-cure walker reset the context to Arg{Borrowed} at the
    // apply and LOST the capture escape ⇒ `r`'s aggregate marked escapes=false
    // (the hard UAF). Truth: capture escapes regardless of use-position.
    let box_span = Span::new(110, 111);
    let env = TestEnv::default().summary(
        "readonly",
        sm(vec![Mode::Borrowed], ResultMode::Fresh, vec![ParamFlow::Consumed]),
    );
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("r"), adt_sp(box_span, vec![var("x")]))],
        body: Box::new(lambda_sp(Span::new(112, 113), vec![], call("readonly", vec![var("r")]))),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("x")], body, env);
    assert_eq!(
        r.facts.escapes.get(&box_span),
        Some(&true),
        "a capture used as a Borrowed arg inside an escaping closure still escapes"
    );
}

#[test]
fn intra_closure_capture_of_param_widens_owned_retained() {
    // spec: R6 — `(defn f [x] (fn [] (readonly x)))`. The param `x` is captured
    // by the returned closure and used borrowed inside ⇒ escapes ⇒ Owned/Retained
    // (so a caller passing a fresh value sees the escape at the call site).
    let env = TestEnv::default().summary(
        "readonly",
        sm(vec![Mode::Borrowed], ResultMode::Fresh, vec![ParamFlow::Consumed]),
    );
    let body = lambda_sp(Span::new(120, 121), vec![], call("readonly", vec![var("x")]));
    let r = run(&[strparam("x")], body, env);
    assert_eq!(r.summary.param_mode(0), Mode::Owned, "captured param widens Owned");
    assert_eq!(r.summary.param_flow(0), ParamFlow::Retained, "captured param is Retained");
}

#[test]
fn inter_procedural_capture_via_callee_summary_escapes() {
    // spec: R6 inter-procedural — `(defn f [x] (make-clo (Box x)))` where
    // `make-clo` captures its param into a returned closure (summary: param0
    // Owned/Retained). `f` has NO closure form of its own; the escape must ride
    // the callee summary — a fresh value passed at the capturing position escapes.
    let box_span = Span::new(130, 131);
    let env = TestEnv::default().summary(
        "make-clo",
        sm(vec![Mode::Owned], ResultMode::Fresh, vec![ParamFlow::Retained]),
    );
    let body = call("make-clo", vec![adt_sp(box_span, vec![var("x")])]);
    let r = run(&[strparam("x")], body, env);
    assert_eq!(
        r.facts.escapes.get(&box_span),
        Some(&true),
        "a fresh value passed to a capturing callee param escapes at the call site"
    );
}

#[test]
fn make_clo_infers_captured_param_owned_retained() {
    // spec: R6 — the producer half of the inter-procedural loop. `make-clo`'s
    // body `(fn [] x)` captures param x into the returned closure ⇒ the inferred
    // summary MUST be Owned/Retained (this is the fact the caller above consumes).
    let body = lambda_sp(Span::new(140, 141), vec![], var("x"));
    let r = run(&[strparam("x")], body, TestEnv::default());
    assert_eq!(r.summary.param_mode(0), Mode::Owned, "make-clo param is Owned");
    assert_eq!(r.summary.param_flow(0), ParamFlow::Retained, "make-clo param is Retained");
}

#[test]
fn nested_closure_capture_escapes() {
    // spec: R6 nested — `(defn f [x] (let [r (Box x)] (fn [] (fn [] r))))`. `r`
    // is captured by an inner closure that is itself captured/returned by the
    // outer escaping closure. Transitive capture ⇒ `r` escapes.
    let box_span = Span::new(150, 151);
    let inner = lambda_sp(Span::new(152, 153), vec![], var("r"));
    let outer = lambda_sp(Span::new(154, 155), vec![], inner);
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("r"), adt_sp(box_span, vec![var("x")]))],
        body: Box::new(outer),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("x")], body, TestEnv::default());
    assert_eq!(r.facts.escapes.get(&box_span), Some(&true), "nested-captured local escapes");
}

#[test]
fn suspension_capture_through_borrow_arg_escapes() {
    // spec: R6 — `LaunchContinue.launched` is a suspension escape edge. A capture
    // used borrowed inside the launched expression still escapes (same gap as the
    // closure body). `launched = (readonly r)` where r is a fresh local aggregate.
    let box_span = Span::new(160, 161);
    let env = TestEnv::default().summary(
        "readonly",
        sm(vec![Mode::Borrowed], ResultMode::Fresh, vec![ParamFlow::Consumed]),
    );
    let launched = call("readonly", vec![var("r")]);
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("r"), adt_sp(box_span, vec![var("x")]))],
        body: Box::new(MonoExpr::LaunchContinue {
            launched: Box::new(launched),
            continuation: Box::new(MonoExpr::IntLit { value: 0, span: s(), ty: ConcreteType::Int }),
            span: s(),
            ty: ConcreteType::Int,
        }),
        span: s(),
        ty: ConcreteType::Int,
    };
    let r = run(&[strparam("x")], body, env);
    assert_eq!(
        r.facts.escapes.get(&box_span),
        Some(&true),
        "a capture used borrowed in a suspension edge still escapes"
    );
}

// ---- over-widen regression pins: a non-escaping capture stays Some(false) ----

#[test]
fn non_escaping_local_lambda_does_not_escape_capture() {
    // spec: R6 (precision pin) — `(defn f [x] (let [r (Box x)] (let [c (fn [] r)] 0)))`.
    // The closure `c` is bound but NEVER escapes (the body returns 0). `r` must
    // stay escapes=false and `x` stay Consumed — the fix must not widen EVERY
    // capture (that would defeat stack allocation entirely).
    let box_span = Span::new(170, 171);
    let inner = MonoExpr::Let {
        bindings: vec![(Symbol::from("c"), lambda_sp(Span::new(172, 173), vec![], var("r")))],
        body: Box::new(MonoExpr::IntLit { value: 0, span: s(), ty: ConcreteType::Int }),
        span: s(),
        ty: ConcreteType::Int,
    };
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("r"), adt_sp(box_span, vec![var("x")]))],
        body: Box::new(inner),
        span: s(),
        ty: ConcreteType::Int,
    };
    let r = run(&[strparam("x")], body, TestEnv::default());
    assert_eq!(
        r.facts.escapes.get(&box_span),
        Some(&false),
        "a capture by a NON-escaping local closure does not escape (precision)"
    );
    assert_eq!(r.summary.param_flow(0), ParamFlow::Consumed, "x stays Consumed (no over-widen)");
}

#[test]
fn lambda_param_shadows_capture_no_spurious_escape() {
    // spec: R6 (precision pin) — a lambda's OWN param is not a capture. In
    // `(defn f [x] (fn [r] (readonly r)))` the `r` used inside is the lambda's
    // param, NOT the enclosing scope — there is no capture of any enclosing local,
    // so `x` (unused) must stay Borrowed. (The lambda escapes, but captures nothing.)
    let env = TestEnv::default().summary(
        "readonly",
        sm(vec![Mode::Borrowed], ResultMode::Fresh, vec![ParamFlow::Consumed]),
    );
    let body = lambda_sp(Span::new(180, 181), vec!["r"], call("readonly", vec![var("r")]));
    let r = run(&[strparam("x")], body, env);
    assert_eq!(
        r.summary.param_mode(0),
        Mode::Borrowed,
        "an unused enclosing param stays Borrowed — lambda param r is not a capture"
    );
}

// ===== Lambda / HOF body-return escape edge (FIXME 0524) =====
//
// A lambda body is its OWN frame: any allocation reaching the lambda's
// tail/return position escapes the LAMBDA frame — the lambda WILL be called
// (that is why it is a value) and its result outlives its frame, exactly as a
// named `defn`'s returned allocation does. The cluster-centric pre-cure walked
// an anonymous lambda body in the ENCLOSING frame's context: a lambda whose
// VALUE does not escape (bound-and-discarded, or a Borrowed arg to a HOF) had
// its returned `(Some y)` marked `escapes=Some(false)` (Neutral) — a hard UAF at
// the B3.4 stack-alloc consumer. Each cell pins the body-return allocation's
// escape fact; the over-widen pins keep the closure VALUE non-escape and a
// captured enclosing local in-frame (B3.4's win). These are the crate-side
// (classifier-output) reproductions of the three e2e regressions the FIXME names
// (`constructor_wrapped_in_lambda_applied_indirectly_works`,
// `polymorphic_higher_order_returning_adt`, `nested_match_in_arm_body`).

fn int_lit(value: i64) -> MonoExpr {
    MonoExpr::IntLit { value, span: s(), ty: ConcreteType::Int }
}

/// A `VecLit` with an explicit span.
fn vec_sp(span: Span, elements: Vec<MonoExpr>) -> MonoExpr {
    MonoExpr::VecLit { elements, span, ty: ConcreteType::String, escapes: None, confined: None, unique_static: None }
}

#[test]
fn lambda_body_return_constructor_escapes_when_value_discarded() {
    // spec: §13.6(k) (FIXME 0524, edge 2 — direct lambda body-return). A lambda
    // bound-and-discarded (its VALUE does not escape) STILL has its body-return
    // `(Some y)` escape the lambda frame. Pre-cure: Neutral ⇒ escapes=false (UAF).
    // `(defn f [] (let [c (fn [y] (Some y))] 0))`.
    let some_span = Span::new(200, 201);
    let lam_span = Span::new(202, 203);
    let lambda = lambda_sp(lam_span, vec!["y"], adt_sp(some_span, vec![var("y")]));
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("c"), lambda)],
        body: Box::new(int_lit(0)),
        span: s(),
        ty: ConcreteType::Int,
    };
    let r = run(&[], body, TestEnv::default());
    assert_eq!(
        r.facts.escapes.get(&some_span),
        Some(&true),
        "the lambda body-return constructor escapes the lambda frame (edge 2)"
    );
    // The closure VALUE itself does not escape the enclosing frame (discarded).
    assert_eq!(
        r.facts.escapes.get(&lam_span),
        Some(&false),
        "the closure value does not escape (bound-and-discarded)"
    );
}

#[test]
fn lambda_body_return_via_hof_borrowed_arg_escapes() {
    // spec: §13.6(k) (FIXME 0524, edge 4 — HOF-mediated flow; THE
    // `constructor_wrapped_in_lambda_applied_indirectly_works` shape). The lambda
    // flows to a HOF that BORROWS it (`apply-it`'s f param is Borrowed) and returns
    // its result — `(Some y)` flows lambda-return → HOF-return → caller. The escape
    // is intrinsic to the lambda body-return (edge 2); it needs NO new HOF-flow
    // carrier — `apply-it` returning `(f x)` merely propagates an already-escaping
    // allocation. `(apply-it (fn [y] (Some y)) 7)`.
    let some_span = Span::new(210, 211);
    let lam_span = Span::new(212, 213);
    let env = TestEnv::default().summary(
        "apply-it",
        sm(vec![Mode::Borrowed, Mode::Copy], ResultMode::Fresh, vec![ParamFlow::Consumed, ParamFlow::Consumed]),
    );
    let lambda = lambda_sp(lam_span, vec!["y"], adt_sp(some_span, vec![var("y")]));
    let body = call("apply-it", vec![lambda, int_lit(7)]);
    let r = run(&[], body, env);
    assert_eq!(
        r.facts.escapes.get(&some_span),
        Some(&true),
        "the constructor returned through a borrowing HOF escapes (edge 4 rides edge 2)"
    );
    assert_eq!(
        r.facts.escapes.get(&lam_span),
        Some(&false),
        "the closure value is only Borrowed by the HOF — it does not escape"
    );
}

#[test]
fn lambda_body_return_veclit_escapes() {
    // spec: §13.6(k) (FIXME 0524, edge 2 — VecLit body-return). Any fresh
    // allocation at the lambda tail escapes, not only ADTs. `(fn [y] [y])` passed
    // Borrowed to a HOF ⇒ the VecLit escapes the lambda frame.
    let vec_span = Span::new(220, 221);
    let env = TestEnv::default().summary(
        "apply-it",
        sm(vec![Mode::Borrowed, Mode::Copy], ResultMode::Fresh, vec![ParamFlow::Consumed, ParamFlow::Consumed]),
    );
    let lambda = lambda_sp(Span::new(222, 223), vec!["y"], vec_sp(vec_span, vec![var("y")]));
    let body = call("apply-it", vec![lambda, int_lit(7)]);
    let r = run(&[], body, env);
    assert_eq!(r.facts.escapes.get(&vec_span), Some(&true), "the lambda body-return VecLit escapes");
}

#[test]
fn lambda_body_return_through_let_tail_escapes() {
    // spec: §13.6(k) (FIXME 0524, edge 2 through a lambda-LOCAL let). A fresh
    // aggregate bound to a lambda-local `let` and returned from the lambda tail
    // escapes the lambda frame: the lambda-local binding drains WITHIN the body
    // (its own `Let` scope runs during the isolated body walk).
    // `(fn [w] (let [z (Some w)] z))` bound-and-discarded.
    let some_span = Span::new(230, 231);
    let inner_let = MonoExpr::Let {
        bindings: vec![(Symbol::from("z"), adt_sp(some_span, vec![var("w")]))],
        body: Box::new(var("z")),
        span: s(),
        ty: ConcreteType::String,
    };
    let lambda = lambda_sp(Span::new(232, 233), vec!["w"], inner_let);
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("c"), lambda)],
        body: Box::new(int_lit(0)),
        span: s(),
        ty: ConcreteType::Int,
    };
    let r = run(&[], body, TestEnv::default());
    assert_eq!(
        r.facts.escapes.get(&some_span),
        Some(&true),
        "a lambda-local let-bound aggregate returned from the lambda tail escapes"
    );
}

#[test]
fn lambda_body_return_in_match_arm_escapes() {
    // spec: §13.6(k) (FIXME 0524, edge 7 — constructor in a match arm returned
    // from a lambda). `(fn [h] (match h [(Box k) (Some k)]))` passed Borrowed to a
    // HOF ⇒ the `(Some k)` arm result escapes the lambda frame.
    let some_span = Span::new(240, 241);
    let arm = MonoMatchArm {
        pattern: Pattern::Constructor {
            name: cranelisp_types::SymbolRef { module: None, name: Symbol::from("Box") },
            bindings: vec![Symbol::from("k")],
            span: s(),
        },
        body: adt_sp(some_span, vec![var("k")]),
        span: Span::new(242, 243),
        provenance: None,
        resolved_ctor: None,
    };
    let m = MonoExpr::Match {
        scrutinee: Box::new(var("h")),
        arms: vec![arm],
        span: s(),
        compiler_generated: false,
        ty: ConcreteType::String,
    };
    let env = TestEnv::default().summary(
        "apply-it",
        sm(vec![Mode::Borrowed, Mode::Copy], ResultMode::Fresh, vec![ParamFlow::Consumed, ParamFlow::Consumed]),
    );
    let lambda = lambda_sp(Span::new(244, 245), vec!["h"], m);
    let body = call("apply-it", vec![lambda, int_lit(7)]);
    let r = run(&[], body, env);
    assert_eq!(
        r.facts.escapes.get(&some_span),
        Some(&true),
        "a constructor in a match arm returned from a lambda escapes (edge 7)"
    );
}

#[test]
fn nested_lambda_body_return_alloc_escapes() {
    // spec: §13.6(k) (FIXME 0524, edge 7 — a lambda returning a lambda whose body
    // constructs). `(fn [] (fn [y] (Some y)))` bound-and-discarded. The OUTER
    // lambda is non-escaping (isolated Return walk); the INNER lambda's value is at
    // the outer tail (Return.escapes()==true ⇒ escaping branch), and its body
    // `(Some y)` escapes. The inner constructor must escape at BOTH levels.
    let some_span = Span::new(250, 251);
    let inner = lambda_sp(Span::new(252, 253), vec!["y"], adt_sp(some_span, vec![var("y")]));
    let outer = lambda_sp(Span::new(254, 255), vec![], inner);
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("c"), outer)],
        body: Box::new(int_lit(0)),
        span: s(),
        ty: ConcreteType::Int,
    };
    let r = run(&[], body, TestEnv::default());
    assert_eq!(
        r.facts.escapes.get(&some_span),
        Some(&true),
        "the inner lambda's body-return constructor escapes (nested composition)"
    );
}

// ---- over-widen regression pins: the non-escaping / no-outflow cases stay false ----

#[test]
fn non_escaping_lambda_returning_captured_local_stays_in_frame() {
    // spec: §13.6(k) (FIXME 0524, precision pin — the isolated-worklist guard). A
    // NON-escaping lambda whose body returns a CAPTURED enclosing fresh local must
    // NOT escape that local — the lambda body-return rule escapes allocations
    // CREATED in the body, not enclosing captures (capture-escape is gated on the
    // lambda VALUE escaping, §13.6(j)). `(defn f [x] (let [r (Box x)] (let [c (fn [] r)] 0)))`
    // is the existing `non_escaping_local_lambda_does_not_escape_capture` shape; this
    // twin pins the DIRECT-tail return of the capture and the param staying in-frame.
    let box_span = Span::new(260, 261);
    let lambda = lambda_sp(Span::new(262, 263), vec![], var("r")); // returns captured `r`
    let inner = MonoExpr::Let {
        bindings: vec![(Symbol::from("c"), lambda)],
        body: Box::new(int_lit(0)),
        span: s(),
        ty: ConcreteType::Int,
    };
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("r"), adt_sp(box_span, vec![var("x")]))],
        body: Box::new(inner),
        span: s(),
        ty: ConcreteType::Int,
    };
    let r = run(&[strparam("x")], body, TestEnv::default());
    assert_eq!(
        r.facts.escapes.get(&box_span),
        Some(&false),
        "a captured enclosing local returned from a NON-escaping lambda stays in-frame"
    );
    assert_eq!(r.summary.param_flow(0), ParamFlow::Consumed, "x stays Consumed (no over-widen through the isolated frame)");
}

#[test]
fn lambda_body_return_scalar_no_spurious_escape() {
    // spec: §13.6(k) (FIXME 0524, no-outflow pin). A lambda whose body returns a
    // scalar/param (no allocation created in the body) produces NO escape=true
    // fact — the body-return rule only fires on genuine allocation sites.
    // `(fn [y] y)` bound-and-discarded.
    let lambda = lambda_sp(Span::new(270, 271), vec!["y"], var("y"));
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("c"), lambda)],
        body: Box::new(int_lit(0)),
        span: s(),
        ty: ConcreteType::Int,
    };
    let r = run(&[], body, TestEnv::default());
    assert!(
        r.facts.escapes.values().all(|v| !*v),
        "a lambda returning a bare param allocates nothing that escapes"
    );
}

#[test]
fn named_fn_return_edge_reconfirmed_after_0524() {
    // spec: §13.6(k) (FIXME 0524, edge 1 re-confirm). The named-fn return edge is
    // unchanged by the lambda-body-return cure: a constructor returned from the
    // top-level body still escapes and the folded param is IntoResult.
    // `(defn keep [x] (Box x))`.
    let box_span = Span::new(280, 281);
    let r = run(&[strparam("x")], adt_sp(box_span, vec![var("x")]), TestEnv::default());
    assert_eq!(r.facts.escapes.get(&box_span), Some(&true), "named-fn returned constructor escapes (edge 1)");
    assert_eq!(r.summary.param_flow(0), ParamFlow::IntoResult);
}

#[test]
fn result_unique_never_set_in_increment_i() {
    // spec: §10 — result_unique is hardwired false throughout increment I.
    let r = run(&[strparam("p")], var("p"), TestEnv::default());
    assert!(!r.summary.result_unique);
}

#[test]
fn value_use_marked_only_in_non_callee_position() {
    // spec: §8.3 — a callable referenced in value position is a value-use;
    // in callee position it is not.
    // (consume helper) — `helper` passed as a value arg to `consume`.
    let env = TestEnv::default().summary("consume", sm(vec![Mode::Owned], ResultMode::Fresh, vec![ParamFlow::Consumed]));
    let body = call("consume", vec![var("helper")]);
    let r = run(&[], body, env);
    assert!(r.value_uses.contains(&Symbol::from("helper")));
    // The callee `consume` itself is NOT a value-use.
    assert!(!r.value_uses.contains(&Symbol::from("consume")));
}

#[test]
fn deps_harvested_for_summarised_callee() {
    // spec: §13.3 — the DepSet harvests every consulted summarised callee.
    let env = TestEnv::default().summary("consume", sm(vec![Mode::Owned], ResultMode::Fresh, vec![ParamFlow::Consumed]));
    let r = run(&[strparam("p")], call("consume", vec![var("p")]), env);
    assert!(r.deps.iter().any(|fq| fq.symbol.as_ref() == "consume"));
}

// ============ Scope-stack mechanism matrix (S102 /qa audit) ============
//
// These cells audit the `ScopeFrame`/`restore_frame` primitive itself
// (§13.6(i), F4 cure), not the specific bugs that motivated it. The existing
// F4 cells above pin the branch-SIBLING shadow and the match-arm-leak found
// bugs; the cells below fill the implied strategy matrix per
// `feedback_dev_strategy_derived_unit_scenarios`: the `Option<BindState>`
// restore BOTH arms (reinstate / remove), ≥3-deep nesting, multi-arm same-name
// independence, Lambda framing, and the scope-stack × F1-drain interaction.
// Every assertion pins the SPECIFIC resolved fact (the ABI-bearing
// `param_modes` value, provenance, or value-use), not "no panic".

#[test]
fn sequential_shadow_scope_restores_param_reinstates() {
    // spec: §13.6(i) (F4) — restore-REINSTATES arm, SEQUENTIAL (not sibling).
    // An inner `let` shadows param `a` inside the RHS of an outer binding; after
    // that inner scope closes, a later `(consume a)` in the ENCLOSING scope means
    // the PARAM. The scope frame must reinstate the param `BindState` so
    // `param_root(a)` reaches param 0 and it widens Owned. Without the reinstate,
    // `a` stays the inner `Projection(g)`, `param_root` misses, and `param_modes[0]`
    // narrows Owned→Borrowed (the ABI-half unsound direction). Distinct from the
    // sibling-branch cells — here the shadow and the use are SEQUENTIAL, the inner
    // scope fully closing before the use.
    // `(defn f [a g] (let [x (let [a (gcells g)] a)] (consume a)))`.
    let env = accessor_env()
        .summary("consume", sm(vec![Mode::Owned], ResultMode::Fresh, vec![ParamFlow::Consumed]));
    let inner_let = MonoExpr::Let {
        bindings: vec![(Symbol::from("a"), call("gcells", vec![var("g")]))],
        body: Box::new(var("a")),
        span: s(),
        ty: ConcreteType::String,
    };
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("x"), inner_let)],
        body: Box::new(call("consume", vec![var("a")])),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("a"), strparam("g")], body, env);
    assert_eq!(
        r.summary.param_mode(0),
        Mode::Owned,
        "param a must be reinstated after the inner shadow scope closes and widen Owned"
    );
}

#[test]
fn inner_scope_binding_removed_on_exit_unresolved_after() {
    // spec: §13.6(i) (F4) — restore-REMOVES arm. A name UNBOUND on entry (`t`) is
    // bound inside an inner scope, then used after that scope closes; the frame
    // must REMOVE it (prior was `None`) so the later use is unresolved/free again —
    // the inner binding did not leak. Observable: a use of `t` after the scope
    // resolves as a free/global name ⇒ recorded in `value_uses` (§8.3). Had the
    // inner binding leaked, `t` would resolve to the leaked `Fresh` binding and
    // would NOT be a value-use.
    // `(defn f [p] (let [x (let [t (Some p)] 0)] (consume t)))`.
    let env = TestEnv::default()
        .summary("consume", sm(vec![Mode::Owned], ResultMode::Fresh, vec![ParamFlow::Consumed]));
    let inner_let = MonoExpr::Let {
        bindings: vec![(Symbol::from("t"), adt(vec![var("p")]))],
        body: Box::new(MonoExpr::IntLit { value: 0, span: s(), ty: ConcreteType::Int }),
        span: s(),
        ty: ConcreteType::Int,
    };
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("x"), inner_let)],
        body: Box::new(call("consume", vec![var("t")])),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("p")], body, env);
    assert!(
        r.value_uses.contains(&Symbol::from("t")),
        "t must be unresolved (free) after its inner scope closes — the frame removed it, no leak"
    );
}

#[test]
fn triple_nested_shadow_unwinds_restore_param() {
    // spec: §13.6(i) (F4) — nesting depth ≥3. Three nested `let` scopes each
    // shadow the same param `a` (each RHS a projection of `g`); after all three
    // close, a `(consume a)` in the enclosing scope must reach the PARAM. Each
    // level's frame must restore correctly on unwind — a miss at ANY level leaves
    // `a` a leaked `Projection(g)`, `param_root` misses, and `param_modes[0]`
    // narrows Owned→Borrowed. `g` is only read borrowed by the accessors, so it
    // must stay Borrowed throughout — the negative half (no nesting corruption).
    // `(defn f [a g] (let [x (let [a (gcells g)] (let [a (gcells g)]
    //                        (let [a (gcells g)] a)))] (consume a)))`.
    let env = accessor_env()
        .summary("consume", sm(vec![Mode::Owned], ResultMode::Fresh, vec![ParamFlow::Consumed]));
    let l3 = MonoExpr::Let {
        bindings: vec![(Symbol::from("a"), call("gcells", vec![var("g")]))],
        body: Box::new(var("a")),
        span: s(),
        ty: ConcreteType::String,
    };
    let l2 = MonoExpr::Let {
        bindings: vec![(Symbol::from("a"), call("gcells", vec![var("g")]))],
        body: Box::new(l3),
        span: s(),
        ty: ConcreteType::String,
    };
    let l1 = MonoExpr::Let {
        bindings: vec![(Symbol::from("a"), call("gcells", vec![var("g")]))],
        body: Box::new(l2),
        span: s(),
        ty: ConcreteType::String,
    };
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("x"), l1)],
        body: Box::new(call("consume", vec![var("a")])),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("a"), strparam("g")], body, env);
    assert_eq!(
        r.summary.param_mode(0),
        Mode::Owned,
        "param a must be reinstated after 3-deep shadow unwinds and widen Owned"
    );
    assert_eq!(
        r.summary.param_mode(1),
        Mode::Borrowed,
        "param g stays Borrowed — nesting must not corrupt the sibling param"
    );
}

#[test]
fn two_match_arms_same_name_independent_param_restored() {
    // spec: §13.6(i) (F4) — multiple Match arms rebinding the SAME name, each in
    // its own frame. Both arms bind field `g` (shadowing param `g`); arm 2's `g`
    // must NOT see arm 1's `g` binding. After the match, a `(consume g)` in the
    // enclosing scope means the PARAM. If arm 1's frame leaked, arm 2's
    // `bind_pattern` would save arm 1's stale `Projection` as the prior and, on
    // arm 2's restore, reinstate THAT (not the param) — permanently losing the
    // param `g` ⇒ `param_modes[0]` narrows Owned→Borrowed. Each-arm-own-frame is
    // what keeps arm 2 independent and the param recoverable.
    // `(defn f [g h] (let [x (match h [(Box g) g] [(Cell g) g])] (consume g)))`.
    let env = TestEnv::default()
        .summary("consume", sm(vec![Mode::Owned], ResultMode::Fresh, vec![ParamFlow::Consumed]));
    let arm1 = MonoMatchArm {
        pattern: Pattern::Constructor {
            name: cranelisp_types::SymbolRef { module: None, name: Symbol::from("Box") },
            bindings: vec![Symbol::from("g")],
            span: s(),
        },
        body: var("g"),
        span: Span::new(70, 71),
        provenance: None,
        resolved_ctor: None,
    };
    let arm2 = MonoMatchArm {
        pattern: Pattern::Constructor {
            name: cranelisp_types::SymbolRef { module: None, name: Symbol::from("Cell") },
            bindings: vec![Symbol::from("g")],
            span: s(),
        },
        body: var("g"),
        span: Span::new(72, 73),
        provenance: None,
        resolved_ctor: None,
    };
    let m = MonoExpr::Match {
        scrutinee: Box::new(var("h")),
        arms: vec![arm1, arm2],
        span: s(),
        compiler_generated: false,
        ty: ConcreteType::String,
    };
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("x"), m)],
        body: Box::new(call("consume", vec![var("g")])),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("g"), strparam("h")], body, env);
    assert_eq!(
        r.summary.param_mode(0),
        Mode::Owned,
        "param g must survive two same-name arms (each its own frame) and widen Owned"
    );
}

#[test]
fn lambda_binds_no_frame_outer_shadow_over_widens_sound() {
    // spec: §13.6(i) (F4, Lambda determination) — the transfer walker's `Lambda`
    // arm pushes NO scope frame and binds NONE of the lambda's own params into
    // `bindings` (`transfer.rs` Lambda arm ignores `params`). Because it inserts
    // nothing, it cannot LEAK a binding past its scope — so Lambda is NOT a fourth
    // instance of the scope-leak class (no `param_modes` narrowing is reachable
    // through it). The only effect of not modeling the lambda param is that an
    // outer param shadowed by a same-named lambda param is OVER-widened at an
    // escaping capture (the lambda-body use resolves to the OUTER param): here
    // `(defn f [a] (fn [a] (consume a)))` widens the outer `a` to Owned even
    // though the lambda's `a` shadows it. Over-widening (Borrowed→Owned) is the
    // SOUND/conservative direction (an extra retain, never an elided one). This
    // cell pins the determination; a future lambda-param frame would flip it.
    let env = TestEnv::default()
        .summary("consume", sm(vec![Mode::Owned], ResultMode::Fresh, vec![ParamFlow::Consumed]));
    let lambda = MonoExpr::Lambda {
        params: vec![Symbol::from("a")],
        body: Box::new(call("consume", vec![var("a")])),
        span: s(),
        ty: ConcreteType::Fn(vec![], Box::new(ConcreteType::String)),
        escapes: None,
        confined: None,
        unique_static: None,
    };
    let r = run(&[strparam("a")], lambda, env);
    assert_eq!(
        r.summary.param_mode(0),
        Mode::Owned,
        "outer param a is over-widened (sound) — Lambda models no frame, cannot narrow"
    );
}

#[test]
fn fold_chain_in_shadowing_scope_drains_in_defining_scope() {
    // spec: §13.6(g)+(i) — the scope-stack × F1-drain interaction. A flat fold
    // chain whose FIRST binding shadows the param `p`, extending
    // `binding_mediated_escape_flat_fold_chain_widens_all` into a shadowed context.
    // `(defn f [p] (let [p (Some p) b (Some p)] b))`: `b` is returned ⇒ escapes;
    // `b`'s RHS `(Some p)` folds the let-bound `p` (the shadow, Fresh) ⇒ `p`
    // escapes ⇒ `p`'s OWN RHS `(Some p_outer)` must re-walk in its DEFINING scope
    // (the binding `p` is not in scope while its own RHS evaluates — sequential-let
    // semantics), resolving that `p` to the PARAM so the param flow widens
    // Consumed→IntoResult. If the drain re-walked without restoring the defining
    // scope, `p` would resolve to the Fresh shadow (param_root None) and the param
    // would stay Consumed — the exact narrowing the defining-scope re-walk cures.
    let x_span = Span::new(80, 81);
    let b_span = Span::new(82, 83);
    let body = MonoExpr::Let {
        bindings: vec![
            (Symbol::from("p"), adt_sp(x_span, vec![var("p")])),
            (Symbol::from("b"), adt_sp(b_span, vec![var("p")])),
        ],
        body: Box::new(var("b")),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("p")], body, TestEnv::default());
    assert_eq!(
        r.summary.param_flow(0),
        ParamFlow::IntoResult,
        "the fold chain must resolve p's RHS in its defining scope (the param), widening IntoResult"
    );
    assert_eq!(
        r.facts.escapes.get(&b_span),
        Some(&true),
        "the returned aggregate b escapes"
    );
    assert_eq!(
        r.facts.escapes.get(&x_span),
        Some(&true),
        "the shadowing p aggregate escapes (folded into returned b)"
    );
}

