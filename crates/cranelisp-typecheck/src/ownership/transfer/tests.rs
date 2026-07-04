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
    MonoExpr::Var { name: Symbol::from(n), span: s(), resolved_call: None, ty: ConcreteType::String }
}
/// A statically-resolved call `(name args...)` via SigDispatch (classifies
/// Summarised(name), consulting the summary registered under `name`).
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
/// A call with no resolved_call (the None+Var classifier row).
fn bare_call(name: &str, args: Vec<MonoExpr>) -> MonoExpr {
    MonoExpr::Apply {
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
    transfer(params, &body, &env, &CopyClassifier::new())
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
fn return_embedded_in_constr_escapes_and_result_fresh() {
    // spec: §3.3/§13.6(c) — a returned ADT is Fresh; its stored param escapes.
    let r = run(&[strparam("x")], adt(vec![var("x")]), TestEnv::default());
    assert_eq!(r.summary.result, ResultMode::Fresh);
    // Escape site fact on the ConstrADT is true (it is returned).
    assert!(r.facts.escapes.values().any(|v| *v));
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

#[test]
fn mixed_return_paths_join_to_fresh() {
    // spec: §13.6(c) — disagreeing return paths ⇒ Fresh.
    // (if c p (other))  — one path AliasOf(0), the other Fresh ⇒ Fresh.
    let env = TestEnv::default().summary("other", sm(vec![], ResultMode::Fresh, vec![]));
    let body = MonoExpr::If {
        cond: Box::new(MonoExpr::BoolLit { value: true, span: s(), ty: ConcreteType::Bool }),
        then_branch: Box::new(var("p")),
        else_branch: Box::new(call("other", vec![])),
        span: s(),
        ty: ConcreteType::String,
    };
    let r = run(&[strparam("p")], body, env);
    assert_eq!(r.summary.result, ResultMode::Fresh);
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
    };
    let arm2 = MonoMatchArm {
        pattern: Pattern::Wildcard { span: s() },
        body: call("consume", vec![var("a")]),
        span: Span::new(62, 63),
        provenance: None,
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

