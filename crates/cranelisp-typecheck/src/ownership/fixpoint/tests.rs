//! CS-3 Principle-23 matrices for `fixpoint.rs`
//! (`design/typecheck/ownership-inference.md` §13.7 `fixpoint.rs` block):
//! SCC-shape, ordering/determinism, re-entry, and boundary-condition negatives.
//!
//! Driven through `compute_cluster` with hand-built `Callable`s whose bodies
//! reference each other via `SigDispatch` (⇒ in-cluster `working`-map lookups),
//! so the fixpoint logic is exercised without a full symbol-table fixture. A
//! `TestFixture` env supplies the (here unused) chain-follow fallback.

use cranelisp_types::{
    ConcreteType, FQTypeName, JitSymbol, Mode, ModuleFullPath, MonoExpr, Span, Symbol, TypeName,
};

use crate::checker::test_support::TestFixture;

use super::*;

fn s() -> Span {
    Span::SYNTHETIC
}
fn var(n: &str) -> MonoExpr {
    MonoExpr::Var { name: Symbol::from(n), span: s(), resolved_call: None, ty: ConcreteType::String, resolved_target: None }
}
fn call(name: &str, args: Vec<MonoExpr>) -> MonoExpr {
    MonoExpr::Apply {
        resolved_target: None,
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
/// `(Box field...)` returned — a fresh ADT embedding its fields.
fn boxed(fields: Vec<MonoExpr>) -> MonoExpr {
    MonoExpr::ConstrADT {
        type_name: FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Box")),
        tag: 0,
        fields,
        span: s(),
        ty: ConcreteType::ADT(FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Box")), vec![]),
        escapes: None,
        confined: None,
        unique_static: None,
    }
}
fn callable(key: &str, params: Vec<&str>, body: MonoExpr) -> Callable {
    Callable {
        key: Symbol::from(key),
        params: params.into_iter().map(|n| (Symbol::from(n), ConcreteType::String)).collect(),
        body,
    }
}
fn run(universe: Vec<Callable>) -> ClusterOwnership {
    let tf = TestFixture::new();
    let module = ModuleFullPath::from("user");
    compute_cluster(&tf.env(), &module, &universe)
}
fn mode(c: &ClusterOwnership, key: &str, i: usize) -> Mode {
    c.summaries[&Symbol::from(key)].param_mode(i)
}

// =================== SCC-shape matrix ===================

#[test]
fn straight_chain_propagates_owned_callee_to_caller() {
    // spec: §3.2 — a straight chain converges in reverse-topo; the Owned callee
    // widens the caller's forwarded param.
    // sink(y) = (Box y)  ⇒ y Owned; caller(x) = (sink x) ⇒ x Owned.
    let uni = vec![
        callable("sink", vec!["y"], boxed(vec![var("y")])),
        callable("caller", vec!["x"], call("sink", vec![var("x")])),
    ];
    let c = run(uni);
    assert_eq!(mode(&c, "sink", 0), Mode::Owned);
    assert_eq!(mode(&c, "caller", 0), Mode::Owned);
}

#[test]
fn self_recursive_borrowed_converges() {
    // spec: §3.2 — a self-recursive fn whose only use is a borrowed self-handoff
    // stays Borrowed (≤2 visits).
    // f(p) = (f p)  — p forwarded to f (in-cluster, Borrowed handoff).
    let uni = vec![callable("f", vec!["p"], call("f", vec![var("p")]))];
    let c = run(uni);
    assert_eq!(mode(&c, "f", 0), Mode::Borrowed);
}

#[test]
fn mutual_two_cycle_converges() {
    // spec: §3.2 — a mutual 2-cycle of pass-through calls converges (both Borrowed).
    let uni = vec![
        callable("a", vec!["p"], call("b", vec![var("p")])),
        callable("b", vec!["q"], call("a", vec![var("q")])),
    ];
    let c = run(uni);
    assert_eq!(mode(&c, "a", 0), Mode::Borrowed);
    assert_eq!(mode(&c, "b", 0), Mode::Borrowed);
}

#[test]
fn recursive_owned_cycle_widens_both() {
    // spec: §3.2 — a cycle where one member consumes its param widens through
    // the cycle (monotone).
    // a(p) = (b p); b(q) = (Box (a q))  — b consumes via a's forwarded Owned.
    let uni = vec![
        callable("a", vec!["p"], boxed(vec![var("p")])), // a consumes p (Owned)
        callable("b", vec!["q"], call("a", vec![var("q")])), // b forwards q to a (Owned)
    ];
    let c = run(uni);
    assert_eq!(mode(&c, "a", 0), Mode::Owned);
    assert_eq!(mode(&c, "b", 0), Mode::Owned);
}

#[test]
fn tail_recursion_base_returns_param_is_alias_not_fresh() {
    // spec: §4.2 (FIXME 0520) — the `build` repro (04_vec_cow_loop), driver
    // grain. `(defn build [v i n] (if c v (build (grow v) i n)))`: the base case
    // returns param `v`, the recursive case returns a fresh-derived vec. Pre-cure
    // the partial-if join collapsed build's result to `Fresh` DESPITE the
    // base-case param return — an ABI-half soundness narrowing (a consumer
    // trusting Fresh frees the returned param → the observed SIGABRT). Truth:
    // may-alias param 0 ⇒ AliasOf(0). `grow` is a boundary leaf (⊤: Owned/Fresh),
    // so the recursive arg is fresh — exactly the vec-push COW shape.
    let cond = MonoExpr::BoolLit { value: true, span: s(), ty: ConcreteType::Bool };
    let recursive = call("build", vec![call("grow", vec![var("v")]), var("i"), var("n")]);
    let body = MonoExpr::If {
        cond: Box::new(cond),
        then_branch: Box::new(var("v")),
        else_branch: Box::new(recursive),
        span: s(),
        ty: ConcreteType::String,
    };
    let uni = vec![callable("build", vec!["v", "i", "n"], body)];
    let c = run(uni);
    let build = &c.summaries[&Symbol::from("build")];
    assert_eq!(
        build.result,
        cranelisp_types::ResultMode::AliasOf(0),
        "build returns param v in the base case ⇒ AliasOf(0), never Fresh"
    );
    // v is returned (IntoResult) ⇒ Owned; the ABI param half was already correct.
    assert_eq!(mode(&c, "build", 0), Mode::Owned, "the returned param v is Owned");
}

// =================== Ordering / determinism ===================

#[test]
fn scrambled_seed_order_converges_identically() {
    // spec: §13.3 — seed order is a hint only; scrambled order ⇒ identical result.
    let mk = || {
        vec![
            callable("sink", vec!["y"], boxed(vec![var("y")])),
            callable("caller", vec!["x"], call("sink", vec![var("x")])),
        ]
    };
    let c1 = run(mk());
    let mut rev = mk();
    rev.reverse();
    let c2 = run(rev);
    assert_eq!(c1.summaries, c2.summaries);
}

// =================== Re-entry / boundary ===================

#[test]
fn absent_boundary_callee_reads_top() {
    // spec: §13.3 gap 4 — a callee absent from the cluster and unresolvable is a
    // boundary condition read as ⊤ (Owned/Retained) — never enqueued.
    // caller(x) = (external x)  where `external` is not in the universe.
    let uni = vec![callable("caller", vec!["x"], call("external", vec![var("x")]))];
    let c = run(uni);
    assert_eq!(mode(&c, "caller", 0), Mode::Owned);
    // `external` is not a cluster member ⇒ no summary published for it.
    assert!(!c.summaries.contains_key(&Symbol::from("external")));
}

#[test]
fn value_use_harvested_across_cluster() {
    // spec: §8.3 — a callable referenced in value position is recorded.
    // caller(x) = (sink helper)  — `helper` passed as a value.
    let uni = vec![
        callable("sink", vec!["y"], boxed(vec![var("y")])),
        callable("caller", vec!["x"], call("sink", vec![var("helper")])),
    ];
    let c = run(uni);
    assert!(c.value_used.contains(&Symbol::from("helper")));
}

#[test]
fn every_callable_gets_a_summary() {
    // spec: §13.2 — every codegen-bound callable in the universe is summarised.
    let uni = vec![
        callable("a", vec!["p"], var("p")),
        callable("b", vec!["q"], var("q")),
    ];
    let c = run(uni);
    assert!(c.summaries.contains_key(&Symbol::from("a")));
    assert!(c.summaries.contains_key(&Symbol::from("b")));
}

#[test]
fn mangled_mono_instance_propagates_in_cluster() {
    // spec: §6 / §13.7 (suggestion 5) — a mono instance keyed by its mangled
    // name (`reduce$Int+Int`) referenced via SigDispatch under the SAME mangled
    // name propagates in-cluster (precise), NOT degrading to ⊤. Pins that the
    // SigDispatch target and the universe key are the one mangled `Symbol`.
    let uni = vec![
        callable("reduce$Int+Int", vec!["y"], boxed(vec![var("y")])), // consumes y ⇒ Owned
        callable("caller", vec!["x"], call("reduce$Int+Int", vec![var("x")])),
    ];
    let c = run(uni);
    assert_eq!(mode(&c, "reduce$Int+Int", 0), Mode::Owned);
    // Precise in-cluster propagation: caller's x widens through the mangled edge.
    assert_eq!(mode(&c, "caller", 0), Mode::Owned);
}

// =================== Confinement fixpoint (blocker 2) ===================

/// A ParBind of one binding whose RHS is `(name args…)`, joined into `body`.
fn parbind(binding: &str, rhs: MonoExpr, body: MonoExpr) -> MonoExpr {
    MonoExpr::ParBind {
        bindings: vec![(Symbol::from(binding), rhs)],
        body: Box::new(body),
        span: s(),
        ty: ConcreteType::String,
    }
}

#[test]
fn transitive_spark_ops_propagate_caller_before_callee() {
    // spec: §5.3 / §13.7 — a callee whose spark_ops is set must propagate to a
    // caller LISTED FIRST (processed before the callee). Blocker 2: confinement
    // is a worklist fixpoint, not a single unordered pass. A single pass over
    // `universe` in vec order would process `caller` while `producer.spark_ops`
    // is still the init `false` and never re-run ⇒ caller under-reports Confined.
    // producer(y) sparks y off-strand (ParBind consuming call); caller(x)
    // forwards x to producer on the PARENT strand ⇒ inherits transitively.
    let uni = vec![
        callable("caller", vec!["x"], call("producer", vec![var("x")])),
        callable(
            "producer",
            vec!["y"],
            parbind("r", call("mystery", vec![var("y")]), var("r")),
        ),
    ];
    let c = run(uni);
    assert!(
        c.summaries[&Symbol::from("producer")].spark_op(0),
        "producer sparks y off-strand"
    );
    assert!(
        c.summaries[&Symbol::from("caller")].spark_op(0),
        "caller must inherit producer's spark_ops transitively regardless of order"
    );
}

#[test]
fn confinement_no_spurious_cross_for_parent_only_chain() {
    // spec: §5.3 (negative twin) — a caller→callee chain with NO off-strand op
    // anywhere stays Confined (spark_ops clear). Guards against the fixpoint
    // over-widening every position.
    let uni = vec![
        callable("caller", vec!["x"], call("sink", vec![var("x")])),
        callable("sink", vec!["y"], boxed(vec![var("y")])),
    ];
    let c = run(uni);
    assert!(!c.summaries[&Symbol::from("sink")].spark_op(0), "sink parent-strand only");
    assert!(!c.summaries[&Symbol::from("caller")].spark_op(0), "caller parent-strand only");
}

// =================== Cap-exhaustion reset (blocker 4) ===================

#[test]
fn cap_exhaustion_publishes_conservative_top() {
    // spec: §13.6 (blocker 4) — forcing the fixpoint to exhaust its cap (cap=0)
    // publishes the conservative ⊤ for every callable, never the too-precise
    // partial. A self-recursive pass-through normally converges to Borrowed
    // (see `self_recursive_borrowed_converges`); under the cap it must be the
    // ⊤ point: Owned / Fresh / Retained / spark-set.
    let tf = TestFixture::new();
    let module = ModuleFullPath::from("user");
    let uni = vec![callable("f", vec!["p"], call("f", vec![var("p")]))];
    let c = compute_cluster_with_cap(&tf.env(), &module, &uni, 0);
    let s = &c.summaries[&Symbol::from("f")];
    assert_eq!(s.param_mode(0), Mode::Owned, "capped param must be ⊤ Owned, not the normal Borrowed");
    assert_eq!(s.result, cranelisp_types::ResultMode::Fresh);
    assert_eq!(s.param_flow(0), cranelisp_types::ParamFlow::Retained);
    assert!(s.spark_op(0), "capped spark_ops must be ⊤ (Crossing)");
}

#[test]
fn cap_exhaustion_forces_conservative_site_facts() {
    // spec: §13.6 (F3) — on cap the SITE FACTS are forced ⊤ too: every escape
    // fact `true`, provenance dropped. A callable un(fully)visited before the
    // cap otherwise has no / too-low escape entries (below-truth ⇒ backend
    // elides a retain ⇒ UAF). Without the reset, `c.facts` has no entry for the
    // un-visited callable at all (indexing panics) — the failing-first shape.
    let tf = TestFixture::new();
    let module = ModuleFullPath::from("user");
    let uni = vec![callable(
        "f",
        vec!["x"],
        MonoExpr::Let {
            bindings: vec![(Symbol::from("a"), boxed(vec![var("x")]))],
            body: Box::new(var("a")),
            span: s(),
            ty: ConcreteType::String,
        },
    )];
    let c = compute_cluster_with_cap(&tf.env(), &module, &uni, 0);
    let f = &c.facts[&Symbol::from("f")];
    assert!(!f.escapes.is_empty(), "conservative escape facts populated under cap");
    assert!(f.escapes.values().all(|v| *v), "all escape facts forced ⊤ (true) under cap");
    assert!(f.provenance.is_empty(), "provenance dropped under cap");
}

// =================== Uniqueness stratum (CS-II-1/2) ===================

fn runique(c: &ClusterOwnership, key: &str) -> bool {
    c.summaries[&Symbol::from(key)].result_unique
}

#[test]
fn result_unique_fresh_return_true() {
    // spec: §14.2 clause 3 (driver) — a body returning a fresh alloc is unique.
    let uni = vec![callable("a", vec![], boxed(vec![]))];
    let c = run(uni);
    assert!(runique(&c, "a"));
}

#[test]
fn result_unique_param_return_false() {
    // spec: §14.2 (negative, driver) — returning a param aliases it ⇒ not unique.
    let uni = vec![callable("c", vec!["x"], var("x"))];
    let c = run(uni);
    assert!(!runique(&c, "c"));
}

#[test]
fn result_unique_chains_across_two_call_cluster() {
    // spec: §14.2 clause 3 (driver) — `a() = (Box)` [unique]; `b() = (a)` chains
    // the proof through the call ⇒ b unique.
    let uni = vec![
        callable("a", vec![], boxed(vec![])),
        callable("b", vec![], call("a", vec![])),
    ];
    let c = run(uni);
    assert!(runique(&c, "a"));
    assert!(runique(&c, "b"), "b chains a.result_unique through the call");
}

#[test]
fn result_unique_greatest_fixpoint_cycle_stays_true() {
    // spec: §14.2 (greatest fixpoint) — a mutual cycle both returning fresh-or-
    // each-other converges to `true` co-inductively (init-optimistic-true holds).
    // ping() = (if c (Box) (pong)); pong() = (ping).
    let cond = MonoExpr::BoolLit { value: true, span: s(), ty: ConcreteType::Bool };
    let ping_body = MonoExpr::If {
        cond: Box::new(cond),
        then_branch: Box::new(boxed(vec![])),
        else_branch: Box::new(call("pong", vec![])),
        span: s(),
        ty: ConcreteType::String,
    };
    let uni = vec![
        callable("ping", vec![], ping_body),
        callable("pong", vec![], call("ping", vec![])),
    ];
    let c = run(uni);
    assert!(runique(&c, "ping"));
    assert!(runique(&c, "pong"));
}

#[test]
fn result_unique_narrows_through_chain() {
    // spec: §14.2 (greatest fixpoint narrowing) — a non-unique leaf narrows its
    // whole caller chain from the optimistic `true` init to `false`, in ANY
    // processing order (the DepSet re-entry). leaf(x)=x [not unique] ⇒ mid(x)=
    // (leaf x) ⇒ top(x)=(mid x): all false.
    let uni = vec![
        callable("top", vec!["x"], call("mid", vec![var("x")])),
        callable("mid", vec!["x"], call("leaf", vec![var("x")])),
        callable("leaf", vec!["x"], var("x")),
    ];
    let c = run(uni);
    assert!(!runique(&c, "leaf"));
    assert!(!runique(&c, "mid"), "mid narrows when leaf narrows");
    assert!(!runique(&c, "top"), "top narrows when mid narrows");
}

#[test]
fn cap_exhaustion_resets_uniqueness_to_false_and_no_sites() {
    // spec: §14.2 cap-reset — under cap=0 the greatest fixpoint sits ABOVE its
    // true fixpoint, so result_unique resets to `false` everywhere and every
    // `unique_static` site fact drops to `None` (empty `unique` map). A body
    // that would normally be unique (`(Box)`) must publish false under the cap.
    let tf = TestFixture::new();
    let module = ModuleFullPath::from("user");
    let uni = vec![callable("a", vec![], boxed(vec![]))];
    let c = compute_cluster_with_cap(&tf.env(), &module, &uni, 0);
    assert!(!runique(&c, "a"), "cap-reset ⇒ result_unique false");
    assert!(
        c.facts[&Symbol::from("a")].unique.is_empty(),
        "cap-reset ⇒ no unique_static site facts"
    );
}

#[test]
fn unique_static_site_fact_emitted_by_driver() {
    // spec: §14.2 (CS-II-2 driver) — `f() = (let [v (Box@30)] (consume v))`: v is
    // a fresh single-use root ⇒ the alloc @30 carries unique_static Some(true).
    let boxsp = Span::new(30, 31);
    let alloc = MonoExpr::ConstrADT {
        type_name: FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Box")),
        tag: 0,
        fields: vec![],
        span: boxsp,
        ty: ConcreteType::ADT(
            FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Box")),
            vec![],
        ),
        escapes: None,
        confined: None,
        unique_static: None,
    };
    let body = MonoExpr::Let {
        bindings: vec![(Symbol::from("v"), alloc)],
        body: Box::new(call("consume", vec![var("v")])),
        span: s(),
        ty: ConcreteType::String,
    };
    let uni = vec![callable("f", vec![], body)];
    let c = run(uni);
    assert_eq!(
        c.facts[&Symbol::from("f")].unique.get(&boxsp),
        Some(&true),
        "the fresh single-use alloc carries unique_static Some(true)"
    );
}
