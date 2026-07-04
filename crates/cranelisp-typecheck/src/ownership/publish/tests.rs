//! CS-4 Principle-23 matrices for `publish.rs`
//! (`design/typecheck/ownership-inference.md` §13.7 `publish.rs` block):
//! placement, site-fact annotation (§13.6(b)), marks, and the negatives.

use std::collections::{HashMap, HashSet};

use cranelisp_types::{
    ConcreteType, DefKind, ModeSummary, ModuleEntry, ModuleFullPath, MonoDefnVariant, MonoExpr,
    ParamFlow, ResultMode, Span, Symbol, UserFnState,
};

use crate::checker::test_support::TestFixture;

use super::super::fixpoint::ClusterOwnership;
use super::super::transfer::SiteFacts;

fn apply_body(span: Span) -> MonoExpr {
    // `(gcells g)` — an accessor Apply we can annotate with provenance.
    MonoExpr::Apply {
        callee: Box::new(MonoExpr::Var {
            name: Symbol::from("gcells"),
            span: Span::SYNTHETIC,
            resolved_call: None,
            ty: ConcreteType::String,
        }),
        args: vec![MonoExpr::Var {
            name: Symbol::from("g"),
            span: Span::SYNTHETIC,
            resolved_call: None,
            ty: ConcreteType::String,
        }],
        span,
        resolved_call: None,
        ty: ConcreteType::String,
        escapes: None,
        confined: None,
        unique_static: None,
        provenance: None,
    }
}

/// Register a concrete `UserFn` callable named `key` with a `codegen_view`
/// whose body is `body`, into the fixture's `user` module.
fn register_callable(tf: &TestFixture, key: &str, body: MonoExpr) {
    let cv = MonoDefnVariant {
        name: Symbol::from(key),
        params: vec![Symbol::from("g")],
        body,
        span: Span::SYNTHETIC,
        mode_summary: None,
    };
    let entry: ModuleEntry = ModuleEntry::def(
        crate::scheme::mono(cranelisp_types::Type::Fn(
            vec![cranelisp_types::Type::String],
            Box::new(cranelisp_types::Type::String),
        )),
        DefKind::UserFn { fn_state: UserFnState::Concrete { got_slot: 1, mode_summary: None } },
    )
    .codegen_view(cv)
    .build();
    tf.modules.get_mut(&ModuleFullPath::from("user")).unwrap().insert(Symbol::from(key), entry);
}

fn summary() -> ModeSummary {
    ModeSummary {
        param_modes: vec![cranelisp_types::Mode::Borrowed],
        result: ResultMode::ProjectionOf(0),
        param_flow: vec![ParamFlow::Consumed],
        spark_ops: vec![false],
        result_unique: false,
    }
}

#[test]
fn summary_lands_on_entry_and_codegen_view() {
    // spec: §13.2/§13.6(b) — publish writes the summary onto the callable entry
    // (persisted twin) AND its codegen_view carrier.
    let tf = TestFixture::new();
    register_callable(&tf, "area", apply_body(Span::new(10, 20)));

    let mut summaries = HashMap::new();
    summaries.insert(Symbol::from("area"), summary());
    let cluster = ClusterOwnership { summaries, facts: HashMap::new(), value_used: HashSet::new() };
    let env = tf.env();
    super::publish(&env, &tf.state, &cluster);

    let read = env.current_symbol_table(&tf.state);
    let view = read.view();
    let entry = view.lookup(&Symbol::from("area")).unwrap();
    assert_eq!(entry.mode_summary(), Some(&summary()));
    assert_eq!(entry.codegen_view().unwrap().mode_summary.as_ref(), Some(&summary()));
}

#[test]
fn site_facts_and_provenance_annotate_the_stored_view() {
    // spec: §13.6(b) — the one-shot walk writes escape/provenance onto the body.
    let tf = TestFixture::new();
    register_callable(&tf, "area", apply_body(Span::new(10, 20)));

    let mut facts = SiteFacts::default();
    facts.escapes.insert(Span::new(10, 20), false);
    facts.provenance.insert(Span::new(10, 20), Symbol::from("g"));
    let mut facts_map = HashMap::new();
    facts_map.insert(Symbol::from("area"), facts);
    let mut summaries = HashMap::new();
    summaries.insert(Symbol::from("area"), summary());
    let cluster =
        ClusterOwnership { summaries, facts: facts_map, value_used: HashSet::new() };
    let env = tf.env();
    super::publish(&env, &tf.state, &cluster);

    let read = env.current_symbol_table(&tf.state);
    let view = read.view();
    let cv = view.lookup(&Symbol::from("area")).unwrap().codegen_view().unwrap();
    match &cv.body {
        MonoExpr::Apply { escapes, provenance, .. } => {
            assert_eq!(*escapes, Some(false));
            assert_eq!(provenance.as_ref(), Some(&Symbol::from("g")));
        }
        _ => panic!("expected Apply body"),
    }
}

#[test]
fn value_use_mark_set_for_referenced_callable() {
    // spec: §8.3 — a callable named in value_used gets its mark set.
    let tf = TestFixture::new();
    register_callable(&tf, "area", apply_body(Span::new(10, 20)));

    let mut value_used = HashSet::new();
    value_used.insert(Symbol::from("area"));
    let cluster =
        ClusterOwnership { summaries: HashMap::new(), facts: HashMap::new(), value_used };
    let env = tf.env();
    super::publish(&env, &tf.state, &cluster);

    let read = env.current_symbol_table(&tf.state);
    let view = read.view();
    assert!(view.lookup(&Symbol::from("area")).unwrap().value_use());
}

#[test]
fn absent_summary_reads_conservative_point() {
    // spec: §13.5 — a default (absent) summary reads as the Decision-24
    // conservative point through the accessors (the round-trip target).
    let empty = ModeSummary::default();
    assert_eq!(empty.param_mode(0), cranelisp_types::Mode::Owned);
    assert_eq!(empty.param_flow(0), ParamFlow::Retained);
    assert!(empty.spark_op(0));
    assert_eq!(empty.result, ResultMode::Fresh);
}

#[test]
fn non_cluster_entry_is_untouched() {
    // spec: §13.7 (negative) — an entry not in the cluster summary map is never
    // written (Constructors / imports / declared primitives stay as-is).
    let tf = TestFixture::new();
    register_callable(&tf, "area", apply_body(Span::new(10, 20)));
    register_callable(&tf, "other", apply_body(Span::new(30, 40)));

    let mut summaries = HashMap::new();
    summaries.insert(Symbol::from("area"), summary());
    let cluster = ClusterOwnership { summaries, facts: HashMap::new(), value_used: HashSet::new() };
    let env = tf.env();
    super::publish(&env, &tf.state, &cluster);

    let read = env.current_symbol_table(&tf.state);
    let view = read.view();
    // `other` was not in the summary map ⇒ stays None.
    assert_eq!(view.lookup(&Symbol::from("other")).unwrap().mode_summary(), None);
}
