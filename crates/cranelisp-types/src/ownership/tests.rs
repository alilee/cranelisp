//! Sibling unit tests for the ownership carrier types (Principle 23) —
//! pinning the ⊤-on-absence accessor contract, full-`Eq` change detection,
//! and the serde conservative-default round-trip that
//! `design/typecheck/ownership-inference.md` §13.1 binds the carrier to.

use super::*;

// --- Conservative-read accessors: ⊤-on-absence in ONE home (item 4) ---

#[test]
fn param_mode_absent_reads_owned() {
    let s = ModeSummary::default();
    assert_eq!(s.param_mode(0), Mode::Owned);
    assert_eq!(s.param_mode(7), Mode::Owned);
}

#[test]
fn param_mode_short_vector_reads_owned_past_end() {
    let s = ModeSummary {
        param_modes: vec![Mode::Borrowed],
        ..Default::default()
    };
    assert_eq!(s.param_mode(0), Mode::Borrowed);
    // Short vector: index 1 is absent ⇒ conservative Owned, never a panic.
    assert_eq!(s.param_mode(1), Mode::Owned);
}

#[test]
fn param_flow_absent_reads_retained() {
    let s = ModeSummary::default();
    assert_eq!(s.param_flow(0), ParamFlow::Retained);
    let s2 = ModeSummary {
        param_flow: vec![ParamFlow::Consumed],
        ..Default::default()
    };
    assert_eq!(s2.param_flow(0), ParamFlow::Consumed);
    assert_eq!(s2.param_flow(1), ParamFlow::Retained);
}

#[test]
fn spark_op_absent_reads_true() {
    let s = ModeSummary::default();
    assert!(
        s.spark_op(0),
        "absent spark_ops must read as may-spark (conservative)"
    );
    let s2 = ModeSummary {
        spark_ops: vec![false],
        ..Default::default()
    };
    assert!(!s2.spark_op(0));
    assert!(s2.spark_op(1));
}

// --- Defaults are the caller-side Decision-24 point (a present default
// summary is NOT the absence fallback — ownership.rs §Monotone defaults) ---

#[test]
fn default_summary_is_the_caller_side_point() {
    let s = ModeSummary::default();
    assert!(s.param_modes.is_empty());
    assert_eq!(s.result, ResultMode::Fresh);
    assert!(!s.result_unique);
    assert_eq!(Mode::default(), Mode::Owned);
    assert_eq!(ResultMode::default(), ResultMode::Fresh);
    assert_eq!(ParamFlow::default(), ParamFlow::Retained);
}

// --- Serde: bare `{}` deserialises to the conservative point (item 2) ---

#[test]
fn serde_empty_object_is_conservative_point() {
    let s: ModeSummary = serde_json::from_str("{}").expect("bare {} must deserialise");
    assert_eq!(s, ModeSummary::default());
    // And reads conservatively through the accessors.
    assert_eq!(s.param_mode(0), Mode::Owned);
    assert_eq!(s.param_flow(0), ParamFlow::Retained);
    assert!(s.spark_op(0));
}

#[test]
fn serde_round_trip_preserves_summary() {
    let s = ModeSummary {
        param_modes: vec![Mode::Borrowed, Mode::Owned, Mode::Copy],
        result: ResultMode::ProjectionOf(0),
        param_flow: vec![ParamFlow::Consumed, ParamFlow::IntoResult],
        spark_ops: vec![false, true],
        result_unique: false,
    };
    let json = serde_json::to_string(&s).unwrap();
    let back: ModeSummary = serde_json::from_str(&json).unwrap();
    assert_eq!(back, s);
}

// --- Full Eq is load-bearing: advisory-half changes are visible (item 2) ---

#[test]
fn eq_detects_advisory_half_change() {
    let a = ModeSummary {
        param_modes: vec![Mode::Borrowed],
        ..Default::default()
    };
    let mut b = a.clone();
    assert_eq!(a, b);
    b.param_flow = vec![ParamFlow::Consumed];
    assert_ne!(
        a, b,
        "advisory-half change must be Eq-visible (fixpoint re-entry)"
    );
}

// --- MayAliasOf (S111 §3.7) — the COW result point ---

// spec: design/arch/ownership-inference.md §3.7 — MayAliasOf is a distinct
// serde-visible variant, equal neither to Fresh nor to the unconditional
// claims at the same index.
#[test]
fn may_alias_of_is_distinct_and_serde_stable() {
    let cow = ModeSummary {
        result: ResultMode::MayAliasOf(0),
        ..Default::default()
    };
    // Serde round-trip preserves the variant + payload.
    let json = serde_json::to_string(&cow).unwrap();
    let back: ModeSummary = serde_json::from_str(&json).unwrap();
    assert_eq!(back.result, ResultMode::MayAliasOf(0));
    assert_ne!(cow.result, ResultMode::Fresh);
    assert_ne!(cow.result, ResultMode::AliasOf(0));
    assert_ne!(cow.result, ResultMode::ProjectionOf(0));
}

// --- MayAliasAny (S121 §19.2) — the result axis's ⊤ ---

// spec: design/typecheck/ownership-inference.md §19.2 — MayAliasAny is a
// distinct, index-less, serde-visible unit variant, equal neither to Fresh
// nor to any indexed may-alias point; the `Default` stays Fresh.
#[test]
fn may_alias_any_is_top_indexless_distinct_and_serde_stable() {
    let top = ModeSummary {
        result: ResultMode::MayAliasAny,
        ..Default::default()
    };
    // Defaults are unchanged by the addition.
    assert_eq!(ResultMode::default(), ResultMode::Fresh);
    // Serde: a unit variant with no payload; the persisted spelling is pinned
    // because it is the schema-27 cache shape.
    let json = serde_json::to_string(&top).unwrap();
    assert!(
        json.contains("\"result\":\"MayAliasAny\""),
        "persisted shape must be the bare unit-variant string: {json}"
    );
    let back: ModeSummary = serde_json::from_str(&json).unwrap();
    assert_eq!(back.result, ResultMode::MayAliasAny);
    assert_eq!(back, top);
    assert_ne!(top, ModeSummary::default());
    for k in 0..2 {
        assert_ne!(top.result, ResultMode::MayAliasOf(k));
    }
}

// --- The toggle is a read-once bool (polarity consistency) ---

#[test]
fn ownership_analysis_off_is_stable_within_process() {
    // Cannot assert the polarity (env-dependent under nextest), but the
    // read-once contract — two reads observe one value — is assertable.
    assert_eq!(ownership_analysis_off(), ownership_analysis_off());
}
