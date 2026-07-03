//! Sibling unit tests for the ownership carrier types (Principle 23) —
//! pinning the ⊤-on-absence accessor contract, the ABI-surface comparison,
//! and the serde conservative-default round-trip that
//! `design/typecheck/ownership-inference.md` §13.1 items 1–5 bind CS-A to.

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
    let s = ModeSummary { param_modes: vec![Mode::Borrowed], ..Default::default() };
    assert_eq!(s.param_mode(0), Mode::Borrowed);
    // Short vector: index 1 is absent ⇒ conservative Owned, never a panic.
    assert_eq!(s.param_mode(1), Mode::Owned);
}

#[test]
fn param_flow_absent_reads_retained() {
    let s = ModeSummary::default();
    assert_eq!(s.param_flow(0), ParamFlow::Retained);
    let s2 = ModeSummary { param_flow: vec![ParamFlow::Consumed], ..Default::default() };
    assert_eq!(s2.param_flow(0), ParamFlow::Consumed);
    assert_eq!(s2.param_flow(1), ParamFlow::Retained);
}

#[test]
fn spark_op_absent_reads_true() {
    let s = ModeSummary::default();
    assert!(s.spark_op(0), "absent spark_ops must read as may-spark (conservative)");
    let s2 = ModeSummary { spark_ops: vec![false], ..Default::default() };
    assert!(!s2.spark_op(0));
    assert!(s2.spark_op(1));
}

// --- Defaults are the Decision-24 conservative point ---

#[test]
fn default_summary_is_abi_conservative() {
    let s = ModeSummary::default();
    assert!(s.is_abi_conservative());
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
    let a = ModeSummary { param_modes: vec![Mode::Borrowed], ..Default::default() };
    let mut b = a.clone();
    assert_eq!(a, b);
    b.param_flow = vec![ParamFlow::Consumed];
    assert_ne!(a, b, "advisory-half change must be Eq-visible (fixpoint re-entry)");
    // ...but NOT abi-visible.
    assert!(a.abi_eq(&b), "advisory-only change is never ABI-changing");
}

// --- abi_eq: (param_modes, result) only, through ⊤-on-absence (item 5) ---

#[test]
fn abi_eq_ignores_advisory_and_normalises_absence() {
    // [] and [Owned, Owned] are the same ABI surface.
    let bare = ModeSummary::default();
    let explicit =
        ModeSummary { param_modes: vec![Mode::Owned, Mode::Owned], ..Default::default() };
    assert!(bare.abi_eq(&explicit));
    assert!(explicit.abi_eq(&bare));

    // A mode difference IS an ABI difference.
    let borrowed = ModeSummary { param_modes: vec![Mode::Borrowed], ..Default::default() };
    assert!(!bare.abi_eq(&borrowed));

    // A result-mode difference IS an ABI difference.
    let proj = ModeSummary { result: ResultMode::ProjectionOf(0), ..Default::default() };
    assert!(!bare.abi_eq(&proj));
}

#[test]
fn abi_eq_opt_treats_none_as_conservative() {
    let conservative =
        ModeSummary { param_modes: vec![Mode::Owned], ..Default::default() };
    let borrowed = ModeSummary { param_modes: vec![Mode::Borrowed], ..Default::default() };
    assert!(ModeSummary::abi_eq_opt(None, None));
    assert!(ModeSummary::abi_eq_opt(Some(&conservative), None));
    assert!(ModeSummary::abi_eq_opt(None, Some(&conservative)));
    assert!(!ModeSummary::abi_eq_opt(None, Some(&borrowed)));
    assert!(!ModeSummary::abi_eq_opt(Some(&borrowed), None));
    assert!(ModeSummary::abi_eq_opt(Some(&borrowed), Some(&borrowed)));
}

// --- The toggle is a read-once bool (polarity consistency) ---

#[test]
fn ownership_analysis_off_is_stable_within_process() {
    // Cannot assert the polarity (env-dependent under nextest), but the
    // read-once contract — two reads observe one value — is assertable.
    assert_eq!(ownership_analysis_off(), ownership_analysis_off());
}
