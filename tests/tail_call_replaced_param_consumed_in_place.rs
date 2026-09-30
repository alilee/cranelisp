//! A heap parameter whose slot a self-tail call replaces with a fresh value,
//! then consumed by an in-place `vec-push` in the base case (S122; found while
//! building the ACT-1021 controls in `tail_call_branch_consumed_let_binder.rs`).
//!
//! No branch forwards anything here. On 2026-09-30, with the ACT-0974 pair in
//! the working tree (source diff `b6219cac…`), the armed
//! `CRANELISP_RC_DEC_CHECK` stopped the subject with `STALE RC DEC … already
//! freed and reclaimed` on a 40-byte block of length 2, the base case's pushed
//! vector. The control moves `p` into its own slot instead and balances; `p`
//! is `Owned` in both (`CRANELISP_OWNERSHIP_TRACE`: `modes=[Copy, Owned]`).
//! Nearby shapes that balanced: returning `p` from the base case, and
//! consuming it by nesting (`(vec-push (vec-push [] p) p)`). The same face
//! reproduces at `e4062202`, before the ACT-0974 change. QA attributed it to
//! the in-place COW producer (ACT-1024): an escape fact of `Some(false)` means
//! the result stays in the frame, not that the source slot's release is
//! suppressed. The same face without recursion is in
//! `cow_result_consumed_in_frame.rs`.
//!
//! The `locus=` token names `cow_retains_reused_gate`, where the defect lived.
//! The ACT-1024 fix deleted that gate: read `vec_codegen.rs::retain_reused_source`
//! and `FnCompiler::holds_consuming_claim` today.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::marginal::{Child, MarginalPair};

/// `go` counts down three steps with `step` as the new `p`, then returns the
/// length of `(vec-push p 0)`. Both halves compute 2.
fn loop_with(step: &str) -> Child {
    Child::new(&format!(
        "(import [primitives [Pure add-i64 eq-i64 vec-len vec-push]])\n\
         (defn go [n p]\n\
           (if (eq-i64 n 0)\n\
               (vec-len (vec-push p 0))\n\
               (go (add-i64 n -1) {step})))\n\
         (defn main [] (Pure (go 3 (vec-push [] 1))))\n"
    ))
    .env("CRANELISP_RC_DEC_CHECK", "1")
}

// spec: spec/12-runtime.md §12.3.1 — a heap parameter replaced by a fresh value
// at a self-tail call and consumed in place at the base case is released
// exactly once.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/vec_codegen.rs::cow_retains_reused_gate found=S122 owner=/dev
#[test]
fn param_replaced_by_a_fresh_value_then_pushed_in_place_balances() {
    let pair = MarginalPair::new(
        "a replaced parameter pushed in place at the base case",
        loop_with("p"),
        loop_with("(vec-push [] 5)"),
    )
    .measure();
    assert!(
        pair.control().exit_code() == Some(2) && pair.subject().exit_code() == Some(2),
        "both halves must exit 2\n{}",
        pair.report()
    );
    pair.assert_balanced("the replaced parameter consumed in place");
}
