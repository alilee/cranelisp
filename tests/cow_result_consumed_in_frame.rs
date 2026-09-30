//! A copy-on-write `Vec` operation on a frame-owned binding at its last use,
//! whose result stays in the same frame (S122, ACT-1024;
//! `tests/plan/s122-evidence-delta.md`, "ACT-1024 — correction evidence
//! delta"). W1, the self-tail face, is in
//! `tail_call_replaced_param_consumed_in_place.rs`.
//!
//! When the binding is at its last use the operation mutates the box in place.
//! Its result then shares that box, and the frame still releases the source
//! binding, so the result must hold its own reference. On 2026-09-30, on the
//! ACT-1021 amendment and alias-correction tree (source diff `872b59a9…` over
//! `e4062202`, binary `a423324d…`), the in-place path took no reference:
//!
//! - W-P and W-L stopped armed with `STALE RC DEC … already freed and
//!   reclaimed` on the 40-byte, length-2 pushed vector;
//! - W-LOOP's subject stopped armed with `USE-AFTER-FREE` in
//!   `vec_push_copy(src)`; its 0-step control balanced;
//! - W-M's subject balanced only by cancellation (see the cell).
//!
//! The W-P, W-L and W-LOOP controls make the source live after the operation,
//! so the operation copies. Every child runs with the seam checks armed, so a
//! premature release stops it at the faulting operation, and each half's
//! result is asserted.
//!
//! The `locus=` token names `cow_retains_reused_gate`, where the defect lived.
//! The ACT-1024 fix deleted that gate: read `vec_codegen.rs::retain_reused_source`
//! and `FnCompiler::holds_consuming_claim` today.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::marginal::{Child, Marginal, MarginalPair};

/// A `--run` child of `defs` with `vec` primitives imported and the seam
/// checks armed.
fn armed(defs: &str) -> Child {
    Child::new(&format!(
        "(import [primitives [Pure add-i64 eq-i64 vec-len vec-push vec-set]])\n{defs}"
    ))
    .env("CRANELISP_RC_DEC_CHECK", "1")
}

/// Measure the pair and require each half's computed result.
fn measure(label: &str, control: (Child, i32), subject: (Child, i32)) -> Marginal {
    let (control, control_exit) = control;
    let (subject, subject_exit) = subject;
    let pair = MarginalPair::new(label, control, subject).measure();
    assert!(
        pair.control().exit_code() == Some(control_exit)
            && pair.subject().exit_code() == Some(subject_exit),
        "{label}: control must exit {control_exit} and subject {subject_exit}\n{}\n\
         --- control stderr ---\n{}\n--- subject stderr ---\n{}",
        pair.report(),
        pair.control().stderr,
        pair.subject().stderr
    );
    pair
}

/// `f` applied to a fresh [1].
fn on_fresh_vec(body: &str) -> Child {
    armed(&format!(
        "(defn f [p] {body})\n(defn main [] (Pure (f (vec-push [] 1))))\n"
    ))
}

// spec: spec/12-runtime.md §12.3.1 and §12.3.3 — a `vec-push` on a parameter
// at its last use, whose result is consumed in the same frame, releases the
// vector exactly once.
//
// W-P. The subject computes 2; the control also reads `p` afterwards and
// computes 2 + 1.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/vec_codegen.rs::cow_retains_reused_gate found=S122 owner=/dev
#[test]
fn parameter_pushed_at_its_last_use_and_consumed_in_frame_balances() {
    measure(
        "(vec-len (vec-push p 0)) at p's last use",
        (
            on_fresh_vec("(add-i64 (vec-len (vec-push p 0)) (vec-len p))"),
            3,
        ),
        (on_fresh_vec("(vec-len (vec-push p 0))"), 2),
    )
    .assert_balanced("the pushed parameter consumed in its frame");
}

/// `f` binds `v` = [1] and `w` = `(vec-push v 0)`, then evaluates `body`.
fn let_chain(body: &str) -> Child {
    armed(&format!(
        "(defn f [] (let [v (vec-push [] 1) w (vec-push v 0)] {body}))\n\
         (defn main [] (Pure (f)))\n"
    ))
}

// spec: spec/12-runtime.md §12.3.1 and §12.3.3 — a `vec-push` on a `let`
// binding at its last use, bound to a second `let` binding, releases the
// vector exactly once at scope exit.
//
// W-L. The subject computes 2; the control also reads `v` and computes 2 + 1.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/vec_codegen.rs::cow_retains_reused_gate found=S122 owner=/dev
#[test]
fn let_binding_pushed_at_its_last_use_and_bound_again_balances() {
    measure(
        "(let [v … w (vec-push v 0)] …) at v's last use",
        (let_chain("(add-i64 (vec-len w) (vec-len v))"), 3),
        (let_chain("(vec-len w)"), 2),
    )
    .assert_balanced("the pushed let binding released at scope exit");
}

/// `go` pushes `n` onto `v` through a `let` intermediate for `steps` steps,
/// then returns the length of `(vec-push v 0)`. `v` never reaches the result
/// (`Consumed` flow). From [1] it computes `steps + 2`.
fn let_intermediate_loop(steps: i64) -> Child {
    armed(&format!(
        "(defn go [n v]\n\
           (if (eq-i64 n 0)\n\
               (vec-len (vec-push v 0))\n\
               (let [w (vec-push v n)] (go (add-i64 n -1) w))))\n\
         (defn main [] (Pure (go {steps} (vec-push [] 1))))\n"
    ))
}

/// One `key=N` counter from the child's `[RC_STATS]` exit line.
fn rc_stat(stderr: &str, key: &str) -> Option<i64> {
    let line = stderr.lines().rev().find(|l| l.contains("[RC_STATS]"))?;
    line.split_whitespace()
        .find_map(|word| word.strip_prefix(key)?.strip_prefix('=')?.parse().ok())
}

// spec: spec/12-runtime.md §12.3.1 and §12.3.3 — a self-tail loop that pushes
// onto its uniquely owned parameter through a `let` intermediate reuses the
// vector in place and releases every reference exactly once.
//
// W-LOOP. The pair differs only in the step count: the control runs no step
// and computes 2, the subject runs five and computes 7. Each step must take
// the in-place arm, so the subject reports exactly five more reuse hits than
// the control; a fix that makes the loop copy fails here.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/vec_codegen.rs::cow_retains_reused_gate found=S122 owner=/dev
#[test]
fn let_intermediate_push_loop_balances_and_reuses_in_place() {
    const STEPS: i64 = 5;
    let pair = measure(
        "five pushes through a let intermediate in a self-tail loop, Consumed flow",
        (let_intermediate_loop(0), 2),
        (let_intermediate_loop(STEPS), 7),
    );
    pair.assert_balanced("the let-intermediate push loop");
    let hits = |stderr: &str| rc_stat(stderr, "reuse_hit").expect("reuse_hit in [RC_STATS]");
    let added = hits(&pair.subject().stderr) - hits(&pair.control().stderr);
    assert_eq!(
        added,
        STEPS,
        "each step must reuse the vector in place\n{}\n--- subject stderr ---\n{}",
        pair.report(),
        pair.subject().stderr
    );
}

// spec: spec/12-runtime.md §12.3.1 and §12.3.3 — a `vec-set` on a parameter at
// its last use, forwarded by a variable-pattern `match` arm and consumed in
// the same frame, releases the vector exactly once.
//
// W-M, a safety fence for the `match` seam over an in-place scrutinee. The
// control matches the parameter itself; both halves start from [1 2] and
// compute 2. The residual is pinned at exactly 1: ACT-1026's missing release
// of a forwarded binder consumed in its frame (D1-M in
// `join_forwards_its_binder.rs`). Before the ACT-1024 fix the missing
// increment cancels it and the cell reads 0; a fault means a release remains
// on the forwarded value. ACT-1026's correction restores `assert_balanced`.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/vec_codegen.rs::cow_retains_reused_gate found=S122 owner=/dev
#[test]
fn parameter_set_at_its_last_use_and_forwarded_by_a_match_arm_balances() {
    let on_two_elements = |body: &str| {
        armed(&format!(
            "(defn f [v] {body})\n\
             (defn main [] (Pure (f (vec-push (vec-push [] 1) 2))))\n"
        ))
    };
    measure(
        "(match (vec-set v 0 5) [r r]) at v's last use",
        (on_two_elements("(vec-len (match v [r r]))"), 2),
        (
            on_two_elements("(vec-len (match (vec-set v 0 5) [r r]))"),
            2,
        ),
    )
    .assert_residual(
        1,
        "the in-place set forwarded by a match arm, with ACT-1026's leak",
    );
}
