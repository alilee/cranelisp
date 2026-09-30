//! A `let` or `match` whose value is its own binder hands that binder's
//! reference to its consumer (S122, ACT-1026 and ACT-1027;
//! `tests/plan/s122-evidence-delta.md`, "ACT-1024 — V1 record and the W-M
//! ruling" and "ACT-1024 with the R3 retirement"). Each side of that handoff
//! has a measured face:
//!
//! - D1 (ACT-1026, a leak): consumed in the same frame, the value is never
//!   released. The join transfers the reference out while the consumer reads a
//!   `Var`-valued join as not owned here.
//! - D2 (ACT-1027, use-after-free): a variable-pattern arm over a retaining
//!   copy-on-write scrutinee releases the scrutinee at the arm's end, but the
//!   retain exists only on the mutate branch, so on a copy the arm frees the
//!   only reference to the value it forwards.
//!
//! On 2026-09-30 (HEAD `e4062202`, source diff `872b59a9…`, binary
//! `a423324d…`) QA measured every D1 and D2 subject failing; the D1 subjects
//! leak with the ownership analysis on and off. The D1 and D2 `locus=` tokens
//! name the seams where the defects live, as the R3 ruling confirms.
//!
//! Every child runs with the seam checks armed, so a premature release stops
//! it at the faulting operation, and each half's result is asserted.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::marginal::{Child, Marginal, MarginalPair};

/// A `--run` child of `defs` with `vec` primitives imported and the seam
/// checks armed.
fn armed(defs: &str) -> Child {
    Child::new(&format!(
        "(import [primitives [Pure add-i64 vec-len vec-push vec-set]])\n{defs}"
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

// spec: spec/12-runtime.md §12.3.1 — a `match` whose arm yields its binder,
// consumed in the same frame, releases the matched vector exactly once.
//
// D1-M. The control returns the `match` from `f` and `main` takes its length;
// both compute 2.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::value_provenance_with_calls found=S122 owner=/dev
#[test]
fn match_yielding_its_binder_consumed_in_frame_releases_the_value() {
    measure(
        "(vec-len (match [1 2] [r r])) in f",
        (
            armed("(defn f [] (match [1 2] [r r]))\n(defn main [] (Pure (vec-len (f))))\n"),
            2,
        ),
        (
            armed("(defn f [] (vec-len (match [1 2] [r r])))\n(defn main [] (Pure (f)))\n"),
            2,
        ),
    )
    .assert_balanced("the forwarded match binder consumed in its frame");
}

// spec: spec/12-runtime.md §12.3.1 — a `let` whose body is its binder,
// consumed in the same frame, releases the bound vector exactly once.
//
// D1-L. The control returns the `let` from `f`; both compute 2.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::value_provenance_with_calls found=S122 owner=/dev
#[test]
fn let_yielding_its_binder_consumed_in_frame_releases_the_value() {
    measure(
        "(vec-len (let [r [1 2]] r)) in f",
        (
            armed("(defn f [] (let [r [1 2]] r))\n(defn main [] (Pure (vec-len (f))))\n"),
            2,
        ),
        (
            armed("(defn f [] (vec-len (let [r [1 2]] r)))\n(defn main [] (Pure (f)))\n"),
            2,
        ),
    )
    .assert_balanced("the forwarded let binder consumed in its frame");
}

/// `f` binds `w` to `value`, then `bindings`, and returns `w`; `main` takes
/// its length, 1.
fn bound_then(value: &str, bindings: &str) -> Child {
    armed(&format!(
        "(defn f [v] (let [w {value}{bindings}] w))\n\
         (defn main [] (Pure (vec-len (f (vec-push [] 1)))))\n"
    ))
}

const SET: &str = "(vec-set v 0 5)";
const SET_FORWARDED: &str = "(match (vec-set v 0 5) [r r])";
const V_USED_AFTER: &str = " n (vec-len v)";

// spec: spec/12-runtime.md §12.3.1 and §12.3.3 — a `vec-set` whose source is
// used afterwards yields a copy; a `match` arm forwarding that copy keeps it
// live for its consumer.
//
// D2-C, the compile-time copy path. Both halves read `v` after the set, so
// both copy; the control binds the copy without the `match`, so the pair
// isolates the match seam. The control leaks one block of its own, which the
// pair subtracts; that leak is ACT-1028's, so a balanced pair shows only that
// the arm forwards transparently. Both compute 1.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/match_codegen.rs::scrutinee_lifetime_for_arm found=S122 owner=/dev
#[test]
fn match_arm_forwarding_a_compile_time_cow_copy_keeps_it_live() {
    measure(
        "(match (vec-set v 0 5) [r r]) with v used afterwards",
        (bound_then(SET, V_USED_AFTER), 1),
        (bound_then(SET_FORWARDED, V_USED_AFTER), 1),
    )
    .assert_balanced("the forwarded copy returned from f");
}

/// `f` forwards a `vec-set` of its parameter through a variable-pattern arm;
/// `main` is `main_body`.
fn set_forwarded_by_callee(main_body: &str) -> Child {
    armed(&format!(
        "(defn f [v] (match (vec-set v 0 5) [r r]))\n(defn main [] {main_body})\n"
    ))
}

// spec: spec/12-runtime.md §12.3.1 and §12.3.3 — a `vec-set` on a shared
// vector copies at runtime; a `match` arm forwarding that copy keeps it live
// for its consumer.
//
// D2-R, the runtime copy branch. The subject keeps `v` in `main`, so the set
// copies, and adds both lengths, 2; the control passes a fresh vector, so the
// set mutates in place, and computes 1.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/match_codegen.rs::scrutinee_lifetime_for_arm found=S122 owner=/dev
#[test]
fn match_arm_forwarding_a_runtime_cow_copy_keeps_it_live() {
    measure(
        "(match (vec-set v 0 5) [r r]) on a shared v",
        (
            set_forwarded_by_callee("(Pure (vec-len (f (vec-push [] 1))))"),
            1,
        ),
        (
            set_forwarded_by_callee(
                "(let [v (vec-push [] 1) w (f v)] (Pure (add-i64 (vec-len w) (vec-len v))))",
            ),
            2,
        ),
    )
    .assert_balanced("the forwarded copy returned to a caller that keeps v");
}
