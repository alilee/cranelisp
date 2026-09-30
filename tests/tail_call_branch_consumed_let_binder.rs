//! A heap value forwarded bare through a branch of a self-tail-call argument
//! (ACT-1021; S122 intake, found executing the `repl/spec/16-test-discovery.md`
//! §16.5 runner example).
//!
//! `sel` walks a vector; each iteration binds `pair` and passes
//! `(if keep (vec-push lines (run-one pair)) lines)` to its tail call. With
//! `keep` true the branch consumes `pair` and the program balances. With `keep`
//! false `pair` is unused on the taken branch and the loop parameter `lines`
//! is forwarded bare by the `else`. On 2026-09-30 (source diff `66d4f7a4…`)
//! the armed `CRANELISP_RC_DEC_CHECK` stopped the child with
//! `STALE RC DEC … already freed and reclaimed`; unarmed, the §16.5 REPL
//! session aborted in glibc (`corrupted double-linked list`). The first pair
//! differs only in `keep`, so it confirms the symptom but not which of `pair`
//! and `lines` is freed. D1 and D2 below separate them: the forwarded
//! parameter is freed, and the `let` binder is released correctly.
//!
//! The marginal pairs are the ACT-1021 correction evidence
//! (`tests/plan/s122-evidence-delta.md`, "ACT-1021 — correction evidence
//! delta"). The C-cells pin which slots need a protective reference when a
//! branch forwards a binding, and C-IR fences the in-place push loop beside
//! them. Every child runs with the seam checks armed, so a
//! premature release stops it at the faulting operation, and each half's
//! computed result is asserted.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;
use helpers::marginal::{Child, Marginal, MarginalPair};

fn program(keep: &str) -> String {
    format!(
        "(import [primitives [Pair Some None Pure str-concat add-i64 eq-i64 vec-len \
                              vec-get vec-push]])\n\
         (defn t [] (if true None (Some \"x\")))\n\
         (defn run-one [pair] (match pair [(Pair name run) name]))\n\
         (defn sel [pairs keep i lines]\n\
           (if (eq-i64 i (vec-len pairs))\n\
               lines\n\
               (let [pair (vec-get pairs i)]\n\
                 (sel pairs keep (add-i64 i 1)\n\
                   (if keep (vec-push lines (run-one pair)) lines)))))\n\
         (defn main []\n\
           (let [pairs [(Pair (str-concat \"a\" \"b\") t)]\n\
                 out (sel pairs {keep} 0 [])]\n\
             (Pure (vec-len out))))\n"
    )
}

/// One `key=N` counter from the child's `[RC_STATS]` exit line.
fn rc_stat(stderr: &str, key: &str) -> Option<i64> {
    let line = stderr.lines().rev().find(|l| l.contains("[RC_STATS]"))?;
    line.split_whitespace()
        .find_map(|word| word.strip_prefix(key)?.strip_prefix('=')?.parse().ok())
}

fn allocs_and_deallocs(stderr: &str) -> Option<(i64, i64)> {
    Some((rc_stat(stderr, "allocs")?, rc_stat(stderr, "deallocs")?))
}

/// Run with `keep`, the seam checks armed: the program must return `exit`,
/// report no seam violation, and free every allocation.
fn releases_exactly_once(keep: &str, exit: i32) {
    let out = Cranelisp::new()
        .file("user.cl", &program(keep))
        .run("user.cl")
        .env("CRANELISP_RC_DEC_CHECK", "1")
        .env("CRANELISP_RC_STATS", "1")
        .output();
    let counts = allocs_and_deallocs(&out.stderr);
    assert!(
        out.status.code() == Some(exit)
            && !out.stderr.contains("STALE RC DEC")
            && !out.stderr.contains("SEAM VIOLATION")
            && counts.is_some_and(|(a, d)| a == d),
        "keep={keep}: exit {exit}, no stale release and balanced counts expected; \
         got exit {:?}, counts {counts:?}\n--- stderr:\n{}",
        out.status.code(),
        out.stderr
    );
}

// spec: spec/12-runtime.md §12.3.1 — a heap value that one branch of a tail-call
// argument leaves unused is released exactly once, and never before its last use.
//
// The freed value is the parameter `lines`, forwarded by the `else` (D1, D2).
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::tail_flush_will_dec found=S122 owner=/dev
#[test]
fn let_binder_unused_on_the_taken_branch_of_a_tail_argument_is_released_once() {
    releases_exactly_once("false", 0);
}

// spec: spec/12-runtime.md §12.3.1 — the control: the taken branch consumes
// the binder.
#[test]
fn let_binder_consumed_on_the_taken_branch_of_a_tail_argument_control() {
    releases_exactly_once("true", 1);
}

// ---------------------------------------------------------------------------
// ACT-1021 marginal pairs
// ---------------------------------------------------------------------------

const IMPORTS: &str = "(import [primitives [Pair Some None Pure str-concat add-i64 eq-i64 \
                                          vec-len vec-get vec-push]])\n";

/// A `--run` child of `IMPORTS` + `defs`, with the seam checks armed.
fn armed(defs: &str) -> Child {
    Child::new(&format!("{IMPORTS}{defs}")).env("CRANELISP_RC_DEC_CHECK", "1")
}

/// Measure the pair and require each half's computed result, so a freed or
/// shared value cannot hide behind balanced counts. A half stopped by the
/// armed check fails inside `measure` with the check's report.
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

/// The filed loop without its `let` binder: `lines` is a heap parameter and
/// the `else` branch forwards it bare into its own slot.
fn d1(keep: &str) -> Child {
    armed(&format!(
        "(defn t [] (if true None (Some \"x\")))\n\
         (defn sel [pairs keep i lines]\n\
           (if (eq-i64 i (vec-len pairs))\n\
               lines\n\
               (sel pairs keep (add-i64 i 1)\n\
                 (if keep (vec-push lines \"x\") lines))))\n\
         (defn main []\n\
           (let [pairs [(Pair (str-concat \"a\" \"b\") t)]\n\
                 out (sel pairs {keep} 0 [])]\n\
             (Pure (vec-len out))))\n"
    ))
}

// spec: spec/12-runtime.md §12.3.1 — a heap loop parameter forwarded bare
// through the `else` of an `if` tail argument is released once, after its
// last use.
//
// D1. The pair differs only in `keep`; the control takes the consuming branch.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::tail_flush_will_dec found=S122 owner=/dev
#[test]
fn param_forwarded_bare_through_an_if_tail_argument_balances() {
    measure(
        "a heap parameter forwarded through the else branch",
        (d1("true"), 1),
        (d1("false"), 0),
    )
    .assert_balanced("the parameter forwarded through an if tail argument");
}

/// The filed subject with its `else` branch made a fresh value, so `lines` is
/// never forwarded bare while `pair` stays unused on the taken branch.
fn d2(keep: &str) -> Child {
    armed(&format!(
        "(defn t [] (if true None (Some \"x\")))\n\
         (defn run-one [pair] (match pair [(Pair name run) name]))\n\
         (defn sel [pairs keep i lines]\n\
           (if (eq-i64 i (vec-len pairs))\n\
               lines\n\
               (let [pair (vec-get pairs i)]\n\
                 (sel pairs keep (add-i64 i 1)\n\
                   (if keep (vec-push lines (run-one pair)) (vec-push [] \"y\"))))))\n\
         (defn main []\n\
           (let [pairs [(Pair (str-concat \"a\" \"b\") t)]\n\
                 out (sel pairs {keep} 0 [])]\n\
             (Pure (vec-len out))))\n"
    ))
}

// spec: spec/12-runtime.md §12.3.1 — a `let` binder left unused by the taken
// branch of a tail argument is released exactly once.
//
// D2, the attribution observer: it separates the `let` binder from the
// forwarded parameter.
#[test]
fn let_binder_unused_by_a_fresh_else_branch_balances() {
    measure(
        "the let binder unused on a fresh else branch",
        (d2("true"), 1),
        (d2("false"), 1),
    )
    .assert_balanced("the let binder with no forwarded parameter");
}

/// A loop over two heap slots `p` and `q` whose recursive step is `step`.
/// Three steps run from `p` = [1] and `q` = [9]; the base case reads both
/// lengths and then nests both slots into a new vector, so each is `Owned`
/// with `IntoResult` flow. The result is `len p + len q + 2`.
///
/// The base case avoids `(vec-push p 0)`: an in-place push on a parameter
/// whose slot a fresh value replaced is a separate fault
/// (`tail_call_replaced_param_consumed_in_place.rs`), and it would stop C-LT's
/// control.
fn two_slots(step: &str) -> Child {
    two_slots_with(
        "(add-i64 (add-i64 (vec-len p) (vec-len q))\n\
                  (vec-len (vec-push (vec-push [] p) q)))",
        step,
    )
}

/// A base case with `Consumed` flow: it reads both lengths and then pushes onto
/// each slot, so neither parameter reaches the result. The result is
/// `len p + len q + (len p + 1) + (len q + 1)`.
const CONSUMED_BASE: &str = "(add-i64 (add-i64 (vec-len p) (vec-len q))\n\
                                      (add-i64 (vec-len (vec-push p 0)) (vec-len (vec-push q 0))))";

/// `two_slots` with the base case given.
fn two_slots_with(base: &str, step: &str) -> Child {
    armed(&format!(
        "(defn go [n c p q]\n\
           (if (eq-i64 n 0)\n\
               {base}\n\
               {step}))\n\
         (defn main [] (Pure (go 3 true (vec-push [] 1) (vec-push [] 9))))\n"
    ))
}

/// The self-tail call with `p_arg` and `q_arg` in the two heap slots.
fn recur(p_arg: &str, q_arg: &str) -> String {
    format!("(go (add-i64 n -1) c {p_arg} {q_arg})")
}

// spec: spec/12-runtime.md §12.3.1 — a heap parameter moved into its own slot
// and also forwarded, on the taken branch, into another slot is released
// exactly once per reference.
//
// C-PT. `p` is `Owned` (`CRANELISP_OWNERSHIP_TRACE`: `modes=[Copy, Copy,
// Owned, Owned]`). The control's branch yields a fresh vector; both compute
// 1 + 1 + 2.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::tail_flush_will_dec found=S122 owner=/dev
#[test]
fn param_moved_and_forwarded_through_a_branch_balances() {
    measure(
        "a moved parameter also forwarded through a branch",
        (two_slots(&recur("p", "(if c (vec-push [] 7) q)")), 4),
        (two_slots(&recur("p", "(if c p q)")), 4),
    )
    .assert_balanced("the moved parameter forwarded through a branch");
}

// spec: spec/12-runtime.md §12.3.1 — a `let`-bound heap value moved into a
// parameter slot and also forwarded, on the taken branch, into another slot
// is released exactly once per reference.
//
// C-LT: C-PT with a `let` binding in place of the parameter. Both compute
// 1 + 1 + 2.
#[test]
fn let_value_moved_and_forwarded_through_a_branch_balances() {
    let step = |forward: &str| format!("(let [v (vec-push [] 5)] {})", recur("v", forward));
    measure(
        "a moved let binding also forwarded through a branch",
        (two_slots(&step("(if c (vec-push [] 7) q)")), 4),
        (two_slots(&step("(if c v q)")), 4),
    )
    .assert_balanced("the moved let binding forwarded through a branch");
}

/// `lines` = [a b c] forwarded by the constructor-pattern arm of a `match`
/// tail argument, or a fresh two-element vector in its place. The subject
/// computes 3 and the control 2; neither is the exit of a rejected program.
fn match_forward(arm: &str) -> Child {
    armed(&format!(
        "(defn go [n o lines]\n\
           (if (eq-i64 n 0)\n\
               (vec-len lines)\n\
               (go (add-i64 n -1) o\n\
                 (match o [(Some s) {arm} None (vec-push lines \"z\")]))))\n\
         (defn main []\n\
           (Pure (go 3 (Some (str-concat \"a\" \"b\"))\n\
                       (vec-push (vec-push (vec-push [] \"a\") \"b\") \"c\"))))\n"
    ))
}

// spec: spec/12-runtime.md §12.3.1 — a heap parameter forwarded bare by a
// constructor-pattern arm of a `match` tail argument is released once.
//
// C-M. The control's arm yields a fresh vector.
#[test]
fn param_forwarded_by_a_constructor_pattern_arm_balances() {
    measure(
        "a parameter forwarded by a constructor-pattern arm",
        (match_forward("(vec-push (vec-push [] \"y\") \"w\")"), 2),
        (match_forward("lines"), 3),
    )
    .assert_balanced("the parameter forwarded by a match arm");
}

// spec: spec/12-runtime.md §12.3.1 and §12.3.3 — a parameter forwarded
// through a branch before an in-place-eligible `vec-push` on it keeps its own
// value; the push copies and every reference is released once.
//
// C-C1 (branch first). `p` = [1] throughout and `q` = [1 1], so the subject
// computes 1 + 2 + 2; the control (`p` = [7], `q` = [7 1]) computes the same.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::tail_flush_will_dec found=S122 owner=/dev
#[test]
fn branch_forward_before_an_inplace_push_balances() {
    measure(
        "a branch forward of p before (vec-push p 1)",
        (
            two_slots(&recur("(if c (vec-push [] 7) q)", "(vec-push p 1)")),
            5,
        ),
        (two_slots(&recur("(if c p q)", "(vec-push p 1)")), 5),
    )
    .assert_balanced("the branch-forwarded parameter beside an in-place push");
}

// spec: spec/12-runtime.md §12.3.1 and §12.3.3 — a parameter forwarded
// through a branch before a `vec-push` on it, with neither parameter reaching
// the result, releases every reference exactly once.
//
// C-C1c: C-C1's step over the `Consumed` base, the only difference from C-C1.
// The branch forward leaves `p` shared, so the push copies and must release
// the parameter slot's reference itself. The subject keeps `p` = [1] and ends
// with `q` = [1 1]; the control ends with `p` = [7] and `q` = [7 1]. Both
// compute 1 + 2 + 2 + 3. At `e4062202` the subject's copying push read a freed
// `p`.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::tail_flush_will_dec found=S122 owner=/dev
#[test]
fn branch_forward_before_an_inplace_push_with_consumed_flow_balances() {
    measure(
        "a branch forward of p before (vec-push p 1), Consumed flow",
        (
            two_slots_with(
                CONSUMED_BASE,
                &recur("(if c (vec-push [] 7) q)", "(vec-push p 1)"),
            ),
            8,
        ),
        (
            two_slots_with(CONSUMED_BASE, &recur("(if c p q)", "(vec-push p 1)")),
            8,
        ),
    )
    .assert_balanced("the copying push beside a branch-forwarded parameter");
}

// spec: spec/12-runtime.md §12.3.1 and §12.3.3 — an in-place-eligible
// `vec-push` on a parameter followed by a branch that forwards it releases
// every reference exactly once.
//
// C-C2 (COW first), with `Consumed` flow. After three steps `p` = [1 1 1 1]
// and `q` is the previous `p`, so the subject computes 4 + 3 + 5 + 4; the
// control's fresh `q` gives 4 + 1 + 5 + 2. A safety fence that gates ACT-1021
// acceptance: the push here only copies, so the parameter flush must release
// `p` even though a push is rooted at it.
#[test]
fn inplace_push_before_a_branch_forward_balances() {
    measure(
        "(vec-push p 1) before a branch forward of p, Consumed flow",
        (
            two_slots_with(
                CONSUMED_BASE,
                &recur("(vec-push p 1)", "(if c (vec-push [] 7) q)"),
            ),
            12,
        ),
        (
            two_slots_with(CONSUMED_BASE, &recur("(vec-push p 1)", "(if c p q)")),
            16,
        ),
    )
    .assert_balanced("the in-place push beside a branch-forwarded parameter");
}

// spec: spec/12-runtime.md §12.3.1 and §12.3.3 — the same step as C-C2 when
// the parameters flow into the result.
//
// C-C2′: C-C2 with `IntoResult` flow (`two_slots`), the only difference from
// the cell above. It computes 4 + 3 + 2 and 4 + 1 + 2. Before the ACT-1021
// correction both twins copied at the push and forwarded `p` bare through the
// branch; this twin's jump then released `p`, freeing the forwarded copy,
// while the `Consumed` twin's flush skipped `p` and hid the fault.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::tail_flush_will_dec found=S122 owner=/dev
#[test]
fn inplace_push_before_a_branch_forward_into_the_result_balances() {
    measure(
        "(vec-push p 1) before a branch forward of p, IntoResult flow",
        (
            two_slots(&recur("(vec-push p 1)", "(if c (vec-push [] 7) q)")),
            7,
        ),
        (two_slots(&recur("(vec-push p 1)", "(if c p q)")), 9),
    )
    .assert_balanced("the in-place push beside a branch-forwarded parameter");
}

/// `build` pushes `i` onto `v` for `i` from 0 to `steps - 1` and returns `v`,
/// so `v` flows into the result. `main` starts from [7 7] and computes the
/// final length plus the last element.
fn build_loop(steps: i64) -> Child {
    armed(&format!(
        "(defn build [v i n]\n\
           (if (eq-i64 i n) v (build (vec-push v i) (add-i64 i 1) n)))\n\
         (defn main []\n\
           (let [out (build (vec-push (vec-push [] 7) 7) 0 {steps})]\n\
             (Pure (add-i64 (vec-len out) (vec-get out (add-i64 (vec-len out) -1))))))\n"
    ))
}

// spec: spec/12-runtime.md §12.3.1 and §12.3.3 — a self-tail loop that pushes
// onto its own uniquely owned vector reuses it in place and releases every
// reference exactly once.
//
// C-IR. The pair differs only in the step count: the control runs no step and
// computes 2 + 7, the subject runs five and computes 7 + 4. Each step must
// take the in-place arm, so the subject reports exactly five more reuse hits
// than the control; a push that copies instead, or releases the box it
// forwarded, fails here.
#[test]
fn inplace_push_loop_into_the_result_balances_and_reuses_in_place() {
    const STEPS: i64 = 5;
    let pair = measure(
        "five in-place pushes in a self-tail loop, IntoResult flow",
        (build_loop(0), 9),
        (build_loop(STEPS), 11),
    );
    pair.assert_balanced("the in-place push loop");
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
