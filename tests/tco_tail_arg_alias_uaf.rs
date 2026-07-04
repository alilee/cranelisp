//! Wave 11 B3.1a-R â F1 use-after-free repro (VALUE-correctness).
//!
//! The TCO scope-flush (`flush_let_scopes_before_tail_jump`, commit `f87b128`)
//! dec's every heap `let`-binding before a tail self-call jump, EXCEPT bindings
//! passed as a literal top-level `MonoExpr::Var` tail argument (`transfer_skip`,
//! `apply.rs`). A binding whose pointer is **aliased into a tail argument
//! through a control-flow form** (`if` / `match`) reaches the arg value with NO
//! owning inc (`compile_if` merges the raw branch value; a bare local `Var` is a
//! plain `use_var`). It is NOT in `transfer_skip`, so the flush dec's it to rc=0
//! and frees it â then the jump hands the freed pointer to the next iteration's
//! loop param â **use-after-free**.
//!
//! This is exactly the `feedback_verify_fix_not_symptom_absence` false-green: the
//! RC-balance is NEAR-BALANCED (`allocsâ201 deallocsâ200`) because the freed
//! alloc *is* accounted â memory is corrupt while the leak guard reads green.
//! So this repro asserts the **computed RESULT**, not RC balance.
//!
//! spec: spec/12-runtime.md Â§12.3.1 â heap values MUST stay live while
//! reachable; a value handed forward into the next tail-recursive iteration is
//! reachable and MUST NOT be freed by the scope flush.
//!
//! RED on HEAD (returns garbage / corrupted-header out-of-bounds, not `7`).
//! FIXME(/backend): resolver = the control-flow-alias protection in
//! `compile_tail_self_call` / `compile_if` / `compile_match`.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

fn prims_repl(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(lines)
        .output()
}

// The exact reduced shape from the /review B3.1a finding. The tail arg
// `(if (eq-i64 n 1) a a)` aliases the heap `let`-binding `a` = [7 8 9] into the
// tail call with no owning inc. On HEAD the flush frees `a`, so the final
// `(vec-get xs 0)` reads freed memory and returns garbage instead of `7`.
// spec: spec/12-runtime.md §12.3.1 — heap values MUST stay live while reachable
#[test]
fn tco_if_aliased_tail_arg_same_binding_is_not_freed() {
    prims_repl(
        "(defn g [:Int n :(Vec Int) xs] \
           (if (eq-i64 n 0) \
               (vec-get xs 0) \
               (let [a [7 8 9]] \
                 (g (sub-i64 n 1) (if (eq-i64 n 1) a a)))))\n\
         (g 200 [1 2 3])\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 7");
}

// Two DIFFERENT bindings selected per-branch (the quicksort `(recur (if flag lo
// hi) â¦)` shape). Whichever branch runs, that binding must move forward and the
// OTHER (dead) binding must be freed â a single static flush-dec cannot do
// "dec lo XOR dec hi", so per-branch protection + uniform flush is required.
// At the last recursive step n==1 â `(eq-i64 n 1)` true â `lo` is selected, so
// the forwarded vec is `lo` = [1 2 3] and `xs[0]` must read `1` (a stable value,
// not HEAD's garbage â proving `lo` survived and `hi` was freed on the dead arm).
// spec: spec/12-runtime.md §12.3.1 — heap values MUST stay live while reachable
#[test]
fn tco_if_aliased_tail_arg_distinct_bindings_selects_correctly() {
    prims_repl(
        "(defn g [:Int n :(Vec Int) xs] \
           (if (eq-i64 n 0) \
               (vec-get xs 0) \
               (let [lo [1 2 3] hi [7 8 9]] \
                 (g (sub-i64 n 1) (if (eq-i64 n 1) lo hi)))))\n\
         (g 200 [0 0 0])\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 1");
}

// Behavioral UAF hardening (`feedback_verify_fix_not_symptom_absence`): run the
// aliased-tail-arg repro at high N under `MALLOC_PERTURB_`, which fills freed
// chunks with a byte pattern. If the flush still freed `a` while the next
// iteration owned it, the reused chunk would be poisoned and `vec-get` would
// read the pattern (garbage), not `7` â across 3000 iterations. A stable `7`
// under perturbation is behavioral evidence the value stays live, not a
// balance-passing false-green.
// spec: spec/12-runtime.md §12.3.1 — heap values MUST stay live while reachable
#[test]
fn tco_if_aliased_tail_arg_no_uaf_under_malloc_perturb() {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .env("MALLOC_PERTURB_", "165")
        .stdin(
            "(defn g [:Int n :(Vec Int) xs] \
               (if (eq-i64 n 0) \
                   (vec-get xs 0) \
                   (let [a [7 8 9]] \
                     (g (sub-i64 n 1) (if (eq-i64 n 1) a a)))))\n\
             (g 3000 [1 2 3])\n",
        )
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 7");
}

// A `match`-arm aliased tail arg exercises the constructor-pattern arm path
// (match-arm aliasing must be handled too): body `a` is an outer live heap
// let-binding aliased through the arm into the tail call. Must read `7`.
// spec: spec/12-runtime.md §12.3.1 — heap values MUST stay live while reachable
#[test]
fn tco_match_aliased_tail_arg_is_not_freed() {
    prims_repl(
        "(deftype Box [:Int v])\n\
         (defn g [:Int n :(Vec Int) xs] \
           (if (eq-i64 n 0) \
               (vec-get xs 0) \
               (let [a [7 8 9]] \
                 (g (sub-i64 n 1) (match (Box n) [(Box k) a])))))\n\
         (g 200 [1 2 3])\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 7");
}

// The bare-Var control the /review names: `(g (sub-i64 n 1) a)` moves `a`
// forward with no inc and the flush correctly SKIPS it (transfer_skip). Value
// must be right; the fix must not disturb the move path. GREEN on HEAD.
// (No RC-balance claim here: forwarding a fresh heap `a` into a heap `xs` param
// leaks the *previous* param each iteration â a pre-existing TCO param-frame
// leak explicitly out of F1's scope; the let-binding cure is isolated in the
// next test with non-heap params.)
// spec: spec/12-runtime.md §12.3.1 — heap values MUST stay live while reachable
#[test]
fn tco_bare_var_tail_arg_control_is_correct() {
    prims_repl(
        "(defn g [:Int n :(Vec Int) xs] \
           (if (eq-i64 n 0) \
               (vec-get xs 0) \
               (let [a [7 8 9]] \
                 (g (sub-i64 n 1) a))))\n\
         (g 200 [1 2 3])\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 7");
}

// The ORIGINAL leak `f87b128` cured, isolated: a heap `let`-binding created
// and USED each iteration but NOT forwarded into the tail call, with non-heap
// params (no param-frame confound). The flush MUST dec `a` each iteration;
// pre-`f87b128` this leaked ~200 allocs. Confirms the fix keeps that cure while
// adding the control-flow-alias protection. Result = 200 Ã 7 = 1400.
// spec: spec/12-runtime.md §12.3.1 — heap values MUST stay live while reachable
#[test]
fn tco_surviving_let_binding_still_flushed_no_leak() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .env("CRANELISP_RC_STATS", "1")
        .stdin(
            "(defn g [:Int n :Int acc] \
               (if (eq-i64 n 0) \
                   acc \
                   (let [a [7 8 9]] \
                     (g (sub-i64 n 1) (add-i64 acc (vec-get a 0))))))\n\
             (g 200 0)\n",
        )
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 1400");

    let imbalance = out
        .stderr
        .lines()
        .find(|l| l.contains("[RC_STATS]"))
        .and_then(|line| {
            let field = |k: &str| -> Option<i64> {
                line.split_whitespace()
                    .find_map(|t| t.strip_prefix(&format!("{k}=")))
                    .and_then(|v| v.parse().ok())
            };
            Some(field("allocs")? - field("deallocs")?)
        })
        .unwrap_or_else(|| panic!("no [RC_STATS] line on stderr: {}", out.stderr));
    assert!(
        imbalance <= 16,
        "surviving heap let-binding must be flushed each iteration (original \
         f87b128 cure intact): imbalance {imbalance}"
    );
}
