// shadowing_scope_lookup.rs — S112 W6, /qa rulings 4 & 5 (plan §11, §12).
//
// The name-shadowing × callee-kind matrix — a RELATIONAL cell family that
// NO S112 matrix enumerated (the standing-category finding, plan §12): a
// let-binding that lexically shadows a same-named top-level definition MUST win
// at the call site. Two mechanisms, two rows:
//
//   Ruling 4 — SINGLE-sig defn shadowed. `(defn s1 [x] (let [s1 (fn [y] y)]
//   (s1 x)))` + `(s1 5)`: the local `s1` is the identity, so `(s1 x)` MUST call
//   it → 5. On HEAD the call-head resolves to the OUTER defn instead
//   (self-recursion → TCO loop, not stack overflow) → the session HANGS. The
//   /clif lens is blocked by the runtime hang (JIT-on-call never returns; a
//   codegen trace emits nothing before the loop), so attribution stays
//   PROVISIONAL: typecheck records `s1`'s type as `(Fn [a] a)` — consistent with
//   the LOCAL-identity reading, so the TYPE is right; the bug is the call-head's
//   scope resolution / emission. `class=wrong-scope-lookup owner=/dev`
//   (typecheck, call-head scope-resolution seam; pending call-chain confirmation
//   per ruling 4 — if the carrier is correct and the backend emits a top-level
//   call anyway, attribution moves backend-side).
//
//   Ruling 5 — MULTI-sig base shadowed (SIBLING cell, distinct mechanism).
//   `infer.rs:605` defers ANY Var call whose name is an overload base — even
//   when let-shadowed — so the local binding is bypassed at the GATE (before
//   resolution proper). The failure face differs from ruling 4: NOT a hang but a
//   wrong-REJECT (ambiguity at the enclosing defn, so it never defines). Two
//   rows because they will not necessarily fix together.
//
// Both PRE-EXISTING (found by W2-review probing, not a wave regression).
//
// HANG-BUDGET CAVEAT: the ruling-4 call cell HANGS, so it is bounded with an
// explicit short `.timeout(...)` and driven via `try_output()`; a hang consumes
// that whole timeout. The value-ref twin and the ruling-5 cell terminate
// promptly. See the /testing W6 report for the run-duration note.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{CrError, Cranelisp, PreludeVariant};
use std::time::Duration;

// Short bound for the hanging cell — long enough to distinguish a genuine loop
// from a slow-but-terminating run, short enough to not blow the suite budget.
const HANG_BOUND: Duration = Duration::from_secs(8);

// spec: spec/05-definitions.md §5.1.2 + spec/04-expressions.md §4.6 (let
// scoping) — a `let`-bound name lexically shadows a same-named top-level defn;
// a CALL to that name inside the let body MUST resolve to the LOCAL binding.
// `(defn s1 [x] (let [s1 (fn [y] y)] (s1 x)))` makes `s1` the identity, so
// `(s1 5)` MUST yield 5.
//
// RED at HEAD: `(s1 x)` resolves to the OUTER `s1` (self-recursion → TCO loop)
// → the session HANGS; `(s1 5)` never produces `:primitives/Int 5`. The bound
// timeout turns the hang into a loud, failing-not-ignored RED.
// defect: class=wrong-scope-lookup locus=crates/cranelisp-typecheck call-head scope resolution seam (let-shadowed single-sig defn — call resolves to the outer defn, TCO loop; provisional, /clif blocked by the hang) found=S112 owner=/dev
#[test]
fn let_shadowed_single_sig_defn_call_resolves_to_local_not_outer() {
    let result = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("(defn s1 [x] (let [s1 (fn [y] y)] (s1 x)))\n(s1 5)\n")
        .timeout(HANG_BOUND)
        .try_output();

    match result {
        Ok(out) => {
            let c = format!("{}{}", out.stdout, out.stderr);
            assert!(
                out.stdout.contains(":primitives/Int 5"),
                "`(s1 5)` MUST call the LOCAL identity `(fn [y] y)` (the let \
                 binding shadows the outer defn) and yield 5 — the call-head \
                 MUST NOT resolve to the outer `s1`; got:\n{c}"
            );
        }
        Err(CrError::Timeout(d)) => panic!(
            "`(s1 5)` HUNG (timed out after {d:?}): the let-shadowed `(s1 x)` \
             call resolved to the OUTER `s1` (self-recursion → TCO loop) instead \
             of the LOCAL identity binding — it MUST yield `:primitives/Int 5` \
             (wrong-scope-lookup, ruling 4)"
        ),
        Err(e) => panic!("unexpected harness error: {e}"),
    }
}

// spec: spec/04-expressions.md §4.6 — the VALUE-REF twin cell (ruling 4, second
// cell of the §12 shadowing matrix): returning the let-bound `s1` as a VALUE
// (not calling it) resolves to the LOCAL binding correctly and TERMINATES — the
// contrast that isolates the CALL-head as the bug. `(defn s2 [x] (let [s1 (fn
// [y] y)] s1))` echoes `s1`'s type as the inner closure `(Fn [a] (Fn [b] b))`,
// proving the value-ref position sees the local binding. It MUST NOT hang.
// GREEN control (terminates); pins that the defect is CALL-position-specific.
#[test]
fn let_shadowed_single_sig_value_ref_resolves_to_local_and_terminates() {
    let result = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("(defn s2 [x] (let [s1 (fn [y] y)] s1))\n")
        .timeout(HANG_BOUND)
        .try_output();

    match result {
        Ok(out) => {
            let c = format!("{}{}", out.stdout, out.stderr);
            // The value-ref sees the LOCAL `(fn [y] y)` — s2's type carries the
            // inner closure `(Fn [b] b)` in return position (not the outer s1).
            assert!(
                c.contains("(Fn [b] b)") || c.contains("(Fn [a] (Fn [b] b))"),
                "the value-ref `s1` MUST resolve to the LOCAL closure `(fn [y] \
                 y)` — s2's scheme carries the inner `(Fn [b] b)` in return \
                 position (proving the value-ref position sees the local \
                 binding, unlike the call position which hangs); got:\n{c}"
            );
        }
        Err(CrError::Timeout(d)) => panic!(
            "the value-ref twin HUNG (timed out after {d:?}) — it MUST terminate \
             (only the CALL position mis-resolves; this is the isolating control)"
        ),
        Err(e) => panic!("unexpected harness error: {e}"),
    }
}

// spec: spec/05-definitions.md §5.1.2 + §4.6 — the MULTI-sig-base sibling
// (ruling 5): `m1` is a multi-signature base; a `let` binding shadows it, and a
// CALL to the shadowed name inside the let body MUST resolve to the LOCAL
// binding. `(defn t1 [x] (let [m1 (fn [y] y)] (m1 x)))` + `(t1 5)` MUST yield 5.
//
// RED at HEAD (distinct mechanism from ruling 4): the overload gate
// (`infer.rs:605`) defers ANY Var call whose name is an overload base EVEN when
// let-shadowed, so the local binding is bypassed at the GATE — `t1` wrong-
// rejects with a residual-var ambiguity and is never defined (`undefined
// variable: t1` at the call). Failing-not-ignored.
// defect: class=wrong-scope-lookup locus=crates/cranelisp-typecheck/src/infer.rs:605 overload-base gate (let-shadowed multi-sig base bypassed at the gate before resolution) found=S112 owner=/dev
#[test]
fn let_shadowed_multi_sig_base_call_resolves_to_local_not_overload() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(
            "(defn m1 ([x] x) ([a b] a))\n\
             (defn t1 [x] (let [m1 (fn [y] y)] (m1 x)))\n\
             (t1 5)\n",
        )
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains(":primitives/Int 5"),
        "`(t1 5)` MUST call the LOCAL identity `m1` (the let binding shadows the \
         multi-sig base) and yield 5 — the overload-base gate MUST NOT bypass \
         the local binding; got:\n{c}"
    );
    assert!(
        !c.contains("undefined variable: t1"),
        "`t1` MUST define (the shadowed `(m1 x)` resolves to the local binding, \
         not the ambiguous overload base); got:\n{c}"
    );
}

// PS-SH1 matrix completion — the MULTI-sig-base × VALUE-REF cell (the missing
// {multi-sig} × {value-ref} corner of {single,multi} × {call,value-ref}). A `let`
// shadows a multi-sig base `h` with a local closure, and the shadowed name is used
// in VALUE position (passed to a HOF). The value-ref MUST resolve to the LOCAL
// closure `(fn [y] 100)` → `(use-hof h)` = 100.
//
// RED at HEAD: the value-ref resolves to the module-level multi-sig BASE (not the
// let-local) → `multi-sig function 'h' cannot be used as a value` — the shadowing
// fix (PS-SH1 call cell, closed W2) did not cover the value-ref position. The
// single-sig value-ref twin is GREEN; this multi-sig sibling is the residual.
// spec: spec/05-definitions.md §5.1.2 + §4.6 — a let binding shadows a multi-sig
// base in VALUE position; the value-ref sees the local binding.
// defect: class=wrong-scope-lookup locus=crates/cranelisp-typecheck value-ref of a let-shadowed multi-sig base resolves to the module overload base, not the local binding found=S113 owner=/dev
#[test]
fn let_shadowed_multi_sig_base_value_ref_resolves_to_local_not_overload() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(
            "(defn h ([x] (add-i64 x 1)) ([a b] a))\n\
             (defn use-hof [f] (f 5))\n\
             (defn g [] (let [h (fn [y] 100)] (use-hof h)))\n\
             (defn main [] (Pure (g)))\n",
        )
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        out.status.code() == Some(100) && !c.contains("cannot be used as a value"),
        "the VALUE-REF of a let-shadowed multi-sig base `h` MUST resolve to the \
         LOCAL closure `(fn [y] 100)` (passed to `use-hof` → 100), NOT the module \
         overload base ('cannot be used as a value'); got exit {:?}:\n{c}",
        out.status.code()
    );
}

// PS-SH1 completion NEW #1 (s114-test-plan §3.5) — the multi-sig-base value-ref
// RETURNED position (distinct from the HOF-arg position above). A `let` shadows a
// multi-sig base `h` with a local closure and RETURNS the shadowed name as a value;
// the caller then applies it. The value-ref MUST resolve to the LOCAL closure
// `(fn [y] 100)` → `((g) 5)` = 100. GREEN twins: the multi-sig CALL cell
// (`let_shadowed_multi_sig_base_call_resolves_to_local_not_overload`, flipped S113)
// and the single-sig value-ref control below. Flips with the Track-A typecheck
// drain. RED today (resolves to the module overload base → error).
// spec: spec/05-definitions.md §5.1.2 + spec/04-expressions.md §4.6 — a let binding
// shadows a multi-sig base in VALUE position; a returned value-ref sees the local.
// defect: class=wrong-scope-lookup locus=crates/cranelisp-typecheck value-ref of a let-shadowed multi-sig base (returned position) resolves to the module overload base, not the local binding found=S114 owner=/dev
#[test]
fn let_shadowed_multi_sig_base_value_ref_returned_resolves_to_local_not_overload() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(
            "(defn h ([x] x) ([a b] a))\n\
             (defn g [] (let [h (fn [y] 100)] h))\n\
             (defn main [] (Pure ((g) 5)))\n",
        )
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        out.status.code() == Some(100) && !c.contains("cannot be used as a value"),
        "a RETURNED value-ref of a let-shadowed multi-sig base `h` MUST resolve to \
         the LOCAL closure `(fn [y] 100)` (`((g) 5)` = 100), NOT the module overload \
         base ('cannot be used as a value'); got exit {:?}:\n{c}",
        out.status.code()
    );
}

// PS-SH1 completion NEW #2 (s114-test-plan §3.5) — the multi-sig-base value-ref
// STORED-IN-CONTAINER position (a third value-ref position: the shadowed name is
// placed in a vec, projected out, then applied). MUST resolve to the LOCAL closure
// → `((vec-get (g) 0) 5)` = 100. Same seam as NEW #1, different value-ref position
// (the matrix pressures ONE codepath — a per-position fix that greens one but not
// the sibling names a divergent resolver). Flips with the Track-A drain. RED today.
// spec: spec/05-definitions.md §5.1.2 + spec/04-expressions.md §4.6 — a let binding
// shadows a multi-sig base placed in a container in VALUE position.
// defect: class=wrong-scope-lookup locus=crates/cranelisp-typecheck value-ref of a let-shadowed multi-sig base (container-store position) resolves to the module overload base, not the local binding found=S114 owner=/dev
#[test]
fn let_shadowed_multi_sig_base_value_ref_in_container_resolves_to_local_not_overload() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(
            "(defn h ([x] x) ([a b] a))\n\
             (defn g [] (let [h (fn [y] 100)] [h]))\n\
             (defn main [] (Pure ((vec-get (g) 0) 5)))\n",
        )
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        out.status.code() == Some(100) && !c.contains("cannot be used as a value"),
        "a CONTAINER-STORED value-ref of a let-shadowed multi-sig base `h` MUST \
         resolve to the LOCAL closure `(fn [y] 100)` (`((vec-get (g) 0) 5)` = 100), \
         NOT the module overload base; got exit {:?}:\n{c}",
        out.status.code()
    );
}

// PS-SH1 single-sig value-ref GREEN control (the uniform twin for the multi-sig
// value-ref REDs above): a let-shadowed SINGLE-sig defn `h`, value-ref passed to a
// HOF, resolves to the local closure → 100. Single-sig value-refs work in every
// position; only the multi-sig OVERLOAD BASE bypasses the local binding. This is
// the parallel-shape green twin proving the bug is the overload gate, not value-ref
// resolution generally. GREEN today, must stay green.
// spec: spec/04-expressions.md §4.6 — a let binding shadows a single-sig defn in
// VALUE position; the value-ref sees the local binding.
#[test]
fn let_shadowed_single_sig_defn_value_ref_hof_resolves_to_local() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(
            "(defn h [x] (add-i64 x 1))\n\
             (defn use-hof [f] (f 5))\n\
             (defn g [] (let [h (fn [y] 100)] (use-hof h)))\n\
             (defn main [] (Pure (g)))\n",
        )
        .output()
        .assert_exit(100);
}
