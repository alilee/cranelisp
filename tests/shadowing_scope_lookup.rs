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

// ============================================================================
// S114 W3-review Important-1 — let-shadowed TRAIT OPERATOR mis-dispatch
// ============================================================================
//
// The shadowing family's TRAIT-METHOD face (the operator sibling of the
// defn-shadow cells above): a `let` binds a same-named local `+`, but the call
// resolves to the Num trait method `+` (→ 3) instead of the local closure (→ 0).
// §11.8.8 "name is the TRIGGER, the carrier is the IDENTITY" + P24 are violated —
// the post-unify call-resolution block keys on the RAW AST name `+` and ignores
// both the available carrier verdict and the lexical shadow. Two positions
// mis-dispatch (call, auto-curry); the value-ref position is CORRECT (the
// born-green control), exactly mirroring the single-sig defn matrix above where
// value-refs see the local but the call-head does not. These use TestStandard
// (the Num trait supplies the operator `+`). Flip trigger: the W7 /dev(typecheck)
// rider (priority behind MS-P7, ahead of 0590). PRE-EXISTING (W3-review probe).

// spec: spec/04-expressions.md §4.6 — a `let`-bound name lexically shadows a
// same-named TRAIT METHOD; a CALL to that name inside the let body MUST resolve to
// the LOCAL binding (§11.8.8: the name is the trigger, the carrier is the identity).
// `(let [+ (fn [a b] 0)] (+ 1 2))` MUST yield 0.
//
// RED at HEAD: the post-unify call-resolution block keys on the raw AST name `+`,
// resolves it to the Num/Int trait method, and returns 3 (verified /testing
// 2026-07-20: `--run` exit 3, REPL `:primitives/Int 3`, `--link` exit 3 — mode-
// uniform). Failing-not-ignored.
// defect: class=wrong-scope-lookup locus=crates/cranelisp-typecheck/src/infer.rs:966 post-unify call resolution keys on the raw AST name (ignores the carrier verdict + local shadow, dispatches the trait method over the let binding) found=S114 owner=/dev
#[test]
fn let_shadowed_trait_operator_call_resolves_to_local_not_dispatch() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::TestStandard)
        .run("user.cl")
        .user(
            "(defn f [] (let [+ (fn [a b] 0)] (+ 1 2)))\n\
             (defn main [] (Pure (f)))\n",
        )
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert_eq!(
        out.status.code(),
        Some(0),
        "`(let [+ (fn [a b] 0)] (+ 1 2))` MUST call the LOCAL `+` (`(fn [a b] 0)`) \
         and yield 0 — the call-head MUST NOT dispatch the Num trait method `+` \
         (which returns 3); got exit {:?}:\n{c}",
        out.status.code()
    );
}

// spec: spec/04-expressions.md §4.6 — the REPL mode twin of the call cell above.
// `(let [+ (fn [a b] 0)] (+ 1 2))` MUST echo `:primitives/Int 0`.
//
// RED at HEAD: echoes `:primitives/Int 3` (the Num trait method). The mode twin
// pins that the mis-dispatch is not `--run`-specific (it is shared across the one
// resolution seam — a REPL/`--run` agreement guard).
// defect: class=wrong-scope-lookup locus=crates/cranelisp-typecheck/src/infer.rs:966 post-unify call resolution keys on the raw AST name (REPL mode face) found=S114 owner=/dev
#[test]
fn let_shadowed_trait_operator_call_repl_resolves_to_local() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .stdin("(let [+ (fn [a b] 0)] (+ 1 2))\n")
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains(":primitives/Int 0"),
        "`(let [+ (fn [a b] 0)] (+ 1 2))` MUST echo `:primitives/Int 0` (the LOCAL \
         `+`), NOT `:primitives/Int 3` (the Num trait method); got:\n{c}"
    );
}

// spec: spec/04-expressions.md §4.6.3 — the AUTO-CURRY sibling. A PARTIAL application
// of the shadowed local `+` — `((+ 1) 2)` — MUST auto-curry the LOCAL closure and
// yield 0.
//
// HISTORY (FIXED — GREEN; this cell is a regression guard, not an open defect).
// Two successive faults lived here. (1) Typecheck: the `infer.rs` auto-curry filler
// keyed on the raw AST name `+` and dispatched the Num trait method → 3; fixed by
// the S114 W7 trait-shadow carrier discipline. (2) The cell did NOT flip green then
// — its SYMPTOM CHANGED (the MC-E1 "a non-flip is evidence" pattern) to a codegen
// failure, `fn-as-value wrapper for '+' reached codegen with no GOT-slot carrier`:
// `resolve_auto_curry` correctly produced an `AutoCurry` over the LOCAL closure
// (`VarRef::Local`, no Dispatch FQ), and the BACKEND then looked up `+`'s GOT slot,
// which a local closure does not have. That re-attributed to the backend and was
// FIXED in S115 W3 change-set 3 (totality over the closed carrier sums — no `_ =>`
// arm; a `ViaCallee` + `Global` pairing is now a located producer-contradiction
// error rather than a GOT-slot lookup). FIXME 0705 retired at that flip.
//
// FAMILY CROSS-REF: `fn_as_value_carrier_loss.rs::
// trait_operator_partial_app_impl_present_has_got_carrier` pins the impl-PRESENT
// (non-shadowed, global) trait-op partial-app face of the same fn-as-value-wrapper
// carrier family; it is separately owned (`/dev`(typecheck), producer gap at
// `mono_collect.rs::resolve_auto_curry`) and is the record for that face.
// defect: class=carrier-loss locus=crates/cranelisp-backend AutoCurry-over-local-target fn-as-value wrapper — a local closure has no GOT slot (FIXME 0705; re-attributed out of typecheck infer.rs; plausibly the fn_as_value_carrier_loss seam family) found=S114 owner=/dev
#[test]
fn let_shadowed_trait_operator_auto_curry_resolves_to_local() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::TestStandard)
        .run("user.cl")
        .user(
            "(defn f [] (let [+ (fn [a b] 0)] ((+ 1) 2)))\n\
             (defn main [] (Pure (f)))\n",
        )
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert_eq!(
        out.status.code(),
        Some(0),
        "`((+ 1) 2)` with a let-shadowed local `+` MUST auto-curry the LOCAL closure \
         (`(fn [a b] 0)`) and yield 0 — the auto-curry filler MUST NOT dispatch the \
         Num trait method `+` (which returns 3); got exit {:?}:\n{c}",
        out.status.code()
    );
}

// spec: spec/04-expressions.md §4.6.3 — the NON-TRAIT auto-curry control (born
// green; FIXME 0705's requested cell, added S115 W3c).
//
// The TWIN of the auto-curry cell above with the ONLY difference being the callee's
// name: a plain local closure `g` instead of the trait-shadowing `+`. Same prelude,
// same shape, same assertion. It isolates AutoCurry-over-a-LOCAL-TARGET from trait
// dispatch — the backend carrier fault above was in the local-target wrapper, not in
// trait resolution, and this cell would have named that without the trait shadow
// confounding it. A coverage-by-definition-variants cell (the local-closure variant
// of the auto-curry family, `tests/CLAUDE.md` §"Coverage by definition variants"),
// not a nice-to-have: if a future fix re-keys the wrapper on trait-ness, the twins
// diverge and the failing one names the site.
#[test]
fn local_closure_auto_curry_non_trait_control_resolves_to_local() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::TestStandard)
        .run("user.cl")
        .user(
            "(defn f [] (let [g (fn [a b] 0)] ((g 1) 2)))\n\
             (defn main [] (Pure (f)))\n",
        )
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert_eq!(
        out.status.code(),
        Some(0),
        "`((g 1) 2)` over a plain local closure MUST auto-curry the LOCAL target and \
         yield 0 — no trait dispatch is involved, so this face must never depend on \
         the trait-shadow path; got exit {:?}:\n{c}",
        out.status.code()
    );
}

// spec: spec/04-expressions.md §4.6.2 — the VALUE-REF GREEN control (the isolating
// twin). Passing the shadowed local `+` as a VALUE to a HOF resolves to the LOCAL
// binding correctly. `(defn ap [g] (g 1 2))` + `(ap +)` inside the let → 0. This is
// the same contrast as the single-sig defn matrix: the value-ref position sees the
// local binding; only the CALL and AUTO-CURRY positions mis-dispatch — isolating the
// two call-resolution blocks (not value-position resolution) as the seam. GREEN
// today (verified /testing 2026-07-20: exit 0 across `--run`/`--link`), must stay
// green through the W7 fix.
#[test]
fn let_shadowed_trait_operator_value_ref_passed_to_hof_resolves_to_local() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::TestStandard)
        .run("user.cl")
        .user(
            "(defn ap [g] (g 1 2))\n\
             (defn f [] (let [+ (fn [a b] 0)] (ap +)))\n\
             (defn main [] (Pure (f)))\n",
        )
        .output()
        .assert_exit(0);
}
