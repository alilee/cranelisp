// w2_close_fences.rs — S113 W2-close fences. The W2 typecheck+backend fixes are
// landed and reviewed (typecheck APPROVE; backend APPROVE-WITH-FIXES drained);
// these e2e cells PIN them. All GREEN on landing. Where a cell was RED-verified
// pre-fix by /review's probes, the in-comment note records the pre-fix symptom
// (the durable record that this guards a real revert, not a vacuous pass).
//
// Free-standing (no stdlib).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

fn repl_prims(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(lines)
        .output()
}

fn run_prims_exit(src: &str, code: i32) {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(src)
        .output()
        .assert_exit(code);
}

// A library module exporting a MULTI-SIG defn `h` (arity-1 + arity-2), reused by
// the Fix-A qualified-call cells.
const MLIB: &str =
    "(import [primitives [add-i64]])\n(defn h ([x] (add-i64 x 1)) ([a b] (add-i64 a b)))\n";

// =============================================================================
// Cell 1 — NON-TAIL shadowed self-call sibling (/arch-REQUIRED). A let rebinds the
// defn's OWN name `s1` to a local `(fn [y] y)`; the call `(s1 x)` sits in NON-TAIL
// position (an argument to `add-i64`). The LOCAL must win (value-correct), not the
// outer defn — calling the outer would infinitely self-recurse. `(s1 5)` =
// `(add-i64 ((fn [y] y) 5) 1)` = 6. WRONG-VALUE assert (not merely no-hang).
// =============================================================================

// spec: spec/04-expressions.md §4.6 + spec/05-definitions.md §5.1.2 — a let-bound
// name shadows the enclosing defn's own name in a non-tail self-call position.
#[test]
fn non_tail_shadowed_self_call_local_wins_repl() {
    repl_prims("(defn s1 [x] (let [s1 (fn [y] y)] (add-i64 (s1 x) 1)))\n(s1 5)\n")
        .assert_stdout_contains(":primitives/Int 6");
}

// spec: spec/04-expressions.md §4.6 + spec/05-definitions.md §5.1.2 — the `--run`
// face (mode uniformity).
#[test]
fn non_tail_shadowed_self_call_local_wins_run() {
    run_prims_exit(
        "(defn s1 [x] (let [s1 (fn [y] y)] (add-i64 (s1 x) 1)))\n\
         (defn main [] (Pure (s1 5)))\n",
        6,
    );
}

// =============================================================================
// Cell 2 — LET-REBINDS-BASE in a mono recheck (the falsified-§11.8.7 cell). A
// let inside a monomorphised body rebinds a MULTI-SIG base `h` to a local fn; the
// mono recheck must resolve `h` to the LOCAL, not re-dispatch the base.
// RED-VERIFIED PRE-FIX (/review probe): resolved to the base → 6; post-fix the
// local wins → 100.
// =============================================================================

// spec: spec/04-expressions.md §4.6 — a let-shadow of a multi-sig base inside a
// monomorphised body binds the local, not the base overload set.
#[test]
fn let_rebinds_multi_sig_base_in_mono_recheck_local_wins() {
    repl_prims(
        "(defn h ([x] (add-i64 x 1)) ([a b] a))\n\
         (defn g [:a x] (let [h (fn [y] 100)] (h x)))\n\
         (g 5)\n",
    )
    .assert_stdout_contains(":primitives/Int 100");
}

// =============================================================================
// Cell 3 — FIX A: the QUALIFIED cross-module call `(mlib/h 1)`. RED-VERIFIED
// PRE-FIX: the module key was DOUBLED (`user/user/…`) so the qualified reference
// missed with `undefined function`. Three faces: top-level, in-defn, and with only
// the bare member imported. All → 2.
// =============================================================================

// spec: spec/08-modules.md §8.5 + spec/05-definitions.md §5.1.2 — a fully-qualified
// reference to a multi-sig defn at TOP LEVEL resolves and dispatches.
#[test]
fn fix_a_qualified_multi_sig_call_top_level() {
    repl_prims_with_mlib("(import [mlib [h]])\n(mlib/h 1)\n").assert_stdout_contains(":primitives/Int 2");
}

// spec: spec/08-modules.md §8.5 + spec/05-definitions.md §5.1.2 — a qualified call
// INSIDE a defn body resolves.
#[test]
fn fix_a_qualified_multi_sig_call_in_defn() {
    repl_prims_with_mlib("(import [mlib [h]])\n(defn use1 [] (mlib/h 1))\n(use1)\n")
        .assert_stdout_contains(":primitives/Int 2");
}

// spec: spec/08-modules.md §8.5 + spec/05-definitions.md §5.1.2 — a qualified call
// resolves even when only the BARE member was imported (the alias-only-import
// face — the doubled-key symptom's originating shape).
#[test]
fn fix_a_qualified_multi_sig_call_alias_only_import() {
    // Only `h` (bare) imported; the qualified `mlib/h` reference must still resolve.
    repl_prims_with_mlib("(import [mlib [h]])\n(defn use2 [] (add-i64 (h 1) (mlib/h 1)))\n(use2)\n")
        .assert_stdout_contains(":primitives/Int 4");
}

fn repl_prims_with_mlib(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("mlib.cl", MLIB)
        .stdin(lines)
        .output()
}

// =============================================================================
// Cell 4 — FIX B: shadow cells. A let-shadow of a callable inside a mono body or a
// concrete caller must bind the LOCAL. RED-VERIFIED PRE-FIX: these returned SILENT
// WRONG VALUES (the outer callable's result — the worst class: no error, wrong
// answer). Post-fix the local wins; the unshadowed control still dispatches.
// =============================================================================

// spec: spec/04-expressions.md §4.6 — a shadowed CONSTRAINED callable inside a mono
// body binds the local (was a silent wrong value: dispatched the outer `con`).
#[test]
fn fix_b_shadowed_constrained_in_mono_body_local_wins() {
    repl_prims(
        "(deftrait Disp (dp [x] Int))\n\
         (impl Disp Int (defn dp [x] 9))\n\
         (defn con [:Disp x] (dp x))\n\
         (defn g [:a y] (let [con (fn [z] 77)] (con y)))\n\
         (g 5)\n",
    )
    .assert_stdout_contains(":primitives/Int 77");
}

// spec: spec/04-expressions.md §4.6 — a shadowed PARAMETRIC callable inside a mono
// body binds the local (was a silent wrong value: the outer identity → y).
#[test]
fn fix_b_shadowed_parametric_in_mono_body_local_wins() {
    repl_prims(
        "(defn p [x] x)\n\
         (defn g [:a y] (let [p (fn [z] 55)] (p y)))\n\
         (g 7)\n",
    )
    .assert_stdout_contains(":primitives/Int 55");
}

// spec: spec/04-expressions.md §4.6 — a shadowed PARAMETRIC callable inside a
// CONCRETE caller binds the local (was a silent wrong value).
#[test]
fn fix_b_shadowed_parametric_in_concrete_caller_local_wins() {
    repl_prims(
        "(defn p [x] x)\n\
         (defn caller [] (let [p (fn [z] 55)] (p 7)))\n\
         (caller)\n",
    )
    .assert_stdout_contains(":primitives/Int 55");
}

// spec: spec/04-expressions.md §4.6 — CONTROL twin: the UNSHADOWED constrained
// callable still dispatches (the fix must not break ordinary dispatch).
#[test]
fn fix_b_unshadowed_constrained_still_dispatches_control() {
    repl_prims(
        "(deftrait Disp (dp [x] Int))\n\
         (impl Disp Int (defn dp [x] 9))\n\
         (defn con [:Disp x] (dp x))\n\
         (con 5)\n",
    )
    .assert_stdout_contains(":primitives/Int 9");
}

// =============================================================================
// Cell 5 — GENUINE self-call + gate-3 coherence (backend 0654). Deep TAIL
// self-recursion must TCO (no stack growth) — the e2e face of the carrier-keyed
// TCO ↔ stack-alloc agreement (gate-3). Countdown from 100000 → 0 in constant
// stack; a broken TCO overflows the stack instead of exiting 0.
// =============================================================================

// spec: spec/05-definitions.md §5.1.2 — a genuine tail self-call is TCO'd; deep
// recursion runs in constant stack.
#[test]
fn genuine_deep_tail_self_recursion_tco_no_stack_growth() {
    run_prims_exit(
        "(defn countdown [n] (if (eq-i64 n 0) 0 (countdown (sub-i64 n 1))))\n\
         (defn main [] (Pure (countdown 100000)))\n",
        0,
    );
}
