// safety_oracle_lane.rs — the memory-safety differential-oracle lane (MS-P2/P4/P5,
// tests/plan/s113-test-plan.md §2; user-approved W5 depth, W0 gate CONFIRMED
// memory-safety as the top correctness risk).
//
// The lane drives memory-safety probes through the `assert_safety_matrix`
// combinator (MS-P1, `helpers/e2e.rs`) — modes × ownership-toggle {on, off} ×
// {behavioral equivalence, RC balance, RC_DEC_CHECK zero, `--link` face}. The
// conservative all-Owned lowering (`CRANELISP_NO_OWNERSHIP=1`) is the reference
// semantics; an ownership-elision defect diverges the ON path from it.
//
// ACCEPTANCE (strategy §1.3 / plan §2 MS-P2):
//   - the 0641 B-1 program goes RED under the lane on day one (the elision frees a
//     returned alias — ON diverges from the conservative fallback / --link aborts);
//   - a clean program and a §3.7-cured COW program stay GREEN (the lane does not
//     false-positive);
//   - lane wall ≤ 60s.
//
// The drop-glue collision family (0633, MS-P4) is ORDER-keyed, NOT toggle-
// dependent, so the differential combinator is the wrong instrument for it — that
// cell is hand-authored on the ABSOLUTE corruption face (no SIGABRT / no
// RC_DEC_CHECK abort / REPL≡run) below.
//
// Stdlib-free: `primitives` only (root CLAUDE.md §Design Principles). RC-reading
// runs are per-subprocess, safe under nextest process isolation.
//
// SCOPE NOTE (W1): MS-P1/P2/P4/P5 land here. MS-P3 (mechanical retro-wrap of the
// ~10 existing ownership/RC repro files through the combinator) is the follow-on
// (may ride or follow MS-P1); MS-P6 (diagnostic-mode self-tests) rides the W5
// build change-sets per the depth ruling. Neither is W1 authoring.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant, SafetyMatrix, assert_safety_matrix};

// MS-P2 ACCEPTANCE (RED day one) — 0641 B-1. `(defn f [v] (vec-get [v] 0))`
// returns its own param `v` via a fresh-container projection; the ownership walk
// publishes a false `result=Fresh`, the return protect is elided, and the alias
// is freed before the caller reads it. `(vec-get (f [1 2 3]) 1)` MUST yield 2
// (`main` returns `(Pure 2)` → exit 2). Under ownership ON the elision corrupts
// (the `--link` binary deterministically aborts, 6/6; the differential diverges);
// toggle-off is clean. The lane catches it → RED, flips when 0641's false-`Fresh`
// class closes by mechanism (§3 frame, W5).
// spec: spec/12-runtime.md §12.1 — a param returned via a fresh-container
// projection MUST remain live for the caller.
// defect: class=uaf locus=crates/cranelisp-typecheck/src/ownership/transfer.rs::VecLit-element-store-ProjectionOf-composition found=S111 owner=/dev
#[test]
fn safety_lane_b1_false_fresh_returned_alias_differential_red() {
    SafetyMatrix::new(
        "(defn f [v] (vec-get [v] 0))\n\
         (defn main [] (Pure (vec-get (f [1 2 3]) 1)))\n",
    )
    .prelude(PreludeVariant::PrimitivesOnly)
    .expect_exit(2)
    .without_rc_balance() // the corrupting path aborts; the differential + link faces are the RED
    .assert();
}

// MS-P2 GREEN acceptance — a trivially clean vec read. `[10 20 30]` element 1 = 20.
// No aliasing subtlety: ON≡OFF, RC balanced, `--link` clean, no dec-check abort.
// Proves the lane does NOT false-positive.
// spec: spec/12-runtime.md §12.1 — vec construction + indexed read is memory-safe.
#[test]
fn safety_lane_clean_vec_read_green() {
    assert_safety_matrix(
        "(defn main [] (Pure (vec-get [10 20 30] 1)))\n",
        PreludeVariant::PrimitivesOnly,
        20,
    );
}

// The COW-set→project program: `(vec-set v 0 9)` returns a COW copy; reading
// element 0 = 9. Under `--run` the answer is correct (9); the `--link` binary
// DETERMINISTICALLY ABORTS ("corrupted double-linked list"). The §3.7 `MayAliasOf`
// COW-truth work (S111) did NOT cover this direct COW-set→project shape.
const COW_SET_READ_PROG: &str = "(defn f [v] (vec-get (vec-set v 0 9) 0))\n\
     (defn main [] (Pure (f [1 2 3])))\n";

// 0706 face (a) — nested COW projected out in one frame: inner (vec-set v 0 1) is the
// unprotected inner may-alias link; f [9 9 9] → 1.
const CHAINED_NESTED_COW_PROG: &str = "(defn f [v] (vec-get (vec-set (vec-set v 0 1) 1 2) 0))\n\
     (defn main [] (Pure (f [9 9 9])))\n";

// 0706 face (b) — let-bound intermediate `w`, single set over the alias, projected
// out; `w` is the unprotected inner may-alias link; f [9 9 9] → 1.
const CHAINED_LET_COW_PROG: &str = "(defn f [v] (let [w (vec-set v 0 1)] (vec-get (vec-set w 1 2) 0)))\n\
     (defn main [] (Pure (f [9 9 9])))\n";

// 0706 negative control — whole-value nested transfer, caller-projected; CLEAN both
// modes. f [9 9 9] → [1 2 9]; (vec-get (f …) 0) → 1.
const WHOLE_VALUE_NESTED_TRANSFER_PROG: &str = "(defn f [v] (vec-set (vec-set v 0 1) 1 2))\n\
     (defn main [] (Pure (vec-get (f [9 9 9]) 0)))\n";

// MS-P7 (immediate-link face FIXED S114 W7; chained faces carry — 0706 pins below)
// — the SPEC-CORRECT CONTRACT for the FLAT/single-link shape, now a GREEN regression
// guard. `(vec-get (vec-set v 0 9) 0)` MUST return the set value 9, abort-free, in
// EVERY mode. This asserts the contract directly (NOT the differential detection
// shape), so its color tracks the DEFECT's existence, never lane-config/detection
// quality. SCOPE: the W7 fix protects exactly ONE may-alias link (the immediately-
// projected container); a chain of length ≥2 in one frame still double-decs an INNER
// link — pinned failing-not-ignored by the two `_chained_*` cells below (0706, fix =
// S115). This pin covers ONLY the immediate-link face; do NOT read it as closing the
// `class=uaf` MayAliasOf family.
//
// History (strip-when-fixed discipline): this was RED under `--link` while the COW
// in-place `vec-set` arm double-dec'd its result. The W3 evidence brief (commit
// 078d324b) discharged the §3.6 mode-divergence gate with a result the dichotomy
// did not enumerate — CLIF is BYTE-IDENTICAL across `--run` and `--link`, and the
// shared IR itself carried the double-dec: the in-place branch returns the SAME
// heap pointer as the input vec, so both the result temp and the param got dec'd.
// `--run` silently tolerated the corruption in-process; `--link`'s glibc allocator
// aborted. The mode axis was only the DETECTOR, never the cause. The fix landed in
// the /dev(typecheck) ownership analysis (§3.7 `MayAliasOf` projection-out — the
// vec-set result released as an arg-temp). The `_red` suffix on the fn name is
// retained for the plan's flip-record citation (s114-test-plan §3.6/§11).
// spec: spec/12-runtime.md §12.1 — a COW `vec-set` result read by the caller returns
// the set value and is memory-safe in all modes.
// defect: class=uaf locus=crates/cranelisp-typecheck/src/ownership/transfer.rs::MayAliasOf projection-out — COW vec-set result released as an arg-temp; shared-IR double-dec (--run tolerated in-process, --link aborted); §3.7 gap, 0641-adjacent; fixed S114 W7 found=S113 owner=/dev
#[test]
fn safety_lane_cow_set_read_returns_set_value_abort_free_red() {
    // --run: returns the set value 9.
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(COW_SET_READ_PROG)
        .output()
        .assert_exit(9);
    // --link: MUST also return 9 (was the `--link`-abort RED before the S114 W7 fix).
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .link_then_run("user.cl")
        .user(COW_SET_READ_PROG)
        .output()
        .assert_exit(9);
    // REPL: MUST evaluate to 9.
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("(defn f [v] (vec-get (vec-set v 0 9) 0))\n(f [1 2 3])\n")
        .output()
        .assert_stdout_contains(":primitives/Int 9");
}

// 0706 (S114 W7-review Blocker; fix = S115) — CHAINED may-alias link, face (a):
// NESTED COW projected out. `(vec-get (vec-set (vec-set v 0 1) 1 2) 0)` on [9 9 9]
// MUST return 1 (inner set → [1 9 9], outer set → [1 2 9], get 0 → 1), abort-free, in
// EVERY mode. The W7 `ProjectionOf`/`MayAliasOf` escape-force protects ONLY the
// immediately-projected (outer) container; a chain of length ≥2 in one frame still
// double-decs the INNER link — the `vec-set v 0 1` intermediate is released twice.
// `--run` tolerates the corruption in-process (returns 1); the `--link` binary
// DETERMINISTICALLY ABORTS ("corrupted double-linked list", exit 134; 2/2 this VM,
// HEAD 89d2f09c). Polarity probe-verified before landing (/testing, S114 Phase-5
// close). This is the 4th reaching context of the §3.7 `MayAliasOf` family (chained
// links), NOT a regression (pre-W7 the flat outer link aborted too; the escape-force
// only ADDS incs — the failure is in the too-many-decs direction). Contract-asserting
// (color tracks the defect's existence); flips GREEN when the S115 typecheck fix
// protects every may-alias link whose accounting includes a consumer-emitted release.
// spec: spec/12-runtime.md §12.1 — a chained COW `vec-set` result read by the caller
// returns the set value and is memory-safe in all modes.
// defect: class=uaf locus=crates/cranelisp-typecheck/src/ownership/transfer.rs::ProjectionOf — chained may-alias link unprotected (W7 fixed the immediate/outer link only); inner vec-set intermediate double-dec'd, --run tolerated in-process / --link aborted; §3.7 MayAliasOf family reaching-context 4 found=S114 owner=/dev
#[test]
fn safety_lane_chained_nested_cow_projection_returns_set_value_abort_free_red() {
    // --run: returns the correct set value 1.
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(CHAINED_NESTED_COW_PROG)
        .output()
        .assert_exit(1);
    // --link: MUST also return 1 (currently the `--link`-abort RED — 0706, fix S115).
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .link_then_run("user.cl")
        .user(CHAINED_NESTED_COW_PROG)
        .output()
        .assert_exit(1);
    // REPL: MUST evaluate to 1 (JIT tolerates in-process, like the flat MS-P7 face).
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("(defn f [v] (vec-get (vec-set (vec-set v 0 1) 1 2) 0))\n(f [9 9 9])\n")
        .output()
        .assert_stdout_contains(":primitives/Int 1");
}

// 0706 (S114 W7-review Blocker; fix = S115) — CHAINED may-alias link, face (b):
// LET-BOUND intermediate, single set over the alias binding, projected out.
// `(let [w (vec-set v 0 1)] (vec-get (vec-set w 1 2) 0))` on [9 9 9] MUST return 1
// (w → [1 9 9], set w 1 2 → [1 2 9], get 0 → 1), abort-free, in EVERY mode. Repro (b)
// shows the projected (outer) container DOES receive the W7 escape-force (the Apply
// container, Conditional via the `w` binding) — so the double-dec is on the INNER
// link (`w`), confirming the open face is chained-may-alias × projection-in-the-same-
// frame, not nested COW per se. `--run` returns 1; `--link` DETERMINISTICALLY ABORTS
// (exit 134, "corrupted double-linked list"; 2/2 this VM, HEAD 89d2f09c). Polarity
// probe-verified before landing (/testing, S114 Phase-5 close). Contract-asserting;
// flips GREEN with the S115 family-grain typecheck fix.
// spec: spec/12-runtime.md §12.1 — a let-chained COW `vec-set` result read by the
// caller returns the set value and is memory-safe in all modes.
// defect: class=uaf locus=crates/cranelisp-typecheck/src/ownership/transfer.rs::ProjectionOf — chained may-alias link unprotected (let-bound inner alias `w` double-dec'd; outer container got the W7 escape-force, inner did not); --run tolerated in-process / --link aborted; §3.7 MayAliasOf family reaching-context 4 found=S114 owner=/dev
#[test]
fn safety_lane_chained_let_bound_cow_projection_returns_set_value_abort_free_red() {
    // --run: returns the correct set value 1.
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(CHAINED_LET_COW_PROG)
        .output()
        .assert_exit(1);
    // --link: MUST also return 1 (currently the `--link`-abort RED — 0706, fix S115).
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .link_then_run("user.cl")
        .user(CHAINED_LET_COW_PROG)
        .output()
        .assert_exit(1);
    // REPL: MUST evaluate to 1 (JIT tolerates in-process, like the flat MS-P7 face).
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(
            "(defn f [v] (let [w (vec-set v 0 1)] (vec-get (vec-set w 1 2) 0)))\n\
             (f [9 9 9])\n",
        )
        .output()
        .assert_stdout_contains(":primitives/Int 1");
}

// 0706 NEGATIVE CONTROL (green fence) — the whole-value nested transfer is CLEAN. Two
// chained `vec-set`s returned WHOLE (no in-frame projection), then read by the CALLER:
// `(defn f [v] (vec-set (vec-set v 0 1) 1 2))` + `(vec-get (f [9 9 9]) 0)`. Exit 1 in
// BOTH `--run` and `--link` (probe-verified 2/2 this VM). This fences the family
// boundary: the open face is chained-may-alias × projection-IN-THE-SAME-FRAME, NOT
// nested COW per se — when the chain crosses a call boundary before projection, the
// W7 fix (and the pre-W7 return-protect) already cover it. If the S115 fix over-widens
// and this cell regresses to a `--link` abort, the fix has broken the clean nested-
// transfer shape. Contract-asserting; MUST stay GREEN.
// spec: spec/12-runtime.md §12.1 — a whole-value nested COW transfer across a call
// boundary, projected by the caller, is memory-safe in all modes.
#[test]
fn safety_lane_whole_value_nested_transfer_clean_green() {
    // --run: whole-value nested transfer, caller-projected → exit 1, no abort.
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(WHOLE_VALUE_NESTED_TRANSFER_PROG)
        .output()
        .assert_exit(1);
    // --link: MUST also be clean exit 1 (the chained-face defect does NOT reach here).
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .link_then_run("user.cl")
        .user(WHOLE_VALUE_NESTED_TRANSFER_PROG)
        .output()
        .assert_exit(1);
}

// ---------------------------------------------------------------------------
// 0772 / 0773 — face 3 of the MS-P7 chained-may-alias family: the `If`-JOINED
// COW container. `join_origin` (`ownership/transfer.rs`) computes the §17.2
// row-4 union of the two arms' cow span-sets and then DISCARDS it unless the
// FIRST operand happens to be `Origin::Conditional` (`other => other`), so the
// row-6 projection-out force never fires for the dropped links. `MonoExpr::If`
// joins `then` before `else`, which makes the hole reachable from SOURCE ORDER:
// the same runtime path is safe or corrupting depending on which arm the COW
// producer was written in.
//
// The four cells below are a 2×2: {bare `If` arm, `let`-bound arm} × {cow arm
// second, cow arm first}. All four programs take the SAME runtime branch (the
// `vec-set` one) and the condition is a dynamic PARAMETER, so constant folding
// cannot mask any of them. Measured this VM at `bd5628a8`, deterministic 2/2:
//
//   | shape                                        | --run | --link            |
//   |----------------------------------------------|-------|-------------------|
//   | A1 `(if b v (vec-set v 0 1))`   cow SECOND    | 1     | 134 corrupted dll |
//   | A2 `(if b (vec-set v 0 1) v)`   cow FIRST     | 1     | 1  (MASKS)        |
//   | B1 `let w; (if b v w)`          cow SECOND    | 1     | 134 smallbin      |
//   | B2 `let w; (if b w v)`          cow FIRST     | 1     | 134 smallbin      |
//
// `--run` exit 1 is the CORRECT ANSWER, not a defect face: for `[9 9 9]` the
// `vec-set` arm yields `[1 9 9]` and `(vec-get … 0)` is 1. `--run` tolerates the
// double-dec in-process (same shared IR as `--link`; the mode axis is only the
// DETECTOR — see the MS-P7 history note above), so every cell asserts the same
// spec-correct contract in every mode: value 1, abort-free. Colour therefore
// tracks the DEFECT's existence — RED while 0772 is open, GREEN when fixed —
// and never inverts on the fix (no cell asserts "it aborts").

// 0772 A1 — bare `If`, COW producer in the SECOND (else) arm. RED (`--link` 134).
const IF_JOINED_COW_ARM_SECOND_PROG: &str = "(defn f [v b] (vec-get (if b v (vec-set v 0 1)) 0))\n\
     (defn main [] (Pure (f [9 9 9] false)))\n";

// 0772 A2 — the ARM-SWAPPED TWIN of A1. Same runtime path, same contract; only
// the static arm order differs. GREEN today — which is the finding, not comfort.
const IF_JOINED_COW_ARM_FIRST_PROG: &str = "(defn f [v b] (vec-get (if b (vec-set v 0 1) v) 0))\n\
     (defn main [] (Pure (f [9 9 9] true)))\n";

// 0772 B1/B2 — the `let`-mediated `If` join: the COW result is bound to `w`, and
// the join is over {param `v`, binding `w`}. Aborts in BOTH arm orders, so this
// face is not covered by the row-4 union at all (row 2 / row 4 composition
// through the binding env).
const LET_IF_JOINED_COW_ARM_SECOND_PROG: &str = "(defn f [v b] (let [w (vec-set v 0 1)] (vec-get (if b v w) 0)))\n\
     (defn main [] (Pure (f [9 9 9] false)))\n";
const LET_IF_JOINED_COW_ARM_FIRST_PROG: &str = "(defn f [v b] (let [w (vec-set v 0 1)] (vec-get (if b w v) 0)))\n\
     (defn main [] (Pure (f [9 9 9] true)))\n";

// 0772 A1 — `If`-joined COW container, COW producer in the SECOND arm.
// `(vec-get (if b v (vec-set v 0 1)) 0)` on `[9 9 9]` with `b` = false MUST
// return 1 (the else arm sets index 0 to 1, then reads it back), abort-free, in
// EVERY mode. `join_origin` drops the joined cow link-set here because the first
// operand (the `then` arm, bare `v`) is `Unconditional`, so the may-alias link
// contributed by the `else` arm is never force-protected at projection-out and
// the COW intermediate is released twice. `--run` tolerates it in-process;
// `--link` DETERMINISTICALLY ABORTS ("corrupted double-linked list", exit 134;
// 2/2 this VM at `bd5628a8`). Contract-asserting; flips GREEN when 0772's fix
// makes the link-set survive regardless of which operand contributed it.
//
// READ THIS CELL WITH ITS TWIN below (`…_arm_first_…`): the twin is byte-for-byte
// the same contract with the arms swapped and it PASSES. A passing twin beside a
// failing sibling is the Principle-24 acid test FAILING — the answer depends on
// incidental order (here, `MonoExpr::If`'s then-before-else walk order). A fix
// that cures only this cell and leaves the asymmetry in place has not closed the
// defect; both cells must hold for the same reason.
// spec: spec/12-runtime.md §12.1 — an `If`-joined COW `vec-set` result read in
// the same frame returns the set value and is memory-safe in all modes.
// defect: class=uaf locus=crates/cranelisp-typecheck/src/ownership/transfer.rs::join_origin — the §17.2 row-4 cow link-set UNION is computed then discarded unless the FIRST operand is Origin::Conditional, so an else-arm may-alias link is never projection-out forced; arm-order-dependent (P24 acid test), --run tolerated in-process / --link aborted; §3.7 MayAliasOf family face 3 found=S115 owner=/dev
#[test]
fn safety_lane_if_joined_cow_arm_second_returns_set_value_abort_free_red() {
    // --run: returns the correct set value 1.
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(IF_JOINED_COW_ARM_SECOND_PROG)
        .output()
        .assert_exit(1);
    // --link: MUST also return 1 (currently the `--link`-abort RED — 0772).
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .link_then_run("user.cl")
        .user(IF_JOINED_COW_ARM_SECOND_PROG)
        .output()
        .assert_exit(1);
    // REPL: MUST evaluate to 1 (JIT tolerates in-process, like the sibling faces).
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("(defn f [v b] (vec-get (if b v (vec-set v 0 1)) 0))\n(f [9 9 9] false)\n")
        .output()
        .assert_stdout_contains(":primitives/Int 1");
}

// 0772 A2 — the ARM-ORDER-SYMMETRY FENCE, and the sharpest single piece of
// evidence in this file. Identical contract to the cell above with the two `If`
// arms swapped and the condition inverted so the SAME runtime branch executes:
// `(vec-get (if b (vec-set v 0 1) v) 0)` on `[9 9 9]` with `b` = true MUST
// return 1, abort-free, in every mode. It PASSES today (`--run` 1, `--link` 1)
// purely because `join_origin`'s first operand is the `Conditional` one here, so
// the union it computes happens to survive.
//
// Its value is entirely as a fence, in two directions:
//   (1) It documents the asymmetry — a GREEN cell whose twin is RED for no
//       semantic reason is the P24 violation stated as a test.
//   (2) It must NOT be allowed to go RED. A 0772 fix that special-cases the
//       reversed operand order, or that widens the force so aggressively that it
//       breaks the currently-working order, trips this cell.
// A fix is only complete when this cell and its `_arm_second_` twin are green
// together; a fix that cures one order cannot pass the pair.
// spec: spec/12-runtime.md §12.1 — an `If`-joined COW `vec-set` result read in
// the same frame returns the set value and is memory-safe in all modes,
// independently of which arm the COW producer is written in.
// defect: class=uaf locus=crates/cranelisp-typecheck/src/ownership/transfer.rs::join_origin — order-symmetry fence for the discarded cow link-set (this arm order masks the defect); found=S115 owner=/dev
#[test]
fn safety_lane_if_joined_cow_arm_first_order_symmetry_twin_green() {
    // --run: returns the correct set value 1.
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(IF_JOINED_COW_ARM_FIRST_PROG)
        .output()
        .assert_exit(1);
    // --link: clean today (this arm order masks 0772) — MUST STAY clean.
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .link_then_run("user.cl")
        .user(IF_JOINED_COW_ARM_FIRST_PROG)
        .output()
        .assert_exit(1);
    // REPL: MUST evaluate to 1.
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("(defn f [v b] (vec-get (if b (vec-set v 0 1) v) 0))\n(f [9 9 9] true)\n")
        .output()
        .assert_stdout_contains(":primitives/Int 1");
}

// 0772 B1 — the `let`-mediated `If` join, COW binding in the SECOND arm.
// `(let [w (vec-set v 0 1)] (vec-get (if b v w) 0))` on `[9 9 9]` with `b` =
// false MUST return 1, abort-free, in every mode. FIXED (S115 W4c) — GREEN
// regression guard; the `_red` in the fn name is historical.
//
// RE-ATTRIBUTED (S115 W5a, FIXME 0781 item 1). This face was carried as a
// `join_origin` row-2/row-4 composition gap ("the may-alias link travels through
// the LET BINDING env"). It was not. The 0772 `join_origin` fix landed and left
// this cell RED, and reduction showed neither `let` nor COW was necessary —
// `(defn f [v b] (vec-get (if b v v) 0))` aborted identically. The real cause
// was BACKEND: the RC-emission gates decided "is this container an owned
// temporary?" from the container EXPRESSION's node kind, so any `If`/`Let`
// yielding a borrowed value took the release path. Closed by routing all five
// gates through `fn_compiler::value_provenance`. The lesson worth keeping: an
// ownership-walk attribution asserted from the shape of the source, without a
// reduction that removes the suspected mechanism, named the wrong crate.
// spec: spec/12-runtime.md §12.1 — a `let`-bound COW `vec-set` result joined by
// an `If` and read in the same frame returns the set value and is memory-safe in
// all modes.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/vec_codegen.rs::emit_vec_drop_if_temporary found=S115 owner=/dev
#[test]
fn safety_lane_let_bound_if_joined_cow_arm_second_returns_set_value_abort_free_red() {
    // --run: returns the correct set value 1.
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(LET_IF_JOINED_COW_ARM_SECOND_PROG)
        .output()
        .assert_exit(1);
    // --link: MUST also return 1 (currently the `--link`-abort RED — 0772).
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .link_then_run("user.cl")
        .user(LET_IF_JOINED_COW_ARM_SECOND_PROG)
        .output()
        .assert_exit(1);
    // REPL: MUST evaluate to 1.
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(
            "(defn f [v b] (let [w (vec-set v 0 1)] (vec-get (if b v w) 0)))\n\
             (f [9 9 9] false)\n",
        )
        .output()
        .assert_stdout_contains(":primitives/Int 1");
}

// 0772 B2 — the ARM-SWAPPED twin of B1, and the cell that proved the
// `let`-mediated face is NOT an order artifact: `(if b w v)` with `b` = true
// took the same runtime branch and aborted with the SAME signature (`--link`
// 134 "free(): chunks in smallbin corrupted", 2/2 this VM at `bd5628a8`). Both
// orders were RED, both are now GREEN — the pair pins order-independence on this
// face the way A1/A2 pins it on the bare-`If` face. Order-independence was in
// fact the first clue that the join was not the mechanism (see B1's
// re-attribution note above). FIXED S115 W4c; the `_red` in the fn name is
// historical.
// spec: spec/12-runtime.md §12.1 — a `let`-bound COW `vec-set` result joined by
// an `If` and read in the same frame returns the set value and is memory-safe in
// all modes, independently of arm order.
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/vec_codegen.rs::emit_vec_drop_if_temporary found=S115 owner=/dev
#[test]
fn safety_lane_let_bound_if_joined_cow_arm_first_returns_set_value_abort_free_red() {
    // --run: returns the correct set value 1.
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(LET_IF_JOINED_COW_ARM_FIRST_PROG)
        .output()
        .assert_exit(1);
    // --link: MUST also return 1 (currently the `--link`-abort RED — 0772).
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .link_then_run("user.cl")
        .user(LET_IF_JOINED_COW_ARM_FIRST_PROG)
        .output()
        .assert_exit(1);
    // REPL: MUST evaluate to 1.
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(
            "(defn f [v b] (let [w (vec-set v 0 1)] (vec-get (if b w v) 0)))\n\
             (f [9 9 9] true)\n",
        )
        .output()
        .assert_stdout_contains(":primitives/Int 1");
}

// 0772 GREEN CONTROL 1 (over-forcing fence) — the WHOLE-VALUE `If` join. Same
// `If`-over-{param, COW-result} shape as the four cells above, but the joined
// container is returned WHOLE and projected by the CALLER, so there is no
// in-frame projection-out. Clean in BOTH arm orders today (probe-verified 2/2
// this VM at `bd5628a8`) and MUST STAY clean: a 0772 fix that reacts to the
// `If` join itself — rather than to the projection of a joined may-alias link —
// will force a retain on a value that is legitimately transferred, and that
// over-force shows up here (leak direction) or as an abort if the direction is
// wrong. This is the `If`-shaped sibling of
// `safety_lane_whole_value_nested_transfer_clean_green`.
// spec: spec/12-runtime.md §12.1 — a whole-value `If`-joined COW transfer across
// a call boundary, projected by the caller, is memory-safe in all modes.
#[test]
fn safety_lane_if_joined_whole_value_transfer_clean_green() {
    const ARM_SECOND: &str = "(defn f [v b] (if b v (vec-set v 0 1)))\n\
         (defn main [] (Pure (vec-get (f [9 9 9] false) 0)))\n";
    const ARM_FIRST: &str = "(defn f [v b] (if b (vec-set v 0 1) v))\n\
         (defn main [] (Pure (vec-get (f [9 9 9] true) 0)))\n";
    for prog in [ARM_SECOND, ARM_FIRST] {
        Cranelisp::new()
            .with_prelude(PreludeVariant::PrimitivesOnly)
            .run("user.cl")
            .user(prog)
            .output()
            .assert_exit(1);
        Cranelisp::new()
            .with_prelude(PreludeVariant::PrimitivesOnly)
            .link_then_run("user.cl")
            .user(prog)
            .output()
            .assert_exit(1);
    }
}

// 0772 GREEN CONTROL 2 (generalization fence for the S115 W4 family fix) — the
// three chain shapes that were the W4 fix's own generalization evidence and were
// until now UNPINNED. All three project a chained may-alias link out in-frame,
// like the 0706 `_chained_*` cells, but at chain length 3 / across a call
// boundary / through nested `let`s:
//   1. three-link nested chain — RED at `d4efdf08~1`, GREEN from `d4efdf08`; the
//      only evidence the family fix generalizes past the two faces it was
//      written against;
//   2. chain across a function boundary;
//   3. nested `let` chain, three links.
// All MUST stay GREEN through the 0772 fix — they are the fence against a fix
// that narrows the W4 force while widening the `If` join.
// spec: spec/12-runtime.md §12.1 — a chained COW `vec-set` result read by the
// caller returns the set value and is memory-safe in all modes.
#[test]
fn safety_lane_chained_cow_generalization_shapes_clean_green() {
    const THREE_LINK_NESTED: &str = "(defn f [v] (vec-get (vec-set (vec-set (vec-set v 0 1) 1 2) 2 3) 0))\n\
         (defn main [] (Pure (f [9 9 9])))\n";
    const ACROSS_FN_BOUNDARY: &str = "(defn g [v] (vec-set v 0 1))\n\
         (defn f [v] (vec-get (vec-set (g v) 1 2) 0))\n\
         (defn main [] (Pure (f [9 9 9])))\n";
    const NESTED_LET_THREE_LINK: &str = "(defn f [v] (let [w (vec-set v 0 1)] \
           (let [x (vec-set w 1 2)] (vec-get (vec-set x 2 3) 0))))\n\
         (defn main [] (Pure (f [9 9 9])))\n";
    for prog in [THREE_LINK_NESTED, ACROSS_FN_BOUNDARY, NESTED_LET_THREE_LINK] {
        Cranelisp::new()
            .with_prelude(PreludeVariant::PrimitivesOnly)
            .run("user.cl")
            .user(prog)
            .output()
            .assert_exit(1);
        Cranelisp::new()
            .with_prelude(PreludeVariant::PrimitivesOnly)
            .link_then_run("user.cl")
            .user(prog)
            .output()
            .assert_exit(1);
    }
}

// MS-P6 capability RE-PLANT (§4.1 prong 2; rode the MS-P7 flip, S114 W7) — the
// safety LANE's DETECTION CAPABILITY, kept SEPARATE from any live pin (detection
// quality is separately valuable but must not be a pin's color). The prior plant
// used the LIVE MS-P7 defect as its fault; when MS-P7 was FIXED (S114 W7) that plant
// stopped tripping and this cell INVERTED to RED — the exact coupling the §4.1
// ruling names. Per memory-safety-coverage.md §4.1 prong 2 it is re-planted on a
// SYNTHETIC fault constructible regardless of compiler health: a CLEAN program
// (`(Pure 5)` → exit 5) run through the matrix with a deliberately-FALSIFIED clean
// expectation (`expect_exit(2)`). That is the shape a value-corrupting elision
// presents to the lane — ownership-ON's observed value diverging from the asserted
// clean result — and it trips the SAME Face-1 value-equivalence guard
// (`on exit == expect`) a real UAF-to-wrong-value would trip. GREEN: the matrix
// flags it (panics). If `SafetyMatrix::assert` ever stops asserting the clean
// result, this cell goes RED (fail-on-revert of the lane's detection logic). The
// panic hook is silenced around the expected panic so the detection is not mistaken
// for a test failure. Verified to trip before landing (/testing, S114 W7).
// spec: spec/12-runtime.md §12.1 — the safety lane detects a value divergence from
// the asserted-clean result.
#[test]
fn safety_lane_detects_falsified_clean_expectation_capability_green() {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let detected = std::panic::catch_unwind(|| {
        // A clean program that exits 5, asserted (falsely) as clean-exit 2. The
        // lane's Face-1 value-equivalence guard MUST catch the divergence and panic.
        SafetyMatrix::new("(defn main [] (Pure 5))\n")
            .prelude(PreludeVariant::PrimitivesOnly)
            .expect_exit(2)
            .without_rc_balance()
            .assert();
    })
    .is_err();
    std::panic::set_hook(prev);
    assert!(
        detected,
        "the safety-matrix lane MUST DETECT a divergence from the asserted-clean \
         result — running a clean program with a falsified expectation through the \
         matrix must flag it (panic); it did not"
    );
}

// MS-P4 — 0633 module-axis drop-glue collision, RE-AUTHORED on the CORRUPTION
// face. Two ADTs with the SAME bare type name `Thing` from two different modules,
// different field layouts (String = heap; Int = non-heap). `FQTypeName`
// distinguishes them everywhere upstream; only the glue-naming fn drops the module
// qualifier, so `runtime/drop_glue_Thing` collides in the importing module's batch
// — first-build-wins serves ONE glue for both instantiations. The existing leak
// cell (`adt_drop_glue_underkey.rs::adt_vec_drop_glue_module_axis_leak_r2`) pins
// the LEAK face; this cell adds the CORRUPTION face the leak cell lacks: the
// `--link` binary must not SIGABRT, `CRANELISP_RC_DEC_CHECK` must not trip an
// underflow abort (a DEC on a non-heap Int-as-pointer slot), and the REPL must
// agree with `--run` (the S111 reachability record's REPL-vs-`--run` divergence
// face: per-turn Jit batches vs whole-module ObjectModule). Correct answer: two
// vec-lens of 1 → exit 2. RED until the 0633 re-key (W5 R4 census).
// spec: spec/12-runtime.md §12.3.1 — heap value freed when no longer reachable;
// drop glue must not DEC a non-heap slot.
// defect: class=drop-glue-underkey locus=crates/cranelisp-backend/src/compiler/{resolution.rs::adt_drop_glue_name,vec_codegen.rs::build_elem_dec_fn} found=S111 owner=/dev
#[test]
fn safety_lane_module_axis_same_name_adt_corruption_face() {
    let ma = "(deftype Thing (MkA [:String s]))\n";
    let mb = "(deftype Thing (MkB [:Int n]))\n";
    let main = "(import [primitives [Pure]])\n\
         (import [ma [MkA]])\n\
         (import [mb [MkB]])\n\
         (defn main []\n\
           (let [va [(MkA \"hi\")]\n\
                 vb [(MkB 7)]]\n\
             (Pure (add-i64 (vec-len va) (vec-len vb)))))\n";

    // --run: correct value, no abort.
    let run = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("ma.cl", ma)
        .file("mb.cl", mb)
        .file("main.cl", main)
        .run("main.cl")
        .output();
    assert_eq!(
        run.status.code(),
        Some(2),
        "[--run] two same-bare-name `Thing` ADTs must produce exit 2 (vec-len 1 + \
         1); got {:?}:\n{}{}",
        run.status.code(),
        run.stdout,
        run.stderr
    );

    // --link corruption face: the linked binary must run cleanly, never SIGABRT on
    // a mis-slotted DEC.
    let link = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("ma.cl", ma)
        .file("mb.cl", mb)
        .file("main.cl", main)
        .link_then_run("main.cl")
        .output();
    assert_eq!(
        link.status.code(),
        Some(2),
        "[--link] the bare-name-keyed drop-glue collision must NOT corrupt the heap \
         (SIGABRT / DEC-on-wrong-slot); linked binary MUST exit 2; got {:?}:\n{}{}",
        link.status.code(),
        link.stdout,
        link.stderr
    );

    // RC_DEC_CHECK corruption face: a DEC of the non-heap Int slot (served the
    // String-field glue) trips the underflow check — the run must stay exit 2.
    let dc = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .env("CRANELISP_RC_DEC_CHECK", "1")
        .file("ma.cl", ma)
        .file("mb.cl", mb)
        .file("main.cl", main)
        .run("main.cl")
        .output();
    assert_eq!(
        dc.status.code(),
        Some(2),
        "[RC_DEC_CHECK] the collision must not trip an RC-underflow abort (a DEC on \
         a non-heap Int slot); got {:?}:\n{}{}",
        dc.status.code(),
        dc.stdout,
        dc.stderr
    );

    // REPL-vs-run divergence face (per-turn Jit batch vs whole-module ObjectModule).
    let repl = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("ma.cl", ma)
        .file("mb.cl", mb)
        .stdin(
            "(import [ma [MkA]])\n\
             (import [mb [MkB]])\n\
             (add-i64 (vec-len [(MkA \"hi\")]) (vec-len [(MkB 7)]))\n",
        )
        .output();
    let rc = format!("{}{}", repl.stdout, repl.stderr);
    assert!(
        rc.contains(":primitives/Int 2"),
        "[repl] the REPL must agree with `--run` (exit 2 ⇒ `:primitives/Int 2`); \
         a REPL-vs-run divergence is the S111 reachability-record collision-scope \
         face; got:\n{rc}"
    );
}
