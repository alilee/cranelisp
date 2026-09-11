//! S101 Phase-5 stage 1 — R3 redefinition-machinery QA-first set (lanes
//! L-R1–L-R4 of `tests/plan/s100-ownership-verification.md` §3.6/§6.1).
//!
//! Drafted FAILING-FIRST per `memory/feedback_failing_not_ignored.md`: the
//! RED tests below pin the behaviour `repl/spec.md` §18 (landed S101) promises
//! and today's binary does not deliver — the dependent-recompilation
//! transaction, trap stubs for BROKEN symbols, the cascade report, and the
//! type-change-hole cure. They flip green as the S101 `/dev` waves land
//! (typecheck 0470 → backend trap stub → src/ transaction).
//!
//! Draft-time polarity (verified by hand against HEAD 0b0e234 before
//! authoring — every RED shape was probed; crashes are SIGBUS/SIGSEGV):
//!   RED  ×11: L-R1(a)(b)(c)(d)(e×2)(f), L-R2(a), L-R3(b), L-R4(a)(b)
//!   GREEN ×2 pins: L-R2(b) late binding, L-R3(a) no-cascade (vacuous today)
//!
//! ## RESOLVED — S101 Wave 4 (2026-07-03): all 11 RED flipped GREEN
//!
//! The `/dev`(src/) session transaction (fire §13) landed at Wave 4; verified
//! stable at Wave 5 (double-run 3447/0/1 pre-Wave-5-additions). All tests
//! stand as permanent regression guards; `repl/spec.md` §18 rows carry the
//! `[Tested …]` citations. The T1 coherent-stale pins at the bottom carry
//! flip notes (they fail loudly when the full T1 cure lands — deliberate).
//!
//! ## The pre-break VALUE-carrier residue (documented per the Wave-1 brief)
//!
//! L-R1(b)/(c) and L-R2(a) ideally hold a closure/partial VALUE minted before
//! the ABI-changing redefinition and invoke it after. At stage M **no
//! cross-turn value carrier is REPL-reachable**: the language has no top-level
//! value binding (stdlib `def` is a macro expanding to a zero-arg `defn`, so
//! it re-evaluates through a recompiled static caller — the `/repl` Phase-3
//! finding; and stdlib is out of bounds for tests anyway), bare-expression
//! results are printed and dropped, and strand/channel carriers would need
//! effect-concurrency machinery that cannot be driven deterministically
//! across REPL turns from a stdin script. The closest reachable shapes used
//! here instead:
//!   - L-R1(b)/(c): a pre-break-COMPILED zero-arg minting fn (`(defn hold []
//!     g)` / `(defn mkp [] (g2 1))`). The fn-as-value / auto-curry wrapper it
//!     embeds is compiled before the break and targets the broken symbol's
//!     existing GOT slot — the same slot the in-place trap patch must cover,
//!     which is the mechanism §18.5 "every route traps" pins.
//!   - L-R2(a): the by-name/new-world half of §18.7 plus the no-mixed-ABI
//!     coherence fence. The frozen-world half (§18.7 requirement 1: a
//!     pre-break value sees OLD behaviour) is NOT directly assertable at
//!     stage M; its structural witness is L-R5(b) (fresh slot + surviving
//!     hole, `tests/repl_persist_redefine.rs`).
//! Residue: when a cross-turn value carrier exists (session value bindings,
//! or REPL-drivable strand state), add the direct frozen-world test — the
//! old-chain-behaviour assertion of §18.7. Recorded in
//! `tests/plan/s100-ownership-verification.md` §6.1 (drafting-notes addendum).

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

/// Count non-overlapping occurrences of `needle` in `hay`.
fn count(hay: &str, needle: &str) -> usize {
    hay.matches(needle).count()
}

// S121 deliberately retires the former trap/BROKEN/recovery acceptance band.
// `tests/plan/s121-test-plan.md` §10.3 names those cells and their disposition:
// guarded publication now refuses an incompatible replacement while the old
// target and callers are still live. The compact GR-1/GR-2 cells at the end of
// this file replace the applicable admission evidence; trap presentation and
// recovery have no replacement because that language behavior no longer exists.

// =============================================================================
// L-R2 — frozen-world vs late-binding (repl/spec.md §18.7, §18.2)
// =============================================================================

// spec: repl/spec.md §18.2 — GREEN PIN: a body-only (signature-preserving)
// redefinition late-binds: closures minted by existing compiled code pick up
// the new body at their next call. Today's prized semantic, pinned so slot
// versioning never eats it. GREEN at draft.
#[test]
fn redefine_body_only_stale_closure_late_binds_new_body() {
    let cap = repl_prims(
        "(defn base [:Int x] (add-i64 x 10))\n\
         (defn c [] (fn [z] (base z)))\n\
         ((c) 2)\n\
         (defn base [:Int x] (add-i64 x 20))\n\
         ((c) 2)\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 12")
    .assert_stdout_contains(":primitives/Int 22");
    // Exactly one old-body result: after the edit the closure must not serve
    // the old body again.
    assert_eq!(
        count(&cap.stdout, ":primitives/Int 12"),
        1,
        "post-edit ((c) 2) must late-bind to the new body (22), not 12; stdout={}",
        cap.stdout
    );
}

// =============================================================================
// L-R3 — summary-diff fast path / cascade report (repl/spec.md §18.2, §18.3)
// =============================================================================

const LR3_BASE: &str = "(defn callee [:Int x] (add-i64 x 1))\n\
                        (defn caller-a [:Int x] (callee x))\n\
                        (defn caller-p [x] (callee x))\n\
                        (defn unrelated [:Int x] (add-i64 x 100))\n";

/// True iff any stdout comment line (`; …` — the cascade-report section
/// format of §18.3) contains the needle. Definition confirmations start with
/// `:` and do not count.
fn any_report_line_contains(stdout: &str, needle: &str) -> bool {
    stdout
        .lines()
        .any(|l| l.trim_start().starts_with(';') && l.contains(needle))
}

// spec: repl/spec.md §18.2 — GREEN PIN (vacuous until the transaction lands,
// stated honestly): a body-only edit prints NO cascade sections and triggers
// no dependent recompiles; callers still work via late binding. Today no
// report machinery exists so the absence legs pass vacuously; the pin becomes
// load-bearing the moment the transaction lands (guards the fast path against
// over-triggering — L-D1 is its latency twin).
#[test]
fn redefine_body_only_neg_no_cascade_report_no_dependent_recompiles() {
    let cap = repl_prims(&format!(
        "{LR3_BASE}(defn callee [:Int x] (add-i64 x 2))\n\
         (caller-a 5)\n"
    ))
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 7"); // late-bound new body
    for needle in ["recompiled", "broken", "caller-a", "caller-p", "unrelated"] {
        assert!(
            !any_report_line_contains(&cap.stdout, needle),
            "body-only edit must print no cascade section naming `{needle}`; stdout={}",
            cap.stdout
        );
    }
}

// =============================================================================
// L-R4 — the latent type-change hole cure (repl/spec.md §18.1) — the sprint's
// own RED witness (spine design/arch/ownership-inference.md §5.2)
// =============================================================================

// =============================================================================
// T1-kind target: concrete fn redefined as a POLYMORPHIC template (the staged
// entry is slot-less) — FIXME 0478's repro, cured memory-safe by FIXME 0479
// =============================================================================

// spec: repl/spec.md §18.1 — coherence guarantee; design/int/session-transaction.md
// §10 T1 (the stage-M per-symbol-precision hole for non-concrete-UserFn targets).
//
// Shape: `f` compiled concrete + slotted; `g` compiled against it; `f` is then
// redefined as `(defn f [x] x)` — the staged entry is a slot-less Polymorphic
// TEMPLATE, so the commit gate classifies OUTSIDE per-symbol precision (T1) and
// no transaction runs. Before the 0479 fix the gate's `callable_got_slot()
// .is_some()` guard skipped the displacement entirely: `live.insert` dropped
// the last `Code` Arc for the old `f` while `g`'s compiled code still loads
// `f`'s (now-orphaned) GOT slot — `(g 5)` was a use-after-free SIGSEGV, exit
// 139 (verified live by /review at S101 Wave 4).
//
// Post-0479 sound behaviour pinned here: the session SURVIVES and `(g 5)` runs
// the FROZEN old chain (`add-i64 5 1` → 6) through the still-populated slot —
// coherent-stale execution, the design §4.3 frozen-world argument.
//
// T1 RESIDUE (deliberately pinned, not cured): semantically the redefinition
// changed `f`, so stale `g` silently answering through the OLD `f` is the
// known stage-M coherence hole for T1-kind targets — the full cure
// (recompile-or-trap for T1 targets) is FIXME 0477's design question. When it
// lands, the `:primitives/Int 6` pin below MUST flip to the cured behaviour
// (recompiled `g` → 5, or a trap with provenance); this test failing at that
// point is the prompt to update it. The concrete → `Overloaded` (multi-sig)
// sibling shape — same mechanism — is guarded by the next test (0478 drain).
// S102 reconciliation: the full cure is ruled OUT of S102 → S103
// (design/int/s102-defect-wave.md §2); the S102 A1 interim cure makes the
// downgrade turn PRINT the §18.1.1 `stale:` section — additive, this pin's
// assertions are unaffected. Acceptance wording for the S103 flip:
// report-or-recompile per §18.1.1's cure note (stale set renders empty).
// S103 FLIPPED (2026-07-06, T1 full cure landed): the end-of-turn reload
// recompiles `g` against the new identity `f`, so the former coherent-stale
// `:primitives/Int 6` pin is now the recompiled value 5 (`f x = x` ⇒ g(5)=5),
// and the `; stale:` section is omitted (nothing is stale after the recompile).
// The old-chain residue is superseded by the cure (design/int/session-
// transaction.md §10 T1 CS-1/2/3).
#[test]
fn concrete_to_polymorphic_change_with_caller_is_rejected() {
    let cap = repl_prims(
        "(defn f [x] (add-i64 x 1))\n\
         (defn g [y] (f y))\n\
         (g 1)\n\
         (defn f [x] x)\n\
         (g 5)\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 2")
    .assert_stdout_contains("cannot redefine user/f")
    .assert_stdout_contains("blocking dependents: user/g")
    .assert_stdout_contains(":primitives/Int 6")
    .assert_stdout_does_not_contain("; stale:");
    drop(cap);
}

// spec: repl/spec.md §18.1 — coherence guarantee; design/int/session-transaction.md
// §10 T1. SIBLING shape (FIXME 0478's named cheap sibling): concrete single-sig
// `f` redefined as a MULTI-SIG (Overloaded) defn — the staged entry is likewise
// spec: repl/spec/18-redefinition.md §18.1–§18.3 — single- and
// multi-signature defns are one callable class, but adding a signature changes
// the whole family's language type. A prior external caller blocks the complete
// candidate before the old single-signature definition is displaced.
#[test]
fn single_to_overload_family_change_with_caller_is_rejected() {
    let cap = repl_prims(
        "(defn f [x] (add-i64 x 1))\n\
         (defn g [y] (f y))\n\
         (g 1)\n\
         (defn f ([:Int x] x) ([:String s] (str-len s)))\n\
         (g 5)\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 2")
    .assert_stdout_contains("cannot redefine user/f")
    .assert_stdout_contains("blocking dependents: user/g")
    .assert_stdout_contains(":primitives/Int 6")
    .assert_stdout_does_not_contain("module error");
    drop(cap);
}

// =============================================================================
// S101 Phase 6a/6b defect-set guards (/qa guard batch, 2026-07-03).
// Four §18 conformance defects surfaced by the 6a/6b proxy exercise, all
// deterministic, all RED-first-verified on the S101 change-set binary.
//   - FIXME 0491: the internal `__expr` eval-wrapper leaks into the cascade
//     report's `broken:` section (both directions — break and revert).
//   - trap presentation format (no FIXME — these guards are the record): the
//     trap surfaces wrapped as `Error: codegen error at 0..0: runtime error:
//     runtime panic: <msg>` instead of §18.5's normative `runtime error:
//     <msg>` presentation.
//   - FIXME 0492 (target /repl — arbitration): `/sig`'s primary line is not
//     fully qualified, diverging from §18.4's "same primary line as bare
//     lookup" MUST. Guard authored against the CURRENT normative §18.4 text;
//     if /repl's arbitration amends the spec instead, re-anchor the expected
//     values here.
//   - FIXME 0486 broken-symbol arm: bare lookup corrupts the introspection
//     source that §18.4 requires /info to include for a broken symbol.
// Resolver for all four fix-side items: /int (report rendering, trap
// presentation, /sig display, bare-lookup source recording).
// =============================================================================

// =============================================================================
// S102 Phase-5 Stage-1 — lane L-U1: unannotated-default siblings + the §18.1.1
// downgrade-report acceptance pair (`tests/plan/s102-test-plan.md` §1.1;
// `tests/plan/coverage-audit-s101.md` §2.4 L-U1).
//
// The at-scale DEFAULT path: unannotated fns generalize, so their
// redefinition takes the §18.1 scope note's reuse-and-patch path (T1,
// design/int/session-transaction.md §10) — no transaction, no cascade, no
// trap. The audit found this path nearly unrepresented (39 concrete
// annotation sites vs ~2 polymorphic-target pins across the redefine lanes).
// The siblings below pin the CURRENT coherent-stale behaviour per transaction
// lane shape (GREEN at draft, probed 2026-07-03 on the CS-A binary), each
// with a flip note naming the cure acceptance; the report pair (RED at draft)
// is the acceptance surface for the S102 A1 interim cure — the §18.1.1
// `stale:` section, worded as a transaction-report line the S103 full cure
// keeps (Principle-8 pin, rendered empty under the cure).
//
// FLIP NOTES (uniform for the siblings): when the full T1 cure lands (S103 —
// end-of-turn-sequenced module reload, session-transaction.md §10; the two
// S101 coherent-stale pins above carry the same note), the stale-old-chain
// pins below MUST flip to the cured behaviour (caller recompiled against the
// new definition, or broken+trapped with provenance) and the §18.1.1 section
// renders empty. A sibling failing at that point is the prompt to update it.
// S103 RECONCILIATION: the cure acceptance surface is the pair at the end of
// this file — `t1_full_cure_recompiles_stale_callers_stale_section_empty`
// (positive: recompiled caller + empty stale section) and
// `t1_full_cure_body_only_edit_still_no_report_no_recompile` (over-trigger
// guard). When the positive one flips green, reconcile every coherent-stale
// pin's disposition in the same change-set.
// =============================================================================

// spec: repl/spec/18-redefinition.md §18.1–§18.2 — a generic-to-concrete
// language-type change is rejected when direct authored dependents exist; the
// sorted blocker list excludes unrelated definitions and the old body remains live.
#[test]
fn generic_to_concrete_change_reports_direct_blockers_and_keeps_old_body() {
    let cap = repl_prims(
        "(defn id [x] x)\n\
         (defn gcall [x] (id (add-i64 x 1)))\n\
         (defn bystander [x] (id x))\n\
         (defn unrelated [:Int x] (add-i64 x 9))\n\
         (gcall 1)\n\
         (defn id [x] (add-i64 x 100))\n\
         (gcall 1)\n\
         (defn newcomer [x] (id x))\n\
         (newcomer 1)\n",
    )
    .assert_ok()
    .assert_stdout_contains("cannot redefine user/id")
    .assert_stdout_contains("blocking dependents: user/bystander, user/gcall")
    .assert_stdout_does_not_contain("; stale:");
    assert_eq!(
        count(&cap.stdout, ":primitives/Int 2"),
        2,
        "the rejected replacement leaves the old generic body live; stdout={}",
        cap.stdout
    );
    let cap = cap
        .assert_stdout_contains(":primitives/Int 1")
        .assert_stdout_does_not_contain(":primitives/Int 102")
        .assert_stdout_does_not_contain(":primitives/Int 101");
    drop(cap);
}

// spec: repl/spec/18-redefinition.md §18.1 — a same-language-type body edit
// late-binds through the existing slot and prints no special redefinition report.
#[test]
fn same_type_body_edit_prints_no_special_report() {
    repl_prims(
        "(defn f [:Int x] (add-i64 x 1))\n\
         (defn g [:Int x] (f x))\n\
         (g 1)\n\
         (defn f [:Int x] (add-i64 x 2))\n\
         (g 1)\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 3") // late-bound new body (§18.2)
    .assert_stdout_does_not_contain("; stale:");
}

// spec: repl/spec/18-redefinition.md §18.1 — a caller-free language-type
// change publishes normally and prints no dependent-redefinition report.
#[test]
fn caller_free_generic_type_change_prints_no_special_report() {
    repl_prims(
        "(defn id [x] x)\n\
         (defn id [x] (add-i64 x 100))\n\
         (id 1)\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 101") // new definition is live by name
    .assert_stdout_does_not_contain("; stale:");
}

// spec: repl/spec.md §18.1 — L-U1 sibling of the trap lane (L-R1). S103 FLIPPED
// (2026-07-06, T1 full cure landed): with an UNANNOTATED generic target `f`
// (template) redefined to a concrete `Int→Int`, the compiled caller `g` (itself
// concrete `Int→Int`) is now RECOMPILED by the end-of-turn reload — the former
// coherent-stale old chain is superseded. The pre-downgrade `(g 1)` prints 2
// (old identity: f(add-i64 1 1)=2); the post-downgrade `(g 1)` prints 52
// (recompiled: f(2)=2+50=52). No trap (module-grain reload, not per-symbol).
#[test]
fn generic_to_concrete_change_with_caller_is_rejected() {
    let cap = repl_prims(
        "(defn f [x] x)\n\
         (defn g [y] (f (add-i64 y 1)))\n\
         (g 1)\n\
         (defn f [x] (add-i64 x 50))\n\
         (g 1)\n",
    )
    .assert_ok()
    .assert_stdout_contains("cannot redefine user/f")
    .assert_stdout_contains("blocking dependents: user/g");
    assert_eq!(count(&cap.stdout, ":primitives/Int 2"), 2);
    let cap = cap.assert_stdout_does_not_contain(":primitives/Int 52");
    drop(cap);
}

// spec: repl/spec.md §18.1 — L-U1 sibling of the cascade lane (L-R3): a T1
// downgrade runs NO transaction — the turn prints no `recompiled:` and no
// `broken:` section (contrast §18.3, which fires only for concrete
// single-sig targets at stage M). GREEN pin. NOTE: deliberately does NOT
// assert absence of the §18.1.1 `stale:` section — that section is the A1
// acceptance (positive pair above) and appears on exactly this turn shape.
#[test]
fn redefine_unannotated_generic_target_no_cascade_sections_sibling() {
    let cap = repl_prims(
        "(defn f [x] x)\n\
         (defn g [y] (f (add-i64 y 1)))\n\
         (g 1)\n\
         (defn f [x] (add-i64 x 50))\n\
         (g 1)\n",
    )
    .assert_ok();
    for needle in ["recompiled", "broken"] {
        assert!(
            !any_report_line_contains(&cap.stdout, needle),
            "a T1 downgrade must not print a `{needle}:` cascade section \
             (no transaction runs at stage M); stdout={}",
            cap.stdout
        );
    }
}

// spec: repl/spec.md §18.1 — L-U1 sibling of the recovery lane (L-R1(e)):
// on the T1 path the user's manual repair works — re-entering the CALLER's
// definition compiles it against the NEW callee, healing the split world by
// hand. GREEN pin (probed: 52 after the re-entry). This is the manual
// counterpart of the §18.6 transactional recovery the full cure extends to
// T1 targets.
#[test]
fn caller_reentry_after_rejected_change_still_targets_old_callee() {
    let cap = repl_prims(
        "(defn f [x] x)\n\
         (defn g [y] (f (add-i64 y 1)))\n\
         (g 1)\n\
         (defn f [x] (add-i64 x 50))\n\
         (defn g [y] (f (add-i64 y 1)))\n\
         (g 1)\n",
    )
    .assert_ok()
    .assert_stdout_contains("cannot redefine user/f")
    .assert_stdout_does_not_contain(":primitives/Int 52");
    assert_eq!(count(&cap.stdout, ":primitives/Int 2"), 2);
    drop(cap);
}

// spec: repl/spec.md §18.1 — L-U1 sibling: the split world in one session.
// After a T1 downgrade, a caller compiled BEFORE the turn keeps the old
// definition while a caller defined AFTER sees the new one — the two answers
// coexist. GREEN pin. S103 note (T1 full cure landed 2026-07-06): this pin
// does NOT flip, unlike its concrete siblings. `g` here is fully generic
// (`∀a. a→a`) — a slot-less TEMPLATE that is never compiled as a concrete
// function; its mono mint `g$Int` is deliberately edge-less (design §4.1), so
// `g` is never a "compiled caller" in the stale set and the end-of-turn reload
// does not touch it. The coherent-stale answer is genuinely correct here (the
// caller was never on a slotted old chain the cure could recompile). Contrast
// `redefine_unannotated_generic_target_caller_keeps_old_chain_sibling`, whose
// `g` is concrete (Int-forced) and DOES flip.
#[test]
fn rejected_generic_change_creates_no_split_world() {
    let cap = repl_prims(
        "(defn f [x] x)\n\
         (defn g [y] (f y))\n\
         (g 1)\n\
         (defn f [x] (add-i64 x 50))\n\
         (defn h [y] (f y))\n\
         (h 1)\n\
         (g 1)\n",
    )
    .assert_ok()
    .assert_stdout_contains("cannot redefine user/f")
    .assert_stdout_does_not_contain(":primitives/Int 51");
    assert_eq!(
        count(&cap.stdout, ":primitives/Int 1\n"),
        3,
        "old and newly compiled callers must both resolve the retained old definition; stdout={}",
        cap.stdout
    );
    let cap = cap.assert_stdout_does_not_contain("is broken by the redefinition");
    drop(cap);
}

// =============================================================================
// S103 Block C — the T1 FULL-CURE acceptance pair (qa plan
// `tests/plan/s103-test-plan.md` §1.4; repl/spec.md §18.1.1 negative-MUST;
// design/int/session-transaction.md §10 T1).
//
// The full cure replaces the S102 interim `stale:` PRINT with an end-of-turn-
// sequenced module reload: the callers the interim report named as `stale:` are
// now RECOMPILED by the end-of-turn transaction, so (per §18.1.1 "omitted when
// nothing is stale") the `stale:` section is omitted entirely AND a previously-
// stale caller called after the turn observes the NEW definition. The cure keeps
// the SAME report section (Principle-8, arch review pin), rendered empty.
//
// Under the cure the S102/S101 coherent-stale pins above
// (redefine_concrete_to_polymorphic_caller_survives_coherent_stale,
// redefine_concrete_to_overloaded_caller_survives_coherent_stale,
// redefine_unannotated_generic_target_caller_keeps_old_chain_sibling,
// redefine_unannotated_split_world_old_and_new_callers_coexist_sibling) FLIP:
// their coherent-stale residue is superseded (caller recompiled) — each already
// carries a flip note; `/qa` reconciles the disposition in the same change-set as
// the cure lands. NONE deleted or weakened (the "permanently-RED test for
// designed behaviour is wrong" ledger ruling: the flip note makes each fail
// loudly exactly when the cure lands, which is the intended signal).
// =============================================================================

// spec: repl/spec/18-redefinition.md §18.1–§18.2 — a blocked language-type
// change leaves the old callee and caller live and performs no dependent
// recompilation or special report.
#[test]
fn rejected_generic_change_does_not_recompile_callers() {
    let cap = repl_prims(
        "(defn id [x] x)\n\
         (defn gcall [x] (id (add-i64 x 1)))\n\
         (gcall 1)\n\
         (defn id [x] (add-i64 x 100))\n\
         (gcall 1)\n",
    )
    .assert_ok()
    .assert_stdout_contains("cannot redefine user/id")
    .assert_stdout_does_not_contain(":primitives/Int 102");
    assert_eq!(count(&cap.stdout, ":primitives/Int 2"), 2);
    let cap = cap
        .assert_stdout_does_not_contain("; stale:")
        .assert_stdout_does_not_contain("recompiled");
    drop(cap);
}

// spec: repl/spec/18-redefinition.md §18.1 — a same-language-type body edit
// patches its existing slot without recompiling dependents or printing a
// stale/recompiled/broken report.
#[test]
fn same_type_body_edit_late_binds_without_recompile_report() {
    let cap = repl_prims(
        "(defn f [:Int x] (add-i64 x 1))\n\
         (defn g [:Int x] (f x))\n\
         (g 1)\n\
         (defn f [:Int x] (add-i64 x 2))\n\
         (g 1)\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 3") // late-bound new body (§18.2)
    .assert_stdout_does_not_contain("; stale:");
    for needle in ["recompiled", "broken"] {
        assert!(
            !any_report_line_contains(&cap.stdout, needle),
            "a body-only edit must not trigger a reload cascade `{needle}:` \
             section (the cure must not over-trigger); stdout={}",
            cap.stdout
        );
    }
    drop(cap);
}

// spec: repl/spec/18-redefinition.md §18.3 — reordering a concrete overload
// family's unchanged signature set is a same-type redefinition. Existing named
// callers of two disjoint signatures must keep their selected bodies.
#[test]
fn overload_family_clause_reorder_preserves_realized_named_callers() {
    let out = Cranelisp::repl_capture(
        "(defn f ([:primitives/String x :primitives/Int y] 7) ([:primitives/Int x :primitives/String y] 42))\n\
         (defn call-string-int [] (f \"s\" 0))\n\
         (defn call-int-string [] (f 0 \"s\"))\n\
         (call-string-int)\n\
         (call-int-string)\n\
         (defn f ([:primitives/Int x :primitives/String y] 42) ([:primitives/String x :primitives/Int y] 7))\n\
         (call-string-int)\n\
         (call-int-string)\n",
    );
    let details = format!(
        "status={:?}\nstdout:\n{}\nstderr:\n{}",
        out.status, out.stdout, out.stderr
    );
    assert!(
        out.status.success(),
        "overload-family reorder must leave the child successful; {details}"
    );
    assert_eq!(
        count(&out.stdout, " user/f ; defn"),
        2,
        "initial definition and replacement must each confirm the complete family; {details}"
    );
    assert_eq!(
        count(
            &out.stdout,
            ":(Fn [primitives/String primitives/Int] primitives/Int) user/f"
        ),
        2,
        "both family confirmations must include the String/Int signature; {details}"
    );
    assert_eq!(
        count(
            &out.stdout,
            ":(Fn [primitives/Int primitives/String] primitives/Int) user/f"
        ),
        2,
        "both family confirmations must include the Int/String signature; {details}"
    );
    assert_eq!(
        count(&out.stdout, ":primitives/Int 7"),
        2,
        "the string/Int caller must select body 7 before and after reorder; {details}"
    );
    assert_eq!(
        count(&out.stdout, ":primitives/Int 42"),
        2,
        "the Int/string caller must select body 42 before and after reorder; {details}"
    );
    for needle in ["; stale:", "recompiled", "broken"] {
        assert!(
            !out.stdout.contains(needle),
            "same-type family reordering must not report dependent recompilation `{needle}`; {details}"
        );
    }
}

// spec: repl/spec/18-redefinition.md §18.3 — control: the already-reordered
// family has the same unambiguous signature-to-body selection in a fresh
// session, without a redefinition transition.
#[test]
fn overload_family_already_reordered_fresh_session_control() {
    let out = Cranelisp::repl_capture(
        "(defn f ([:primitives/Int x :primitives/String y] 42) ([:primitives/String x :primitives/Int y] 7))\n\
         (defn call-string-int [] (f \"s\" 0))\n\
         (defn call-int-string [] (f 0 \"s\"))\n\
         (call-string-int)\n\
         (call-int-string)\n",
    );
    let details = format!(
        "status={:?}\nstdout:\n{}\nstderr:\n{}",
        out.status, out.stdout, out.stderr
    );
    assert!(
        out.status.success(),
        "fresh reordered overload family must leave the child successful; {details}"
    );
    assert_eq!(
        count(&out.stdout, ":primitives/Int 7"),
        1,
        "the fresh string/Int caller must select body 7; {details}"
    );
    assert_eq!(
        count(&out.stdout, ":primitives/Int 42"),
        1,
        "the fresh Int/string caller must select body 42; {details}"
    );
}

// spec: repl/spec/18-redefinition.md §18.3 — reordering a generic overload
// family's unchanged signatures is a same-type redefinition. The replacement
// must publish completely and preserve existing callers of both realized arms.
#[test]
fn generic_overload_family_reorder_preserves_realized_named_callers() {
    let out = Cranelisp::repl_capture(
        "(defn f ([:a x] 7) ([:a x :b y] 42))\n\
         (defn call-one [] (f 0))\n\
         (defn call-two [] (f 0 0))\n\
         (call-one)\n\
         (call-two)\n\
         (defn f ([:a x :b y] 42) ([:a x] 7))\n\
         (call-one)\n\
         (call-two)\n",
    );
    let details = format!(
        "status={:?}\nstdout:\n{}\nstderr:\n{}",
        out.status, out.stdout, out.stderr
    );
    assert!(
        out.status.success(),
        "generic overload-family reorder must leave the child successful; {details}"
    );
    assert!(
        !out.stdout.contains("Error:"),
        "the same-type replacement must be accepted before its callers are reused; {details}"
    );
    assert_eq!(
        count(&out.stdout, " user/f ; defn"),
        2,
        "initial definition and replacement must each confirm the complete generic family; {details}"
    );
    assert_eq!(
        count(&out.stdout, ":(Fn [a] primitives/Int) user/f"),
        2,
        "both family confirmations must include the one-argument generic signature; {details}"
    );
    assert_eq!(
        count(&out.stdout, ":(Fn [a b] primitives/Int) user/f"),
        2,
        "both family confirmations must include the two-argument generic signature; {details}"
    );
    assert_eq!(
        count(&out.stdout, ":primitives/Int 7"),
        2,
        "the realized one-argument caller must return 7 before and after reorder; {details}"
    );
    assert_eq!(
        count(&out.stdout, ":primitives/Int 42"),
        2,
        "the realized two-argument caller must return 42 before and after reorder; {details}"
    );
    for needle in ["; stale:", "recompiled", "broken"] {
        assert!(
            !out.stdout.contains(needle),
            "same-type generic-family reordering must not report a cascade `{needle}`; {details}"
        );
    }
}

// spec: repl/spec/18-redefinition.md §18.3 — control: the already-reordered
// generic family publishes completely and selects both arms in a fresh session.
#[test]
fn generic_overload_family_already_reordered_fresh_session_control() {
    let out = Cranelisp::repl_capture(
        "(defn f ([:a x :b y] 42) ([:a x] 7))\n\
         (defn call-one [] (f 0))\n\
         (defn call-two [] (f 0 0))\n\
         (call-one)\n\
         (call-two)\n",
    );
    let details = format!(
        "status={:?}\nstdout:\n{}\nstderr:\n{}",
        out.status, out.stdout, out.stderr
    );
    assert!(
        out.status.success(),
        "fresh reordered generic family must leave the child successful; {details}"
    );
    assert!(
        !out.stdout.contains("Error:"),
        "fresh reordered generic family must be accepted; {details}"
    );
    assert_eq!(
        count(&out.stdout, " user/f ; defn"),
        1,
        "the fresh session must confirm one complete generic family; {details}"
    );
    assert_eq!(
        count(&out.stdout, ":(Fn [a] primitives/Int) user/f"),
        1,
        "the family confirmation must include the one-argument generic signature; {details}"
    );
    assert_eq!(
        count(&out.stdout, ":(Fn [a b] primitives/Int) user/f"),
        1,
        "the family confirmation must include the two-argument generic signature; {details}"
    );
    assert_eq!(
        count(&out.stdout, ":primitives/Int 7"),
        1,
        "the fresh one-argument caller must return 7; {details}"
    );
    assert_eq!(
        count(&out.stdout, ":primitives/Int 42"),
        1,
        "the fresh two-argument caller must return 42; {details}"
    );
}

// spec: repl/spec/18-redefinition.md §18.1–§18.2 — a macro clause's
// ordinary call edge blocks an incompatible helper replacement, but the
// diagnostic reports the authored macro parent exactly once and never leaks
// its private clause key. QA allocation: tests/plan/s121-test-plan.md GR-6.
#[test]
fn macro_clause_blocker_is_reported_as_its_authored_parent() {
    let cap = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::None)
        .file(
            "helper.cl",
            "(import [macros [*]])\n\
             (defn bump [:Sexp s] (SexpInt 42))\n",
        )
        .file(
            "mac.cl",
            "(import [helper [bump]])\n\
             (defmacro wrap [a] (bump a))\n",
        )
        .stdin(
            "(import [mac [wrap]])\n\
             (wrap 41)\n\
             /mod helper\n\
             (defn bump [:SList s] (SexpInt 99))\n\
             (bump (SexpInt 1))\n\
             /quit\n",
        )
        .output();
    let cap = cap
        .assert_stdout_contains("cannot redefine helper/bump")
        .assert_stdout_contains("blocking dependents: mac/wrap")
        .assert_stdout_contains("mac/wrap")
        .assert_stdout_contains("SexpInt 42")
        .assert_no_internal_artifacts();
    assert_eq!(
        count(&cap.stdout, "mac/wrap"),
        1,
        "multiple private clauses of one macro must deduplicate to its authored parent; stdout:\n{}",
        cap.stdout
    );
    drop(cap);
}

// spec: repl/spec.md §18.8 / §14.4 — the CS-3 error-blocked floor is
// LIFTABLE by repair, never a lockout (the 0489 floor). S103 Wave-4 /review
// FINDING 5 (recovery leg, verified behaviorally per
// feedback_verify_fix_not_symptom_absence — not just absence-of-crash). A T1
// downgrade (generalizing `id` redefined to a CONCRETE `String -> Int`) makes
// the compiled caller `g` (which passes an `Int`) a genuine type mismatch, so
// the module reload FAILS and the turn enters §14.4 error-blocked. The user
// then re-defines `g` as the repair, the block LIFTS, and `g` runs again. This
// exercises the full round-trip: downgrade → reload-fail → block → refuse →
// repair → lift → run — and the session exits cleanly (never a lockout or exit).
#[test]
fn rejected_generic_change_does_not_enter_error_blocked_state() {
    let cap = repl_prims(
        "(defn id [x] x)\n\
         (defn g [:Int y] (id (add-i64 y 1)))\n\
         (g 1)\n\
         (defn id [:String s] (str-len s))\n\
         (g 5)\n\
         (defn g [:Int y] (add-i64 y 100))\n\
         (g 5)\n",
    )
    .assert_ok()
    .assert_stdout_contains("cannot redefine user/id")
    .assert_stdout_contains(":primitives/Int 6")
    .assert_stdout_does_not_contain("has errors");
    let cap = cap.assert_stdout_contains(":primitives/Int 105");
    drop(cap);
}

// =============================================================================
// S103 increment-II — L-S1 session-history preamble grid on the REDEFINITION
// surface (qa plan `tests/plan/s103-test-plan.md` §1.6; FIXME 0499 L-S1). A
// redefinition outcome (body-only late-binding, defn confirmation) MUST be
// invariant to what preceded it in the session — the generalization to the
// surfaces 6a did NOT burn. GREEN-expected; a RED is a real history-sensitivity
// defect. Companion of the repl_introspection.rs L-S1 grid.
// =============================================================================

/// The L-S1 preamble grid (redefinition surface).
const LS1_PREAMBLES: &[(&str, &str)] = &[
    ("empty", ""),
    ("bare_lookup", "add-i64\n"),
    ("expression_turn", "(add-i64 1 2)\n"),
    ("prior_failed_turn", "(undefined-symbol-xyz 1)\n"),
    ("reset", "/reset\n"),
];

/// Run `body` under each preamble (PrimitivesOnly REPL) and assert `needle`
/// appears in stdout regardless of session history.
fn assert_preamble_invariant(body: &str, needle: &str) {
    for (label, pre) in LS1_PREAMBLES {
        let cap = repl_prims(&format!("{pre}{body}"));
        assert!(
            cap.stdout.contains(needle),
            "L-S1 preamble `{label}`: expected `{needle}` in stdout regardless \
             of session history; stdout:\n{}\nstderr:\n{}",
            cap.stdout,
            cap.stderr
        );
    }
}

// spec: repl/spec.md §18.2 — a body-only redefinition late-binds the new body
// regardless of session history (the caller sees the new result).
#[test]
fn ls1_body_only_redefinition_late_binds_invariant_to_session_history() {
    assert_preamble_invariant(
        "(defn f [:Int x] (add-i64 x 1))\n\
         (defn g [:Int x] (f x))\n\
         (g 10)\n\
         (defn f [:Int x] (add-i64 x 2))\n\
         (g 10)\n",
        ":primitives/Int 12",
    );
}

// spec: repl/spec.md §1.3 — a defn confirmation names the qualified symbol
// regardless of session history.
#[test]
fn ls1_defn_confirmation_invariant_to_session_history() {
    assert_preamble_invariant("(defn h [:Int x] (add-i64 x 7))\n", "user/h");
}

// spec: repl/spec.md §18.1 — a fresh definition-and-call answers correctly
// regardless of session history (the coherent-execution baseline).
#[test]
fn ls1_fresh_definition_and_call_invariant_to_session_history() {
    assert_preamble_invariant(
        "(defn k [:Int x] (add-i64 x 5))\n(k 1)\n",
        ":primitives/Int 6",
    );
}

// =============================================================================
// S106 — L-S1 GENERALIZATION to the redefinition/cascade report surface (FIXME
// 0499). Extends the grid to the §18.1.1 downgrade-report shape under the
// {prior failed turn, /reset} preambles, plus the +neg no-`__expr`-noise guard.
// GREEN-expected robustness guards.
// =============================================================================

/// Run `body` under each preamble and assert `needle` is ABSENT from stdout
/// regardless of session history (the negative complement of
/// `assert_preamble_invariant`).
fn assert_preamble_invariant_absent(body: &str, needle: &str) {
    for (label, pre) in LS1_PREAMBLES {
        let cap = repl_prims(&format!("{pre}{body}"));
        assert!(
            !cap.stdout.contains(needle),
            "L-S1 preamble `{label}`: `{needle}` MUST NOT appear regardless of \
             session history; stdout:\n{}\nstderr:\n{}",
            cap.stdout,
            cap.stderr
        );
    }
}

// spec: repl/spec/18-redefinition.md §18.1 — a same-language-type body edit
// late-binds through an existing caller under every session-history preamble.
#[test]
fn ls1_same_type_late_binding_invariant_to_session_history() {
    assert_preamble_invariant(
        "(defn base [:Int x] (add-i64 x 1))\n\
         (defn caller [:Int x] (base x))\n\
         (caller 10)\n\
         (defn base [:Int x] (add-i64 x 100))\n\
         (caller 10)\n",
        ":primitives/Int 110",
    );
}

// spec: repl/spec/18-redefinition.md §18.1 — same-type redefinition produces no
// special report and therefore cannot leak the synthetic `__expr` name.
#[test]
fn ls1_same_type_redefinition_no_expr_noise_neg() {
    assert_preamble_invariant_absent(
        "(defn base [:Int x] (add-i64 x 1))\n\
         (defn caller [:Int x] (base x))\n\
         (caller 10)\n\
         (defn base [:Int x] (add-i64 x 100))\n\
         (caller 10)\n",
        "__expr",
    );
}

// =============================================================================
// S121 guarded publication — the first replacement for the retired dependent-
// recompilation transaction. These cells deliberately distinguish admission
// from compensation: an incompatible proposal is refused while the old world
// is still intact, rather than published and repaired afterward.
// QA allocation: tests/plan/s121-test-plan.md GR-2.
// =============================================================================

// spec: repl/spec/18-redefinition.md §18.1–§18.2 — a settled direct caller
// blocks a language-type-changing replacement. The diagnostic fields are
// ordered, and rejection preserves both the old callee and its caller.
#[test]
fn type_change_with_direct_caller_is_rejected_before_publication() {
    let cap = repl_prims(
        "(defn f [:Int x] (add-i64 x 1))\n\
         (defn z-call [:Int y] (f y))\n\
         (defn a-value [] f)\n\
         (defn transitive [:Int y] (z-call y))\n\
         (defn unrelated [:Int y] (add-i64 y 10))\n\
         (z-call 1)\n\
         (defn f [:String s] (str-len s))\n\
         (f 2)\n\
         (z-call 2)\n",
    );

    let ordered = [
        "cannot redefine user/f",
        "old language type: (Fn [primitives/Int] primitives/Int)",
        "proposed language type: (Fn [primitives/String] primitives/Int)",
        "blocking dependents: user/a-value, user/z-call",
        "retain the old type or introduce a new name",
    ];
    let mut cursor = 0;
    for needle in ordered {
        let Some(relative) = cap.stdout[cursor..].find(needle) else {
            panic!(
                "missing ordered guarded-redefinition field `{needle}`; stdout:\n{}\nstderr:\n{}",
                cap.stdout, cap.stderr
            );
        };
        cursor += relative + needle.len();
    }

    assert_eq!(
        count(&cap.stdout, ":primitives/Int 3"),
        2,
        "both the rejected target's old body and its caller must remain live; stdout:\n{}",
        cap.stdout
    );
    assert!(
        !cap.stdout.contains(":primitives/Int 1"),
        "the rejected String body must never become live; stdout:\n{}",
        cap.stdout
    );
}

// spec: repl/spec/18-redefinition.md §18.2 — direct recursion is not an
// external blocker, whereas a distinct mutually-recursive sibling is.
// QA allocation: tests/plan/s121-test-plan.md GR-3.
#[test]
fn self_edge_does_not_block_but_mutual_sibling_does() {
    let self_only = repl_prims(
        "(defn f [:Int x] (if (eq-i64 x 0) 0 (f (sub-i64 x 1))))\n\
         (defn f [:String s] (str-len s))\n\
         (f \"four\")\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 4")
    .assert_stdout_does_not_contain("blocking dependents:");
    drop(self_only);

    let mutual = repl_prims(
        "(begin\n\
           (defn left [:Int x] (if (eq-i64 x 0) 0 (right (sub-i64 x 1))))\n\
           (defn right [:Int x] (if (eq-i64 x 0) 0 (left (sub-i64 x 1)))))\n\
         (defn left [:String s] (str-len s))\n\
         (left 1)\n",
    )
    .assert_stdout_contains("cannot redefine user/left")
    .assert_stdout_contains("blocking dependents: user/right")
    .assert_stdout_contains(":primitives/Int 0");
    drop(mutual);
}

// spec: repl/spec/18-redefinition.md §18.2 — concrete realizations of one
// generic dependent normalize to its authored definition. Multiple realized
// types therefore cannot duplicate or hide that blocker. QA allocation:
// tests/plan/s121-test-plan.md GR-3.
#[test]
fn generic_realizations_report_one_authored_blocker() {
    let cap = repl_prims(
        "(defn f [:Int x] (add-i64 x 1))\n\
         (defn generic [x] (f 1))\n\
         (generic 1)\n\
         (generic \"two\")\n\
         (defn f [:String s] (str-len s))\n\
         (f 2)\n",
    )
    .assert_stdout_contains("cannot redefine user/f")
    .assert_stdout_contains("blocking dependents: user/generic")
    .assert_stdout_contains(":primitives/Int 3");
    let blocker_line = cap
        .stdout
        .lines()
        .find(|line| line.contains("blocking dependents:"))
        .unwrap_or_default();
    assert_eq!(
        blocker_line.matches("user/generic").count(),
        1,
        "realizations must deduplicate to one authored blocker; line={blocker_line}"
    );
}

// spec: repl/spec/18-redefinition.md §18.1–§18.2 — absent a blocking
// dependent, a language-type-changing replacement publishes normally.
// QA allocation: tests/plan/s121-test-plan.md GR-2.
#[test]
fn caller_free_type_change_publishes() {
    let cap = repl_prims(
        "(defn f [:Int x] (add-i64 x 1))\n\
         (f 1)\n\
         (defn f [:String s] (str-len s))\n\
         (f \"four\")\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 2")
    .assert_stdout_contains(":primitives/Int 4")
    .assert_stdout_does_not_contain("blocking dependents:");
    drop(cap);
}

// spec: repl/spec/18-redefinition.md §18.1.2 — an unchanged language type
// does not permit an existing live slot to change its ABI-bearing parameter
// mode. Rejection is independent of caller presence and preserves the old
// body. QA allocation: tests/plan/s121-test-plan.md GR-1.
#[test]
fn same_type_ownership_abi_change_is_rejected_before_slot_patch() {
    let cap = repl_prims(
        "(defn f [:String s] (str-len s))\n\
         (f \" x \")\n\
         (defn f [:String s] (str-len (trim s)))\n\
         (f \" x \")\n",
    );
    let cap = cap
        .assert_stdout_contains("cannot redefine user/f")
        .assert_stdout_contains("language type is unchanged")
        .assert_stdout_contains("old ownership ABI: params [Borrowed], result Fresh")
        .assert_stdout_contains("proposed ownership ABI: params [Owned], result Fresh")
        .assert_stdout_contains("the proposed replacement changes the ownership ABI");
    assert_eq!(
        count(&cap.stdout, ":primitives/Int 3"),
        2,
        "the rejected trim body must not patch the old slot; stdout:\n{}",
        cap.stdout
    );
    assert!(
        !cap.stdout.contains(":primitives/Int 1"),
        "the rejected body must never run; stdout:\n{}",
        cap.stdout
    );
}

// spec: repl/spec/18-redefinition.md §18.1, §18.4 — callable and macro
// visibility is immutable in both directions during live redefinition. The
// rejected proposal cannot displace the old definition. QA allocation:
// tests/plan/s121-test-plan.md GR-5.
#[test]
fn live_redefinition_rejects_callable_and_macro_visibility_changes() {
    let cells = [
        (
            "defn public-to-private",
            "(defn f [:Int x] (add-i64 x 1))\n\
             (defn- f [:Int x] (add-i64 x 100))\n\
             (f 1)\n",
            ":primitives/Int 2",
        ),
        (
            "defn private-to-public",
            "(defn- f [:Int x] (add-i64 x 1))\n\
             (defn f [:Int x] (add-i64 x 100))\n\
             (f 1)\n",
            ":primitives/Int 2",
        ),
        (
            "defmacro public-to-private",
            "(defmacro m [x] x)\n\
             (defmacro- m [x] (macros/SexpInt 100))\n\
             (m 2)\n",
            ":primitives/Int 2",
        ),
        (
            "defmacro private-to-public",
            "(defmacro- m [x] x)\n\
             (defmacro m [x] (macros/SexpInt 100))\n\
             (m 2)\n",
            ":primitives/Int 2",
        ),
    ];

    for (label, source, old_result) in cells {
        let cap = repl_prims(source);
        assert!(
            cap.stdout.contains("declaration visibility cannot change")
                && cap.stdout.contains(old_result),
            "{label}: visibility change must be rejected and old definition retained; stdout:\n{}\nstderr:\n{}",
            cap.stdout,
            cap.stderr
        );
        assert!(
            !cap.stdout.contains(":primitives/Int 100"),
            "{label}: rejected definition must never run; stdout:\n{}",
            cap.stdout
        );
    }
}
