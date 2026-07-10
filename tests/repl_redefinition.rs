//! S101 Phase-5 stage 1 — R3 redefinition-machinery QA-first set (lanes
//! L-R1–L-R4 of `tests/plan/s100-ownership-verification.md` §3.6/§6.1).
//!
//! Drafted FAILING-FIRST per `memory/feedback_failing_not_ignored.md`: the
//! RED tests below pin the behaviour `repl/spec.md` §18 (landed S101) promises
//! and today's binary does not deliver — the dependent-recompilation
//! transaction, trap stubs for BROKEN symbols, the cascade report, and the
//! type-change-hole cure. They flip green as the S101 `/dev` waves land
//! (typecheck 0470 → backend trap stub → src/ transaction). Ledger entry:
//! `tests/plan/ledger.md` §"Sprint 101 Phase-5 Stage-1".
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
//! Flip record: `tests/plan/ledger.md` §"Sprint 101 Phase-5 Stage-1".
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

fn repl_prims_env(lines: &str, key: &str, val: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .env(key, val)
        .stdin(lines)
        .output()
}

/// Count non-overlapping occurrences of `needle` in `hay`.
fn count(hay: &str, needle: &str) -> usize {
    hay.matches(needle).count()
}

// The L-R1 base fixture (qa plan §6.1): `g` compiled against Int `f`; the
// redefinition of `f` to a String signature is ABI-(type-scheme-)changing and
// `g`'s annotated body cannot re-typecheck ⇒ g must become BROKEN.
const LR1_BASE: &str = "(defn f [:Int x] (add-i64 x 1))\n\
                        (defn g [:Int y] (f y))\n\
                        (g 41)\n\
                        (defn f [:String s] (str-len s))\n";

// =============================================================================
// L-R1 — trap stubs (repl/spec.md §18.5, §18.4, §18.6)
// =============================================================================

// spec: repl/spec.md §18.5 — direct call of a broken symbol raises the trap
// message with provenance; the session survives. Negative: the stale caller
// must NOT silently execute (no `:primitives/Int 6`), and MUST NOT kill the
// session (today this shape dies SIGBUS passing an Int as a String pointer).
// RED on HEAD.
#[test]
fn redefine_abi_change_broken_caller_direct_call_traps_with_provenance() {
    let cap = repl_prims(&format!("{LR1_BASE}(g 5)\n"));
    let cap = cap.assert_ok(); // process survival — the REPL must never die on this
    assert!(
        cap.stdout.contains(":primitives/Int 42"),
        "pre-break sanity (g 41) must print 42; stdout={}",
        cap.stdout
    );
    let cap = cap
        .assert_stdout_contains("user/g is broken by the redefinition of user/f")
        .assert_stdout_does_not_contain(":primitives/Int 6");
    drop(cap);
}

// spec: repl/spec.md §18.5 — a value use of the broken symbol reaches the
// trap through g's existing (in-place-patched) slot. Closest-reachable
// carrier at stage M: `hold` is COMPILED pre-break and embeds the fn-as-value
// wrapper targeting g's slot (see module header residue note). RED on HEAD
// (SIGBUS today).
#[test]
fn redefine_broken_caller_value_use_wrapper_minted_before_break_reaches_trap() {
    let cap = repl_prims(
        "(defn f [:Int x] (add-i64 x 1))\n\
         (defn g [:Int y] (f y))\n\
         (defn hold [] g)\n\
         ((hold) 41)\n\
         (defn f [:String s] (str-len s))\n\
         ((hold) 5)\n",
    )
    .assert_ok();
    assert!(
        cap.stdout.contains(":primitives/Int 42"),
        "pre-break ((hold) 41) must print 42; stdout={}",
        cap.stdout
    );
    let cap = cap
        .assert_stdout_contains("user/g is broken by the redefinition of user/f")
        .assert_stdout_does_not_contain(":primitives/Int 6");
    drop(cap);
}

// spec: repl/spec.md §18.5 — a curried partial of a broken symbol reaches the
// trap. `mkp` is compiled pre-break; the auto-curry wrapper it embeds targets
// g2's slot (closest-reachable carrier, see module header). RED on HEAD
// (SIGBUS today).
#[test]
fn redefine_broken_caller_curried_partial_reaches_trap() {
    let cap = repl_prims(
        "(defn f [:Int x] (add-i64 x 1))\n\
         (defn g2 [:Int a :Int b] (f (add-i64 a b)))\n\
         (defn mkp [] (g2 1))\n\
         ((mkp) 5)\n\
         (defn f [:String s] (str-len s))\n\
         ((mkp) 5)\n",
    )
    .assert_ok();
    assert!(
        cap.stdout.contains(":primitives/Int 7"),
        "pre-break ((mkp) 5) must print 7; stdout={}",
        cap.stdout
    );
    let cap = cap.assert_stdout_contains("user/g2 is broken by the redefinition of user/f");
    // The trap, not a second successful application: exactly one successful
    // `:primitives/Int 7` (the pre-break one).
    assert_eq!(
        count(&cap.stdout, ":primitives/Int 7"),
        1,
        "post-break curried partial must trap, not re-produce 7; stdout={}",
        cap.stdout
    );
}

// spec: repl/spec.md §18.4 — `/info` and `/sig` on a broken symbol show the
// provenance phrase; `/info` shows no code-size stats for it. The healthy
// redefined symbol `f` shows no broken line (separate session so the negative
// is not polluted by g's output). RED on HEAD.
#[test]
fn redefine_broken_caller_info_and_sig_report_broken_status() {
    let cap = repl_prims(&format!("{LR1_BASE}/info g\n/sig g\n"))
        .assert_ok()
        .assert_stdout_contains("broken by the redefinition of user/f");
    // Both /info and /sig carry the provenance comment line (§18.4).
    assert!(
        count(&cap.stdout, "broken by the redefinition of user/f") >= 2,
        "both /info g and /sig g must carry the provenance line; stdout={}",
        cap.stdout
    );
    // §18.4: /info on a broken symbol MUST NOT present code-size stats
    // (today's healthy /info prints `  NN bytes`).
    let after_info = cap
        .stdout
        .split("broken by the redefinition of")
        .nth(1)
        .unwrap_or("")
        .to_string();
    assert!(
        !after_info.contains(" bytes"),
        "/info on a broken symbol must not show code-size stats; stdout={}",
        cap.stdout
    );
    // §18.4 third MUST component (FIXME 0480): /info on a broken symbol also
    // shows the DEFINITION SOURCE — the thing the user most needs to fix it.
    // The source appears only via /info here (the REPL never echoes input).
    assert!(
        cap.stdout.contains("(defn g") && cap.stdout.contains("(f y)"),
        "/info on a broken symbol must show its definition source \
         (repl/spec.md §18.4); stdout={}",
        cap.stdout
    );

    // Negative leg, clean session: the redefined symbol itself is healthy —
    // /info f and /sig f carry no broken/provenance line (§18.4 negative).
    // Wave-4 amendment: the breaking turn in THIS session normatively prints
    // its §18.3 cascade report (`; broken:` naming g), so the whole-stdout
    // absence check drafted before the report existed is unsatisfiable;
    // scope the negative to the output AFTER the report's broken line.
    let neg = repl_prims(&format!("{LR1_BASE}/info f\n/sig f\n")).assert_ok();
    let after_report = neg.stdout.rsplit("; broken:").next().unwrap_or("");
    // Skip the report explicitly (F8 fix): first the remainder of the
    // `; broken:` line itself (empty), then the section's own body lines —
    // every continuation line starts with `;` (`;  g — <error>`); the section
    // ends at the first non-comment line (the next prompt/primary line). This
    // holds even if the broken-reason wording ever gains the word "broken".
    let intro_output: String = after_report
        .lines()
        .skip(1) // remainder of the `; broken:` line
        .skip_while(|l| l.trim_start().starts_with(';')) // the section body
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        !intro_output.contains("broken"),
        "/info f and /sig f on the healthy redefined symbol must carry no \
         broken line; post-report output:\n{intro_output}\nfull stdout:\n{}",
        neg.stdout
    );
}

// spec: repl/spec.md §18.6 — recovery direction 1: redefining the broken
// symbol to match the new signature makes it green, callable, with no
// provenance residue. RED on HEAD (no broken status exists to observe).
#[test]
fn redefine_recovery_fixing_caller_clears_broken() {
    let cap = repl_prims(&format!(
        "{LR1_BASE}/info g\n\
         (defn g [:String s] (f s))\n\
         (g \"a\")\n\
         /info g\n"
    ))
    .assert_ok()
    // Pre-fix: g is broken with provenance (RED leg today).
    .assert_stdout_contains("broken by the redefinition of user/f")
    // Post-fix: callable.
    .assert_stdout_contains(":primitives/Int 1");
    // Post-fix negative: the tail after the successful call carries no broken
    // residue (§18.6 "indistinguishable from one that was never broken").
    let tail = cap
        .stdout
        .split(":primitives/Int 1")
        .last()
        .unwrap_or("")
        .to_string();
    assert!(
        !tail.contains("broken"),
        "after recovery, /info g must carry no broken/provenance residue; stdout={}",
        cap.stdout
    );
}

// spec: repl/spec.md §18.6 — recovery direction 2: redefining the CAUSE back
// to a compatible signature recompiles the broken symbol, which appears in
// the turn's `recompiled:` section, and works again. RED on HEAD (no cascade
// report machinery exists).
#[test]
fn redefine_recovery_reverting_callee_recompiles_caller() {
    let cap = repl_prims(&format!(
        "{LR1_BASE}(defn f [:Int x] (add-i64 x 1))\n\
         (g 41)\n\
         /info g\n"
    ))
    .assert_ok()
    // The revert turn reports g recompiled (§18.3/§18.6 worked example).
    .assert_stdout_contains("recompiled");
    assert!(
        count(&cap.stdout, ":primitives/Int 42") >= 2,
        "g must work both pre-break and after the revert; stdout={}",
        cap.stdout
    );
    // No broken residue after the revert-recovery.
    let tail = cap.stdout.rsplit(":primitives/Int 42").next().unwrap_or("");
    assert!(
        !tail.contains("broken by the redefinition"),
        "after reverting f, /info g must be clean; stdout={}",
        cap.stdout
    );
}

// spec: repl/spec.md §18.5 — repeated traps neither crash nor corrupt; the
// per-trap reference leak is BOUNDED, not zero (the RC-mid-panic caveat).
// Self-calibrating bound: a control session with the same call count but no
// break measures the baseline alloc/dealloc imbalance; the trap session may
// exceed it by at most TRAPS × PER_TRAP_TOLERANCE. RED on HEAD (the first
// post-break call kills the session, so no RC_STATS line is ever printed).
#[test]
fn redefine_trap_invocations_leak_bounded_per_trap() {
    const TRAPS: i64 = 20;
    // Generous per-trap tolerance: the String arg + trap-message/raise
    // buffers. Documented tolerance per §18.5 "bounded leak note".
    const PER_TRAP_TOLERANCE: i64 = 4;

    fn rc_imbalance(stderr: &str) -> i64 {
        // `[RC_STATS] rc_inc=N rc_dec=N allocs=N deallocs=N` (emitted at exit)
        let line = stderr
            .lines()
            .find(|l| l.contains("[RC_STATS]"))
            .unwrap_or_else(|| {
                panic!("no [RC_STATS] line on stderr (session died before exit?): {stderr}")
            });
        let field = |k: &str| -> i64 {
            line.split_whitespace()
                .find_map(|tok| tok.strip_prefix(&format!("{k}=")))
                .and_then(|v| v.parse().ok())
                .unwrap_or_else(|| panic!("no {k}= field in RC_STATS line: {line}"))
        };
        field("allocs") - field("deallocs")
    }

    let calls: String = (0..TRAPS).map(|_| "(g \"abc\")\n").collect();

    // Broken fixture: g takes a heap (String) arg; f's break makes g BROKEN.
    let trap_session = repl_prims_env(
        &format!(
            "(defn f [:Int x] (add-i64 x 1))\n\
             (defn g [:String s] (f 1))\n\
             (defn f [:String s] (str-len s))\n\
             {calls}"
        ),
        "CRANELISP_RC_STATS",
        "1",
    )
    .assert_ok();
    assert_eq!(
        count(&trap_session.stdout, "is broken by the redefinition of"),
        TRAPS as usize,
        "all {TRAPS} calls must trap (session survives every one); stdout={}",
        trap_session.stdout
    );

    // Control: same shape, no break, same number of calls.
    let control = repl_prims_env(
        &format!(
            "(defn f [:Int x] (add-i64 x 1))\n\
             (defn g [:String s] (f 1))\n\
             {calls}"
        ),
        "CRANELISP_RC_STATS",
        "1",
    )
    .assert_ok();

    let trap_imb = rc_imbalance(&trap_session.stderr);
    let ctl_imb = rc_imbalance(&control.stderr);
    assert!(
        trap_imb - ctl_imb <= TRAPS * PER_TRAP_TOLERANCE,
        "per-trap leak must be bounded: trap imbalance {trap_imb} vs control {ctl_imb} \
         (allowed delta {} = {TRAPS} traps x {PER_TRAP_TOLERANCE})",
        TRAPS * PER_TRAP_TOLERANCE
    );
}

// =============================================================================
// L-R2 — frozen-world vs late-binding (repl/spec.md §18.7, §18.2)
// =============================================================================

// spec: repl/spec.md §18.7 — by-name calls and recompiled callers see the new
// definitions after a signature-changing redefinition, coherently: no crash,
// no mixed-signature execution, sustained. Closest-reachable stage-M shape
// (see module header): `mint` is a pre-break-compiled closure factory; after
// the break the transaction recompiles it, so its minted closures live in the
// new world. Today its stale code is left aimed at the in-place-patched slot:
// `((mint) 1)` sends an Int into the new String body — SIGBUS. RED on HEAD.
//
// The direct frozen-world assertion (§18.7 requirement 1 — a PRE-BREAK VALUE
// sees old-chain behaviour) is not REPL-reachable at stage M; structural
// witness: tests/repl_persist_redefine.rs::persist_abi_change_allocates_fresh_slot_hole_survives_restart.
#[test]
fn redefine_abi_change_closure_minting_caller_rejoins_new_world_coherently() {
    let cap = repl_prims(
        "(defn base [:Int x] (add-i64 x 10))\n\
         (defn wrap [:Int y] (base y))\n\
         (defn mint [] (fn [z] (wrap z)))\n\
         ((mint) 1)\n\
         (defn base [:String s] (str-len s))\n\
         (defn wrap [:String s] (base s))\n\
         (wrap \"abcd\")\n\
         ((mint) \"abcd\")\n\
         (defn spin2 [:Int n :Int acc] (if (eq-i64 n 0) acc (spin2 (sub-i64 n 1) (add-i64 acc ((mint) \"ab\")))))\n\
         (spin2 400 0)\n\
         ((mint) 1)\n",
    )
    .assert_ok(); // no mixed-ABI crash, ever (today: SIGBUS on the last form)
    let cap = cap
        .assert_stdout_contains(":primitives/Int 11") // pre-break world
        .assert_stdout_contains(":primitives/Int 800"); // sustained post-break (S98-class fence)
    // By name AND through the recompiled factory: the new world (4 = str-len "abcd").
    assert!(
        count(&cap.stdout, ":primitives/Int 4") >= 2,
        "(wrap \"abcd\") and ((mint) \"abcd\") must both see the new world; stdout={}",
        cap.stdout
    );
    // The final ((mint) 1) must NOT silently produce the old-world 11 — by-name
    // routes never serve stale behaviour (§18.7; the sanctioned outcome is a
    // clean type error against the recompiled factory).
    assert_eq!(
        count(&cap.stdout, ":primitives/Int 11"),
        1,
        "post-break ((mint) 1) must not silently reproduce the old-chain result; stdout={}",
        cap.stdout
    );
}

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

// spec: repl/spec.md §18.3 — the cascade report names EXACTLY the affected
// set: recompiled callers (caller-p), broken callers with their reason
// (caller-a), and NOT unaffected functions (unrelated). Both worlds then
// behave: the recompiled caller works, the broken one traps. RED on HEAD.
#[test]
fn redefine_abi_change_cascade_report_names_exact_affected_set() {
    let cap = repl_prims(&format!(
        "{LR3_BASE}(defn callee [:String s] (str-len s))\n\
         (caller-p \"abcd\")\n\
         (caller-a 1)\n"
    ))
    .assert_ok();
    // Positive: the report names the recompiled and broken sets (§18.3).
    assert!(
        any_report_line_contains(&cap.stdout, "recompiled"),
        "ABI-changing edit must print a `recompiled:` section; stdout={}",
        cap.stdout
    );
    assert!(
        any_report_line_contains(&cap.stdout, "caller-p"),
        "the recompiled set must name caller-p; stdout={}",
        cap.stdout
    );
    assert!(
        any_report_line_contains(&cap.stdout, "broken"),
        "the report must carry a `broken:` section; stdout={}",
        cap.stdout
    );
    assert!(
        any_report_line_contains(&cap.stdout, "caller-a"),
        "the broken set must name caller-a; stdout={}",
        cap.stdout
    );
    // Negative (exactness): unaffected symbols never appear in report lines.
    assert!(
        !any_report_line_contains(&cap.stdout, "unrelated"),
        "the cascade report must NOT name `unrelated`; stdout={}",
        cap.stdout
    );
    // Both worlds live: recompiled caller works; broken caller traps.
    let cap = cap
        .assert_stdout_contains(":primitives/Int 4")
        .assert_stdout_contains("user/caller-a is broken by the redefinition of user/callee");
    drop(cap);
}

// =============================================================================
// L-R4 — the latent type-change hole cure (repl/spec.md §18.1) — the sprint's
// own RED witness (spine design/arch/ownership-inference.md §5.2)
// =============================================================================

// spec: repl/spec.md §18.1 — the coherence guarantee: a type-changing
// redefinition with a compiled annotated caller must trap-or-recompile; the
// caller MUST NOT reach the new body uncorrected. Today this is silently
// unsound (SIGBUS passing an Int where the new body expects a String
// pointer). RED on HEAD — the machinery sprint's named witness.
#[test]
fn type_change_redefinition_compiled_caller_never_reaches_new_body_uncorrected() {
    let cap = repl_prims(
        "(defn f [:Int x] (add-i64 x 1))\n\
         (defn g [:Int y] (f y))\n\
         (g 1)\n\
         (defn f [:String s] (str-len s))\n\
         (g 5)\n",
    )
    .assert_ok(); // soundness leg 1: the session survives
    let cap = cap
        .assert_stdout_contains(":primitives/Int 2") // pre-break sanity
        // Soundness leg 2: the old-typed call yields an error naming g (at
        // stage M the annotated caller cannot re-typecheck, so the sanctioned
        // outcome is BROKEN + trap with provenance).
        .assert_stdout_contains("user/g is broken by the redefinition of user/f")
        // Soundness leg 3: the new body is never reached with the old Int.
        .assert_stdout_does_not_contain(":primitives/Int 6");
    drop(cap);
}

// spec: repl/spec.md §18.3 — a POLYMORPHIC caller re-typechecks under the new
// signature and is recompiled: post-break calls at the new type succeed.
// Today the call is rejected against g's stale Int scheme. RED on HEAD.
#[test]
fn type_change_redefinition_polymorphic_caller_recompiles_and_works() {
    let cap = repl_prims(
        "(defn f [:Int x] (add-i64 x 1))\n\
         (defn g [y] (f y))\n\
         (g 1)\n\
         (defn f [:String s] (str-len s))\n\
         (g \"abcd\")\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 2") // pre-break sanity
    .assert_stdout_contains(":primitives/Int 4"); // recompiled g at the new type
    drop(cap);
}

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
fn redefine_concrete_to_polymorphic_caller_survives_coherent_stale() {
    let cap = repl_prims(
        "(defn f [x] (add-i64 x 1))\n\
         (defn g [y] (f y))\n\
         (g 1)\n\
         (defn f [x] x)\n\
         (g 5)\n",
    )
    .assert_ok() // the crash leg: no SIGSEGV / exit 139
    .assert_stdout_contains(":primitives/Int 2") // pre-break sanity
    // CURED: the reload recompiled `g` against the new identity `f` ⇒ g(5)=5.
    .assert_stdout_contains(":primitives/Int 5")
    // Nothing is stale after the recompile: the section is omitted.
    .assert_stdout_does_not_contain("; stale:");
    drop(cap);
}

// spec: repl/spec.md §18.1 — coherence guarantee; design/int/session-transaction.md
// §10 T1. SIBLING shape (FIXME 0478's named cheap sibling): concrete single-sig
// `f` redefined as a MULTI-SIG (Overloaded) defn — the staged entry is likewise
// slot-less, so the commit gate classifies T1 and the same displacement arm
// (0479) must retain the prior slotted Code. Probed 2026-07-03 post-0479:
// session survives; `(g 5)` runs the frozen old chain (6, not the new Int-arm's
// 5) — coherent-stale, same residue + flip note as the polymorphic sibling
// above: when the full T1 cure lands (S103 per the S102 ruling), the
// `:primitives/Int 6` pin MUST flip; the S102 A1 `stale:` print (§18.1.1) is
// additive and does not disturb this pin.
// S103 FLIPPED (2026-07-06, T1 full cure landed) — with a CORRECTION to the
// design's predicted value. The Phase-3 flip note predicted g(5)=5 (the Int
// arm), but the reloaded source `(defn g [y] (f y))` is GENUINELY AMBIGUOUS
// under an Overloaded `f`: nothing constrains `y` to Int, so g's recompile is a
// real "ambiguous type; add an annotation" error (identical to what `--run`
// would report for this file). The T1 module-grain reload therefore FAILS, and
// per CS-3 the turn degrades to the §14.4 error-blocked floor (never a lockout
// or crash) while keeping the informational `; stale:` print. This is the
// honest cured behaviour: the split world is surfaced, not silently answered
// (the former coherent-stale `6`). The design's "5" prediction is corrected via
// FIXME 0529 (target /design). Contrast the polymorphic sibling above, whose
// reload succeeds (identity `f` leaves `g` well-typed ⇒ g(5)=5).
#[test]
fn redefine_concrete_to_overloaded_caller_survives_coherent_stale() {
    let cap = repl_prims(
        "(defn f [x] (add-i64 x 1))\n\
         (defn g [y] (f y))\n\
         (g 1)\n\
         (defn f ([:Int x] x) ([:String s] (str-len s)))\n\
         (g 5)\n",
    )
    .assert_ok() // the crash leg: session survives (no SIGSEGV / exit 139)
    .assert_stdout_contains(":primitives/Int 2") // pre-break sanity
    // CURED: the reload fails (g ambiguous under overloaded f) ⇒ the §14.4
    // error-blocked floor; the split world is surfaced, never silently answered.
    .assert_stdout_contains("has errors")
    // The old coherent-stale answer is gone.
    .assert_stdout_does_not_contain(":primitives/Int 6");
    drop(cap);
}

// =============================================================================
// S101 Phase 6a/6b defect-set guards (/qa guard batch, 2026-07-03).
// Four §18 conformance defects surfaced by the 6a/6b proxy exercise, all
// deterministic, all RED-first-verified on the S101 change-set binary.
// Ledger: tests/plan/ledger.md §"Sprint 101 Phase 6a/6b defect set".
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

// spec: repl/spec.md §18.3 — the `broken:` set MUST be exact: it names the
// symbols the transaction broke and MUST NOT name any symbol that was not
// (an internal eval-wrapper is not a user symbol). RED on HEAD (FIXME 0491):
// after any expression turn, a signature-changing redefinition lists
// `__expr` in `broken:` alongside the real dependent.
#[test]
fn redefine_cascade_report_neg_no_internal_expr_wrapper_in_broken() {
    repl_prims(
        "(defn f [x] (add-i64 x 1))\n\
         (defn g [x] (f x))\n\
         (defn k [x] (f (mul-i64 x 2)))\n\
         (g 1)\n\
         (defn f [s] (str-len s))\n",
    )
    .assert_ok()
    .assert_stdout_contains("k —") // the real broken dependent is named…
    .assert_stdout_does_not_contain("__expr"); // …the internal wrapper never is
}

// spec: repl/spec.md §18.3 — empty sections are omitted: an all-green revert
// turn prints no `broken:` section at all. RED on HEAD (FIXME 0491, revert
// direction — the /repl 6b sharpening: the eval wrapper rejoins any later
// transaction where a symbol it called changes signature, reverts included,
// so the otherwise-all-green revert prints `; broken:` naming only `__expr`).
#[test]
fn redefine_revert_after_expression_turn_neg_no_wrapper_broken_section() {
    repl_prims(
        "(defn f [x] (add-i64 x 1))\n\
         (defn g [x] (f x))\n\
         (defn f [s] (str-len s))\n\
         (g \"hello\")\n\
         (defn f [x] (add-i64 x 1))\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 5") // the expression turn (new world)
    .assert_stdout_does_not_contain("__expr")
    // No user symbol breaks in this script, so per §18.3 no turn may print a
    // broken: section at all — today the revert turn prints one for __expr.
    .assert_stdout_does_not_contain("; broken:");
}

// spec: repl/spec.md §18.5 — the trap is presented through the standard §5.1
// runtime-error format: `runtime error: {broken} is broken by the
// redefinition of {cause}: {original error}`. RED on HEAD (no FIXME — this
// guard is the record; /repl 6a defect 2): the actual presentation wraps the
// message as `Error: codegen error at 0..0: runtime error: runtime panic:
// <msg>` — an internal-wrapper chain, a bogus 0..0 span, and a non-normative
// `runtime panic:` prefix between the category and the message.
#[test]
fn trap_presented_in_normative_runtime_error_format() {
    repl_prims(&format!("{LR1_BASE}(g 5)\n"))
        .assert_ok()
        // The §18.5 normative juxtaposition: category prefix directly
        // followed by the trap message.
        .assert_stdout_contains("runtime error: user/g is broken by the redefinition of user/f")
        // The observed wrapper chain MUST NOT appear.
        .assert_stdout_does_not_contain("runtime panic:")
        .assert_stdout_does_not_contain("codegen error at 0..0");
}

// spec: repl/spec.md §18.4 — `/sig` on a broken symbol MUST show the SAME
// primary line as bare lookup (fully-qualified types, fully-qualified name,
// per §1.4). RED on HEAD (FIXME 0492): `/sig g` renders `:(Fn [Int] Int) g ;
// defn` while bare `g` renders `:(Fn [primitives/Int] primitives/Int) user/g
// ; defn` — only the provenance comment line matches. The count-based
// assertion requires the FQ primary line from BOTH surfaces. NOTE: 0492 asks
// /repl to arbitrate spec-vs-impl; if §18.4/§3.1 are amended to pin the short
// form instead, update the expected values here.
#[test]
fn sig_broken_symbol_primary_line_matches_bare_lookup_fully_qualified() {
    let cap = repl_prims(&format!("{LR1_BASE}/sig g\ng\n"));
    let cap = cap.assert_ok();
    // Occurrence accounting: g's §1.3 defn-turn confirmation emits the FQ
    // primary line once; bare lookup emits it once; /sig MUST emit the same
    // line — so a conforming session shows it 3 times. Today /sig renders the
    // short form `:(Fn [Int] Int) g ; defn` and the count is 2.
    let fq_primary = count(&cap.stdout, ":(Fn [primitives/Int] primitives/Int) user/g ; defn");
    assert!(
        fq_primary >= 3,
        "/sig and bare lookup MUST render the same fully-qualified primary \
         line for a broken symbol (§18.4); expected the FQ line ≥3 times \
         (defn echo + /sig + bare lookup), got {fq_primary} (FIXME 0492); stdout:\n{}",
        cap.stdout
    );
    drop(cap);
}

// spec: repl/spec.md §18.4 — `/info` on a broken symbol MUST include the
// definition source. A prior bare lookup of the broken symbol MUST NOT
// replace that source with the lookup text. RED on HEAD (FIXME 0486, broken
// arm): after bare `k`, `/info k` renders the source line as `  k` instead of
// the `(defn k …)` form (the healthy-arm sibling lives in
// tests/repl_introspection.rs).
#[test]
fn bare_lookup_broken_symbol_info_still_shows_definition_source() {
    repl_prims(
        "(defn f [:Int x] (add-i64 x 1))\n\
         (defn k [:Int y] (f y))\n\
         (defn f [:String s] (str-len s))\n\
         k\n\
         /info k\n",
    )
    .assert_ok()
    .assert_stdout_contains("broken by the redefinition of user/f") // §18.4 provenance intact
    .assert_stdout_contains("(defn k [:Int y] (f y))"); // the definition source (the defect)
}

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

// spec: repl/spec.md §18.1.1 — the downgrade report, S103 FLIPPED (2026-07-06,
// T1 full cure landed). The S102 interim PRINT is replaced by the end-of-turn
// reload: the previously-stale compiled caller `gcall` is now RECOMPILED, so
// the `; stale:` section is OMITTED (nothing is stale) and the post-turn
// `(gcall 1)` observes the NEW `id` (102, not the old 2). The exactness
// negatives still hold: `bystander` (never-compiled template) is untouched,
// `unrelated` (no edge) is unaffected, `newcomer` (defined after) sees the new
// `id` too (101). This is the Principle-8 kept-machinery pin viewed from the
// report side — the same TransactionReport `stale:` channel, rendered empty.
#[test]
fn t1_downgrade_report_names_stale_compiled_callers_exactly() {
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
    // CURED: nothing is stale after the recompile — the section is omitted.
    .assert_stdout_does_not_contain("; stale:");
    // The previously-stale caller is recompiled: the post-turn `(gcall 1)` now
    // sees the new `id` ⇒ id(2)=102, and the pre-turn call printed 2 exactly
    // once (no coherent-stale second answer).
    assert_eq!(
        count(&cap.stdout, ":primitives/Int 2"),
        1,
        "only the PRE-downgrade gcall prints 2; the post-turn call is \
         recompiled (102), not coherent-stale; stdout={}",
        cap.stdout
    );
    let cap = cap.assert_stdout_contains(":primitives/Int 102");
    // A caller compiled after the turn also sees the new definition.
    let cap = cap.assert_stdout_contains(":primitives/Int 101");
    drop(cap);
}

// spec: repl/spec.md §18.1.1 — negative leg of the A1 acceptance pair: a
// NON-downgrade body-only redefinition MUST NOT print the `stale:` section
// (no over-triggering — §18.2 body-only turns print only the §1.3
// confirmation). GREEN at draft (vacuously — no report machinery exists);
// load-bearing the moment the A1 print lands.
#[test]
fn t1_downgrade_report_neg_body_only_turn_prints_no_stale_section() {
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

// spec: repl/spec.md §18.1.1 — the section is omitted entirely when nothing
// is stale: a downgraded (T1) redefinition with NO compiled caller left
// behind prints only the §1.3 confirmation. GREEN at draft (vacuously);
// load-bearing with the A1 print — guards the empty-set omission rule.
#[test]
fn t1_downgrade_report_neg_omitted_when_no_compiled_caller() {
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
fn redefine_unannotated_generic_target_caller_keeps_old_chain_sibling() {
    let cap = repl_prims(
        "(defn f [x] x)\n\
         (defn g [y] (f (add-i64 y 1)))\n\
         (g 1)\n\
         (defn f [x] (add-i64 x 50))\n\
         (g 1)\n",
    )
    .assert_ok() // the session never dies on the default path
    .assert_stdout_contains(":primitives/Int 2") // pre-downgrade (old identity)
    // CURED: the reload recompiled `g` against the new `f` ⇒ f(2)=52.
    .assert_stdout_contains(":primitives/Int 52");
    let cap = cap.assert_stdout_does_not_contain("is broken by the redefinition");
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
fn redefine_unannotated_caller_reentry_rejoins_new_world_sibling() {
    let cap = repl_prims(
        "(defn f [x] x)\n\
         (defn g [y] (f (add-i64 y 1)))\n\
         (g 1)\n\
         (defn f [x] (add-i64 x 50))\n\
         (defn g [y] (f (add-i64 y 1)))\n\
         (g 1)\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 2") // pre-downgrade world
    .assert_stdout_contains(":primitives/Int 52"); // re-entered caller: new world
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
fn redefine_unannotated_split_world_old_and_new_callers_coexist_sibling() {
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
    .assert_stdout_contains(":primitives/Int 51"); // h: the new world
    // g's post-downgrade call still answers through the old chain: both
    // (g 1) turns print 1 (pre-break sanity + coherent-stale).
    assert_eq!(
        count(&cap.stdout, ":primitives/Int 1\n"),
        2,
        "the pre-downgrade caller keeps the old chain while the new caller \
         sees the new definition (T1 split world, §18.1 scope note); stdout={}",
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

// spec: repl/spec.md §18.1.1 — the T1 full-cure positive acceptance: after a
// downgrading (unannotated, generalizing) redefinition, the end-of-turn
// transaction RECOMPILES the stale compiled callers, so the `stale:` section is
// OMITTED entirely AND a previously-stale caller called after the turn observes
// the NEW definition. RED at draft: today `gcall` keeps the old chain, so the
// post-turn `(gcall 1)` prints 2 (old `id x = x` ⇒ id(2)=2), not the cured 102
// (new `id x = add-i64 x 100` ⇒ id(2)=102). Flips when the cure lands.
#[test]
fn t1_full_cure_recompiles_stale_callers_stale_section_empty() {
    let cap = repl_prims(
        "(defn id [x] x)\n\
         (defn gcall [x] (id (add-i64 x 1)))\n\
         (gcall 1)\n\
         (defn id [x] (add-i64 x 100))\n\
         (gcall 1)\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 2"); // pre-downgrade world (old id)
    // Positive: the previously-stale caller, recompiled by the end-of-turn
    // transaction, now sees the new `id` — id(2) = 102. RED until the cure.
    let cap = cap.assert_stdout_contains(":primitives/Int 102");
    // The `stale:` section is omitted (nothing is stale after the recompile) —
    // the Principle-8 same-section-rendered-empty shape, NOT a printed stale set.
    let cap = cap.assert_stdout_does_not_contain("; stale:");
    drop(cap);
}

// spec: repl/spec.md §18.1.1 — the T1 full-cure negative (over-trigger) pin: a
// BODY-ONLY edit (same signature) must NOT trigger a reload — it prints only the
// §1.3 confirmation + late-binds the new body via the GOT (§18.2), with no
// `stale:`/`recompiled:`/`broken:` section. Guards the cure against recompiling
// the world on every turn. GREEN at draft (vacuously — no reload machinery);
// load-bearing the moment the cure's end-of-turn transaction lands.
#[test]
fn t1_full_cure_body_only_edit_still_no_report_no_recompile() {
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

// spec: repl/spec.md §18.3 — the cascade report MUST NOT name any internal
// artifact: a `__macro_{name}_clause_{idx}` caller renders as its owning user
// macro `{name}`, never the raw clause symbol. S103 Wave-4 /review FINDING 1
// (a leak this wave newly enabled): narrowing the reverse-index feed exclusion
// to `__expr`-only lets a macro clause join `affected_closure`; a CONCRETE dep
// fn redefined AbiChanging with a cross-module macro-clause caller routes the
// clause through T2 (no standalone sexp), and the report-push sites must fold
// the name. RED before the fix: the `broken:` line read
// `mac/__macro_wrap_clause_0`; GREEN after: `mac/wrap`.
//
// Setup: `helper/bump` is a concrete `Sexp -> Sexp` fn; `mac/wrap`'s clause
// calls `bump` (a legal cross-module §9.3.4 reference); `(wrap 41)` compiles
// the clause + records its callee edge to `bump`. Redefining `bump` to
// `SList -> Sexp` (AbiChanging) fires the transaction, whose closure now
// includes the clause; the clause has no introspection sexp → T2 module-grain
// → the clause's module reload fails the new type → `broken:` names the macro.
#[test]
fn redefine_cascade_report_neg_macro_clause_caller_folds_to_owning_macro() {
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
             /quit\n",
        )
        .output();
    // NB: no `assert_ok` — the redefinition GENUINELY breaks the macro clause
    // (its body now type-mismatches the new `bump`), so the `mac` module ends
    // the session in a legitimate error state (exit 1 at shutdown). That is the
    // correct outcome; this test pins the REPORT NAME, not the exit code.
    let cap = cap
        // The transaction reached the macro clause and reported it…
        .assert_stdout_contains("; broken:")
        // …as its owning user macro (base-folded, §18.3)…
        .assert_stdout_contains("mac/wrap")
        // …never the raw internal clause symbol (the class guard also sweeps
        // `__expr`/`__macro_`/debug-format leaks).
        .assert_no_internal_artifacts();
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
fn t1_reload_failure_error_block_lifts_on_caller_repair() {
    let cap = repl_prims(
        "(defn id [x] x)\n\
         (defn g [:Int y] (id (add-i64 y 1)))\n\
         (g 1)\n\
         (defn id [:String s] (str-len s))\n\
         (g 5)\n\
         (defn g [:Int y] (add-i64 y 100))\n\
         (g 5)\n",
    )
    .assert_ok() // exits cleanly — never a lockout or session exit
    .assert_stdout_contains(":primitives/Int 2") // pre-downgrade sanity
    // The downgrade turn's reload fails (g: Int vs the new String id) ⇒ the
    // §14.4 block refuses the next expression…
    .assert_stdout_contains("has errors");
    // …then the re-definition of `g` LIFTS the block and `g` runs again
    // (g(5) = 105). If the block never lifted (the Option-B lockout bug — an
    // `error_modules` entry with no draining `failed_forms`), this 105 would
    // never appear.
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

// spec: repl/spec.md §18.1.1 — a redefinition that late-binds through a caller
// produces the corrected result under every preamble (the cascade/late-binding
// report is invariant to session history — 0491 cascade surface generalized).
#[test]
fn ls1_redefinition_cascade_result_invariant_to_session_history() {
    assert_preamble_invariant(
        "(defn base [:Int x] (add-i64 x 1))\n\
         (defn caller [:Int x] (base x))\n\
         (caller 10)\n\
         (defn base [:Int x] (add-i64 x 100))\n\
         (caller 10)\n",
        ":primitives/Int 110",
    );
}

// spec: repl/spec.md §18.1.1 — +neg: the redefinition report/surface MUST NOT leak
// the synthetic `__expr` internal name regardless of session history (the 0491
// cascade-report artifact-leak class).
#[test]
fn ls1_redefinition_no_expr_noise_neg() {
    assert_preamble_invariant_absent(
        "(defn base [:Int x] (add-i64 x 1))\n\
         (defn caller [:Int x] (base x))\n\
         (caller 10)\n\
         (defn base [:Int x] (add-i64 x 100))\n\
         (caller 10)\n",
        "__expr",
    );
}
