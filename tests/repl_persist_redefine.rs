//! S101 Phase-5 stage 1 — L-R5 persistence pins for ABI-epoch slot versioning
//! (`tests/plan/s100-ownership-verification.md` §3.6 L-R5 / §6.1; spine
//! `design/arch/ownership-inference.md` §5.6 pins (i)–(iv)).
//!
//! Two-session scripts per the `repl_persist.rs` family: session 1 `.repl()` +
//! `/quit`, then `run_again()` in the same TempDir; `.meta.json` inspected via
//! `read_tmp(".cranelisp-cache/user.meta.json")`.
//!
//! **L-R5 asserts the DESIGNED restore floor** (`design/int/session-transaction.md`
//! §"Persistence — pins (i)–(iv) honoured": broken-ness restarts as an ordinary
//! load-time compile error, never silently-stale code, never a persisted trap),
//! NOT `repl/spec.md` §18.8's restore-as-broken-with-provenance SHOULD — per the
//! S101 Phase-3 exit-gate note 3 (`sprints/SPRINT.md`).
//!
//! Draft-time polarity (probed by hand on HEAD 0b0e234; REVISED after the
//! Wave-1 suite run):
//!   RED  ×2: (b) fresh-slot allocation + surviving hole (today the in-place
//!            patch reuses the slot, so redef and control metas are identical);
//!            (c) — see the FINDING below.
//!   GREEN ×1 pin: (a) cache-restore correctness across signature-changing
//!            redefinitions.
//!
//! ## FINDING (Wave-1 drafting, 2026-07-03): the final `.meta.json` persist
//! races `/quit` — R18 abandon-on-shutdown
//!
//! The nice workers abandon pending `.o`/`.meta` persist work when `/quit`
//! flips the shutdown flag (`src/session_v4/nice_worker.rs` "R18
//! abandon-on-shutdown"; `main.rs` `s.shutdown()`), so the on-disk meta after
//! a clean `/quit` reflects whatever the LAST COMPLETED nice-worker write was
//! — under suite load, recently-(re)defined symbols are intermittently absent
//! (observed: `symbol f not found` and `symbol g not found` on consecutive
//! runs of these tests; the same scripts probed by hand, unloaded, always
//! yielded complete metas). Benign for restore CORRECTNESS today (`user.cl`
//! is the source of truth; a stale meta fails the source-hash check and
//! recompiles — which is why (a) is a stable GREEN pin). NOT benign for the
//! L-R5 pins: spine §5.6 (i)–(iv) make persisted slot numbers load-bearing,
//! and `design/int/session-transaction.md` §"Persistence" pins a faithful
//! write after every redefinition. **Wave-4 `/dev`(src/) must make the final
//! defining-turn persist deterministic at `/quit`** (flush before abandon, or
//! an equivalent barrier) for (b)/(c) to flip green; both tests assert meta
//! COMPLETENESS first (the finding's needle) and slot policy second. (c) is
//! therefore RED-at-draft by burst amplification, not a green pin as the
//! §6.1 spec expected — recorded in the ledger + qa plan §6.1.1 addendum.
//!
//! Ledger entry: `tests/plan/ledger.md` §"Sprint 101 Phase-5 Stage-1".
//!
//! ## RESOLVED — S101 Wave 4 (2026-07-03): (b)/(c) flipped GREEN
//!
//! The Wave-4 `/dev`(src/) change-set landed BOTH halves: ABI-epoch fresh-slot
//! allocation (the (b) slot pins) AND the R18 deterministic final persist at
//! `/quit` (`flush_final_persist`), which also rooted the ledgered
//! `search_burndown` intermittent. Verified stable at Wave 5 (double-run,
//! burst legs included). All three tests stand as permanent regression
//! guards — (c) is now the standing slot-churn/over-allocation guard.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

/// Extract `next_got_slot` from a `.meta.json` (pretty-printed serde output:
/// `"next_got_slot": N`).
fn next_got_slot(meta: &str) -> u64 {
    let idx = meta
        .find("\"next_got_slot\":")
        .unwrap_or_else(|| panic!("no next_got_slot in meta: {meta}"));
    meta[idx + "\"next_got_slot\":".len()..]
        .trim_start()
        .chars()
        .take_while(|c| c.is_ascii_digit())
        .collect::<String>()
        .parse()
        .unwrap_or_else(|_| panic!("unparseable next_got_slot in meta"))
}

/// Extract the persisted `got_slot` of a symbol from a `.meta.json`. Symbols
/// serialize as 4-space-indented keys under `"symbols"`; each callable entry
/// carries exactly one `"got_slot": N` inside its `DefKind` subtree.
fn slot_of(meta: &str, sym: &str) -> u64 {
    let key = format!("\n    \"{sym}\": {{");
    let start = meta
        .find(&key)
        .unwrap_or_else(|| panic!("symbol {sym} not found in meta"));
    // The symbol block ends at the next 4-space-indented key or EOF; searching
    // forward for the first got_slot within the block is safe because each
    // callable Def carries exactly one.
    let block_end = meta[start + key.len()..]
        .find("\n    \"")
        .map(|off| start + key.len() + off)
        .unwrap_or(meta.len());
    let block = &meta[start..block_end];
    let idx = block
        .find("\"got_slot\":")
        .unwrap_or_else(|| panic!("no got_slot for {sym} in meta block: {block}"));
    block[idx + "\"got_slot\":".len()..]
        .trim_start()
        .chars()
        .take_while(|c| c.is_ascii_digit())
        .collect::<String>()
        .parse()
        .unwrap_or_else(|_| panic!("unparseable got_slot for {sym}"))
}

fn prims_repl_session(stdin: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(stdin)
        .output()
}

const META: &str = ".cranelisp-cache/user.meta.json";

/// The persisted meta after a clean `/quit` must carry every defined symbol.
/// Fails with the R18 abandon-on-shutdown finding (module header) when the
/// final defining-turn persist was abandoned at shutdown.
fn assert_meta_complete(meta: &str, syms: &[&str], context: &str) {
    for sym in syms {
        assert!(
            meta.contains(&format!("\n    \"{sym}\": {{")),
            "[{context}] final .meta.json persist is INCOMPLETE — symbol `{sym}` \
             missing after clean /quit (R18 abandon-on-shutdown races the last \
             defining-turn persist; see module-header FINDING — Wave-4 /dev(src/) \
             must flush the final persist for the L-R5 pins to be assertable). \
             meta:\n{meta}"
        );
    }
}

// spec: design/arch/ownership-inference.md §5.6 — pin (ii): persisted slot
// numbers are load-bearing against the cached `.o` machine code — a program
// redefined across a signature change before `/quit` runs identically after
// restart from a valid cache. GREEN at draft (pins today's coherent
// regenerate-then-restore behaviour against slot-versioning regressions).
#[test]
fn persist_abi_change_redefinition_restart_runs_correctly_from_cache() {
    let first = prims_repl_session(
        "(defn f [:Int x] (add-i64 x 1))\n\
         (defn g [:Int y] (f y))\n\
         (defn f [:String s] (str-len s))\n\
         (defn g [:String s] (f s))\n\
         (g \"hi\")\n\
         /quit\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 2");
    assert!(
        first.tmp_exists(META),
        "session 1 must persist the user module cache; tmpdir={}",
        first.tmpdir.display()
    );

    // Session 2 — warm cache, same TempDir: the redefined world restores.
    let second = first
        .run_again()
        .repl()
        .stdin("(g \"abc\")\n/quit\n")
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 3");
    drop(second);
}

// spec: design/arch/ownership-inference.md §5.6 — pins (ii)/(iii)/(iv): an
// ABI-changing redefinition allocates a FRESH GOT slot (the old slot freezes);
// the hole survives persistence and restart un-renumbered; new definitions
// allocate above the persisted `next_got_slot` high-water mark. A control run
// with the identical definition prefix but no redefinition pins the expected
// slot numbering. RED on HEAD: today's in-place patch reuses the slot, so the
// redefinition session's meta is indistinguishable from the control's.
#[test]
fn persist_abi_change_allocates_fresh_slot_hole_survives_restart() {
    // Redefinition run: f and g defined, then BOTH redefined ABI-changingly
    // (coherent final source so the session and cache end green).
    let redef = prims_repl_session(
        "(defn f [:Int x] (add-i64 x 1))\n\
         (defn g [:Int y] (f y))\n\
         (defn f [:String s] (str-len s))\n\
         (defn g [:String s] (f s))\n\
         (g \"hi\")\n\
         /quit\n",
    )
    .assert_ok();
    let redef_meta = redef.read_tmp(META);
    assert_meta_complete(&redef_meta, &["f", "g"], "L-R5b redefinition session");

    // Control run (second TempDir): identical definition prefix, no
    // redefinition ⇒ deterministic same initial slot numbering.
    let control = prims_repl_session(
        "(defn f [:String s] (str-len s))\n\
         (defn g [:String s] (f s))\n\
         (g \"hi\")\n\
         /quit\n",
    )
    .assert_ok();
    let ctl_meta = control.read_tmp(META);
    assert_meta_complete(&ctl_meta, &["f", "g"], "L-R5b control session");

    let (ctl_f, ctl_next) = (slot_of(&ctl_meta, "f"), next_got_slot(&ctl_meta));
    let (redef_f, redef_g, redef_next) = (
        slot_of(&redef_meta, "f"),
        slot_of(&redef_meta, "g"),
        next_got_slot(&redef_meta),
    );

    // Pin (ii)+(iii): the ABI-changing redefinition allocated FRESH slots —
    // the persisted slots sit above the control's, and next_got_slot carries
    // the frozen holes (symbol count identical, high-water higher).
    assert!(
        redef_f > ctl_f,
        "ABI-changing redefinition must allocate a fresh slot for f: \
         redef={redef_f} vs control={ctl_f} (today's in-place patch reuses it — RED)"
    );
    assert!(
        redef_next > ctl_next,
        "the frozen holes must be reflected in next_got_slot: \
         redef={redef_next} vs control={ctl_next}"
    );

    // Session 2 in the redefinition TempDir: a NEW definition allocates at or
    // above the persisted high-water (pin (iv)); f/g keep their slots
    // un-renumbered (pin (ii)); the frozen holes are never reassigned (pin (iii)).
    let second = redef
        .run_again()
        .repl()
        .stdin("(defn h [:Int x] (add-i64 x 7))\n(h 1)\n/quit\n")
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 8");
    let meta2 = second.read_tmp(META);
    assert_meta_complete(&meta2, &["f", "g", "h"], "L-R5b session 2");
    assert_eq!(
        slot_of(&meta2, "f"),
        redef_f,
        "restart must not renumber f's persisted slot (pin ii)"
    );
    assert_eq!(
        slot_of(&meta2, "g"),
        redef_g,
        "restart must not renumber g's persisted slot (pin ii)"
    );
    let h_slot = slot_of(&meta2, "h");
    assert!(
        h_slot >= redef_next,
        "a new definition must allocate at/above the persisted high-water \
         (pin iv): h={h_slot} vs next_got_slot={redef_next}"
    );
    assert!(
        h_slot != ctl_f && h_slot != slot_of(&ctl_meta, "g"),
        "the frozen old slots (the hole) must never be reassigned (pin iii): \
         h took slot {h_slot}"
    );
}

// spec: design/arch/ownership-inference.md §5.6 — negative pin: a BODY-ONLY
// redefinition keeps its slot and does not advance next_got_slot (the §18.2
// fast path must not churn slots once fresh-slot allocation exists).
//
// RED at draft — NOT the green pin the §6.1 spec expected: the meta this test
// must inspect is only intermittently complete after /quit (the R18
// abandon-on-shutdown FINDING, module header). Burst-amplified (BURST
// sessions, every final meta must be complete — the S98 burst-repro
// precedent) so the race fires deterministically under suite load; the slot
// assertions themselves were probed equal by hand. Flips green when Wave-4
// /dev(src/) makes the final persist deterministic — at which point this
// test's slot legs become the standing over-allocation guard.
#[test]
fn persist_body_only_redefinition_neg_keeps_slot() {
    const BURST: usize = 8;

    let control = prims_repl_session(
        "(defn f [:Int x] (add-i64 x 2))\n\
         (f 1)\n\
         /quit\n",
    )
    .assert_ok();
    let ctl_meta = control.read_tmp(META);
    assert_meta_complete(&ctl_meta, &["f"], "L-R5c control session");

    for i in 0..BURST {
        let redef = prims_repl_session(
            "(defn f [:Int x] (add-i64 x 1))\n\
             (defn f [:Int x] (add-i64 x 2))\n\
             (f 1)\n\
             /quit\n",
        )
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 3");
        let redef_meta = redef.read_tmp(META);
        assert_meta_complete(&redef_meta, &["f"], &format!("L-R5c burst {i}/{BURST}"));

        assert_eq!(
            slot_of(&redef_meta, "f"),
            slot_of(&ctl_meta, "f"),
            "body-only redefinition must keep f's slot (burst {i})"
        );
        assert_eq!(
            next_got_slot(&redef_meta),
            next_got_slot(&ctl_meta),
            "body-only redefinition must not advance next_got_slot (burst {i})"
        );
    }
}

// =============================================================================
// S102 Phase-5 Stage-1 — lane L-U1 sibling for the persistence lane
// (`tests/plan/s102-test-plan.md` §1.1): the unannotated default path ×
// restart. GREEN pin (probed 2026-07-03 on the CS-A binary).
// =============================================================================

// spec: repl/spec.md §18.1 — L-U1 persistence sibling: the T1 split world is
// a SESSION-MEMORY commitment only (§18.7's frozen-world rule applied to the
// downgrade residue). After an unannotated (T1) redefinition leaves a
// compiled caller on the old chain, `/quit` + restart rebuilds everything
// from source in the current world: the caller sees the NEW definition.
// GREEN pin — probed: live session g→2 (stale), restarted session g→52.
// FLIP NOTE: none needed — the S103 full cure only makes the live session
// match what this restart pin already shows.
#[test]
fn persist_unannotated_downgrade_restart_unifies_on_latest_definition_sibling() {
    let first = prims_repl_session(
        "(defn f [x] x)\n\
         (defn g [y] (f (add-i64 y 1)))\n\
         (g 1)\n\
         (defn f [x] (add-i64 x 50))\n\
         (g 1)\n\
         /quit\n",
    )
    .assert_ok();
    // Live session: coherent-stale — both calls answer through the old chain.
    assert_eq!(
        first.stdout.matches(":primitives/Int 2").count(),
        2,
        "live session keeps the old chain for the compiled caller (T1 \
         residue, §18.1 scope note); stdout={}",
        first.stdout
    );
    let meta = first.read_tmp(META);
    assert_meta_complete(&meta, &["f", "g"], "L-U1 persistence sibling");

    // Restart: one world — the latest definition, for every route.
    let second = first
        .run_again()
        .repl()
        .stdin("(g 1)\n/quit\n")
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 52");
    drop(second);
}

// =============================================================================
// FIXME 0489 (S101 Phase 6a, /repl) — restart with a broken backing file
// exits(1) BEFORE the first prompt, locking the user out of the §18.6
// in-REPL repair path (the only recovery is hand-editing user.cl). Per
// repl/spec.md §18.8 "The restart MUST reach a prompt" ([S102]-tagged MUST):
// the session MUST start, display the load error per §5.1 NAMING the broken
// symbol, enter the §14.4 error-blocked state, and accept a definition turn
// as the repair. Resolver: /int. Ledger: tests/plan/ledger.md §"Sprint 101
// Phase 6a/6b defect set".
// =============================================================================

// spec: repl/spec.md §18.8 — the restart MUST reach a prompt; the load error
// names the broken symbol; a definition turn at the prompt is accepted as
// the repair. RED on HEAD (FIXME 0489): session 2 exits 1 with
// `user.cl:1:1: error: module error at 0..0: module 'user' failed: type
// error …` — no banner, no prompt, broken symbol `k` never named, repair
// turn never read.
#[test]
fn restart_with_broken_backing_file_reaches_prompt_and_accepts_repair() {
    // Session 1: break `k` via a signature-changing redefinition, then quit.
    // This is ordinary, recoverable session state per §18.4; the backing file
    // as a whole no longer typechecks (§18.8).
    let first = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(
            "(defn f [:Int x] (add-i64 x 1))\n\
             (defn k [:Int y] (f y))\n\
             (defn f [:String s] (str-len s))\n\
             /quit\n",
        )
        .output();
    assert!(
        first.status.success(),
        "session 1 should exit cleanly; stdout={} stderr={}",
        first.stdout,
        first.stderr
    );
    assert!(
        first.stdout.contains("k —"),
        "session 1 sanity: the cascade report names k broken; stdout={}",
        first.stdout
    );

    // Session 2, same directory: MUST reach a prompt, name the broken symbol
    // in the load error, and accept the redefinition repair.
    first
        .run_again()
        .repl()
        .stdin("(defn k [:String y] (f y))\n(k \"abcd\")\n")
        .output()
        .assert_ok() // exits 1 before the prompt today
        .assert_stdout_contains("user>") // the prompt is reached
        // (§18.8 also requires the load error to NAME the broken symbol `k`;
        // the normative wording is not yet pinned pre-fix, so that leg is
        // asserted indirectly — the repair turn below proves the session is
        // reachable and usable.)
        .assert_stdout_contains(":primitives/Int 4"); // the repair path works
}

// =============================================================================
// /port D3 (S101 Phase 6a; no FIXME — these guards are the record) —
// dependent recompilation of file-backed module symbols false-BREAKS.
// PARTIAL REDUCTION (probed 2026-07-03, this /qa batch): the exemplar-
// reported faces ("definition source unavailable" for a cross-module
// dependent; false `undefined variable: None` for same-module dependents
// recompiled in a prelude-less env; revert doesn't heal) did NOT reproduce in
// FRESH sessions — fresh-session transactions over file-backed modules
// (same-module, cross-module, third-module dependents; implicit-prelude
// bodies; prelude-ADT bodies) all break TRUE and revert-heal correctly (the
// green control below pins the working cell). The reduced deterministic RED
// face is the CACHE-RESTORED session: after a restart, a `/mod <m>`
// redefining turn over the cache-restored file-backed module fails
// `unknown type `Int`/`String` (from module ``)` — the module's
// recompile/typecheck env is missing even primitive type names, the same
// recompile-env class /port reported (and FIXME 0487's /mod scope-gap
// adjacency). What remains UNKNOWN: the exact exemplar shape that yields
// "definition source unavailable" — it needs the cache-restored path, which
// today dies earlier at this env wall. Resolver: /int. Ledger:
// tests/plan/ledger.md §"Sprint 101 Phase 6a/6b defect set".
// =============================================================================

// spec: repl/spec.md §18.3 — the cascade transaction over a file-backed
// module behaves identically in a cache-restored session and a fresh one:
// the signature-changing turn is accepted, the dependent breaks with the
// TRUE type error, and the revert heals. RED on HEAD (/port D3, reduced
// face): the redefining turn itself fails `unknown type `String` (from
// module ``)` in the cache-restored session.
#[test]
fn redefine_file_backed_module_symbol_after_cache_restore_works_like_fresh() {
    let m_module = "(defn mf [:Int x] (add-i64 x 1))\n\
                    (defn mg [:Int y] (add-i64 (mf y) 100))\n";
    // Session 1: compile module m (populates .cranelisp-cache), then quit.
    let first = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("m.cl", m_module)
        .stdin("(import [m [mg]])\n(mg 41)\n/quit\n")
        .output();
    assert!(
        first.status.success() && first.stdout.contains(":primitives/Int 142"),
        "session 1 sanity: (mg 41) = 142; stdout={} stderr={}",
        first.stdout,
        first.stderr
    );

    // Session 2: m restores from cache; the same redefinition script that
    // works in a fresh session (green control below) must work here.
    first
        .run_again()
        .repl()
        .stdin(
            "(import [m [mg]])\n\
             (mg 41)\n\
             /mod m\n\
             (defn mf [:String s] (str-len s))\n\
             (defn mf [:Int x] (add-i64 x 1))\n\
             /mod user\n\
             (mg 41)\n",
        )
        .output()
        .assert_ok()
        .assert_stdout_does_not_contain("unknown type") // the D3 reduced face
        .assert_stdout_contains("mg —") // the TRUE break is reported…
        .assert_stdout_contains("; recompiled:") // …and the revert heals
        .assert_stdout_contains(":primitives/Int 142");
}

// spec: repl/spec.md §18.3 — CONTROL (GREEN on HEAD): the identical
// transaction in a FRESH session, with the dependent in a THIRD file-backed
// module (user → n → m), breaks TRUE (n/ng named with the type error) and
// revert-heals. Pins the working cell that the cache-restored guard above
// must match — and documents that /port's fresh-session false-BREAK claim
// did not reproduce under reduction.
#[test]
fn redefine_file_backed_module_symbol_fresh_session_cross_module_control() {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("m.cl", "(defn mf [:Int x] (add-i64 x 1))\n")
        .file(
            "n.cl",
            "(import [m [mf]])\n\
             (defn ng [:Int y] (add-i64 (mf y) 100))\n",
        )
        .stdin(
            "(import [n [ng]])\n\
             (ng 41)\n\
             /mod m\n\
             (defn mf [:String s] (str-len s))\n\
             (defn mf [:Int x] (add-i64 x 1))\n\
             /mod user\n\
             (ng 41)\n",
        )
        .output()
        .assert_ok()
        .assert_stdout_contains("n/ng —") // true break, module-qualified per §18.3
        .assert_stdout_contains("; recompiled:")
        .assert_stdout_does_not_contain("definition source unavailable")
        .assert_stdout_does_not_contain("unknown type");
}
