//! Persistence evidence for live redefinition. These tests distinguish an
//! accepted replacement from one rejected before publication and verify that
//! restart reconstructs the last coherent source.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

/// Extract the persisted callable `slot` of a symbol from a `.meta.json`. Symbols
/// serialize as 4-space-indented keys under `"symbols"`; each callable entry
/// carries exactly one `"slot": N` inside its concrete lifecycle state.
fn slot_of(meta: &str, sym: &str) -> u64 {
    let key = format!("\n    \"{sym}\": {{");
    let start = meta
        .find(&key)
        .unwrap_or_else(|| panic!("symbol {sym} not found in meta"));
    // The symbol block ends at the next 4-space-indented key or EOF; searching
    // forward for the first slot within the block is safe because each
    // callable Def carries exactly one.
    let block_end = meta[start + key.len()..]
        .find("\n    \"")
        .map(|off| start + key.len() + off)
        .unwrap_or(meta.len());
    let block = &meta[start..block_end];
    let idx = block
        .find("\"slot\":")
        .unwrap_or_else(|| panic!("no slot for {sym} in meta block: {block}"));
    block[idx + "\"slot\":".len()..]
        .trim_start()
        .chars()
        .take_while(|c| c.is_ascii_digit())
        .collect::<String>()
        .parse()
        .unwrap_or_else(|_| panic!("unparseable slot for {sym}"))
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
         (f 1)\n\
         (defn f [:String s] (str-len s))\n\
         (f \"hi\")\n\
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
        .stdin("(f \"abc\")\n/quit\n")
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 3");
    drop(second);
}

// spec: repl/spec/18-redefinition.md §18.1, §18.8 — a body-only replacement
// preserves its callable identity across persistence.
#[test]
fn persist_body_only_redefinition_neg_keeps_slot() {
    let control = prims_repl_session(
        "(defn f [:Int x] (add-i64 x 2))\n\
         (f 1)\n\
         /quit\n",
    )
    .assert_ok();
    let ctl_meta = control.read_tmp(META);
    assert_meta_complete(&ctl_meta, &["f"], "L-R5c control session");

    let redef = prims_repl_session(
        "(defn f [:Int x] (add-i64 x 1))\n\
         (defn f [:Int x] (add-i64 x 2))\n\
         (f 1)\n\
         /quit\n",
    )
    .assert_ok()
    .assert_stdout_contains(":primitives/Int 3");
    let redef_meta = redef.read_tmp(META);
    assert_meta_complete(&redef_meta, &["f"], "body-only redefinition");

    assert_eq!(
        slot_of(&redef_meta, "f"),
        slot_of(&ctl_meta, "f"),
        "body-only redefinition must keep f's slot"
    );
}

// =============================================================================
// S102 Phase-5 Stage-1 — lane L-U1 sibling for the persistence lane
// (`tests/plan/s102-test-plan.md` §1.1): the unannotated default path ×
// restart. GREEN pin (probed 2026-07-03 on the CS-A binary).
// =============================================================================

// spec: repl/spec.md §18.1 — L-U1 persistence sibling. S103 FLIPPED (2026-07-06,
// T1 full cure landed): the caller `g` here is CONCRETE (`(add-i64 y 1)` forces
// `y:Int`), so the end-of-turn reload recompiles it against the new `f` in the
// LIVE session — the former coherent-stale second answer (2) is now the cured
// value (52). The restart already showed 52; the cure makes the live session
// match it too (as the prior "no flip needed" note anticipated in spirit — but
// the live count assertion DID need updating: the second `(g 1)` is now 52, not
// a second 2). Contrast the pure-template split-world sibling in
// repl_redefinition.rs, whose generic `g` is never compiled concretely and
// stays coherent-stale.
#[test]
fn rejected_generic_change_persists_and_restarts_with_prior_source() {
    let first = prims_repl_session(
        "(defn f [x] x)\n\
         (defn g [y] (f (add-i64 y 1)))\n\
         (g 1)\n\
         (defn f [x] (add-i64 x 50))\n\
         (g 1)\n\
         /quit\n",
    )
    .assert_ok();
    let first = first
        .assert_stdout_contains("cannot redefine user/f")
        .assert_stdout_does_not_contain(":primitives/Int 52");
    assert_eq!(
        first.stdout.matches(":primitives/Int 2").count(),
        2,
        "the rejected replacement must leave the prior body live; stdout={}",
        first.stdout
    );
    let meta = first.read_tmp(META);
    assert_meta_complete(&meta, &["f", "g"], "L-U1 persistence sibling");

    // Restart reconstructs the retained prior source, not the rejected form.
    let second = first
        .run_again()
        .repl()
        .stdin("(g 1)\n/quit\n")
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 2")
        .assert_stdout_does_not_contain(":primitives/Int 52");
    drop(second);
}

// spec: repl/spec/15-session-persistence.md §15.6 — a rejected redefinition
// MUST NOT change regenerated source; §15.2 — restart resumes coherent prior state.
#[test]
fn rejected_change_does_not_write_an_incoherent_backing_file() {
    // Session 1: the incompatible change is rejected before publication and
    // before persistence; the old coherent source remains authoritative.
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
    assert!(first.stdout.contains("cannot redefine user/f"));

    // Session 2 reaches a prompt with the prior definitions already usable.
    first
        .run_again()
        .repl()
        .stdin("(k 3)\n")
        .output()
        .assert_ok()
        .assert_stdout_contains("user>")
        .assert_stdout_contains(":primitives/Int 4")
        .assert_stdout_does_not_contain("has errors");
}

// spec: repl/spec/18-redefinition.md §18.1–§18.2 — a cache-restored direct
// caller blocks a type-changing replacement before publication, exactly as it
// does in a fresh session, and remains callable afterward.
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

    let second = first
        .run_again()
        .repl()
        .stdin(
            "(import [m [mg]])\n\
             (mg 41)\n\
             /mod m\n\
             (defn mf [:String s] (str-len s))\n\
             /mod user\n\
             (mg 41)\n",
        )
        .output()
        .assert_ok()
        .assert_stdout_contains("cannot redefine m/mf")
        .assert_stdout_contains("blocking dependents: m/mg")
        .assert_stdout_does_not_contain("; broken:")
        .assert_stdout_does_not_contain("; recompiled:");
    assert_eq!(second.stdout.matches(":primitives/Int 142").count(), 2);
}

// spec: repl/spec/18-redefinition.md §18.1–§18.2 — the fresh-session control
// for the same rule, with the direct caller in another file-backed module.
#[test]
fn redefine_file_backed_module_symbol_fresh_session_cross_module_control() {
    let cap = Cranelisp::new()
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
             /mod user\n\
             (ng 41)\n",
        )
        .output()
        .assert_ok()
        .assert_stdout_contains("cannot redefine m/mf")
        .assert_stdout_contains("blocking dependents: n/ng")
        .assert_stdout_does_not_contain("; broken:")
        .assert_stdout_does_not_contain("; recompiled:")
        .assert_stdout_does_not_contain("definition source unavailable")
        .assert_stdout_does_not_contain("unknown type");
    assert_eq!(cap.stdout.matches(":primitives/Int 142").count(), 2);
}
