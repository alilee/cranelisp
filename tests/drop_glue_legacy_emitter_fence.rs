//! Structural fence for arch ruling 10 — the **atomic** deletion of the legacy
//! inline drop-glue emitter (`sprints/SPRINT.md` §Architecture review ruling 10;
//! `tests/plan/s118-test-plan.md` §4.3, extended by the 0878 disposition;
//! `design/backend/transitive-drop-glue.md` §8). Authored by `/testing` in S118
//! W1 as an INTENDED RED; it flips exactly at the Track-B W3 migration
//! change-set (backend slice S5's final commit).
//!
//! WHAT RULING 10 SAYS. The canonical `DropGlueRegistry` coexisting with the
//! legacy inline emitter was an APPROVED TRANSITIONAL state, and its closure
//! condition is exactly one thing: consumers migrate **and** the depth constant
//! plus the inline recursive emitter delete **in the same wave**. A partial
//! migration that leaves both mechanisms alive is a `/review` REJECT — not a
//! capacity call, an architectural one (Principle 8's bridge closes this
//! sprint). The behaviour cells (0810 ×10, 0760/0796, the TCO family) cannot
//! express that condition: they go green the moment SOMETHING releases the
//! value, whichever mechanism did it. Only a structural assertion can say
//! "and the other mechanism is gone".
//!
//! WHY THE FENCE IS EXTENDED (FIXME 0878, `/qa`-disposed 2026-07-25). The fence
//! as originally specified would have PASSED with a second type-directed glue
//! mechanism still alive: `vec_codegen` mints its own named per-instantiation
//! ADT glue under the backend-local `adt_instantiation_mangle` key
//! (`transitive-drop-glue.md` §1.1 M3 — the `/design`(backend) census found five
//! mechanisms, not two). Two glue mechanisms under two identity schemes is the
//! exact state ruling 10 exists to prevent, so `build_adt_drop_glue_fn`,
//! `build_elem_dec_fn` and `adt_drop_glue_name` are in the grep-zero set.
//!
//! `adt_instantiation_mangle` is deliberately NOT in the set: §8 conditions its
//! deletion on it retaining no other consumer at migration time, so a surviving
//! consumer-less mangle is a `/review` dead-code catch, not a fence FAIL.
//!
//! ALSO DELIBERATELY NOT IN THE SET (§8 "Explicitly NOT deleted"), so that a
//! correct migration is not blocked by a fence that over-reaches:
//! `emit_closure_dec_into`, `emit_capture_dec_glue` (the capture-LAYOUT owner),
//! `closure_drop_glue_name` / `curry_drop_glue_name` (they name capture
//! envelopes, not type glue), `match_forwards_scrutinee` (retained for
//! `operand_live_binding_root`'s provenance trace), `substitute_type_inline` and
//! `collect_var_ids_from_type` (live consumers elsewhere).
//!
//! NAMED SEAMS, NEVER LINE NUMBERS (plan §4.3's explicit requirement): the fence
//! asserts on symbol names, so it survives every reshuffle of the files it
//! guards and fails only when a named mechanism is actually still there.
//!
//! SCOPE: production sources only — `crates/cranelisp-backend/src/`, excluding
//! `#[cfg(test)]` unit-test modules. A `/dev` unit test naming a deleted symbol
//! cannot keep the mechanism alive (the crate would not compile), so counting
//! those would only produce noise; the mode-gating tripwire
//! (`tests/mode_gating_guard.rs`) draws the same line for the same reason.
//
// spec: design/backend/transitive-drop-glue.md §8 — "The atomic deletion
//       condition (S118 arch ruling 10)": the deletion enumeration this fence
//       greps for, and the ruling it implements (arch ruling 10, recorded in the
//       active sprint plan's architecture review).

use std::process::Command;

/// The grep-zero set. Each entry is `(symbol, why it must be gone)`.
///
/// Groups, in the order `transitive-drop-glue.md` §8 lists them:
///  1. the transitional DEPTH BOUND and its carrier — the bound exists only
///     because the legacy inline emitter expands recursive source types forever
///     without it; the canonical registry is declaration-first and has no
///     cutoff, so a surviving bound means a surviving inline expander;
///  2. the inline recursive EMITTER seams themselves;
///  3. the SECOND GLUE-IDENTITY HOME in `vec_codegen` (the 0878 extension).
const FORBIDDEN: &[(&str, &str)] = &[
    (
        "MAX_DROP_GLUE_DEPTH",
        "the transitional depth bound — the canonical registry has no cutoff, \
         so this constant existing means the inline expander still does",
    ),
    (
        "drop_glue_depth",
        "the `FnCompiler` recursion counter the depth bound reads; it deletes \
         with the bound (field, initialiser and both mutations)",
    ),
    (
        "emit_rc_dec_with_inline_drop_glue",
        "the legacy inline recursive emitter's entry seam — the mechanism \
         ruling 10 requires deleted atomically with the consumer migration",
    ),
    (
        "emit_inline_drop_glue",
        "the legacy inline field-dec walk the entry seam drives",
    ),
    (
        "build_adt_drop_glue_fn",
        "0878: `vec_codegen`'s SECOND named per-instantiation ADT glue builder \
         — a second type-directed glue mechanism under a second identity scheme",
    ),
    (
        "build_elem_dec_fn",
        "0878: the elem-dec half of the same second mechanism, keyed on the \
         same backend-local mangle",
    ),
    (
        "adt_drop_glue_name",
        "0878: the second mechanism's identity scheme (the backend-local \
         `adt_instantiation_mangle` key); two identity schemes alive is the \
         state ruling 10 exists to prevent",
    ),
];

fn workspace_root() -> &'static str {
    env!("CARGO_MANIFEST_DIR")
}

/// `grep -rn` for `symbol` under `crates/cranelisp-backend/src/`, returning
/// `(file, code)` for LIVE code only: comment-only lines and `#[cfg(test)]`
/// module files are dropped (see the scope note in the module header).
fn live_hits(symbol: &str) -> Vec<(String, String)> {
    let out = Command::new("grep")
        .args([
            "-rn",
            "--include=*.rs",
            symbol,
            "crates/cranelisp-backend/src/",
        ])
        .current_dir(workspace_root())
        .output()
        .expect("grep must be available");
    let text = String::from_utf8_lossy(&out.stdout);
    let mut hits = Vec::new();
    for line in text.lines() {
        // grep -n output: `path:lineno:code` (code may itself contain `:`).
        let mut parts = line.splitn(3, ':');
        let file = parts.next().unwrap_or("").to_string();
        let lineno = parts.next().unwrap_or("").to_string();
        let code = parts.next().unwrap_or("").to_string();
        let trimmed = code.trim_start();
        if trimmed.starts_with("//") || trimmed.starts_with("*") {
            continue; // rustdoc / line comment — describes a mechanism, is not one
        }
        if file.ends_with("tests.rs") || file.contains("/tests/") {
            continue; // #[cfg(test)] unit tier — deletes with its subject
        }
        hits.push((format!("{file}:{lineno}"), code.trim().to_string()));
    }
    hits
}

// THE FENCE. RED today by construction; it flips exactly at the W3 change-set
// that migrates the consumers, and it is the assertion that makes "migrate the
// behaviour but keep the emitter" impossible to land quietly.
//
// A wave that flips the behaviour cells (0810 ×10, 0760/0796, the TCO family)
// while THIS cell stays RED is the partial-migration state arch ruling 10
// declares a `/review` REJECT — so read a green behaviour set with this cell red
// as a REJECT signal, never as progress.
// spec: (CI guard) — `design/backend/transitive-drop-glue.md` §8; arch ruling 10.
#[test]
fn legacy_inline_drop_glue_mechanism_is_absent_from_backend_sources() {
    let mut report: Vec<String> = Vec::new();
    for (symbol, why) in FORBIDDEN {
        let hits = live_hits(symbol);
        if hits.is_empty() {
            continue;
        }
        report.push(format!(
            "  `{symbol}` — {why}\n{}",
            hits.iter()
                .map(|(loc, code)| format!("      {loc}: {code}"))
                .collect::<Vec<_>>()
                .join("\n")
        ));
    }
    assert!(
        report.is_empty(),
        "ARCH RULING 10 NOT SATISFIED — the legacy drop-glue mechanism is still \
         live in `crates/cranelisp-backend/src/`. The canonical \
         `DropGlueRegistry` coexisting with it was an APPROVED TRANSITIONAL \
         state whose closure condition is that the consumers migrate AND these \
         symbols delete IN THE SAME WAVE (`design/backend/transitive-drop-glue.md` \
         §8; `tests/plan/s118-test-plan.md` §4.3). Surviving symbols:\n\n{}\n\n\
         If a symbol here is being deliberately RETAINED, that is an \
         architecture question for `/arch`, not an edit to this list: §8's \
         \"Explicitly NOT deleted\" set is already excluded, and \
         `adt_instantiation_mangle` is deliberately out of scope (its deletion \
         is conditioned in §8; a consumer-less survivor is a `/review` dead-code \
         catch, not a fence FAIL).",
        report.join("\n\n"),
    );
}

// The fence's own capability fence (METHOD §2.2 — an instrument is unverified
// until it is proven to detect). Two independent ways this guard could pass
// vacuously: the grep could be pointed at a path that does not exist (returning
// nothing forever), and the comment/test-module filters could swallow live code.
// Both are asserted here against the CURRENT tree, so the guard cannot silently
// become a no-op — and unlike the fence above, this cell must stay GREEN through
// the migration, because it probes a symbol the §8 enumeration explicitly
// RETAINS.
// spec: (CI guard) — `design/backend/transitive-drop-glue.md` §8.
#[test]
fn fence_capability_reads_live_backend_sources() {
    // `emit_capture_dec_glue` is in §8's "Explicitly NOT deleted" set (it is the
    // capture-LAYOUT owner), so it is live before AND after the migration — the
    // right probe for "the grep reaches real code".
    let live = live_hits("emit_capture_dec_glue");
    assert!(
        !live.is_empty(),
        "the fence's grep read NOTHING for a symbol §8 explicitly RETAINS \
         (`emit_capture_dec_glue`). Either the search path moved or the \
         comment/test filters are swallowing live code — in that state the \
         fence above would report GREEN no matter what survives."
    );
    // And the filters really do drop non-code: a symbol that appears ONLY in
    // rustdoc must produce no live hits. `Principle 8` is prose-only in this
    // crate; if that ever stops being true, this assertion says so rather than
    // letting the filter rot go unnoticed.
    let out = Command::new("grep")
        .args([
            "-rn",
            "--include=*.rs",
            "Principle 8",
            "crates/cranelisp-backend/src/",
        ])
        .current_dir(workspace_root())
        .output()
        .expect("grep must be available");
    let raw = String::from_utf8_lossy(&out.stdout).lines().count();
    if raw > 0 {
        assert!(
            live_hits("Principle 8").is_empty(),
            "a prose-only phrase produced LIVE hits — the comment filter is not \
             dropping rustdoc, so the fence above would trip on documentation \
             rather than on a surviving mechanism"
        );
    }
}
