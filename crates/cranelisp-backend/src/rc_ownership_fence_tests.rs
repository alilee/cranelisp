//! S115 W4c / FIXME 0781 — the standing structural fence for the recurring
//! class **"a syntactic node-kind test standing in for the derived answer"**.
//!
//! Four instances in S115 alone: 0693's name-keyed COW gate, 0752's two
//! surviving spelling-keyed sites, 0749's ad-hoc fresh-kind list, and 0781's
//! five `matches!(e, MonoExpr::Var { .. })` ownership gates. Every one was the
//! same move — an RC-emission decision re-derived at its own site from the
//! shape of the node in hand, instead of read from the one derived answer.
//! Every one was a live memory-safety defect or leak.
//!
//! ## What this fence asserts
//!
//! In the files where **RC emission decisions live**, no `matches!` may test a
//! `MonoExpr` node's KIND ALONE (`MonoExpr::Kind { .. }` — every field
//! discarded, so the only information extracted is "which variant"). A gate
//! phrased that way is, by construction, not reading a derived fact; the
//! derived facts live in `compiler::fn_compiler::{value_provenance,
//! is_fresh_construction, yields_owned_temporary}` and in the resolution
//! carriers, and a seam must consult those.
//!
//! A test that KEEPS a field is not fenced — `MonoExpr::Var { name, .. } if
//! name == …` asks about the identity a node carries, which is a real
//! question about the program, not a stand-in for an analysis result.
//!
//! ## Why these files and not others
//!
//! The fenced set is the RC-decision surface: the vec container gates, the
//! match scrutinee gates, the typed-release classifier, and the capture-release
//! classifier. `apply.rs` is deliberately EXCLUDED: its one bare kind test
//! (`matches!(a, MonoExpr::If { .. } | MonoExpr::Match { .. })`) selects a
//! CODEGEN MODE for compiling an argument (branch results need the tail-arg
//! protect enabled while they compile), not an ownership verdict about a value.
//! Widening the fence there would make it a lint about syntax rather than about
//! ownership, and it would have to be suppressed immediately — which is how
//! fences die.
//!
//! ## Detection proof (METHOD §2.2 — an instrument is unverified until proven
//! to detect)
//!
//! MEASURED: restoring any one of the five 0781 gates to its pre-fix form
//! flips this test RED, naming the file and the line. Verified for
//! `vec_codegen::emit_vec_drop_if_temporary` and for both `match_codegen`
//! gates; the fence reports 1 violation per reverted gate.

/// The RC-decision files, as `(path, source)` pairs. `include_str!` is
/// relative to THIS file, so the fence needs no CWD and no path discovery.
const RC_DECISION_SOURCES: &[(&str, &str)] = &[
    (
        "compiler/vec_codegen.rs",
        include_str!("compiler/vec_codegen.rs"),
    ),
    (
        "compiler/match_codegen.rs",
        include_str!("compiler/match_codegen.rs"),
    ),
    (
        "compiler/rc_emission.rs",
        include_str!("compiler/rc_emission.rs"),
    ),
    (
        "compiler/control_flow/capture_rc.rs",
        include_str!("compiler/control_flow/capture_rc.rs"),
    ),
];

/// Is this line Rust comment text (line, doc, or inner-doc)? Comments
/// legitimately QUOTE the fenced pattern — every 0781 site carries a comment
/// recording what it used to say, and that record is the point.
fn is_comment(line: &str) -> bool {
    let t = line.trim_start();
    t.starts_with("//") || t.starts_with("/*") || t.starts_with('*')
}

/// Every fenced violation: a non-comment line performing a bare `MonoExpr`
/// kind test inside a `matches!`.
fn violations() -> Vec<String> {
    let mut out = Vec::new();
    for (path, src) in RC_DECISION_SOURCES {
        for (i, line) in src.lines().enumerate() {
            if is_comment(line) {
                continue;
            }
            if line.contains("matches!") && line.contains("MonoExpr::") && line.contains("{ .. }") {
                out.push(format!("{path}:{}: {}", i + 1, line.trim()));
            }
        }
    }
    out
}

// spec: design/arch/safety-invariants.md §2 (the assertion ladder, tier 3 —
// seam assert) / FIXME 0781 — an RC-emission decision must read a derived
// ownership answer, never the node kind it happens to be looking at. This is
// the standing instrument for the class; the four S115 instances are its
// motivation and its calibration.
#[test]
fn no_rc_decision_reads_a_bare_monoexpr_node_kind() {
    let found = violations();
    assert!(
        found.is_empty(),
        "an RC-emission decision is testing a `MonoExpr` node KIND alone. That \
         is a stand-in for a derived answer, and it is the S115 class that \
         produced 0693 / 0749 / 0752 / 0781 — the last of which was a `--link` \
         exit-134 use-after-free reachable from `(defn f [v b] (vec-get (if b v \
         v) 0))`.\n\nRead the derived answer instead: \
         `fn_compiler::yields_owned_temporary` (is this value mine to \
         release?), `fn_compiler::is_fresh_construction` (can it alias a scope \
         binding?), or the resolution carrier (what does this call resolve \
         to?). If the question really IS about a node's identity rather than \
         its analysis result, keep the field you are asking about — \
         `MonoExpr::Var {{ name, .. }} if name == x` is not fenced.\n\n\
         Violations:\n  {}",
        found.join("\n  ")
    );
}

// spec: FIXME 0781 — the fence's FALSE-FIRE control (METHOD §2.2: a validator
// proves itself per variant, with a false-fire fence). The fence must not fire
// on a comment that quotes the pattern (every fixed site carries one), nor on
// a field-keeping test (`MonoExpr::Var { name, .. }` — a real identity
// question, which `cow_source_has_separate_owner` still asks and must keep
// asking). Without this cell the fence could be "passing" because it matches
// nothing at all.
#[test]
fn the_fence_ignores_comments_and_field_keeping_tests() {
    assert!(is_comment(
        "        // matches!(scrutinee, MonoExpr::Var { .. })"
    ));
    assert!(is_comment(
        "    /// was `matches!(source, MonoExpr::Var { .. })`"
    ));
    assert!(is_comment("//! MonoExpr::Var { .. }"));
    assert!(!is_comment(
        "        if matches!(v, MonoExpr::Var { .. }) {"
    ));

    // The live field-keeping test in `cow_source_has_separate_owner` is real
    // code and must NOT be a violation — it asks which BINDING this is.
    let (_, vec_src) = RC_DECISION_SOURCES[0];
    assert!(
        vec_src.contains("MonoExpr::Var { name, .. } if return_cow_source == Some(name)"),
        "the field-keeping identity test this control is calibrated against has \
         moved; re-verify that the fence still distinguishes it from a bare \
         kind test before editing this cell"
    );
    // Deliberately does NOT re-assert `violations().is_empty()` — that is the
    // cell above's job, and duplicating it would make a real violation redden
    // both cells and blur which signal fired.
}
