// spec_08_prelude_outer_scope.rs — Prelude-as-outer-scope import model (S78 Wave 4 §2).
//
// Covers the SETTLED prelude-as-outer-scope model (user, 2026-06-11):
//   `design/int/s78-entry-module.md §2`.
//
// The implicit prelude is an OUTER SCOPE resolved by symbol-lookup fallback,
// NOT materialised (flattened) into each module's symbol table. The module's
// own table is the INNER scope (local defs + explicit imports); the prelude
// is the OUTER scope, consulted only on a resolution miss in the inner scope.
//
// Consequences this file pins (per the Wave 4 /qa row in `sprints/SPRINT.md`):
//   - Explicit/local SILENTLY shadows prelude (no ambiguity error; the
//     explicit/local binding wins).                                   [§2.2 (1)]
//   - Two explicit imports/globs of the same name from different sources
//     remain AMBIGUOUS (spec §8.6.5 poisoning) — unaffected by the reshape.
//                                                                     [§2.2 (2)]
//   - Prelude refusal `(import [prelude []])` → NO fallback; prelude names
//     are NOT available bare. Selective `(import [prelude [X]])` → only X,
//     no fallback for other prelude names.                            [§2.3]
//   - Primitives reach user code VIA prelude's re-export through the fallback;
//     qualified `primitives/...` always works.                        [§2.2 (4)]
//
// RED-by-design vs GREEN classification (the §2 tripwire — see the per-test
// notes). The §1 def-over-prelude / explicit-over-prelude rows were the RED
// guards of the S102 prelude-arm defect (the flattened `is_seeded` model let
// the local/explicit binding silently win over the prelude); the outer-scope
// fallback landed and all §1 rows are GREEN on HEAD (verified 2026-07-12).
// Refusal, selective-import, ambiguity, and primitives-via-prelude in `--run`
// mode were already correct and stand as GREEN behaviour-preservation guards.
//
// Test prelude shape: every test writes its own `prelude.cl` into the
// per-test project root (which shadows stdlib per §8.8.2). The prelude does
// `(export [primitives [*]])` so primitive names flow as bare names through
// the implicit glob, and defines `gulp` as a sentinel prelude-provided name
// to shadow / refuse / collide against.
//
// ─────────────────────────────────────────────────────────────────────────
// S102 RE-ANCHOR (user ruling 2026-07-04; /spec `a953de0`; FIXME 0514/0515):
// the "explicit/local SILENTLY shadows the prelude" model this file was built
// around is REVERSED. The prelude is just an implicit `(import [prelude [*]])`;
// its provided names are in scope like any import, and redefining/shadowing a
// prelude-provided name is the SAME compile-time error as shadowing an
// explicit import — NO exceptions (spec/08-modules.md §8.6.4/§8.8.1). The
// outer/inner-scope layering is retained as an IMPLEMENTATION detail of
// resolution, but it grants no exemption. Consequently the five §1
// "silently shadows" tests below are FLIPPED to expect REJECTION:
//   * def-over-prelude   → §8.6.4 def-over-name-in-scope error
//   * explicit-import-over-prelude (distinct terminal) → §8.6.5 ambiguity poison
// They once FAILED (the impl rejected only inner-table import/export on the
// REPL path — the prelude/outer-scope + batch arms were unimplemented); the
// 0514 prelude-fallback arm landed and all five are GREEN on HEAD. The §2
// (ambiguity), §3 (refusal/selective = not-loading, legal), and §4
// (primitives-via-prelude, legal) tests were already error-preserving or legal
// under the rule and are unchanged.
// ─────────────────────────────────────────────────────────────────────────

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, CrOutput};

/// A §8.6.4/§8.6.5 shadow/collision rejection: a collision diagnostic is
/// present AND the shadow did not run to its exit code (no effect). Used by
/// the §1 tests (GREEN on HEAD since the prelude-arm fallback landed).
fn assert_shadow_rejected(out: &CrOutput, shadow_exit: i32) {
    let c = format!("{}\n{}", out.stdout, out.stderr).to_lowercase();
    assert!(
        c.contains("conflict") || c.contains("ambiguous") || c.contains("error"),
        "expected a §8.6.4/§8.6.5 collision rejection diagnostic;\nstdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    assert_ne!(
        out.status.code(),
        Some(shadow_exit),
        "the shadow MUST be rejected (must not run to exit {});\nstdout:\n{}\nstderr:\n{}",
        shadow_exit,
        out.stdout,
        out.stderr
    );
}

/// A test prelude that re-exports primitives and defines a sentinel
/// prelude-provided function `gulp`. Mirrors the `(export [primitives [*]])`
/// shape of `tests/fixtures/preludes/*.cl` so bare primitive names resolve.
const PRELUDE_WITH_GULP: &str = "\
(export [primitives [*]])
(defn gulp [x] (add-i64 x 1))
";

// =============================================================================
// 1. SHADOW — explicit/local silently shadows prelude (no ambiguity error)
// =============================================================================

// spec: spec/08-modules.md §8.6.4/§8.8.1 — a local `defn` of a name the
//   prelude also provides is a compile-time error (def-over-name-in-scope);
//   the prelude carries no exemption. The rejected def has no effect.
//
// Was a 0514 prelude-arm RED (the local def silently won, exit 105); GREEN on
// HEAD since the prelude/outer-scope arm landed at the shared typecheck seam.
// defect: class=prelude-scope-miss locus=crates/cranelisp-typecheck/src/checker.rs::reject_def_over_binding found=S102 owner=/dev
#[test]
fn local_defn_over_prelude_is_rejected() {
    // prelude `gulp` is (+1); local `gulp` is (+100) → would be 105 if it won.
    let out = Cranelisp::new()
        .prelude(PRELUDE_WITH_GULP)
        .file(
            "user.cl",
            "(defn gulp [x] (add-i64 x 100))\n(defn main [] (Pure (gulp 5)))",
        )
        .run("user.cl")
        .output();
    assert_shadow_rejected(&out, 105);
}

// spec: spec/08-modules.md §8.6.4 — the def-over-prelude rejection names the
//   collision (conflict/ambiguity), NOT a silent accept. Negative companion
//   to the above: the diagnostic MUST be present.
//
// Was a 0514 prelude-arm RED (NO diagnostic appeared — silent accept); GREEN on
// HEAD.
// defect: class=prelude-scope-miss locus=crates/cranelisp-typecheck/src/checker.rs::reject_def_over_binding found=S102 owner=/dev
#[test]
fn local_defn_over_prelude_neg_emits_collision_diagnostic() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_WITH_GULP)
        .file(
            "user.cl",
            "(defn gulp [x] (add-i64 x 100))\n(defn main [] (Pure (gulp 5)))",
        )
        .run("user.cl")
        .output();
    let lower = format!("{}\n{}", out.stdout, out.stderr).to_lowercase();
    assert!(
        lower.contains("conflict") || lower.contains("ambiguous"),
        "def-over-prelude MUST emit a §8.6.4 collision diagnostic;\nstdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    assert_ne!(
        out.status.code(),
        Some(105),
        "the rejected def MUST have no effect (must not run to 105);\nstdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/08-modules.md §8.6.4/§8.6.5 — an EXPLICIT GLOB import bringing a
//   name that the prelude also provides is a DISTINCT-terminal collision
//   (libc/gulp vs prelude/gulp): the bare name is POISONED (ambiguous), not
//   silently won by the explicit import. There is no "explicit shadows
//   prelude" precedence tier.
//
// Was a 0514/0515 RED (the explicit import silently won, exit 105); GREEN on
// HEAD since the outer-scope reshape poisons distinct-terminal prelude overlaps.
// defect: class=prelude-scope-miss locus=crates/cranelisp-typecheck/src/checker.rs::reject_def_over_binding found=S102 owner=/dev
#[test]
fn explicit_glob_import_over_prelude_distinct_terminal_poisons() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_WITH_GULP)
        .file("libc.cl", "(defn gulp [x] (add-i64 x 100))")
        .file(
            "user.cl",
            "(import [libc [*]])\n(defn main [] (Pure (gulp 5)))",
        )
        .run("user.cl")
        .output();
    assert_shadow_rejected(&out, 105);
}

// spec: spec/08-modules.md §8.6.4/§8.6.5 — an explicit SPECIFIC import of a
//   name the prelude also provides (distinct terminal) is the same poison.
//
// Was an S102 re-anchor RED (the explicit specific import silently won, 105);
// GREEN on HEAD since the reshape poisons distinct-terminal overlaps.
// defect: class=prelude-scope-miss locus=crates/cranelisp-typecheck/src/checker.rs::reject_def_over_binding found=S102 owner=/dev
#[test]
fn explicit_specific_import_over_prelude_distinct_terminal_poisons() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_WITH_GULP)
        .file("libc.cl", "(defn gulp [x] (add-i64 x 100))")
        .file(
            "user.cl",
            "(import [libc [gulp]])\n(defn main [] (Pure (gulp 5)))",
        )
        .run("user.cl")
        .output();
    assert_shadow_rejected(&out, 105);
}

// spec: spec/08-modules.md §8.6.5 — the distinct-terminal explicit-over-prelude
//   overlap MUST poison the bare name (a collision diagnostic), NOT silently
//   resolve to the explicit import's binding. Negative companion.
//
// Was an S102 re-anchor RED (NO ambiguity appeared — silent win, 105); GREEN on
// HEAD since the reshape poisons distinct-terminal overlaps.
// defect: class=prelude-scope-miss locus=crates/cranelisp-typecheck/src/checker.rs::reject_def_over_binding found=S102 owner=/dev
#[test]
fn explicit_import_over_prelude_neg_emits_ambiguity() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_WITH_GULP)
        .file("libc.cl", "(defn gulp [x] (add-i64 x 100))")
        .file(
            "user.cl",
            "(import [libc [*]])\n(defn main [] (Pure (gulp 5)))",
        )
        .run("user.cl")
        .output();
    let lower = format!("{}\n{}", out.stdout, out.stderr).to_lowercase();
    assert!(
        lower.contains("ambiguous") || lower.contains("conflict"),
        "distinct-terminal explicit-over-prelude MUST poison the bare name;\n\
         stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    assert_ne!(
        out.status.code(),
        Some(105),
        "the poisoned bare name MUST NOT silently resolve to the explicit import \
         (must not run to 105);\nstdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
}

// =============================================================================
// 2. AMBIGUITY (preserved) — two explicit sources of the same name remain
//    ambiguous (§8.6.4 / §8.6.5 poisoning). Unaffected by the reshape.
// =============================================================================

// spec: spec/08-modules.md §8.6.5 — two explicit glob imports both providing
//   the same bare name → the name is ambiguous (poisoned); using it bare is
//   a compile-time error.
//
// CLASSIFICATION: GREEN guard. Both colliding entries live in the inner
// table; the prelude fallback never enters the picture. Must stay erroring
// after `is_seeded` deletes (the deletion must NOT remove real ambiguity).
#[test]
fn two_explicit_globs_same_name_is_ambiguous() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_WITH_GULP)
        .file("liba.cl", "(defn zonk [x] (add-i64 x 1))")
        .file("libb.cl", "(defn zonk [x] (add-i64 x 2))")
        .file(
            "user.cl",
            "(import [liba [*]])\n(import [libb [*]])\n(defn main [] (zonk 5))",
        )
        .run("user.cl")
        .output();
    // The build MUST fail (non-zero) — the ambiguous bare name cannot resolve.
    assert!(
        out.status.code() != Some(0),
        "two explicit globs providing 'zonk' MUST be a compile error; \
         exit={:?} stderr=\n{}",
        out.status.code(),
        out.stderr
    );
    // FIXME(/typecheck): the diagnostic currently reads "undefined variable:
    // zonk" rather than the §8.6.5-mandated "ambiguous bare name 'zonk' …
    // use 'liba/zonk' or 'libb/zonk'". Wording is a separate /typecheck
    // concern; this test pins only that the name does NOT silently resolve.
    assert!(
        out.stderr.contains("zonk"),
        "the conflict diagnostic MUST name the offending symbol 'zonk'; \
         stderr=\n{}",
        out.stderr
    );
}

// spec: spec/08-modules.md §8.6.4 — two explicit SPECIFIC imports of the same
//   bare name from different source modules → compile-time error (duplicate
//   import / ambiguity).
//
// CLASSIFICATION: GREEN guard. Must stay erroring after `is_seeded` deletes.
#[test]
fn two_explicit_specific_imports_same_name_is_error() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_WITH_GULP)
        .file("liba.cl", "(defn zonk [x] (add-i64 x 1))")
        .file("libb.cl", "(defn zonk [x] (add-i64 x 2))")
        .file(
            "user.cl",
            "(import [liba [zonk]])\n(import [libb [zonk]])\n(defn main [] (zonk 5))",
        )
        .run("user.cl")
        .output();
    assert!(
        out.status.code() != Some(0),
        "two explicit specific imports of 'zonk' from different sources MUST be \
         a compile error; exit={:?} stderr=\n{}",
        out.status.code(),
        out.stderr
    );
    assert!(
        out.stderr.contains("zonk"),
        "the conflict diagnostic MUST name 'zonk'; stderr=\n{}",
        out.stderr
    );
}

// spec: spec/08-modules.md §8.6.4 — a name brought by an explicit import that
//   does NOT collide with another explicit source resolves cleanly. This is
//   the CONTROL for the ambiguity tests above: it proves the failure in those
//   tests is the collision, not the import machinery itself.
//
// CLASSIFICATION: GREEN guard.
#[test]
fn explicit_import_no_collision_resolves() {
    Cranelisp::new()
        .prelude(PRELUDE_WITH_GULP)
        .file(
            "libc.cl",
            "(defn other [x] (add-i64 x 7))",
        )
        .file(
            "user.cl",
            "(import [libc [other]])\n(defn main [] (Pure (other 5)))",
        )
        .run("user.cl")
        .output()
        .assert_exit(12);
}

// =============================================================================
// 3. PRELUDE REFUSAL — `(import [prelude []])` → no fallback; selective import
//    → only named names, no fallback for the rest.
// =============================================================================

// spec: spec/08-modules.md §8.8.1 / design/int/s78-entry-module.md §2.3 — a
//   module that refuses the prelude with `(import [prelude []])` gets NO
//   implicit prelude fallback: a prelude-provided name (`gulp`) is NOT
//   available bare.
//
// CLASSIFICATION: GREEN guard. In `--run` mode the refusal gate already
// suppresses the implicit glob, so bare `gulp` is unresolved today. The
// outer-scope model keeps this (the fallback bit is OFF when the module
// references prelude). Must stay erroring after the reshape.
#[test]
fn prelude_refusal_neg_prelude_name_not_bare() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_WITH_GULP)
        .file(
            "user.cl",
            "(import [prelude []])\n(defn main [] (gulp 5))",
        )
        .run("user.cl")
        .output();
    assert!(
        out.status.code() != Some(0),
        "refusing the prelude MUST leave the prelude name 'gulp' unavailable \
         bare; exit={:?} stderr=\n{}",
        out.status.code(),
        out.stderr
    );
    assert!(
        out.stderr.contains("gulp"),
        "the diagnostic MUST name the unresolved prelude symbol 'gulp'; \
         stderr=\n{}",
        out.stderr
    );
}

// spec: spec/08-modules.md §8.8.1 / §8.9.1 — even when the prelude is refused,
//   FULLY-QUALIFIED `primitives/...` references still resolve (qualified reach
//   never relied on the prelude fallback).
//
// CLASSIFICATION: GREEN guard.
#[test]
fn prelude_refusal_qualified_primitive_still_resolves() {
    // primitives/add-i64 2 3 = 5 → exit 5.
    Cranelisp::new()
        .prelude(PRELUDE_WITH_GULP)
        .file(
            "user.cl",
            "(import [prelude []])\n(defn main [] (primitives/Pure (primitives/add-i64 2 3)))",
        )
        .run("user.cl")
        .output()
        .assert_exit(5);
}

// spec: design/int/s78-entry-module.md §2.3 — a SELECTIVE prelude import
//   `(import [prelude [gulp]])` brings only the named binding into the inner
//   table; the named name IS available bare.
//
// CLASSIFICATION: GREEN guard.
#[test]
fn selective_prelude_import_brings_named_name() {
    // gulp = (+1); (gulp 10) = 11.
    Cranelisp::new()
        .prelude(PRELUDE_WITH_GULP)
        .file(
            "user.cl",
            "(import [prelude [gulp]])\n(defn main [] (primitives/Pure (gulp 10)))",
        )
        .run("user.cl")
        .output()
        .assert_exit(11);
}

// spec: design/int/s78-entry-module.md §2.3 — a SELECTIVE prelude import
//   suppresses the implicit fallback for OTHER prelude names: a prelude name
//   not in the selective list (here the re-exported primitive `add-i64`) is
//   NOT available bare.
//
// CLASSIFICATION: GREEN guard. The selective import references prelude, so
// the fallback bit is OFF — same gate as today. Must stay erroring.
#[test]
fn selective_prelude_import_neg_other_name_not_bare() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_WITH_GULP)
        .file(
            "user.cl",
            "(import [prelude [gulp]])\n(defn main [] (add-i64 1 2))",
        )
        .run("user.cl")
        .output();
    assert!(
        out.status.code() != Some(0),
        "a selective prelude import of [gulp] MUST NOT make other prelude names \
         (add-i64) available bare; exit={:?} stderr=\n{}",
        out.status.code(),
        out.stderr
    );
    assert!(
        out.stderr.contains("add-i64"),
        "the diagnostic MUST name the unresolved 'add-i64'; stderr=\n{}",
        out.stderr
    );
}

// =============================================================================
// 4. PRIMITIVES VIA PRELUDE — bare primitive names resolve through the prelude
//    re-export; qualified `primitives/...` always works.
// =============================================================================

// spec: spec/08-modules.md §8.9.1 / design/int/s78-entry-module.md §2.2 (4) —
//   in a NORMAL module (implicit prelude active), a bare primitive name
//   (`add-i64`) resolves through the prelude's `(export [primitives [*]])`
//   re-export, chain-followed via the fallback.
//
// CLASSIFICATION: GREEN guard. This is precisely the case the `"primitives"`
// arm of `is_seeded` currently papers over — it must keep working WITHOUT the
// hack. After `is_seeded` deletes, a bare primitive reaches the canonical
// entry via prelude's `Import`→primitives edge through the outer-scope
// fallback (Decision 0048 uniformity), not via a name-keyed skip.
#[test]
fn bare_primitive_resolves_via_prelude_reexport() {
    // add-i64 40 2 = 42.
    Cranelisp::new()
        .prelude(PRELUDE_WITH_GULP)
        .file("user.cl", "(defn main [] (Pure (add-i64 40 2)))")
        .run("user.cl")
        .output()
        .assert_exit(42);
}

// spec: spec/08-modules.md §8.9.1 — a FULLY-QUALIFIED `primitives/add-i64`
//   reference resolves in a normal module regardless of the prelude fallback.
//
// CLASSIFICATION: GREEN guard.
#[test]
fn qualified_primitive_resolves_in_normal_module() {
    Cranelisp::new()
        .prelude(PRELUDE_WITH_GULP)
        .file("user.cl", "(defn main [] (Pure (primitives/add-i64 40 2)))")
        .run("user.cl")
        .output()
        .assert_exit(42);
}

// spec: design/int/s78-entry-module.md §2.2 (4) — both a bare primitive AND a
//   bare prelude-defined function resolve together in a normal module: the
//   fallback covers re-exported primitives and prelude-local defs uniformly.
//
// CLASSIFICATION: GREEN guard.
#[test]
fn bare_primitive_and_prelude_defn_coexist() {
    // (gulp (add-i64 40 1)) = (gulp 41) = 42.
    Cranelisp::new()
        .prelude(PRELUDE_WITH_GULP)
        .file("user.cl", "(defn main [] (Pure (gulp (add-i64 40 1))))")
        .run("user.cl")
        .output()
        .assert_exit(42);
}

// =============================================================================
// 5. PARITY PINS — prelude ≡ explicit import (PLAN.md §III G1–G4)
//
// Twin fixtures: one program, two provenances for the contested name (explicit
// import vs implicit prelude), asserting the SAME outcome. These are GREEN
// today — they exist to make the NEXT forgotten-fallback resolution site fail
// loudly and to guard the resolution convergence refactor [S109]. The twin's
// outcome-equality IS the signal: any site lacking the prelude fallback
// diverges the two arms. (The RED counterparts — sites that DO diverge today —
// live in `spec_08_name_shadowing.rs` §7 and `spec_07_traits.rs` R1.)
// =============================================================================

// A prelude that re-exports primitives and provides a sentinel TYPE `Zed`
// (constructor `ZedC`), reached bare (leg B) or explicitly imported (leg A).
const PRELUDE_WITH_ZED: &str = "\
(export [primitives [*]])
(deftype Zed (ZedC [:Int n]))
";

// spec: spec/08-modules.md §8.6.4 (same-terminal dedup) + §8.8.1 — an explicit
//   `(import [primitives [add-i64]])` while the implicit prelude re-exports the
//   SAME terminal `primitives/add-i64` MUST dedup silently: no false collision,
//   the bare name resolves. (Importing from `primitives` does NOT suppress the
//   implicit prelude glob — only referencing `prelude` does — so `Pure` still
//   flows through the glob.)
//
// CLASSIFICATION: GREEN pin (G1). The terminal-source comparison sees one
// terminal (`primitives/add-i64`) behind both entries and dedups.
#[test]
fn prelude_and_explicit_import_same_terminal_dedup() {
    Cranelisp::new()
        .prelude(PRELUDE_WITH_ZED)
        .file(
            "user.cl",
            "(import [primitives [add-i64]])\n\
             (defn main [] (Pure (add-i64 40 2)))",
        )
        .run("user.cl")
        .output()
        .assert_exit(42);
}

// spec: spec/08-modules.md §8.8.1 + §3 (annotations) — a `:Zed` param/return
//   annotation naming a prelude-provided type resolves through the annotation-
//   position chokepoint (`resolve_type` -> `resolve_current_or_prelude`)
//   identically whether `Zed` is explicitly imported (leg A) or implicit-
//   prelude-provided (leg B).
//
// CLASSIFICATION: GREEN twin pin (G2). Both legs return 7; the outcome-equality
// is the parity signal.
#[test]
fn type_annotation_prelude_provided_type_twin() {
    // Leg A — `Zed`/`ZedC` explicitly imported (primitives imported directly so
    // `Int`/`Pure` remain in scope, since the prelude import suppresses the glob).
    let leg_a = Cranelisp::new()
        .prelude(PRELUDE_WITH_ZED)
        .file(
            "user.cl",
            "(import [primitives [Int Pure add-i64]])\n\
             (import [prelude [Zed ZedC]])\n\
             (defn takes [:Zed z] :Int (match z [(ZedC n) n]))\n\
             (defn main [] (Pure (takes (ZedC 7))))",
        )
        .run("user.cl")
        .output();
    // Leg B — same program, `Zed`/`ZedC` reached via the implicit prelude.
    let leg_b = Cranelisp::new()
        .prelude(PRELUDE_WITH_ZED)
        .file(
            "user.cl",
            "(defn takes [:Zed z] :Int (match z [(ZedC n) n]))\n\
             (defn main [] (Pure (takes (ZedC 7))))",
        )
        .run("user.cl")
        .output();
    leg_a.assert_exit(7);
    leg_b.assert_exit(7);
}

// spec: spec/08-modules.md §8.8.1 + §5.2 (deftype fields) — a deftype field
//   `[:Zed z]` naming a prelude-provided type registers identically whether
//   `Zed` is explicitly imported (leg A) or implicit-prelude-provided (leg B).
//
// CLASSIFICATION: GREEN twin pin (G3). Both legs return 9.
#[test]
fn deftype_field_type_prelude_provided_twin() {
    let leg_a = Cranelisp::new()
        .prelude(PRELUDE_WITH_ZED)
        .file(
            "user.cl",
            "(import [primitives [Int Pure]])\n\
             (import [prelude [Zed ZedC]])\n\
             (deftype Wrap (WrapC [:Zed z]))\n\
             (defn unwrap [:Wrap w] :Int (match w [(WrapC inner) (match inner [(ZedC n) n])]))\n\
             (defn main [] (Pure (unwrap (WrapC (ZedC 9)))))",
        )
        .run("user.cl")
        .output();
    let leg_b = Cranelisp::new()
        .prelude(PRELUDE_WITH_ZED)
        .file(
            "user.cl",
            "(deftype Wrap (WrapC [:Zed z]))\n\
             (defn unwrap [:Wrap w] :Int (match w [(WrapC inner) (match inner [(ZedC n) n])]))\n\
             (defn main [] (Pure (unwrap (WrapC (ZedC 9)))))",
        )
        .run("user.cl")
        .output();
    leg_a.assert_exit(9);
    leg_b.assert_exit(9);
}

// spec: spec/08-modules.md §8.8.1 + §6 (patterns) — a prelude-provided ctor
//   works in VALUE position (`(ZedC 7)`) and PATTERN position (`[(ZedC n) n]`)
//   identically whether `ZedC` is explicitly imported (leg A) or implicit-
//   prelude-provided (leg B). Covers the value-position chokepoint and the
//   `lookup_constructor_type_with_state` pattern chokepoint at once.
//
// CLASSIFICATION: GREEN twin pin (G4). Both legs return 7.
#[test]
fn ctor_value_and_pattern_position_prelude_provided_twin() {
    let leg_a = Cranelisp::new()
        .prelude(PRELUDE_WITH_ZED)
        .file(
            "user.cl",
            "(import [primitives [Pure]])\n\
             (import [prelude [ZedC]])\n\
             (defn main [] (Pure (match (ZedC 7) [(ZedC n) n])))",
        )
        .run("user.cl")
        .output();
    let leg_b = Cranelisp::new()
        .prelude(PRELUDE_WITH_ZED)
        .file(
            "user.cl",
            "(defn main [] (Pure (match (ZedC 7) [(ZedC n) n])))",
        )
        .run("user.cl")
        .output();
    leg_a.assert_exit(7);
    leg_b.assert_exit(7);
}

// =============================================================================
// 6. `super`-imported wrapper vs implicit prelude — the num.bits hygiene twin
//
// The blessed `stdlib/num/bits` hygiene (§8.6.4, the "standard-library
// consequence" para): a module DEFINES its own `bit-and` wrapper and
// FULLY-QUALIFIES `primitives/bit-and` in the body (a qualified USE is not a
// re-export). Its private `(mod- test)` submodule reaches the wrapper via
// `(import [super [bit-and]])` (§8.3.8). The bare name `bit-and` in the
// submodule then has ONE terminal — the parent's wrapper `bits/bit-and` —
// UNLESS the implicit prelude ALSO provides `bit-and` (a distinct terminal),
// in which case §8.6.5 poisons the bare name (globs are peers of specifics).
//
// The two legs below pin that the poison is a pure function of WHETHER the
// prelude provides the name:
//   * SPECIFIC prelude export (real stdlib shape) → no prelude terminal → clean
//   * GLOB prelude export (`[primitives [*]]`)    → prelude terminal → poison
// =============================================================================

// spec: spec/08-modules.md §8.6.4/§8.6.5 + §8.3.8 — a `(mod- test)` submodule
//   that `(import [super [bit-and]])`s a wrapper its PARENT defines MUST compile
//   clean when the prelude does NOT provide `bit-and`. The real stdlib prelude
//   SPECIFICALLY exports only [Int Bool Float String] and never the raw
//   primitive `bit-and`, so the super-import has the single terminal
//   `bits/bit-and` — no §8.6.5 collision, and `main` runs (12 & 10 = 8).
//
// GREEN regression guard. It pins the CORRECT behaviour that the live num.bits
// super-import defect breaks INTERMITTENTLY: against the full real stdlib the
// `prelude` module's LIVE table racily acquires a PHANTOM `bit-and →
// primitives/bit-and` binding it never exports (i.e. the specific-export prelude
// starts behaving like the glob-export `_neg` twin below), which then fires the
// §8.6.5 prelude-overlap poison SPURIOUSLY and fails `num.bits.test` with
// "ambiguous bare name 'bit-and' — provided by distinct sources
// 'num.bits/bit-and' and 'primitives/bit-and'". Reproduced live (racy, under the
// concurrent background file-index feed over the full stdlib); the deterministic
// WRITE trigger could NOT be reduced free-standing — this leg holds the correct
// pole and goes RED if the phantom write ever becomes deterministic here.
// FIXME(/dev): the phantom-prelude write is unlocalized. Only `bit-and` leaks
//   into `prelude`, never the identically-shaped `bit-or`/`bit-xor` wrappers, so
//   it is a concurrent mis-attribution — a bare `bit-and → primitives/bit-and`
//   edge written into the `prelude` module's table during the racy background
//   index of the full stdlib. Trace with CRANELISP_MODULE_TRACE over `stdlib/`.
//   The seam where the poison FIRES is src/imports.rs::insert_detecting_ambiguity
//   (prelude-overlap branch, ~L547-560, via `prelude_terminal`); the ROOT is the
//   WRITE into prelude's table, not the fire. Attribution owed to /qa.
// defect: class=enumeration-miss locus=src/imports.rs::insert_detecting_ambiguity found=S109 owner=/dev
#[test]
fn super_import_wrapper_over_specific_prelude_compiles_clean() {
    Cranelisp::new()
        .prelude("(export [primitives [Int Bool Float String]])\n")
        .file(
            "bits.cl",
            "(import [prelude []])\n\
             (import [primitives [Int Pure]])\n\
             (defn bit-and \"AND of a and b\" [:Int a :Int b] :Int (primitives/bit-and a b))\n\
             (defn main [] (Pure (bit-and 12 10)))\n\
             (mod- test)",
        )
        .file(
            "bits/test.cl",
            "(import [super [bit-and]])\n\
             (import [primitives [Int]])\n\
             (defn test-and [] :Int (bit-and 12 10))",
        )
        .run("bits.cl")
        .output()
        // CORRECT: the prelude does not provide `bit-and`, so the super-imported
        // wrapper is the sole terminal; the project compiles and `main` exits 8.
        .assert_exit(8);
}

// spec: spec/08-modules.md §8.6.5 + §8.3.8 — WHEN the prelude legitimately
//   provides `bit-and` (here via a glob `(export [primitives [*]])`, which
//   re-exports every raw primitive INCLUDING `bit-and`), a submodule that ALSO
//   `(import [super [bit-and]])`s its parent's DISTINCT wrapper has two distinct
//   terminals for the bare name — `prelude`→`primitives/bit-and` vs
//   `super`→`bits/bit-and` — and the name MUST be poisoned. The implicit prelude
//   glob is a PEER of the explicit super-import; there is no precedence tier.
//
// GREEN negative anchor. This is the deterministic twin of the guard above and
// the SEAM the num.bits defect abuses: it reproduces the EXACT real error
// signature, but here the prelude LEGITIMATELY provides `bit-and`, so the poison
// is spec-CORRECT. The defect is that the real (SPECIFIC-export) prelude fires
// this same poison SPURIOUSLY (see the twin's FIXME) — the difference between
// the two legs is exactly the phantom prelude binding.
#[test]
fn super_import_wrapper_collides_when_prelude_globs_primitive_neg() {
    let out = Cranelisp::new()
        .prelude("(export [primitives [*]])\n")
        .file(
            "bits.cl",
            "(import [prelude []])\n\
             (import [primitives [Int Pure]])\n\
             (defn bit-and \"AND of a and b\" [:Int a :Int b] :Int (primitives/bit-and a b))\n\
             (defn main [] (Pure (bit-and 12 10)))\n\
             (mod- test)",
        )
        .file(
            "bits/test.cl",
            "(import [super [bit-and]])\n\
             (import [primitives [Int]])\n\
             (defn test-and [] :Int (bit-and 12 10))",
        )
        .run("bits.cl")
        .output();
    let lower = format!("{}\n{}", out.stdout, out.stderr).to_lowercase();
    assert!(
        lower.contains("ambiguous"),
        "prelude-glob-provided `bit-and` + super-imported distinct wrapper MUST \
         poison the bare name (§8.6.5 distinct terminals);\nstdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr,
    );
    assert_ne!(
        out.status.code(),
        Some(8),
        "the poisoned bare name MUST NOT silently resolve to one terminal \
         (must not run to 8);\nstdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr,
    );
}
