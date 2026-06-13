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
// notes). Under the CURRENT flattened-table + `is_seeded` model:
//   * Tests that exercise explicit-import-SHADOWS a prelude-provided name
//     are RED: the flattened model poisons the colliding bare name instead
//     of letting the explicit import win. These stay failing-not-ignored
//     until /dev lands the outer-scope fallback (deletes `is_seeded`).
//   * Refusal, selective-import, ambiguity, and primitives-via-prelude in
//     `--run` mode already behave correctly under the current model and
//     stand as GREEN behaviour-preservation guards (they must stay green
//     after `is_seeded` deletes).
//
// Test prelude shape: every test writes its own `prelude.cl` into the
// per-test project root (which shadows stdlib per §8.8.2). The prelude does
// `(export [primitives [*]])` so primitive names flow as bare names through
// the implicit glob, and defines `gulp` as a sentinel prelude-provided name
// to shadow / refuse / collide against.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;

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

// spec: design/int/s78-entry-module.md §2 — a local `defn` of a name the
//   prelude also provides silently shadows the prelude binding. NO ambiguity
//   error; the local definition wins.
//
// CLASSIFICATION: GREEN. The directly-defined-takes-priority branch already
// holds under the current model (a local def over an indirect prelude entry
// is not poisoned). This guards that the local-shadows-prelude path survives
// `is_seeded` deletion.
#[test]
fn local_defn_silently_shadows_prelude() {
    // prelude `gulp` is (+1); local `gulp` is (+100). Local must win → 105.
    Cranelisp::new()
        .prelude(PRELUDE_WITH_GULP)
        .file(
            "user.cl",
            "(defn gulp [x] (add-i64 x 100))\n(defn main [] (Pure (gulp 5)))",
        )
        .run("user.cl")
        .output()
        .assert_exit(105);
}

// spec: design/int/s78-entry-module.md §2 — a local `defn` shadowing a
//   prelude name MUST NOT raise an ambiguity / duplicate error.
//
// CLASSIFICATION: GREEN (negative guard companion to the above).
#[test]
fn local_defn_shadows_prelude_neg_no_ambiguity_error() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_WITH_GULP)
        .file(
            "user.cl",
            "(defn gulp [x] (add-i64 x 100))\n(defn main [] (Pure (gulp 5)))",
        )
        .run("user.cl")
        .output();
    let lower = out.stderr.to_lowercase();
    assert!(
        !lower.contains("ambiguous")
            && !lower.contains("conflict")
            && !lower.contains("duplicate"),
        "local shadow of a prelude name MUST NOT raise ambiguity/conflict/duplicate; \
         stderr=\n{}",
        out.stderr
    );
    out.assert_exit(105);
}

// spec: design/int/s78-entry-module.md §2 — an EXPLICIT import of a name the
//   prelude also provides silently shadows the prelude binding; the explicit
//   import wins, with NO ambiguity error.
//
// CLASSIFICATION: GREEN (was RED-by-design until the outer-scope reshape
// landed). The outer-scope model makes prelude an OUTER scope, so the inner
// explicit `libc/gulp` import is the sole inner-table entry and wins — no
// poisoning. `(gulp 5)` = (add-i64 5 100) = 105.
//
// NOTE the body is `+100 → 105` (NOT `+1000 → 1005`): a POSIX process exit
// code is a u8 (0–255), so `1005` truncates to `1005 % 256 == 237` and could
// never match `assert_exit(1005)`. 105 fits in a u8 and matches the sibling
// `local_defn_silently_shadows_prelude`, so the exit code transports the
// shadow result faithfully. (FIXME 0313 issue 2.)
#[test]
fn explicit_glob_import_silently_shadows_prelude() {
    Cranelisp::new()
        .prelude(PRELUDE_WITH_GULP)
        .file("libc.cl", "(defn gulp [x] (add-i64 x 100))")
        .file(
            "user.cl",
            "(import [libc [*]])\n(defn main [] (Pure (gulp 5)))",
        )
        .run("user.cl")
        .output()
        .assert_exit(105);
}

// spec: design/int/s78-entry-module.md §2 — an explicit SPECIFIC import of a
//   prelude-provided name silently shadows the prelude binding.
//
// CLASSIFICATION: GREEN (was RED-by-design). The explicit specific import
// wins under the outer-scope model. `(gulp 5)` = 105. Body is `+100` (not
// `+1000`) for the u8-exit-code reason above (FIXME 0313 issue 2).
#[test]
fn explicit_specific_import_silently_shadows_prelude() {
    Cranelisp::new()
        .prelude(PRELUDE_WITH_GULP)
        .file("libc.cl", "(defn gulp [x] (add-i64 x 100))")
        .file(
            "user.cl",
            "(import [libc [gulp]])\n(defn main [] (Pure (gulp 5)))",
        )
        .run("user.cl")
        .output()
        .assert_exit(105);
}

// spec: design/int/s78-entry-module.md §2 — when an explicit import shadows a
//   prelude name, the SHADOWING binding (not the prelude one) is the bare
//   resolution. Asserts the explicit import's behaviour is observed, and no
//   ambiguity error appears.
//
// CLASSIFICATION: GREEN (was RED-by-design). Companion negative guard to
// `explicit_glob_import_silently_shadows_prelude`: the explicit import shadow
// MUST NOT raise an ambiguity error, and the shadowing binding (libc's `+100`)
// is the observed bare resolution. Body is `+100 → 105` for the u8-exit-code
// reason above (FIXME 0313 issue 2).
#[test]
fn explicit_import_shadows_prelude_neg_no_ambiguity_error() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_WITH_GULP)
        .file("libc.cl", "(defn gulp [x] (add-i64 x 100))")
        .file(
            "user.cl",
            "(import [libc [*]])\n(defn main [] (Pure (gulp 5)))",
        )
        .run("user.cl")
        .output();
    assert!(
        !out.stderr.to_lowercase().contains("ambiguous"),
        "explicit import shadowing a prelude name MUST NOT poison the bare name \
         as ambiguous; stderr=\n{}",
        out.stderr
    );
    out.assert_exit(105);
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
