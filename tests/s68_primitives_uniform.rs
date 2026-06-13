//! Sprint 68 — Primitives as uniform module + facade lockdown + FQTypeName
//! completion. /qa Phase 5 Stage 1 failing-tests authoring.
//!
//! These tests gate the simplification described in `sprints/SPRINT.md` and
//! pinned by `design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md`:
//!
//!   - `cranelisp-primitives` exposes `PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<Code, ()>>>`
//!     populated with raw `*const u8` fn ptrs at statically-known GOT slot indices.
//!   - Backend has NO Rust-path visibility into primitives' fns (see the
//!     dep-ban test in `crates/cranelisp-backend/tests/no_primitives_dep.rs`).
//!   - `ring0_jit_symbols()` retires; backend's `intrinsic_symbols()` shrinks
//!     to intrinsics-only enumeration.
//!   - `cranelisp-exe-bundle` retires its `pub use cranelisp_primitives::*`
//!     force-link incantation in favour of an explicit
//!     `cranelisp_init_primitives()` startup hook that forces
//!     `LazyLock::force(&PRIMITIVES_TABLE)`.
//!   - `not` is authored as a primitive per spec/appendix-a-builtins.md §A.3
//!     and Decision C1 — see `tests/spec_appendix_a_builtins.rs`
//!     (`primitive_not_true`, `primitive_not_false`).
//!   - `(trace ...)` in `--link` mode fails at link time per the
//!     spec/04-expressions.md §4.12.9 rework.
//!
//! All tests in this file are **failing-not-ignored** at S68 Phase 5 Stage 1
//! per `memory/feedback_failing_not_ignored.md`. Wave 2/3/4 of Phase 5
//! Stage 2 makes them green.
//!
//! Test numbering follows the /qa Phase 3 16-test plan referenced in
//! `sprints/SPRINT.md` §"Phase 3 — DELIVERED — /qa". Cross-file rows:
//!
//!   #1, #2  — `tests/spec_appendix_a_builtins.rs::primitive_not_true,_false`
//!             (pre-existing; spec annotations updated to cite Decision 0048).
//!   #4      — `crates/cranelisp-backend/tests/no_primitives_dep.rs`
//!             (next to the crate it polices).
//!   #16     — in this file (`s68_trace_in_link_mode_rejected_at_link_time`).
//!   #3, #5–#15 — in this file.

#![allow(dead_code)]

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};
use std::fs;
use std::path::PathBuf;

// =============================================================================
// Helpers
// =============================================================================

/// Workspace root from the test crate's `CARGO_MANIFEST_DIR`. The integration
/// tests in `tests/` are compiled as part of the workspace's root binary
/// crate (`cranelisp`); CARGO_MANIFEST_DIR points at the workspace root.
fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn read_cargo_toml(crate_dir: &str) -> String {
    let p = workspace_root().join("crates").join(crate_dir).join("Cargo.toml");
    fs::read_to_string(&p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()))
}

fn read_source(rel: &str) -> String {
    let p = workspace_root().join(rel);
    fs::read_to_string(&p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()))
}

fn repl_prims(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(lines)
        .output()
}

// =============================================================================
// #3 — Sentinel: `not` works through every mode TODAY (pre-S68).
//
// GREEN at authoring time and remains GREEN through Wave 4 (when force-link
// retires and is replaced by `cranelisp_init_primitives()`). The point of
// this test is to be a TRIPWIRE: if Wave 4 breaks `--link` mode dispatch
// for primitives during the force-link → init-hook transition, this test
// flips red. It is intentionally simple — `(not true)` exercises the
// primitives-dispatch path end-to-end in both REPL and `--link` modes.
// =============================================================================

// spec: spec/appendix-a-builtins.md §A.3 (not) +
//       design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md
//       §"The invariant" — primitives dispatch must remain functional
//       through the Wave 3/4 cutover. Sentinel; not failing-now.
#[test]
fn s68_not_primitive_works_in_link_mode_sentinel() {
    // `(not true) -> false`; in `--link` mode `main` must return an Int.
    // Use `(if (not true) 1 0)` to convert the Bool to a process exit code.
    let out = Cranelisp::new()
        .link_then_run("not_sentinel.cl")
        .file(
            "not_sentinel.cl",
            "(defn main [] (Pure (if (not true) 1 0)))",
        )
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .output();

    // Sentinel rationale: GREEN today via force-link `pub use cranelisp_primitives::*`;
    // GREEN post-S68 via `cranelisp_init_primitives()` + statically-constructed
    // PRIMITIVES_TABLE. If this test ever fails, the Wave 4 cutover regressed
    // the `--link`-mode primitives dispatch path.
    out.assert_exit(0);
}

// =============================================================================
// #5 — `PRIMITIVES_TABLE` is `LazyLock<Arc<SymbolTable<(), ()>>>`.
//
// Source-level structural assertion against the S73 severed-dependency shape.
// S73 (FIXME 0244) reverses the S68 `Code::Primitive` marker: with `code: None`
// everywhere, primitives never constructs a `Code` value, so it builds a
// `()`-flavoured table and drops the `cranelisp-backend` dependency entirely.
// `int` concretizes to `<Code, ()>` via `into_concrete` at the S74 session mount.
// =============================================================================

// spec: design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md §"Shape"
//       (A2 reversed; dep-ban → bidirectional severance per the S73 Phase 2
//       top-up) + design/arch/fixmes/0244-arch-revert-0048-a2-code-primitive-marker.md
//       §"Proposed resolution" (ratified S73 Phase 2) — the table is
//       `pub static PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<(), ()>>>`.
#[test]
fn s68_primitives_table_is_arc_symboltable_unit_unit() {
    let src = read_source("crates/cranelisp-primitives/src/lib.rs");

    // S73 target: the severed `<(), ()>` shape — no `Code` type param, because
    // primitives no longer names `cranelisp-backend` at all (FIXME 0244 + the
    // Phase 2 bidirectional-severance top-up). `int` concretizes to `<Code, ()>`
    // at the S74 mount via `into_concrete`, preserving the shared `Arc<GotTable>`.
    assert!(
        src.contains("PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<(), ()>>>"),
        "PRIMITIVES_TABLE MUST be typed `LazyLock<Arc<SymbolTable<(), ()>>>` per \
         FIXME 0244 + Decision 0048 §Shape (S73 severance). Current declaration in \
         crates/cranelisp-primitives/src/lib.rs does not match the target shape."
    );
}

// =============================================================================
// #6 — Sentinel: NO S68-touched crate retains a binding facade (all retired).
//
// Adjacent to #3. `tests/facade_compliance.rs` is the facade-compliance drift
// guard. Its premise NARROWED at S74 W4 (facade-compliance applies only to
// crates that still have a binding facade `.md`) and FULLY COLLAPSED at S75 W5c.
// As of S74 W3 the `primitives.md` and `intrinsics.md` facades RETIRED (joining
// `types.md`/`frontend.md`/`platform.md`/`typecheck.md`); at S75 W5b
// `backend.md` and `backend-cache.md` retired too — the LAST two binding
// facades. Once a facade is retired the crate's public surface is DEFINED by
// its source — `public-api.txt` + the compiler ARE the definition and the
// guard — so there is no facade left to comply WITH and nothing for a
// facade-compliance test to check. All eight crates are therefore
// INTENTIONALLY ABSENT from `tests/facade_compliance.rs`: not moved to a
// different check, dropped out. `facade_pairs()` is now an empty tombstone.
//
// This sentinel flips with that collapse (S75 W5c — mirroring exactly the S74
// primitives/intrinsics flip): the backend POSITIVE assertion ("backend stays
// in facade_pairs()") is REMOVED, and `cranelisp-backend` JOINS the
// MUST-BE-ABSENT set alongside `cranelisp-primitives` + `cranelisp-intrinsics`.
// Net: all three are asserted absent, locking in the retirement (so a refactor
// can't silently re-assert any retired contract). `int.md` remains binding but
// `int` is a binary crate with no `public-api.txt`, so it was never part of
// this grep check (it is covered by `facade_pif_rows.rs`).
// =============================================================================

// spec: design/arch/CLAUDE.md §"Baseline-diff discipline" — collapsed at S75 W5c
//       (/qa) when backend.md + backend-cache.md retired (the last two binding
//       facades, after S74's primitives.md + intrinsics.md): facade-compliance
//       now applies to NO crate; every retired-facade crate has source as its
//       canonical surface and is absent from the check. This is the S74 flip
//       extended to backend (the corrected, simpler form of the deleted FIXME
//       0218 — restating the source is not a contract check).
// Sentinel: NONE of the S68-touched crates carries a binding facade as of S75
// W5c, so none has a facade-compliance contract. This meta-row asserts
// primitives/intrinsics/backend are all ABSENT from `facade_pairs()` (the empty
// tombstone) — the positive proof all eight retirements hold.
#[test]
fn s68_facade_compliance_test_exists_for_s68_touched_crates() {
    let fc = read_source("tests/facade_compliance.rs");

    // The `facade_pairs()` grep anchor MUST still exist — it is retained as a
    // documented empty tombstone (returns `vec![]`) so this sentinel's
    // `split_once` survives the S75 W5c reduction. If a future refactor deletes
    // the function outright, this lookup fails loudly (the panic below).
    let pairs_block = fc
        .split_once("fn facade_pairs()")
        .and_then(|(_, after)| after.split_once("\nfn "))
        .map(|(body, _)| body)
        .unwrap_or_else(|| {
            panic!(
                "tests/facade_compliance.rs MUST define `facade_pairs()` — the \
                 binding-facade text-grep anchor (now an empty tombstone)."
            )
        });

    // primitives + intrinsics + backend: facades ALL RETIRED → source IS each
    // crate's canonical surface (public-api.txt + the compiler are the guard),
    // so none has a facade-compliance contract. None MUST appear in
    // `facade_pairs()`; their collective absence is the positive proof the
    // retirements hold (primitives/intrinsics retired S74 W3; backend +
    // backend-cache retired S75 W5b — `backend-cache` was a sub-facade of the
    // `cranelisp-backend` entry, so absence of `cranelisp-backend` covers both).
    // The backend POSITIVE assertion (was: backend MUST be present) is removed
    // at S75 W5c — backend's facade is retired, so it must no longer be
    // required present. This mirrors exactly the S74 primitives/intrinsics flip.
    for name in ["cranelisp-primitives", "cranelisp-intrinsics", "cranelisp-backend"] {
        assert!(
            !pairs_block.contains(name),
            "tests/facade_compliance.rs `facade_pairs()` MUST NOT list `{name}` \
             — its facade is retired (primitives/intrinsics S74 W3; backend + \
             backend-cache S75 W5b), so source is its canonical surface and \
             there is nothing for a facade-compliance test to check. It is \
             intentionally absent from facade_compliance.rs (all eight facades \
             retired; `facade_pairs()` is an empty tombstone)."
        );
    }
}

// =============================================================================
// #7 — `ring0_jit_symbols()` is retired.
//
// Failing-now-fail-until-impl-lands. Wave 3 (primitives side) deletes the
// free fn; Wave 4 (backend side) stops consuming it.
// =============================================================================

// spec: design/arch/fixmes/0182-*.md — `ring0_jit_symbols()` retirement;
//       Decision 0048 §Consequences — "ring0_jit_symbols() retires".
#[test]
fn s68_ring0_jit_symbols_free_fn_is_retired() {
    let primitives_lib = read_source("crates/cranelisp-primitives/src/lib.rs");

    // Failing-now: the `pub use ring0::ring0_jit_symbols;` re-export still
    // appears in primitives lib.rs. Will pass once Wave 3 deletes the fn
    // body in ring0.rs and the re-export from lib.rs.
    assert!(
        !primitives_lib.contains("pub use ring0::ring0_jit_symbols"),
        "`ring0_jit_symbols` MUST NOT be re-exported from \
         crates/cranelisp-primitives/src/lib.rs per FIXME 0182 + Decision 0048. \
         The free fn body and its re-export both retire in Wave 3."
    );

    // Strong form: the fn name should not appear in the primitives source
    // tree at all (other than possibly in retired-comments).
    let ring0_rs = read_source("crates/cranelisp-primitives/src/ring0.rs");
    assert!(
        !ring0_rs.contains("pub fn ring0_jit_symbols"),
        "`ring0_jit_symbols` MUST be deleted from \
         crates/cranelisp-primitives/src/ring0.rs per FIXME 0182. \
         The replacement is the statically-constructed PRIMITIVES_TABLE."
    );
}

// =============================================================================
// #8 — `cranelisp_init_primitives()` exists in exe-bundle.
//
// Failing-now. Wave 3 (int slice — exe-bundle is its delivery target) adds
// the explicit `LazyLock::force(&PRIMITIVES_TABLE)` startup hook called
// from `cranelisp_init_platform`. Replaces the implicit `pub use` force-link.
// =============================================================================

// spec: Decision 0048 §Cascade — "cranelisp-exe-bundle's force-link `pub use`
//       lines retire; replaced by an explicit `cranelisp_init_primitives()`
//       no-op that forces `LazyLock::force(&PRIMITIVES_TABLE)` at startup".
//       /arch recommendation in `sprints/SPRINT.md` Phase 2 outcomes.
#[test]
fn s68_exe_bundle_publishes_cranelisp_init_primitives_hook() {
    let lib = read_source("crates/cranelisp-exe-bundle/src/lib.rs");

    // Failing-now: the explicit startup hook is not yet authored. Will pass
    // when Wave 3 adds `pub extern "C" fn cranelisp_init_primitives()` and
    // wires it from `cranelisp_init_platform`.
    assert!(
        lib.contains("pub extern \"C\" fn cranelisp_init_primitives"),
        "cranelisp-exe-bundle MUST publish `pub extern \"C\" fn cranelisp_init_primitives` \
         per Decision 0048 §Cascade (Wave 3). The explicit LazyLock::force hook \
         replaces the implicit force-link `pub use cranelisp_primitives::*` incantation."
    );

    // Negative: the force-link `pub use cranelisp_primitives::*` re-exports
    // must NOT survive Wave 3 (they exist today and retire in Wave 3).
    // Spot-check three of the most distinctive `pub use` lines.
    for forced in [
        "pub use cranelisp_primitives::bool;",
        "pub use cranelisp_primitives::int;",
        "pub use cranelisp_primitives::marshal;",
    ] {
        assert!(
            !lib.contains(forced),
            "exe-bundle MUST NOT carry the force-link line `{forced}` post-S68 — \
             the explicit `cranelisp_init_primitives()` hook replaces it \
             per Decision 0048 §Cascade."
        );
    }
}

// =============================================================================
// #9 — Backend `intrinsic_symbols()` enumerates ONLY intrinsics.
//
// Failing-now-fail-until-impl-lands. Backend's current `intrinsic_symbols()`
// contains direct Rust-path references to `cranelisp_primitives::*`. Wave 4
// deletes them all and removes the `cranelisp-primitives` dep line from
// `crates/cranelisp-backend/Cargo.toml`. The dep-ban test (#4 in
// `crates/cranelisp-backend/tests/no_primitives_dep.rs`) is the structural
// half; this test is the source-side companion that asserts the
// `cranelisp_primitives::*` paths are deleted.
// =============================================================================

// spec: design/arch/fixmes/0191-*.md — `intrinsic_symbols()` primitives entries
//       retirement + backend dep-ban source cleanup; Decision 0048 §"Structural
//       invariant — backend dep-ban" (S73 Phase 2: → bidirectional severance).
//       This is the DEFERRED backend-side work: the `intrinsic_symbols()` shrink
//       and the backend Cargo.toml dep-line removal are the future backend sprint
//       (FIXME 0191) — backend is UNTOUCHED this sprint. The body's source-grep
//       assertions are kept intact so they re-enable when the backend sprint
//       lands the dep-ban cleanup.
#[ignore = "backend sprint — Code::Primitive deletion deferred; FIXME 0221/0191"]
#[test]
fn s68_backend_intrinsic_symbols_drops_primitives_paths() {
    let jit = read_source("crates/cranelisp-backend/src/jit.rs");

    // Failing-now: the file currently uses `cranelisp_primitives::PRIMITIVES_TABLE`
    // and references `ring0_jit_symbols`. Wave 4 deletes all such references.
    assert!(
        !jit.contains("cranelisp_primitives"),
        "crates/cranelisp-backend/src/jit.rs MUST NOT name `cranelisp_primitives` \
         per Decision 0048 §dep-ban (Wave 4). All references retire in the same \
         change-set that removes the dep line from backend's Cargo.toml."
    );

    // Companion: `primitives_inline.rs` may keep its inlined Ring 0 ops
    // (they emit raw Cranelift IR, never touch the symbol table) but
    // MUST NOT name the primitives crate by path either.
    let inline = read_source("crates/cranelisp-backend/src/primitives_inline.rs");
    assert!(
        !inline.contains("cranelisp_primitives::"),
        "crates/cranelisp-backend/src/primitives_inline.rs MUST NOT name \
         `cranelisp_primitives::*` per Decision 0048 §dep-ban (Wave 4)."
    );
}

// =============================================================================
// #10 — `Code` enum carries the `Code::Primitive` marker variant.
//
// Failing-now. Wave 2 (backend additive prep, serial gate) lands the variant
// before Wave 3 can construct entries with `code = Some(Code::Primitive)`.
// =============================================================================

// spec: design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md
//       §"Shape" — A2 (`Code::Primitive` marker) REVERSED by FIXME 0244 (S73
//       Phase 2). The S73 *target* is the variant DELETED from `code.rs`, but
//       that deletion is the deferred backend sprint (FIXME 0221) — backend is
//       UNTOUCHED this sprint (the variant still exists). This test's body
//       asserts the variant's presence (the pre-deletion state); it is ignored
//       until the backend sprint deletes the variant, at which point the body
//       flips to asserting absence and is re-enabled.
#[ignore = "backend sprint — Code::Primitive deletion deferred; FIXME 0221/0191"]
#[test]
fn s68_code_enum_has_primitive_marker_variant() {
    let src = read_source("crates/cranelisp-backend/src/code.rs");

    // Failing-now: at authoring time the `Code` enum has only `Jit { … }`
    // and `Linker { … }` variants. Wave 2 adds `Primitive` as a no-payload
    // marker (full word per user direction; not abbreviated to `Prim`).
    assert!(
        src.contains("Primitive,") || src.contains("Primitive ,") || src.contains("Primitive\n"),
        "Code enum MUST carry a `Primitive` marker variant per Decision 0048 §Shape \
         (S68 Phase 3 amendment, 2026-05-17 user revision). Variant carries no payload — \
         it expresses the process-static lifecycle category only. \
         crates/cranelisp-backend/src/code.rs must include `Primitive` alongside \
         `Jit {{ ... }}` and `Linker {{ ... }}`."
    );
}

// =============================================================================
// #11 — Primitives' `ModuleEntry::Def` entries carry `code: None`; primitive-
// ness is read from `kind: DefKind::Primitive`.
//
// S73 (FIXME 0244) reverses the S68 `Code::Primitive` marker. Entries are built
// via `ModuleEntry::def(scheme, DefKind::Primitive)...build()` — the builder
// default `code: None` is now *correct*, and primitive-ness reads from the
// canonical `kind: DefKind::Primitive` (no marker smuggled into the lifecycle
// `code` field). The `Code::Primitive` *variant deletion* in backend's code.rs
// is the deferred backend sprint (see #10) — but primitives no longer names
// `Code` at all, so it constructs no marker regardless.
// =============================================================================

// spec: design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md §"Shape"
//       (A2 reversed; A1b `code: None` accepted) +
//       design/arch/fixmes/0244-arch-revert-0048-a2-code-primitive-marker.md
//       §"Proposed resolution" (ratified S73 Phase 2) — every primitives
//       `ModuleEntry::Def` carries `code: None` via the builder default;
//       primitive-ness is `matches!(kind, DefKind::Primitive)`.
#[test]
fn s68_primitives_entries_carry_code_none_kind_primitive() {
    let src = read_source("crates/cranelisp-primitives/src/lib.rs");

    // S73 target: entries are built through the `ModuleEntry::def` builder
    // with `DefKind::Primitive`, never naming `Code` (FIXME 0244 severance).
    // The builder's `code: None` default is the lifecycle value; primitive-ness
    // is the `kind` fact, not a `code` marker.
    assert!(
        src.contains("ModuleEntry::def(scheme, DefKind::Primitive)"),
        "crates/cranelisp-primitives/src/lib.rs MUST construct entries via \
         `ModuleEntry::def(scheme, DefKind::Primitive)...build()` per FIXME 0244 \
         (S73). The builder default `code: None` is the lifecycle value; \
         primitive-ness reads from `kind: DefKind::Primitive`."
    );

    // Negative companion: the reverted `Code::Primitive` marker MUST NOT be
    // constructed anywhere in the primitives source — primitives names no
    // `Code` value post-severance (FIXME 0244 + the Phase 2 bidirectional
    // severance top-up). Check CODE only: the module docs legitimately mention
    // `Code::Primitive` to document that the marker is retired, so strip the
    // `//`-comment portion of each line before scanning (else the prose that
    // explains the absence trips the absence check).
    let names_marker_in_code = src
        .lines()
        .map(|l| l.split("//").next().unwrap_or(l))
        .any(|code| code.contains("Code::Primitive"));
    assert!(
        !names_marker_in_code,
        "crates/cranelisp-primitives/src/lib.rs MUST NOT name `Code::Primitive` \
         in code post-S73 — the marker is reverted (FIXME 0244) and primitives no \
         longer depends on `cranelisp-backend` (bidirectional severance)."
    );
}

// =============================================================================
// FQTypeName boundary tests (#12 — #15)
//
// Per `sprints/SPRINT.md §"In-scope (FQTypeName completion)"`, the audit at
// the four S68-touched crate edges (primitives, intrinsics, int, platform)
// migrates bare `TypeName` at resolved-stage API boundaries to `FQTypeName`.
//
// Pre-sprint audit confirmed:
//   - cranelisp-primitives: 0 hits (no TypeName at boundary)
//   - cranelisp-intrinsics: 0 hits (no TypeName at boundary)
//   - cranelisp-platform:   0 hits (per /design (platform) Phase 3 audit)
//   - src/ (int binary):    some TypeName uses remain (see audit grep
//                            in this conversation's Phase 3 reply)
//
// The two named exceptions in `facades/types.md` (reverse-lookup;
// receiver-pinned) are respected — the tests below are written against
// resolved-stage API boundaries only.
// =============================================================================

// =============================================================================
// REMOVED 2026-05-17 (S68 Wave 4 post-mortem)
//
// Three tests removed:
//   - s68_fqtypename_int_exe_io_adt_boundary
//   - s68_fqtypename_int_pipeline_io_adt_boundary
//   - s68_fqtypename_int_platform_io_adt_boundary
//
// Rationale: their target (`src/` binary) has no public API; the facade rule
// from Decision 0047 doesn't apply at the level they were checking. The bare
// `TypeName::from("IO")` at the previously-flagged sites is a CONSTRUCTOR
// ARGUMENT inside `FQTypeName::new(ModuleFullPath::from("primitives"),
// TypeName::from("IO"))` — exactly the lift-site pattern Decision 0047
// explicitly PERMITS (bare-`TypeName`-in / `FQTypeName`-out). The original
// tests confused a constructor argument for a free-standing bare-`TypeName`
// violation. `src/` is a binary, not a library: it publishes no `public-api.txt`
// surface against which the boundary rule can be enforced. The corresponding
// PLAN.md rows (12–14) move to "removed — non-applicable target" disposition.
// =============================================================================

// spec: design/arch/decisions/0047-fqtypename-binding-at-resolved-stage-boundaries.md
//       + design/arch/facades/types.md §"FQTypeName" (per-crate disposition).
// Shape A: scan the published cargo-public-api baseline rather than source text.
// The baseline is the as-built record of the crate's edge; if a bare `TypeName`
// appears in a `pub fn` parameter or return position, the facade contract is
// violated. `FQTypeName` is a distinct identifier whose substring contains
// `TypeName`, so we strip those before checking.
#[test]
fn s68_fqtypename_backend_uses_fqtypename_at_resolved_edges() {
    let api = read_source("crates/cranelisp-backend/public-api.txt");

    let mut offenders: Vec<&str> = Vec::new();
    for line in api.lines() {
        if !line.contains("pub fn") {
            continue;
        }
        // Mask FQTypeName so the bare TypeName check doesn't match it.
        let masked = line.replace("FQTypeName", "##FQTN##");
        if masked.contains("TypeName") {
            offenders.push(line);
        }
    }

    assert!(
        offenders.is_empty(),
        "cranelisp-backend's published fn signatures at resolved-stage edges \
         MUST use FQTypeName, not bare TypeName, per Decision 0047 + \
         facades/types.md §\"FQTypeName\". Offending lines in \
         crates/cranelisp-backend/public-api.txt:\n{}",
        offenders.join("\n"),
    );
}

// =============================================================================
// #16 — `(trace ...)` in `--link` mode rejected at LINK time.
//
// Failing-now state is the wording match: this test asserts the test's own
// failure-mode language matches the new spec/04-expressions.md §4.12.9
// wording landed by /spec this sprint (Phase 3, FIXME 0209 deletion):
//
//   > the form is rejected at **link time**: the trace runtime is not included
//   > in the staticlib produced for standalone binaries, so a program that
//   > reaches a `(trace ...)` form when built with `--link` will fail with
//   > an unresolved-symbol error from the system linker
//   > (e.g. `cranelisp_collect_trace` undefined). No compile-time pre-pass
//   > is required; the link-time failure is the architectural enforcement.
//
// Per Decision 0040 (Path B1 — FULL DELETION of trace.rs/io_trace.rs from
// the staticlib; user-arbitrated 2026-05-16), the trace symbols are absent
// from `libcranelisp_exe_bundle.a`, so the linker step itself produces an
// "undefined symbol" error.
//
// Failing-now-fail-until-impl-lands: today, depending on the state of trace
// retirement, this may fail with a compile-time message rather than a
// link-time message. The new spec wording is link-time-only; this test is
// the regression guard for that contract.
// =============================================================================

// spec: spec/04-expressions.md §4.12.9 (post-S68 rework — FIXME 0209
//       resolution); design/arch/decisions/0040-runtime-trace-io-trace-relocate-to-int.md
//       (Path B1 full-deletion amendment).
#[test]
fn s68_trace_in_link_mode_rejected_at_link_time() {
    let out = Cranelisp::new()
        .link("trace_link.cl")
        .file(
            "trace_link.cl",
            "(defn main [] (trace 42))",
        )
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .output();

    // Must fail. Either at link time (post-S68 target shape) or with a
    // clear compile-time diagnostic naming `--link` (the pre-rework state).
    assert!(
        !out.status.success(),
        "`(trace ...)` in --link mode MUST be rejected per spec/04-expressions.md §4.12.9. \
         status={:?}, stdout={}, stderr={}",
        out.status, out.stdout, out.stderr,
    );

    let combined = format!("{}{}", out.stdout, out.stderr);

    // Post-rework target: the failure surfaces as a linker "undefined symbol"
    // error naming a trace-runtime symbol (e.g. `cranelisp_collect_trace`).
    // The §4.12.9 wording is explicit: "fail with an unresolved-symbol error
    // from the system linker (e.g. `cranelisp_collect_trace` undefined)".
    //
    // Pre-rework / current state: the failure may surface as a compile-time
    // diagnostic instead. That's an acceptable transition state ONLY while
    // Wave 4 lands the trace-runtime removal. Phase 7 close requires this
    // assertion to pass without the compile-time-only fallback.
    let link_time = combined.contains("undefined")
        || combined.contains("unresolved")
        || combined.contains("cranelisp_collect_trace")
        || combined.contains("trace");

    assert!(
        link_time,
        "`(trace ...)` in --link mode MUST fail with a link-time \"undefined symbol\" \
         error naming a trace-runtime symbol per spec/04-expressions.md §4.12.9 \
         (post-S68 rework). The new wording explicitly cites \
         `cranelisp_collect_trace undefined` as the canonical failure mode. \
         status={:?}, stdout={}, stderr={}",
        out.status, out.stdout, out.stderr,
    );
}
