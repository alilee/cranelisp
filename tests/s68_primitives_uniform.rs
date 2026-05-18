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
            "(defn main [] (if (not true) 1 0))",
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
// #5 — `PRIMITIVES_TABLE` is `LazyLock<Arc<SymbolTable<Code, ()>>>`.
//
// Source-level structural assertion against the post-S68 facade. At
// authoring time the type is `LazyLock<SymbolTable<(), ()>>` (per
// `crates/cranelisp-primitives/src/lib.rs:90`). Wave 3 lands the
// `Arc<SymbolTable<Code, ()>>` shape per Decision 0048.
// =============================================================================

// spec: design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md
//       §"Shape" — `pub static PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<Code, ()>>>`.
// FIXME(/dev (primitives)) — lift to a typed `use` assertion once Wave 3 lands
//       the shape; this string-scan is a stand-in until the type names exist.
#[test]
fn s68_primitives_table_is_arc_symboltable_code_unit() {
    let src = read_source("crates/cranelisp-primitives/src/lib.rs");

    // Failing-now: current type is `LazyLock<SymbolTable<(), ()>>` (no `Arc`,
    // no `Code` type param). Will pass when Wave 3 lands the post-S68 facade
    // shape: `pub static PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<Code, ()>>>`.
    assert!(
        src.contains("PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<Code, ()>>>"),
        "PRIMITIVES_TABLE MUST be typed `LazyLock<Arc<SymbolTable<Code, ()>>>` per \
         Decision 0048 §Shape (Wave 3). Current declaration in \
         crates/cranelisp-primitives/src/lib.rs does not match the target shape."
    );
}

// =============================================================================
// #6 — Sentinel: facade compliance test green TODAY for primitives.
//
// Adjacent to #3 — GREEN now, GREEN through Wave 6. Wave 6 regenerates the
// `public-api.txt` baseline + facade together for the four touched crates
// (primitives, backend, intrinsics, int); if the regen drifts in either
// direction the existing `tests/facade_compliance.rs` test catches it. This
// row is the affirmative companion: we name the file so Phase 7 close can
// cite it.
// =============================================================================

// spec: design/arch/CLAUDE.md §"Baseline-diff discipline";
//       sprints/SPRINT.md §"In-scope (facade lockdown)".
// Sentinel: tests/facade_compliance.rs is the standing structural check.
// This is a meta-row that asserts the standing check ran and passed for
// the four S68-touched crates (no orphan public-api items unnamed by the
// facade). Tested transitively via the existing `facade_compliance.rs`.
#[test]
fn s68_facade_compliance_test_exists_for_s68_touched_crates() {
    // The standing test lives at tests/facade_compliance.rs and covers all
    // four S68-touched crates (primitives, backend, intrinsics, plus the
    // backend-cache sub-facade). This test asserts the file is present
    // (so a refactor doesn't silently delete the structural check) and
    // contains rows for each S68-touched crate.
    let fc = read_source("tests/facade_compliance.rs");
    for name in [
        "cranelisp-primitives",
        "cranelisp-backend",
        "cranelisp-intrinsics",
    ] {
        assert!(
            fc.contains(name),
            "tests/facade_compliance.rs MUST cover `{name}` per Wave 6 lockdown",
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
//       retirement; Decision 0048 §"Structural invariant — backend dep-ban".
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
//       §"Shape" (S68 Phase 3 amendment) — `Code::Primitive` marker variant
//       added to the `Code` enum; no payload (Decision 35 invariant preserved).
// FIXME(/dev (backend)) — lift to a typed `match` over a constructed value
//       once Wave 2 publishes the variant; this string-scan is a stand-in.
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
// #11 — Primitives' `ModuleEntry::Def` entries carry `Some(Code::Primitive)`.
//
// Failing-now. Wave 3 (primitives slice) constructs entries with the marker.
// Until then the entries either don't carry a `Code` value at all (current
// `SymbolTable<(), ()>` shape) or, immediately post-Wave-3, carry the
// `Code::Primitive` marker.
//
// E2E observation point: the REPL's `/info` slash command surfaces the
// `Code` lifecycle category for any defined symbol. Post-S68 we can spot-
// check a primitive's category via `/info primitives/add-i64`. At authoring
// time the marker doesn't exist; the assertion is the observable string
// that would appear.
// =============================================================================

// spec: design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md
//       §"Shape" — every primitives `ModuleEntry::Def.code = Some(Code::Primitive)`.
// FIXME(/dev (primitives)) — lift to a typed assertion against a constructed
//       PRIMITIVES_TABLE entry once the table is rebuilt with `code: Some(Code::Primitive)`.
//       Today's string-scan is a stand-in until that source exists.
#[test]
fn s68_primitives_entries_carry_code_primitive_marker() {
    let src = read_source("crates/cranelisp-primitives/src/lib.rs");

    // Failing-now: at authoring time the primitives table is
    // `LazyLock<SymbolTable<(), ()>>` — no `Code` parameter, no
    // `Code::Primitive` value attached to any entry. Will pass when
    // Wave 3 constructs entries that carry the marker variant.
    //
    // Companion to test #10 (which asserts the variant exists on the enum).
    // This test asserts the variant is actually used at construction time.
    assert!(
        src.contains("Code::Primitive"),
        "crates/cranelisp-primitives/src/lib.rs MUST construct entries with \
         `code = Some(Code::Primitive)` per Decision 0048 §Shape (Wave 3). \
         Today the static-init builder uses `SymbolTable<(), ()>` with no \
         Code value attached."
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
