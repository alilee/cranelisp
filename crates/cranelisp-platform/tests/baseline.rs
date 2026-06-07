// sprint71_platform_baseline.rs — Sprint 71 Wave 1 (Phase 5 Stage 1).
//
// T23 of `tests/plan/sprint71-platform.md` — the lone workspace-integration
// test /qa authors this sprint. Verifies that the Sprint 71 `cranelisp-
// platform` surface bump is visible in BOTH the source const and the
// committed `cargo-public-api` baseline; the two-update discipline per
// `design/arch/CLAUDE.md` §"Baseline-diff discipline (Sprint 67 close)"
// gates every edge change behind a single change-set that updates source
// + baseline together.
//
// Failing-first per `memory/feedback_failing_not_ignored.md`:
//   - source `pub const ABI_VERSION: u32 = 1;` today → Wave 2 bumps to 2 (A4 ruling)
//   - baseline does not enumerate `CLAdt` / `CLAdtType` / `AnyAdt` / `Schema`
//     / `alloc_with_tag` / `validate_schema` today → Wave 2 lands the new
//     surface + regenerates the baseline.
//
// The test asserts the second-half-discipline of the baseline-diff rule:
// the source bump (`ABI_VERSION` 1 → 2) and the matching baseline regen
// land in the SAME change-set. A green test means Wave 2 honoured both
// halves; a red test means one of the two updates was skipped.
//
// Test is workspace-integration (Layer 3 in the legacy four-layer model,
// per-tier-2 "no middle" classification in `tests/CLAUDE.md` would mark
// it e2e-or-unit; this is one of the explicitly-justified workspace-
// integration exceptions for facade/baseline discipline alongside
// `facade_compliance.rs`, `facade_pif_rows.rs`, `public_api_relocations.rs`,
// and `s68_primitives_uniform.rs`). Per `tests/plan/sprint71-platform.md`
// §4, this is the ONLY workspace-integration test /qa authors this
// sprint; the rest of the new ADT-traversal surface is tested by /dev
// platform's unit + crate-integration tests inside the crate.

use std::fs;
use std::path::PathBuf;

fn crate_root() -> PathBuf {
    // CARGO_MANIFEST_DIR is the crate dir when this test lives under
    // crates/cranelisp-platform/tests/ (Option A relocation from
    // workspace tests/ per Sprint 71 Wave 2).
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn read_source(rel: &str) -> String {
    let path = crate_root().join(rel);
    fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!("could not read {}: {}", path.display(), e);
    })
}

// spec: sprints/SPRINT.md §"Architecture inside cranelisp-platform (target
// this sprint)" item 1 (`ABI_VERSION: u32` constant bump) +
// §"Architecture inside cranelisp-platform" item 2 (`CLAdt<T>` joining the
// CLInt/CLBool/CLFloat/CLString family) + §"Architecture inside
// cranelisp-platform" item 3 (`HostCallbacks` grows by two fn-pointer
// fields) + arbitration A4 (ABI_VERSION bump policy). Cross-ref:
// `design/arch/CLAUDE.md` §"Baseline-diff discipline (Sprint 67 close)" —
// the two-update rule this test enforces.
//
// T23 per tests/plan/sprint71-platform.md row T23.
#[test]
fn sprint71_abi_version_baseline_co_regen() {
    // (1) Source-side: ABI_VERSION must read `= 3;` after the FIXME 0286 bump
    //     (the three-exports macro rework).
    let lib_rs = read_source("src/lib.rs");
    assert!(
        lib_rs.contains("pub const ABI_VERSION: u32 = 3;"),
        "expected `pub const ABI_VERSION: u32 = 3;` in \
         crates/cranelisp-platform/src/lib.rs (FIXME 0286: the three-exports \
         macro rework bumps the ABI from 2 to 3). If you see this failure the \
         source change was skipped or reverted."
    );

    // (2) Baseline-side: the `public-api.txt` baseline must enumerate the
    //     new surface that lands in the same change-set as the ABI bump
    //     (CLAdt + marker types + Schema parser + new HostCallbacks fields).
    //     Failing-first: today the baseline lists none of these.
    //
    // We assert representative names rather than exhaustive lines because
    // cargo-public-api's exact emission shape for generics/lifetimes can
    // change between toolchains (`--simplified` doesn't fix line-shape
    // across nightly versions). The names below are stable identifiers
    // designed to survive `--simplified` formatting drift while still
    // failing loudly if the baseline regen was skipped.
    let baseline = read_source("public-api.txt");

    // ABI_VERSION line itself — currently present (value not emitted by
    // --simplified), kept here as the structural anchor row. Catches the
    // pathological case where someone deletes the const entirely without
    // regenerating.
    assert!(
        baseline.contains("pub const cranelisp_platform::ABI_VERSION: u32"),
        "expected `pub const cranelisp_platform::ABI_VERSION: u32` in \
         crates/cranelisp-platform/public-api.txt — baseline missing the \
         ABI_VERSION row entirely. Regenerate via `cargo +nightly public-api \
         > crates/cranelisp-platform/public-api.txt`."
    );

    // New ADT-traversal surface — these names are the Wave 2 acceptance
    // criterion per `design/platform/sprint71-redesign.md` §3 and the
    // SPRINT.md Wave 2 work list. Each name MUST appear at least once in
    // the regenerated baseline; if not, the baseline regen was skipped.
    // Names refined Wave 2 against the actual landed surface
    // (cargo-public-api emission shape — fields are emitted as
    // `cranelisp_platform::HostCallbacks::alloc_with_tag` rather than
    // top-level; the null-callback placeholders are at the crate root).
    // Surface after the FIXME 0286 rework: CLAdt + CLAdtType stay; Schema /
    // SchemaParseError stay (parser repointed at the generated artifact);
    // set_global_schema + GOT_TABLE_SIZE join (the embed + GOT export surface).
    // AnyAdt / GetSchema retired (the marker-type DSL). validate_schema /
    // null_validate_schema stay transitionally (removed with the int consumers
    // by FIXME 0288).
    let required_new_exports: &[&str] = &[
        "cranelisp_platform::CLAdt",
        "cranelisp_platform::CLAdtType",
        "cranelisp_platform::Schema",
        "cranelisp_platform::SchemaParseError",
        "cranelisp_platform::set_global_schema",
        "cranelisp_platform::GOT_TABLE_SIZE",
        "cranelisp_platform::extract_layout_hash",
        "HostCallbacks::alloc_with_tag",
        "cranelisp_platform::null_alloc_with_tag",
    ];
    // Retired surface MUST be absent — the marker-type DSL.
    let must_be_absent: &[&str] = &[
        "cranelisp_platform::AnyAdt",
        "cranelisp_platform::GetSchema",
    ];
    let leaked: Vec<&&str> = must_be_absent
        .iter()
        .filter(|name| baseline.contains(**name))
        .collect();
    assert!(
        leaked.is_empty(),
        "retired marker-type DSL surface still present in the baseline \
         (FIXME 0286 retires AnyAdt / GetSchema): {:?}. Regenerate the baseline.",
        leaked.iter().map(|s| **s).collect::<Vec<&str>>()
    );
    let missing: Vec<&&str> = required_new_exports
        .iter()
        .filter(|name| !baseline.contains(**name))
        .collect();
    assert!(
        missing.is_empty(),
        "Sprint 71 `cranelisp-platform` baseline regen is missing the \
         following new surface lines that MUST land in the same change-set \
         as the ABI_VERSION 1 → 2 bump (per design/arch/CLAUDE.md \
         §\"Baseline-diff discipline\"):\n\n  {}\n\n\
         If you see this failure post-Wave-2, run `cargo +nightly public-api \
         > crates/cranelisp-platform/public-api.txt` from the crate root and \
         commit the regenerated baseline.",
        missing
            .iter()
            .map(|s| **s)
            .collect::<Vec<&str>>()
            .join("\n  ")
    );
}
