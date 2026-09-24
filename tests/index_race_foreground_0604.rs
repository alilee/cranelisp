//! S122 closure rider — FIXME 0604 public-write isolation regression sweep.
//!
//! The current structural contract routes every public cross-module name
//! candidate through `check_exposed_candidate_closure` before table or GOT
//! mutation. Private and intra-module candidates take their explicit arms; the
//! three session-initialization seams have separate dispositions. The route
//! census and contract live in `design/int/int.md`
//! §6.7.
//!
//! This retained recipe exercises the historical `num.bits` + prelude fan-out
//! and refuses the old phantom-write signatures. It is a no-regression sweep,
//! not proof that the historical race fired in this environment or that its
//! exact writer was established. The old firing record (16/16 in one
//! environment and quiet runs elsewhere) remains provenance in
//! `sprints/archive/sprint-109.md` §Findings. FIXME 0818's contaminated
//! probe is an unconfirmed explanatory lead, not attribution of those runs.
//!
//! Historical defect provenance: class=shared-state-write-race, observed as a
//! public `bit-and → primitives/bit-and` entry outside prelude's declared export
//! closure, found=S109, owner=/dev. The structural gate closes that invalid
//! publication class without claiming a recovered per-interleaving writer.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;

/// The verbatim FIXME 0604 recipe. No `main` — the "entry module has no 'main'
/// function" error is the expected clean outcome after import-triggered
/// compilation completes.
const RECIPE: &str = "(import [num.bits [bit-and]])\n\
    (import [primitives [Int]])\n\
    (defn use-it [:Int x] :Int (bit-and x 7))\n";

/// The workspace `stdlib/` directory supplies the real `num.bits` fan-out.
/// Read-only on project_root.
const WORKSPACE_STDLIB: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/stdlib");

/// Historical phantom-publication signatures. None may appear; the only
/// expected error is the benign "no 'main' function".
const RACE_SIGNATURES: &[&str] = &[
    "ambiguous",
    "has no member 'bit-and'",
    "not found in module 'num",
    "super import",
    "unimportable",
];

// spec: spec/08-modules.md §8.6.5 — an invalid public candidate must not enter
// the live `prelude` table and spuriously poison the valid `num.bits` import.
// Each iteration uses a fresh tempdir and cold cache so compilation traverses
// the guarded publication routes. This sweep is supplemental to the structural
// route/gate evidence; a quiet run does not reconstruct the historical race.
#[test]
fn num_bits_import_not_poisoned_by_foreground_concurrent_compile_race() {
    for i in 0..8 {
        let out = Cranelisp::new()
            .run("di.cl")
            .env("CRANELISP_LIB", WORKSPACE_STDLIB)
            .env("CRANELISP_MODULE_TRACE", "1")
            .user(RECIPE)
            .output();
        let hay = format!("{}\n{}", out.stdout, out.stderr);
        for sig in RACE_SIGNATURES {
            assert!(
                !hay.contains(sig),
                "iteration {i}: `num.bits`/`bit-and` exposed a prohibited \
                 historical phantom-publication signature {sig:?}. \
                 This is the FIXME 0604 no-regression sweep; the observed \
                 signature alone does not identify its writer. \
                 stdout:\n{}\nstderr:\n{}",
                out.stdout,
                out.stderr
            );
        }
    }
}
