//! S111 §G.1 / IR-1 — FIXME 0604 foreground concurrent-compile write race.
//!
//! ## What this is
//!
//! The `--run` path builds `num.bits` + the prelude + ~13 re-exported domain
//! modules CONCURRENTLY (eval thread + priority/nice workers). Under an
//! unlucky interleaving a phantom `bit-and → primitives/bit-and` entry is
//! written into the live `prelude` table, spuriously firing the (spec-correct)
//! §8.6.5 super-import poison and making `num.bits` unimportable — so the
//! `(defn use-it [:Int x] :Int (bit-and x 7))` below fails with a spurious
//! `ambiguous`/unresolved `bit-and`. S110 `/dev` PROVED the *index feed* inert
//! under this recipe (`--run` never arms the index; instrumented 0×), so the
//! writer is on the FOREGROUND concurrent-compile path
//! (`src/process_form/`, `src/imports.rs`, `src/worker.rs`) — re-attributed
//! FOREGROUND for S111. Attribution record:
//! `tests/plan/s109-attribution-index-feed-race.md`.
//!
//! defect: class=shared-state-write-race locus=src/worker.rs (foreground concurrent-compile phantom prelude write — exact seam UNLOCATED) found=S109 owner=/dev
//!
//! ## Environment sensitivity (READ BEFORE TRIAGING A GREEN)
//!
//! The race is scheduling-dependent: it fired 16/16 in the `/sprint` firing
//! environment and 0/140 in earlier `/testing` runs. At S111 Phase-5 authoring
//! it did NOT fire in this environment (0/45 across the verbatim recipe + a
//! main-wrapped variant, `CRANELISP_MODULE_TRACE=1`). Per `tests/CLAUDE.md`
//! §"Isolating Cross-Crate Failures" this lands as an ENVIRONMENT-DRIVEN e2e
//! (binary invocation with `CRANELISP_LIB` → workspace stdlib) rather than an
//! in-process free-standing test, because the recipe INHERENTLY imports the
//! real stdlib module graph (`num.bits` + its re-export fan-out) — that graph
//! is the race substrate and cannot be reduced away without dissolving the
//! race.
//!
//! FIXME(/testing): the exact foreground write seam is UNLOCATED and the race
//! does not fire deterministically here. The deliverable per the /sprint
//! dispatch is this committed repro + the attribution record; `/sprint` runs
//! this lane in the firing environment (16/16). A GREEN here is NOT proof the
//! race is fixed — it is the environment not firing (the S98 false-green /
//! forbidden-"flaky" class: the race is a real bug, named and pinned, not
//! flake). The fail-on-revert guard rides the CS-6 fix; do not weaken the
//! spec-correct §8.6.5 poison consumer (the `super_import_wrapper_*` twins in
//! `tests/spec_08_prelude_outer_scope.rs` pin its two correct poles).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;

/// The verbatim FIXME 0604 recipe. No `main` — the "entry module has no 'main'
/// function" error is the EXPECTED clean outcome; the race is in the
/// import-triggered concurrent compile, which runs regardless.
const RECIPE: &str = "(import [num.bits [bit-and]])\n\
    (import [primitives [Int]])\n\
    (defn use-it [:Int x] :Int (bit-and x 7))\n";

/// The workspace `stdlib/` directory — the real `num.bits` fan-out is the race
/// substrate. read-only on project_root.
const WORKSPACE_STDLIB: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/stdlib");

/// Signatures of the phantom-write firing (the spurious §8.6.5 poison / a
/// `bit-and` mis-resolution making `num.bits` unimportable). None of these may
/// appear — the only expected error is the benign "no 'main' function".
const RACE_SIGNATURES: &[&str] = &[
    "ambiguous",
    "has no member 'bit-and'",
    "not found in module 'num",
    "super import",
    "unimportable",
];

// spec: spec/08-modules.md §8.6.5 — a concurrent phantom write into the live
// `prelude` table MUST NOT spuriously fire the super-import poison; `num.bits`
// stays importable. Environment-bound (0/45 here; fires 16/16 in the /sprint
// firing environment). Each iteration is a FRESH tempdir (cold cache) so the
// concurrent compile actually runs — the race surface.
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
                "iteration {i}: the foreground concurrent-compile write race \
                 fired — `num.bits`/`bit-and` mis-resolved (signature {sig:?}). \
                 This is FIXME 0604 (shared-state-write-race, /dev src/int). \
                 stdout:\n{}\nstderr:\n{}",
                out.stdout,
                out.stderr
            );
        }
    }
}
