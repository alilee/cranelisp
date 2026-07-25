//! L-B1 golden-CLIF lane — nextest gate (S111 CS-0.5).
//!
//! WHY THIS FILE EXISTS (the process fix).
//! The full-corpus golden lane lives in `tests/scripts/clif_golden.sh` and is
//! run via `clif_golden.sh diff`. For three sprints (S104/S109/S110) that lane
//! rotted SILENTLY: `clif_golden.sh diff` is a shell script invisible to
//! `cargo nextest run`, so emission-affecting change-sets drifted goldens
//! without any RED signal — a triple violation of the S102 §6.2 discipline
//! ("re-baseline in the change-set that drifts a frame"). The only in-suite
//! witness was `ownership_fences.rs::clif_golden_single_module_smoke`, which
//! covers ONE frame (06_tco_loop) — and 06 happened not to drift, so the rot
//! stayed hidden. See SPRINT.md §"P5 progress" CS-0.5 and FIXME 0636.
//!
//! This test folds the WHOLE 13-frame lane into nextest so the discipline is
//! mechanically enforced: any emission-affecting change-set that drifts any
//! frame turns this RED until it carries its own scoped + attributed
//! re-baseline (`clif_golden.sh capture`, attribution in the commit body).
//!
//! It shells out to `clif_golden.sh diff` rather than re-implementing frame
//! extraction in Rust: the script is the single source of truth for the entry
//! list, the `--no-cache` + emission-toggle config pins, and the Python frame
//! extractor. A Rust re-implementation would be a THIRD extraction mirror (the
//! script's F6 note bars that until a third consumer forces unification); this
//! gate reuses the exact command a human runs, so it can never drift from it.
//!
//! The binary the script exercises (`target/debug/cranelisp`) is built by cargo
//! before any integration test in this package runs (it is `CARGO_BIN_EXE_*`
//! for the `tests/` targets), so the gate builds nothing itself — it is
//! deterministic (`--no-cache`, emission env unset) and cheap (~0.7s for all 13
//! frames).

use std::path::Path;
use std::process::Command;

// spec: design/backend/ownership-codegen.md §13.1 — the L-B1 golden lane: HEAD
// CLIF for every corpus entry must be byte-identical to its committed golden
// (frames sorted module::symbol, byte-verbatim, no canonicalization). This is
// the whole-corpus counterpart to `ownership_fences.rs::
// clif_golden_single_module_smoke` (single frame), now counted by nextest so
// the lane cannot silently rot between wave-gate script runs.
#[test]
fn clif_golden_lane_no_drift() {
    let script = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/scripts/clif_golden.sh");
    assert!(
        script.is_file(),
        "clif_golden.sh missing at {} — the L-B1 lane script is the gate's \
         single source of truth",
        script.display(),
    );

    // `diff`: dump HEAD CLIF for all 13 entries and byte-compare each to its
    // golden. Exit 0 == zero drift; non-zero == at least one frame drifted (or
    // the binary is not built / a frame is missing / a duplicate frame leaked).
    let out = Command::new("bash")
        .arg(&script)
        .arg("diff")
        .output()
        .unwrap_or_else(|e| panic!("failed to spawn {}: {e}", script.display()));

    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "L-B1 golden lane DRIFTED (or could not run) — `clif_golden.sh diff` \
         exited {code:?}.\n\n\
         Any emission-affecting change-set that drifts a frame MUST carry its \
         own SCOPED + ATTRIBUTED re-baseline (`tests/scripts/clif_golden.sh \
         capture`, attribution cited in the commit body — S102 §6.2). Do NOT \
         re-capture blindly: a re-baseline certifies the reshape is a sound \
         emission change, not a silently-dropped RC op.\n\n\
         --- clif_golden.sh diff (stdout) ---\n{stdout}\n\
         --- stderr ---\n{stderr}",
        code = out.status.code(),
    );
}
