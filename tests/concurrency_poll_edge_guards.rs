//! Sprint 96 — effect-concurrency Chunk A: the poll-capacity edge guard, REVISED
//! for the single-ABI cutover (A4c).
//!
//! SUPERSEDED PREMISE: the pre-pivot ruling ("Chunk A adds ZERO edges, NO ABI
//! bump, v7 stays unfrozen") is RETIRED by the single-ABI cutover
//! (`design/arch/platform-interface.md` §6.8.0/§6.8.0a): the ABI IS bumped 7→8
//! and the host-reactor ABI contracts ARE promoted to the default edge. This
//! guard is updated accordingly. What still holds: poll-shape live capacity rides
//! the IN-PROCESS node `(token, capacity)` convention — there is NO `effect_on_poll`
//! public constructor (the platform writes the leading-pair operands, not a new
//! ctor). Companion: `tests/facade_pif_rows.rs::unified_abi_contracts_present_dual_channel_deleted`.
//!
//! Posture: stays-green (RED if a poll-ctor leaks or the ABI stamp drifts off 8).

use std::path::PathBuf;

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn read_pub_api(crate_name: &str) -> String {
    let p = workspace_root()
        .join("crates")
        .join(crate_name)
        .join("public-api.txt");
    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()))
}

// spec: design/arch/platform-interface.md §6.8.0 — poll-shape live capacity rides
// the in-process node `(token, capacity)` convention (NO new public constructor),
// and the single-ABI cutover stamps `ABI_VERSION = 8`. RED if a poll-capacity
// ctor leaks onto the default edge or the ABI stamp drifts off 8.
#[test]
fn poll_capacity_rides_node_convention_and_abi_is_v8() {
    // (1) No NEW poll-shape public constructor on the default `cranelisp-platform`
    // edge. The S95 blocking `effect_on_resource_with_capacity` is allowed; a
    // `poll`-named capacity constructor on the default edge would be the leak this
    // guards (poll capacity must ride the in-process node convention, gated).
    let platform_api = read_pub_api("cranelisp-platform");
    for leaked in [
        "effect_on_poll",
        "effect_on_poll_with_capacity",
        "poll_with_capacity",
    ] {
        assert!(
            !platform_api.contains(leaked),
            "Chunk A leaked a poll-capacity public constructor `{leaked}` onto the \
             default cranelisp-platform/public-api.txt edge — poll-shape live \
             capacity must ride the reserved in-process node `(token, capacity)` \
             slots (no new default-edge constructor)."
        );
    }

    // (2) The single-ABI cutover stamps `ABI_VERSION = 8` (the unified PlatformFn
    // replaced `scheduling_class` with `concurrency` + added `drop_state`).
    let lib_rs = std::fs::read_to_string(
        workspace_root()
            .join("crates")
            .join("cranelisp-platform")
            .join("src")
            .join("lib.rs"),
    )
    .expect("read cranelisp-platform/src/lib.rs");
    assert!(
        lib_rs.contains("pub const ABI_VERSION: u32 = 8;"),
        "the single-ABI cutover (§6.8.0) stamps `ABI_VERSION = 8`. The \
         `pub const ABI_VERSION: u32 = 8;` line was not found in \
         cranelisp-platform/src/lib.rs."
    );

    // (3) The `ABI_VERSION` const stays on the platform edge (a removal/rename
    // would also be a frozen-edge perturbation).
    assert!(
        platform_api.contains("pub const cranelisp_platform::ABI_VERSION: u32"),
        "the `cranelisp_platform::ABI_VERSION` public const must remain on the \
         default edge (frozen-edge invariant)."
    );
}

// spec: design/arch/platform-interface.md §6.8.0 — Chunk C (the combinator +
// cancellation layer) adds NO new `cranelisp-types` / `cranelisp-platform`
// `public-api.txt` edge line and NO `ABI_VERSION` bump: `race`/`select` are
// new in-process IO node tags (pinned consts off the default edge, the
// `IO_TAG_EFFECT_POLL` precedent), `timeout` is derived `.cl`, and cancellation
// lights up the already-reserved `drop_state` + the Chunk-A future-drop RAII path.
// Combinators are runtime-internal (platforms never see them — effect-concurrency.md
// §9), so there is no platform-ABI surface at all. RED if a Chunk-C wave leaks a
// combinator/cancellation public constructor onto the default edge or bumps the ABI.
#[test]
fn chunk_c_no_new_public_api_edge_or_abi_bump_neg() {
    // (1) No `race`/`select`/`timeout`/cancel constructor on the default
    // `cranelisp-platform` OR `cranelisp-types` edge — they ride the in-process IO
    // node-tag convention, not a public constructor.
    let platform_api = read_pub_api("cranelisp-platform");
    let types_api = read_pub_api("cranelisp-types");
    for leaked in [
        "fn race",
        "fn select",
        "fn timeout",
        "effect_race",
        "effect_select",
        "fn cancel",
        "IoNode::Race",
        "IoNode::Select",
    ] {
        assert!(
            !platform_api.contains(leaked),
            "Chunk C leaked a combinator/cancellation public item `{leaked}` onto the \
             default cranelisp-platform/public-api.txt edge — race/select are in-process \
             IO node tags (no new default-edge constructor; platforms never see them)."
        );
        assert!(
            !types_api.contains(leaked),
            "Chunk C leaked a combinator/cancellation public item `{leaked}` onto the \
             default cranelisp-types/public-api.txt edge — no new edge from Chunk C."
        );
    }

    // (2) The single-ABI cutover ABI stamp stays `ABI_VERSION = 8` — Chunk C bumps
    // nothing (it lights up the already-reserved gated `drop_state`).
    let lib_rs = std::fs::read_to_string(
        workspace_root()
            .join("crates")
            .join("cranelisp-platform")
            .join("src")
            .join("lib.rs"),
    )
    .expect("read cranelisp-platform/src/lib.rs");
    assert!(
        lib_rs.contains("pub const ABI_VERSION: u32 = 8;"),
        "Chunk C must NOT bump the ABI — `ABI_VERSION` must stay 8 (combinators are \
         in-process node tags + derived `.cl`; cancellation reuses `drop_state`)."
    );
}
