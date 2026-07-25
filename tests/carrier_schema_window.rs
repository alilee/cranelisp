// carrier_schema_window.rs — Track A, the ONE schema window (21→22) cells
// (s114-test-plan §3.3; S111 0621 cache-invalidation precedent).
//
// Two bump-worthy changes coordinate into ONE `CACHE_SCHEMA_VERSION` invalidation
// event this sprint: the typed-carrier reshape (serde-visible on persisted
// `codegen_view`) and the B-2 match-var-pattern escape-fact correction. A stale
// persisted `Some(false)` escape fact served warm from cache would reproduce the
// UAF post-fix — the exact hazard F7 names. These cells guard the correction's
// PERSISTENCE (CS-1) and the wholesale-refusal gate that the bump rides (CS-2).
// Free-standing (no stdlib).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};
use std::fs;
use std::time::Duration;

// The B-2 shape: a COW `vec-set` bound by a match var-pattern, projected by the
// caller. `(vec-set [1 2 3] 1 99)` = `[1 99 3]`; `(vec-get (h [1 2 3]) 1)` = 99.
const B2_PROG: &str = "(defn h [v] (match (vec-set v 1 99) [r r]))\n\
     (defn main [] (Pure (vec-get (h [1 2 3]) 1)))\n";

fn nap() {
    std::thread::sleep(Duration::from_millis(50));
}

// Run B2_PROG cold (populating the cache), then warm (from cache), returning the
// two exit codes. `toggle_off` sets `CRANELISP_NO_OWNERSHIP=1` on both runs.
fn b2_cold_then_warm(toggle_off: bool) -> (Option<i32>, Option<i32>, String) {
    let cold_b = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(B2_PROG);
    let cold_b = if toggle_off {
        cold_b.env("CRANELISP_NO_OWNERSHIP", "1")
    } else {
        cold_b
    };
    let cold = cold_b.output();
    let cold_code = cold.status.code();
    nap();
    // Warm: the tmpdir (user.cl, prelude.cl, .cranelisp-cache/) persists.
    let warm_b = cold.run_again().run("user.cl");
    let warm_b = if toggle_off {
        warm_b.env("CRANELISP_NO_OWNERSHIP", "1")
    } else {
        warm_b
    };
    let warm = warm_b.output();
    (
        cold_code,
        warm.status.code(),
        format!("{}{}", warm.stdout, warm.stderr),
    )
}

// CS-1 — warm-cache correctness twin of the B-2 shape (both toggles). cold == warm
// == 99 in BOTH toggle states. The analysis-ON face is correct cold AND warm today
// (born-green half — guards that the escape-fact correction, once persisted, is not
// served stale as `Some(false)`); the toggle-off face is RED until BI-C-off flips
// (`binding_indirection_consume::b2_match_cow_var_pattern_toggle_off_neg`). The
// cache-coherence dimension (cold vs warm) is what this cell adds over the plain
// toggle-off `--run` pin — a stale cached escape fact would diverge warm from cold.
// RED today via the toggle-off arm; flips with BI-C-off + the escape-fact
// persistence landing in the ONE schema window.
// spec: spec/12-runtime.md §12.1 — a COW match result stays live for the caller;
// the escape fact governing it must be cache-coherent across cold/warm compiles.
// defect: class=rc-miscount locus=crates/cranelisp-backend match consume seam + escape-fact cache coherence (B-2 warm-cache; stale persisted escape fact reproduces the UAF — F7 window) found=S114 owner=/dev
#[test]
fn b2_match_cow_warm_cache_correct_both_toggles() {
    let (on_cold, on_warm, on_ctx) = b2_cold_then_warm(false);
    assert_eq!(
        (on_cold, on_warm),
        (Some(99), Some(99)),
        "analysis-ON: the B-2 COW match result MUST be 99 cold AND warm (cache \
         coherence); got cold={on_cold:?} warm={on_warm:?}\n{on_ctx}"
    );
    let (off_cold, off_warm, off_ctx) = b2_cold_then_warm(true);
    assert_eq!(
        (off_cold, off_warm),
        (Some(99), Some(99)),
        "toggle-off (CRANELISP_NO_OWNERSHIP=1): the B-2 COW match result MUST be 99 \
         cold AND warm too (the contract is structural, correct in both toggle \
         states, and the persisted escape fact must be cache-coherent); got \
         cold={off_cold:?} warm={off_warm:?}\n{off_ctx}"
    );
}

// -----------------------------------------------------------------------------
// CS-2 — schema-gate wholesale-refusal fence (mechanism, not per-version).
// -----------------------------------------------------------------------------

const CS2_MAIN: &str =
    "(import [primitives [Pure]])\n(import [util [helper]])\n(defn main [] (Pure (helper 21)))";
const CS2_UTIL: &str = "(import [primitives [add-i64]])\n(defn helper [x] (add-i64 x x))";

/// Rewrite an integer JSON field's value in raw text (mirrors cache.rs's helper).
fn set_json_u32(text: &str, needle: &str, new_value: u32) -> String {
    let idx = text
        .find(needle)
        .unwrap_or_else(|| panic!("text must contain field {needle}"));
    let before = &text[..idx + needle.len()];
    let after = &text[idx + needle.len()..];
    let ws = after.len() - after.trim_start().len();
    let digits = &after.trim_start();
    let end = digits
        .find(|c: char| !c.is_ascii_digit())
        .expect("field value must be terminated");
    let suffix = &after[ws + end..];
    format!("{before}{}{new_value}{suffix}", &after[..ws])
}

// CS-2 — the stale-`CACHE_SCHEMA_VERSION` wholesale-refusal behaviour (AG-1 class).
// A cache whose manifest `cache_format_version` predates the live schema is
// wholesale-invalidated: every module recompiles (no cache hit), never serving an
// incompatible object. This is the gate the 21→22 window rides. Version-AGNOSTIC by
// construction: patching the manifest to a deliberately-low value (1) makes the
// live schema — whatever it is (21 pre-bump, 22 post-bump) — mismatch, so the fence
// holds across the bump. One cell, the mechanism, not per-version. Born-green.
// spec: design/backend/module-caching.md §4 — a cache stamped with a pre-bump
// schema routes through wholesale invalidation (cache-miss → recompute).
#[test]
fn stale_schema_manifest_invalidated_wholesale_mechanism() {
    let mut c = Cranelisp::new();
    for (p, s) in [("main.cl", CS2_MAIN), ("util.cl", CS2_UTIL)] {
        c = c.file(p, s);
    }
    let first = c.run("main.cl").output();
    assert_eq!(first.status.code(), Some(42), "cold compile must exit 42");
    let manifest_path = first.tmpdir.join(".cranelisp-cache").join("manifest.json");
    let original = fs::read_to_string(&manifest_path).expect("read manifest.json");
    let patched = set_json_u32(&original, "\"cache_format_version\":", 1);
    fs::write(&manifest_path, &patched).expect("write patched manifest");
    nap();

    let second = first
        .run_again()
        .env("CRANELISP_MODULE_TRACE", "1")
        .run("main.cl")
        .output();
    assert_eq!(
        second.status.code(),
        Some(42),
        "recompile must still exit 42"
    );
    assert!(
        !second.stderr.contains("cache hit"),
        "a manifest stamped with a pre-bump schema (patched to 1) MUST be \
         wholesale-invalidated against the live schema — util must recompute, not \
         cache-hit; stderr:\n{}",
        second.stderr
    );
}
