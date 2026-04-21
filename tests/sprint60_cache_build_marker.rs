//! Sprint 60 Workstream C — compile-time build-id in cache `.meta.json`.
//!
//! Subprocess-level integration coverage for the build-id invalidation
//! extension. Unit tests for the serialise/deserialise path live with
//! `/backend` in `crates/cranelisp-backend/src/cache/serialize.rs`
//! (`build_id_round_trip_succeeds`, `stale_build_id_produces_build_id_mismatch`,
//! `missing_build_id_field_routes_cache_stale`, etc.). These tests prove the
//! build-id is actually produced by the binary on first compile and that
//! tampering with `.meta.json`'s `build_id` field causes a cache miss on
//! the next compile — the user-surface invariant.
//!
//! Test plan reference: tests/plan/ring4.md §G.20.3.

use std::path::PathBuf;
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

static TEST_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn project_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn binary_path() -> PathBuf {
    project_root().join("target").join("debug").join("cranelisp")
}

fn test_dir(label: &str) -> PathBuf {
    let n = TEST_COUNTER.fetch_add(1, Ordering::SeqCst);
    let dir = project_root()
        .join("tests")
        .join("sprint60")
        .join(".runs")
        .join(format!("cache_{n}_{label}"));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn run(dir: &PathBuf) -> Output {
    let binary = binary_path();
    assert!(binary.exists(), "cranelisp binary not found at {binary:?}");
    let source_path = dir.join("main.cl");
    Command::new(&binary)
        .args(["--run", source_path.to_str().unwrap()])
        .current_dir(dir)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("failed to run cranelisp")
}

/// Read the `.meta.json` file contents as a UTF-8 string. `.meta.json` is a
/// plain JSON document serialised by `cranelisp-backend::cache::write_meta`.
fn read_meta_text(meta: &PathBuf) -> String {
    std::fs::read_to_string(meta).expect("meta.json must exist and be UTF-8")
}

/// Extract the `build_id` string from the raw JSON text. Returns `None` if
/// the field is absent. Narrow parser: looks for `"build_id":"..."` as a
/// top-level field. This avoids a serde_json dependency in the tests crate.
fn extract_build_id(meta_text: &str) -> Option<String> {
    let needle = "\"build_id\":";
    let idx = meta_text.find(needle)?;
    let after = &meta_text[idx + needle.len()..];
    let after = after.trim_start();
    let after = after.strip_prefix('"')?;
    let end = after.find('"')?;
    Some(after[..end].to_string())
}

/// Rewrite the `build_id` field's value in the raw JSON text. Panics if the
/// field is absent — caller must ensure it exists before calling.
fn set_build_id(meta_text: &str, new_value: &str) -> String {
    let needle = "\"build_id\":";
    let idx = meta_text
        .find(needle)
        .expect("meta text must contain build_id field for set_build_id");
    let before = &meta_text[..idx + needle.len()];
    let after = &meta_text[idx + needle.len()..];
    let after_trim = after.trim_start();
    // Advance past the opening quote.
    assert!(
        after_trim.starts_with('"'),
        "build_id value must be a JSON string; got: {after:.60}…"
    );
    let val_start = after.len() - after_trim.len() + 1;
    let rest = &after[val_start..];
    let end = rest
        .find('"')
        .expect("unterminated build_id value in meta.json");
    let suffix = &rest[end..]; // starts with closing `"`
    format!("{before}\"{new_value}{suffix}")
}

/// Remove the `build_id` field (including trailing comma if present). For the
/// pre-Sprint-60 shape simulation.
fn remove_build_id(meta_text: &str) -> String {
    let needle = "\"build_id\":";
    let idx = meta_text
        .find(needle)
        .expect("meta text must contain build_id field for remove_build_id");
    // Find the end of the string value.
    let after = &meta_text[idx + needle.len()..];
    let after_trim_offset = after.len() - after.trim_start().len();
    let val = &after[after_trim_offset + 1..]; // skip opening quote
    let end_quote = val
        .find('"')
        .expect("unterminated build_id value in meta.json");
    let mut end_idx = idx + needle.len() + after_trim_offset + 1 + end_quote + 1;
    // Swallow trailing `,` and any whitespace to keep the JSON object valid.
    let tail = &meta_text[end_idx..];
    if tail.trim_start().starts_with(',') {
        let ws = tail.len() - tail.trim_start().len();
        end_idx += ws + 1 /* the comma */;
        // Also swallow whitespace after the comma.
        let after_comma = &meta_text[end_idx..];
        let ws2 = after_comma.len() - after_comma.trim_start().len();
        end_idx += ws2;
    }
    format!("{}{}", &meta_text[..idx], &meta_text[end_idx..])
}

fn write_meta_text(meta: &PathBuf, text: &str) {
    std::fs::write(meta, text).expect("write meta.json");
}

/// Trivial single-file project. `main` returns 0 (spec §12.6: exit code is
/// `main`'s Int return) so `Command::status.success()` is the right assertion.
/// A secondary function makes the cache hit path do something observable —
/// we only care that the `.meta.json` + `.o` are written.
const SRC: &str = "(import [primitives [add-i64]])\n(defn double [x] (add-i64 x x))\n(defn main [] (double 0))";

// spec: tests/plan/ring4.md §G.20.3 — first compile populates `.meta.json`
// with a build-id; re-compile hits cache (no-op for entry module re-cache
// but the build-id round-trips unchanged).
#[test]
fn cache_meta_carries_build_id_after_first_compile() {
    let dir = test_dir("has_build_id");
    std::fs::write(dir.join("main.cl"), SRC).unwrap();

    let out = run(&dir);
    assert!(
        out.status.success(),
        "first compile must succeed; stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );

    let meta = dir.join(".cranelisp-cache").join("main.meta.json");
    assert!(meta.exists(), "main.meta.json must be written");

    let text = read_meta_text(&meta);
    let build_id = extract_build_id(&text).unwrap_or_else(|| {
        panic!("meta.json must carry a build_id field; got:\n{text}")
    });
    assert!(
        !build_id.is_empty(),
        "build_id must be non-empty; meta=\n{text}"
    );
    // Negative guard: schema_version must also be present (build-id is an
    // additive trigger, not a substitute — Sprint 60 Architecture Review
    // Condition 3).
    assert!(
        text.contains("\"schema_version\":"),
        "schema_version must remain alongside build_id (additive, not substitutive); meta=\n{text}"
    );
}

// spec: tests/plan/ring4.md §G.20.3 — tampering with build_id forces a
// fresh build on the next compile. The test proves the guard fires by:
//  (1) first compile writes meta with BUILD_ID_A
//  (2) patch meta to a fake BUILD_ID_X
//  (3) re-compile — MUST succeed, and the meta's build_id MUST have been
//      rewritten back to BUILD_ID_A (proving the cache miss + re-emit path
//      ran rather than silently returning the stale meta).
#[test]
fn cache_meta_with_stale_build_id_triggers_recompile() {
    let dir = test_dir("stale_build_id");
    std::fs::write(dir.join("main.cl"), SRC).unwrap();

    let first = run(&dir);
    assert!(first.status.success(), "first compile must succeed");

    let meta_path = dir.join(".cranelisp-cache").join("main.meta.json");
    let original_text = read_meta_text(&meta_path);
    let original_build_id =
        extract_build_id(&original_text).expect("first compile wrote build_id");

    // Patch build_id to a synthetic value the compiler cannot match.
    let patched_text = set_build_id(&original_text, "0.0.0+stale-synthetic");
    assert_eq!(
        extract_build_id(&patched_text).as_deref(),
        Some("0.0.0+stale-synthetic"),
        "patch must land"
    );
    write_meta_text(&meta_path, &patched_text);

    let second = run(&dir);
    assert!(
        second.status.success(),
        "second compile must succeed despite stale build_id — cache must miss and rebuild; stderr={}",
        String::from_utf8_lossy(&second.stderr)
    );

    let after_text = read_meta_text(&meta_path);
    let rewritten_build_id =
        extract_build_id(&after_text).expect("rebuild must restore build_id");
    // Negative assertion: the stale sentinel must NOT survive — if the cache
    // had honoured the patched meta, the stale string would still be on disk.
    assert_ne!(
        rewritten_build_id, "0.0.0+stale-synthetic",
        "stale build_id survived — cache did not invalidate on build_id mismatch"
    );
    assert_eq!(
        rewritten_build_id, original_build_id,
        "rebuild must stamp the current BUILD_ID (same as first compile)"
    );
}

// spec: tests/plan/ring4.md §G.20.3 — a pre-Sprint-60 `.meta.json` (no
// `build_id` field at all) MUST be treated as stale. Simulated here by
// removing the field from a freshly-written meta.
#[test]
fn cache_meta_without_build_id_field_triggers_recompile() {
    let dir = test_dir("missing_build_id");
    std::fs::write(dir.join("main.cl"), SRC).unwrap();

    let first = run(&dir);
    assert!(first.status.success(), "first compile must succeed");

    let meta_path = dir.join(".cranelisp-cache").join("main.meta.json");
    let original_text = read_meta_text(&meta_path);
    let original_build_id =
        extract_build_id(&original_text).expect("first compile wrote build_id");

    // Remove the build_id field entirely — pre-Sprint-60 cache shape.
    let patched_text = remove_build_id(&original_text);
    write_meta_text(&meta_path, &patched_text);

    // Confirm the patch landed (no build_id on disk).
    let verify = read_meta_text(&meta_path);
    assert!(
        extract_build_id(&verify).is_none(),
        "patched meta must have no build_id field; got:\n{verify}"
    );

    let second = run(&dir);
    assert!(
        second.status.success(),
        "second compile must succeed despite missing build_id — cache must miss and rebuild; stderr={}",
        String::from_utf8_lossy(&second.stderr)
    );

    let after_text = read_meta_text(&meta_path);
    let restored =
        extract_build_id(&after_text).expect("rebuild must restore build_id field");
    assert_eq!(
        restored, original_build_id,
        "rebuild must stamp the current BUILD_ID on pre-Sprint-60-shape caches"
    );
}
