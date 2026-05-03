// Cache-isolation seed test (Sprint 64 Wave 1, Phase 1 §2).
//
// This is the lock-test the rest of Phase 2's cache-hit tests depend
// on. It cites the spec property that `.cranelisp-cache/` lives under
// `project_root` (per `design/backend/module-caching.md §"Cache
// directory layout"`). The harness exploits the equivalence
// `project_root = std::env::current_dir()` (per
// `design/int/repl-lifecycle.md §"Project root resolution"`) by
// setting the child's CWD to a fresh `TempDir` — but the test cites
// the project-root spec property, not the CWD implementation chain.
//
// Wave 2 Batch 1 merges this seed into the new `tests/cache.rs`
// alongside the audited carry-forwards from the legacy `cache.rs`.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;

/// spec: design/backend/module-caching.md §"Cache directory layout"
///   "All module caches (including stdlib) live in the project's
///    `.cranelisp-cache/` directory."
///
/// Verifies the cache materialises under project_root (= the per-test
/// TempDir) and nowhere else on disk that the test can observe.
#[test]
fn cache_lives_under_project_root() {
    // Use a main that returns 0; the binary maps `main`'s return value to
    // the process exit code, so non-zero values would conflate "failed
    // build" with "ran successfully but returned non-zero".
    let out = Cranelisp::new()
        .run("user.cl")
        .with_prelude(helpers::e2e::PreludeVariant::PrimitivesOnly)
        .user("(defn main [] 0)")
        .output()
        .assert_ok();

    assert!(
        out.tmp_exists(".cranelisp-cache"),
        "cache must materialise under project_root (= TempDir); got tmpdir={}, stdout={:?}",
        out.tmpdir.display(),
        out.stdout
    );
}
