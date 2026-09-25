// cache.rs — Module cache e2e tests (Sprint 64 Wave 2 Batch 1)
//
// Carries forward the language-behaviour assertions from the legacy
// `tests/cache.rs` (~55 tests, 2073 LOC) and merges in the
// `tests/cache_seed.rs` Wave-1 isolation seed. Rust-internal assertions
// (direct `cranelisp_backend::cache::*` API construction, `SymbolTable`
// inspection through `cache::load_meta`, manifest field tampering) are
// quarantined to `tests/legacy/cache.rs` for harvest into
// `cranelisp-backend` unit tests via FIXME 0120.
//
// Discipline:
//   - Each test runs the `cranelisp` binary as a subprocess via the
//     `Cranelisp` builder; cache state is observed through `tmp_exists`,
//     `read_tmp`, exit code, and the `run_again()` cache-hit pattern.
//   - All tests use a fresh `tempfile::TempDir` by construction (the
//     harness's per-builder cwd) — no checked-in path is ever touched.
//   - The binary exit code carries `main`'s i64 return value; cache-hit
//     vs. fresh-build parity is asserted on both exit code AND tmpdir
//     state (manifest/.meta.json/.o presence + mtime preservation on
//     unchanged modules).

#[path = "helpers/mod.rs"]
mod helpers;

use std::fs;
use std::time::{Duration, SystemTime};

use helpers::e2e::Cranelisp;

// spec: spec/03-types.md §3.6.3 — cached generic definitions preserve distinct
// result-context specializations at independent Int and String uses.
#[test]
fn cache_result_only_returned_closure_specializations_agree_uncached_cold_and_warm() {
    let files = [
        ("util.cl", "(defn g [] (fn [y] 100))\n"),
        (
            "main.cl",
            "(import [primitives [Pure add-i64]])\n\
             (import [util [g]])\n\
             (defn main [] (Pure (add-i64 ((g) 5) ((g) \"heap\"))))\n",
        ),
    ];
    let uncached = project(&files)
        .run("main.cl")
        .cli_flag("--no-cache")
        .env("CRANELISP_MODULE_TRACE", "1")
        .output()
        .assert_exit(200);
    assert!(
        !uncached.stderr.contains("cache hit"),
        "{}",
        uncached.stderr
    );
    let cold = project(&files)
        .run("main.cl")
        .env("CRANELISP_MODULE_TRACE", "1")
        .output()
        .assert_exit(200);
    assert!(!cold.stderr.contains("cache hit"), "{}", cold.stderr);
    assert_eq!(uncached.stdout, cold.stdout);
    let warm = cold
        .run_again()
        .run("main.cl")
        .env("CRANELISP_MODULE_TRACE", "1")
        .output()
        .assert_exit(200);
    assert_eq!(uncached.stdout, warm.stdout);
    assert!(
        warm.stderr.contains("cache hit (.meta valid) for util"),
        "warm execution must restore the generic's module from cache:\n{}",
        warm.stderr
    );
}

// spec: spec/12-runtime.md §12.5 + design/backend/module-caching.md §4 — a
// generic self-call with a nested function parameter agrees across cold JIT,
// a real warm object-cache load, and linking from that cached project state.
#[test]
fn cache_generic_self_call_agrees_cold_warm_and_linked() {
    let files = [
        (
            "util.cl",
            "(import [primitives [Int add-i64 eq-i64 sub-i64]])\n\
             (defn repeat-fn [f :Int n x]\n\
               (if (eq-i64 n 0) x (repeat-fn f (sub-i64 n 1) (f x))))\n\
             (defn repeat-five [] (repeat-fn (fn [x] (add-i64 x 1)) 5 0))\n",
        ),
        (
            "main.cl",
            "(import [primitives [Pure]])\n\
             (import [util [repeat-five]])\n\
             (defn main [] (Pure (repeat-five)))\n",
        ),
    ];
    let cold = project(&files)
        .run("main.cl")
        .env("CRANELISP_MODULE_TRACE", "1")
        .output()
        .assert_exit(5);
    assert!(!cold.stderr.contains("cache hit"), "{}", cold.stderr);
    assert!(
        cold.tmp_exists(".cranelisp-cache/util.o"),
        "the concrete util wrapper must emit the generic self-call specialization into util.o"
    );
    let util_object = cold.tmpdir.join(".cranelisp-cache/util.o");
    let cold_object = fs::read(&util_object).expect("read cold util.o");
    let cold_object_mtime = mtime(&cold, ".cranelisp-cache/util.o");

    let warm = cold
        .run_again()
        .run("main.cl")
        .env("CRANELISP_MODULE_TRACE", "1")
        .output()
        .assert_exit(5);
    assert!(
        warm.stderr.contains("cache hit (.meta valid) for util"),
        "warm JIT execution must load the generic self-call's object from cache:\n{}",
        warm.stderr
    );
    assert_eq!(
        fs::read(&util_object).expect("read warm util.o"),
        cold_object,
        "warm JIT execution must reuse the exact util.o bytes"
    );
    assert_eq!(
        mtime(&warm, ".cranelisp-cache/util.o"),
        cold_object_mtime,
        "warm JIT execution must not rewrite util.o"
    );

    let linked = warm
        .run_again()
        .link_then_run("main.cl")
        .env("CRANELISP_MODULE_TRACE", "1")
        .output()
        .assert_exit(5);
    assert!(
        linked.stderr.contains("cache hit (.meta valid) for util"),
        "linking from the warm project must reuse the generic self-call's cached object:\n{}",
        linked.stderr
    );
    assert_eq!(
        fs::read(&util_object).expect("read util.o after linking"),
        cold_object,
        "linking from the warm project must reuse the exact util.o bytes"
    );
    assert_eq!(
        mtime(&linked, ".cranelisp-cache/util.o"),
        cold_object_mtime,
        "linking from the warm project must not rewrite util.o"
    );
}

const PRE_SIGNATURE_IDENTITY_SCHEMA: u32 = 28;

// spec: design/arch/s122-overload-reorder-publication.md §"Verification
// boundary" — schema-28 sidecar/object pairs use the retired executable-key
// identity. Version 29 must reject them with the current compiler fingerprint,
// rebuild the pair, and then serve the rebuilt current pair on a warm run.
#[test]
fn schema28_identity_cache_refused_rebuilt_and_reused_warm() {
    let cold = project(&[("main.cl", SCHEMA_MAIN), ("util.cl", SCHEMA_UTIL)])
        .run("main.cl")
        .env("CRANELISP_MODULE_TRACE", "1")
        .output()
        .assert_exit(42);
    let cache_dir = cold.tmpdir.join(".cranelisp-cache");
    let manifest_path = cache_dir.join("manifest.json");
    let meta_path = cache_dir.join("util.meta.json");
    let object_path = cache_dir.join("util.o");
    let manifest = fs::read_to_string(&manifest_path).expect("read manifest.json");
    let meta = fs::read_to_string(&meta_path).expect("read util.meta.json");
    let current_schema = PRE_SIGNATURE_IDENTITY_SCHEMA + 1;
    assert_eq!(
        extract_manifest_format_version(&manifest),
        Some(current_schema),
        "the identity migration must stamp cache format 29"
    );
    assert_eq!(
        extract_schema_version(&meta),
        Some(current_schema),
        "the identity migration must stamp sidecar schema 29"
    );
    let compiler_fingerprint = extract_json_string_field(&manifest, "compiler_mtime")
        .expect("manifest must carry the current compiler fingerprint")
        .to_string();
    let build_id =
        extract_build_id(&meta).expect("sidecar must carry the current compiler build identifier");
    assert!(
        object_path.is_file(),
        "util.o must exist beside its sidecar"
    );
    let old_object_mtime = mtime(&cold, ".cranelisp-cache/util.o");

    let stale_manifest = set_json_u32(
        &manifest,
        "\"cache_format_version\":",
        PRE_SIGNATURE_IDENTITY_SCHEMA,
    );
    let stale_meta = set_json_u32(&meta, "\"schema_version\":", PRE_SIGNATURE_IDENTITY_SCHEMA);
    assert_eq!(
        extract_json_string_field(&stale_manifest, "compiler_mtime"),
        Some(compiler_fingerprint.as_str()),
        "the stale-version fixture must retain the current compiler fingerprint"
    );
    assert_eq!(
        extract_build_id(&stale_meta).as_deref(),
        Some(build_id.as_str()),
        "the stale-version fixture must retain the current compiler build identifier"
    );
    fs::write(&manifest_path, stale_manifest).expect("write schema-28 manifest");
    fs::write(&meta_path, stale_meta).expect("write schema-28 util sidecar");
    nap_for_mtime();

    let rebuilt = cold
        .run_again()
        .run("main.cl")
        .env("CRANELISP_MODULE_TRACE", "1")
        .output()
        .assert_exit(42);
    assert!(
        !rebuilt.stderr.contains("cache hit") && !rebuilt.stderr.contains("metadata preloaded"),
        "schema 28 must be refused before its table/object can be installed:\n{}",
        rebuilt.stderr
    );
    let rebuilt_manifest = fs::read_to_string(&manifest_path).expect("read rebuilt manifest.json");
    let rebuilt_meta = fs::read_to_string(&meta_path).expect("read rebuilt util.meta.json");
    assert_eq!(
        extract_manifest_format_version(&rebuilt_manifest),
        Some(current_schema)
    );
    assert_eq!(extract_schema_version(&rebuilt_meta), Some(current_schema));
    assert_eq!(
        extract_json_string_field(&rebuilt_manifest, "compiler_mtime"),
        Some(compiler_fingerprint.as_str())
    );
    assert_eq!(extract_build_id(&rebuilt_meta), Some(build_id));
    let rebuilt_object_mtime = mtime(&rebuilt, ".cranelisp-cache/util.o");
    assert_ne!(
        rebuilt_object_mtime, old_object_mtime,
        "schema-28 refusal must rebuild util.o instead of installing the paired object"
    );

    let warm = rebuilt
        .run_again()
        .run("main.cl")
        .env("CRANELISP_MODULE_TRACE", "1")
        .output()
        .assert_exit(42);
    assert!(
        warm.stderr.contains("cache hit (.meta valid) for util"),
        "the rebuilt schema-29 pair must be reusable on the next warm run:\n{}",
        warm.stderr
    );
    assert_eq!(
        mtime(&warm, ".cranelisp-cache/util.o"),
        rebuilt_object_mtime,
        "a current warm hit must retain the rebuilt object"
    );
}

// spec: repl/spec/18-redefinition.md §18.1.2 — restart reconstruction is not
// constrained by the live-slot ownership-ABI gate; cold and warm must agree.
// defect: class=wrong-reject locus=src/session_v4.rs found=S121 owner=/dev
#[test]
fn cache_restored_sum_field_projection_keeps_ownership_abi() {
    let source = "(import [primitives [Int Pure]])\n\
                  (deftype Customer (Addr [:Int a]))\n\
                  (defn r-cust [c] (match c [(Customer.Addr a) a]))\n\
                  (defn main [] (Pure (r-cust (Customer.Addr 40))))\n";
    let uncached = Cranelisp::new()
        .run("main.cl")
        .file("main.cl", source)
        .cli_flag("--no-cache")
        .env("CRANELISP_MODULE_TRACE", "1")
        .output()
        .assert_exit(40);
    assert!(
        !uncached.stderr.contains("entry metadata preloaded"),
        "{}",
        uncached.stderr
    );
    let cold = Cranelisp::new()
        .run("main.cl")
        .file("main.cl", source)
        .env("CRANELISP_MODULE_TRACE", "1")
        .output()
        .assert_exit(40);
    assert!(
        !cold.stderr.contains("entry metadata preloaded"),
        "{}",
        cold.stderr
    );
    let warm = cold
        .run_again()
        .run("main.cl")
        .env("CRANELISP_MODULE_TRACE", "1")
        .output()
        .assert_exit(40);
    assert!(
        warm.stderr
            .lines()
            .any(|line| line == "module-trace: entry metadata preloaded for main"),
        "warm execution must restore the sum projection's module from cache:\n{}",
        warm.stderr
    );
}

// =============================================================================
// Helpers
// =============================================================================

/// Build a per-test program: drop one or more files into the cwd. Each entry is
/// `(rel_path, contents)`. Returns the builder ready for `.run("main.cl")`
/// (or whichever entry the test wants).
fn project(files: &[(&str, &str)]) -> Cranelisp {
    let mut c = Cranelisp::new();
    for (path, contents) in files {
        c = c.file(path, contents);
    }
    c
}

/// Read the mtime of a path under the test tmpdir.
fn mtime(out: &helpers::e2e::CrOutput, rel: &str) -> SystemTime {
    let full = out.tmpdir.join(rel);
    fs::metadata(&full)
        .unwrap_or_else(|e| panic!("mtime: stat {} failed: {e}", full.display()))
        .modified()
        .unwrap_or_else(|e| panic!("mtime: modified {} failed: {e}", full.display()))
}

/// Sleep just long enough that subsequent file rewrites would bump mtime.
fn nap_for_mtime() {
    std::thread::sleep(Duration::from_millis(50));
}

// =============================================================================
// Cache directory layout — Phase 1 §2 seed (merged from cache_seed.rs)
// =============================================================================

/// spec: design/backend/module-caching.md §10 (Edge Cases — Prelude caching) —
/// cache lives under project_root's `.cranelisp-cache/` (= the per-test TempDir).
#[test]
fn cache_lives_under_project_root() {
    let out = Cranelisp::new()
        .run("user.cl")
        .with_prelude(helpers::e2e::PreludeVariant::PrimitivesOnly)
        .user("(defn main [] (Pure 0))")
        .output()
        .assert_ok();

    assert!(
        out.tmp_exists(".cranelisp-cache"),
        "cache must materialise under project_root (= TempDir); got tmpdir={}, stdout={:?}",
        out.tmpdir.display(),
        out.stdout
    );
}

// =============================================================================
// Single-file sanity & artefact emission
// =============================================================================

// spec: design/backend/module-caching.md §5 — single-file compile with caching works
#[test]
fn cache_single_file_sanity() {
    project(&[(
        "main.cl",
        "(import [primitives [Pure]])\n(defn main [] (Pure 42))",
    )])
    .run("main.cl")
    .output()
    .assert_exit(42);
}

// spec: design/backend/module-caching.md §5 — .o file generated after cached compile
#[test]
fn cache_object_file_loadable() {
    let out = project(&[(
        "main.cl",
        "(import [primitives [add-i64 Pure]])\n(defn double [x] (add-i64 x x))\n(defn main [] (Pure (double 21)))",
    )])
    .run("main.cl")
    .output()
    .assert_exit(42);

    assert!(out.tmp_exists(".cranelisp-cache/main.meta.json"));
    assert!(out.tmp_exists(".cranelisp-cache/main.o"));
    assert!(out.tmp_exists(".cranelisp-cache/manifest.json"));
    let obj_size = fs::metadata(out.tmpdir.join(".cranelisp-cache/main.o"))
        .unwrap()
        .len();
    assert!(
        obj_size > 0,
        ".o file should be non-empty (got {obj_size} bytes)"
    );
}

// =============================================================================
// Cache-hit equivalence
// =============================================================================

// spec: design/backend/module-caching.md §8 — cached module equals fresh compile
#[test]
fn cache_load_fresh_compile_equivalence() {
    let fresh = project(&[(
        "main.cl",
        "(import [primitives [add-i64 Pure]])\n(defn double [x] (add-i64 x x))\n(defn main [] (Pure (double 21)))",
    )])
    .run("main.cl")
    .output()
    .assert_exit(42);

    fresh.run_again().run("main.cl").output().assert_exit(42);
}

// spec: design/backend/module-caching.md §8 + spec/09-macros.md §9.12.1 — an
// imported macro behaves identically on cold compilation and warm cache load.
#[test]
fn cache_load_imports_macros_traits_installed() {
    let fresh = project(&[
        (
            "main.cl",
            "(import [ops [increment]])\n\
             (import [primitives [Pure]])\n\
             (defn main [] (Pure (increment 9)))",
        ),
        (
            "ops.cl",
            "(import [primitives [add-i64]])\n\
             (defmacro increment [x] `(add-i64 ~x 1))",
        ),
    ])
    .run("main.cl")
    .output()
    .assert_exit(10);

    fresh.run_again().run("main.cl").output().assert_exit(10);
}

// spec: spec/07-traits.md §7.3 + spec/08-modules.md §8.5 +
// design/backend/module-caching.md §8 — a sibling module's impl remains
// available after cache restoration. Qualified and imported-bare trait
// references are equivalent controls: the cache must preserve both.
// defect: class=enumeration-miss locus=src/process_form/cache_restore.rs::cross-module-impl-enrollment found=S117 owner=/dev
#[test]
fn cache_restores_sibling_written_trait_impls_for_dispatch() {
    fn program(qualified: bool) -> Cranelisp {
        let impl_head = if qualified { "main.lib/Show" } else { "Show" };
        let impl_import = if qualified {
            ""
        } else {
            "(import [main.lib [Show]])\n"
        };
        project(&[
            ("main/lib.cl", "(deftrait Show (show [self] Int))\n"),
            (
                "main/impls.cl",
                &format!(
                    "(import [primitives [Int]])\n\
                     {impl_import}\
                     (deftype W [:Int n])\n\
                     (impl {impl_head} W\n\
                       (defn show [w] (match w [(W n) n])))\n"
                ),
            ),
            (
                "main.cl",
                "(mod lib)\n\
                 (mod impls)\n\
                 (import [primitives [Pure]])\n\
                 (import [main.lib [show]])\n\
                 (import [main.impls [W]])\n\
                 (defn main [] (Pure (show (W 7))))\n",
            ),
        ])
    }

    let qualified_fresh = program(true).run("main.cl").output().assert_exit(7);
    let qualified_warm = qualified_fresh.run_again().run("main.cl").output();

    let bare_fresh = program(false).run("main.cl").output().assert_exit(7);
    let bare_warm = bare_fresh.run_again().run("main.cl").output();

    let failures = [("qualified", qualified_warm), ("bare/imported", bare_warm)]
        .into_iter()
        .filter(|(_, out)| out.status.code() != Some(7))
        .map(|(label, out)| {
            format!(
                "[{label}] exit={:?}\nstdout:\n{}\nstderr:\n{}",
                out.status.code(),
                out.stdout,
                out.stderr
            )
        })
        .collect::<Vec<_>>();
    assert!(
        failures.is_empty(),
        "cache-restored sibling impls MUST remain dispatchable for both trait-reference spellings:\n{}",
        failures.join("\n")
    );
}

// spec: design/backend/module-caching.md §8 — pipeline cache hit second compile
#[test]
fn cache_pipeline_hit_second_compile() {
    let first = project(&[(
        "main.cl",
        "(import [primitives [Pure]])\n(defn val [] 77)\n(defn main [] (Pure (val)))",
    )])
    .run("main.cl")
    .output()
    .assert_exit(77);

    assert!(first.tmp_exists(".cranelisp-cache/main.meta.json"));

    first.run_again().run("main.cl").output().assert_exit(77);
}

// spec: design/backend/module-caching.md §8 — pipeline cache miss on source change
#[test]
fn cache_pipeline_miss_on_source_change() {
    let first = project(&[(
        "main.cl",
        "(import [primitives [Pure]])\n(defn val [] 100)\n(defn main [] (Pure (val)))",
    )])
    .run("main.cl")
    .output()
    .assert_exit(100);

    let second = first.run_again().file(
        "main.cl",
        "(import [primitives [Pure]])\n(defn val [] 123)\n(defn main [] (Pure (val)))",
    );

    second.run("main.cl").output().assert_exit(123);
}

// spec: design/backend/module-caching.md §3 — pipeline transitive invalidation cascade
// (e2e shape: dep change cascades through the pipeline; observable as the
// dependent producing the new value rather than a stale-cache value.)
#[test]
fn cache_invalidation_transitive_pipeline() {
    let first = project(&[(
        "main.cl",
        "(import [primitives [Pure]])\n(defn base [] 10)\n(defn main [] (Pure (base)))",
    )])
    .run("main.cl")
    .output()
    .assert_exit(10);

    first
        .run_again()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(defn base [] 20)\n(defn main [] (Pure (base)))",
        )
        .run("main.cl")
        .output()
        .assert_exit(20);
}

// =============================================================================
// Multi-module cache integration
// =============================================================================

// spec: design/backend/module-caching.md §8 — multi-module cache hit with cross-module call
#[test]
fn cache_multi_module_hit_cross_module_call() {
    let fresh = project(&[
        (
            "main.cl",
            "(import [primitives [Pure]])\n(import [util [helper]])\n(defn main [] (Pure (helper 21)))",
        ),
        (
            "util.cl",
            "(import [primitives [add-i64]])\n(defn helper [x] (add-i64 x x))",
        ),
    ])
    .run("main.cl")
    .output()
    .assert_exit(42);

    assert!(fresh.tmp_exists(".cranelisp-cache/manifest.json"));
    assert!(fresh.tmp_exists(".cranelisp-cache/util.meta.json"));
    assert!(fresh.tmp_exists(".cranelisp-cache/util.o"));

    fresh.run_again().run("main.cl").output().assert_exit(42);
}

// spec: design/backend/module-caching.md §8 — multi-module cache hit with transitive imports
//
// Regression guard for `--run main.cl` over a project whose entry module
// carries `(mod ...)` declarations: the `--run` driver discovers the entry's
// `(mod ...)` declarations before checking for `main`, then serves the whole
// graph from the disk cache on the second run.
#[test]
fn cache_multi_module_transitive_imports() {
    let fresh = project(&[
        (
            "main.cl",
            "(import [primitives [Pure]])\n(mod mid)\n(import [main.mid [relay]])\n(defn main [] (Pure (relay)))",
        ),
        (
            "main/mid.cl",
            "(mod leaf)\n(import [main.mid.leaf [base-val]])\n(defn relay [] (base-val))",
        ),
        ("main/mid/leaf.cl", "(defn base-val [] 77)"),
    ])
    .run("main.cl")
    .output()
    .assert_exit(77);

    assert!(
        fresh.tmp_exists(".cranelisp-cache/main"),
        "submodule cache directory should exist for main/"
    );

    fresh.run_again().run("main.cl").output().assert_exit(77);
}

// spec: spec/08-modules.md §8.2.3/§8.2.5 + design/backend/module-caching.md §8
// — a declared private child is loaded on both the fresh and cache-hit paths.
// defect: class=enumeration-miss locus=src/process_form/cache_restore.rs::declared-submodule-enrollment found=S117 owner=/dev
#[test]
fn cache_restored_parent_enrols_private_test_child() {
    let fresh = project(&[
        (
            "m.cl",
            "(import [primitives [Int]])\n\
             (mod- test)\n\
             (defn probe [] :Int 42)\n",
        ),
        (
            "m/test.cl",
            "(import [primitives [*]])\n\
             (defn test-cache-child [] :(Option String)\n\
               (if true None (Some \"never\")))\n",
        ),
    ])
    .repl()
    .stdin("(import [m [probe]])\n/run-tests m.test\n")
    .output()
    .assert_ok()
    .assert_stdout_contains("1 passed");

    fresh
        .run_again()
        .repl()
        .stdin("(import [m [probe]])\n/run-tests m.test\n")
        .output()
        .assert_ok()
        .assert_stdout_contains("1 passed");
}

// spec: design/backend/module-caching.md §6 — multi-module cache invalidation on dep change
#[test]
fn cache_multi_module_invalidation_dependency_change() {
    let first = project(&[
        (
            "main.cl",
            "(import [primitives [Pure]])\n(import [util [helper]])\n(defn main [] (Pure (helper 10)))",
        ),
        (
            "util.cl",
            "(import [primitives [add-i64]])\n(defn helper [x] (add-i64 x 1))",
        ),
    ])
    .run("main.cl")
    .output()
    .assert_exit(11);

    first
        .run_again()
        .file(
            "util.cl",
            "(import [primitives [add-i64]])\n(defn helper [x] (add-i64 x x))",
        )
        .run("main.cl")
        .output()
        .assert_exit(20);
}

// spec: design/backend/module-caching.md §6 — unchanged dep stays cached (mtime preserved)
#[test]
fn cache_multi_module_unchanged_dep_stays_cached() {
    let first = project(&[
        (
            "main.cl",
            "(import [primitives [Pure]])\n(import [util [helper]])\n(defn main [] (Pure (helper 5)))",
        ),
        (
            "util.cl",
            "(import [primitives [add-i64]])\n(defn helper [x] (add-i64 x x))",
        ),
    ])
    .run("main.cl")
    .output()
    .assert_exit(10);

    let mtime1 = mtime(&first, ".cranelisp-cache/util.meta.json");
    nap_for_mtime();

    let second = first
        .run_again()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(import [util [helper]])\n(defn main [] (Pure (helper 7)))",
        )
        .run("main.cl")
        .output()
        .assert_exit(14);

    let mtime2 = mtime(&second, ".cranelisp-cache/util.meta.json");
    assert_eq!(
        mtime1, mtime2,
        "util's .meta.json must NOT be rewritten when util's source is unchanged"
    );
}

// spec: design/backend/module-caching.md §8 — multi-module with multiple imports from one dep
#[test]
fn cache_multi_module_multiple_imports() {
    let fresh = project(&[
        (
            "main.cl",
            "(import [primitives [Pure]])\n(import [util [add-one double]])\n(defn main [] (Pure (add-one (double 10))))",
        ),
        (
            "util.cl",
            "(import [primitives [add-i64]])\n\
             (defn add-one [x] (add-i64 x 1))\n\
             (defn double [x] (add-i64 x x))",
        ),
    ])
    .run("main.cl")
    .output()
    .assert_exit(21);

    fresh.run_again().run("main.cl").output().assert_exit(21);
}

// spec: design/backend/module-caching.md §8 — main imports from two independent modules
#[test]
fn cache_multi_module_two_deps() {
    let fresh = project(&[
        (
            "main.cl",
            "(import [primitives [Pure]])\n\
             (import [math [square]])\n\
             (import [constants [base-val]])\n\
             (defn main [] (Pure (square (base-val))))",
        ),
        (
            "math.cl",
            "(import [primitives [mul-i64]])\n(defn square [x] (mul-i64 x x))",
        ),
        ("constants.cl", "(defn base-val [] 7)"),
    ])
    .run("main.cl")
    .output()
    .assert_exit(49);

    assert!(fresh.tmp_exists(".cranelisp-cache/math.meta.json"));
    assert!(fresh.tmp_exists(".cranelisp-cache/constants.meta.json"));

    let second = fresh.run_again().run("main.cl").output().assert_exit(49);

    // Change one dep; the other stays cached and main re-runs with new value.
    second
        .run_again()
        .file("constants.cl", "(defn base-val [] 3)")
        .run("main.cl")
        .output()
        .assert_exit(9);
}

// =============================================================================
// Prelude caching
// =============================================================================

// spec: design/backend/module-caching.md §10 — prelude cached on first build
#[test]
fn cache_prelude_modules_cached() {
    let first = project(&[
        (
            "main.cl",
            "(import [primitives [Pure]])\n(defn main [] (Pure 42))",
        ),
        ("prelude.cl", "(defn id [x] x)"),
    ])
    .run("main.cl")
    .output()
    .assert_exit(42);

    assert!(first.tmp_exists(".cranelisp-cache/prelude.meta.json"));

    let mtime1 = mtime(&first, ".cranelisp-cache/prelude.meta.json");
    nap_for_mtime();

    let second = first.run_again().run("main.cl").output().assert_exit(42);

    let mtime2 = mtime(&second, ".cranelisp-cache/prelude.meta.json");
    assert_eq!(
        mtime1, mtime2,
        "prelude .meta.json must not be rewritten on cache hit"
    );
}

// spec: design/backend/module-caching.md §10 — prelude change invalidates user module
#[test]
fn cache_prelude_change_invalidates_user_module() {
    let first = project(&[
        (
            "main.cl",
            "(import [primitives [Pure]])\n(defn main [] (Pure 42))",
        ),
        ("prelude.cl", "(defn id [x] x)"),
    ])
    .run("main.cl")
    .output()
    .assert_exit(42);

    first
        .run_again()
        .file("prelude.cl", "(defn id [x] x)\n(defn const [x y] x)")
        .run("main.cl")
        .output()
        .assert_exit(42);
}

// spec: design/backend/module-caching.md §8 — multi-module with prelude works
#[test]
fn cache_multi_module_with_prelude() {
    let fresh = project(&[
        (
            "main.cl",
            "(import [primitives [Pure]])\n(import [util [helper]])\n(defn main [] (Pure (helper 5)))",
        ),
        (
            "util.cl",
            "(import [primitives [add-i64]])\n(defn helper [x] (add-i64 x x))",
        ),
        ("prelude.cl", "(defn id [x] x)"),
    ])
    .run("main.cl")
    .output()
    .assert_exit(10);

    fresh.run_again().run("main.cl").output().assert_exit(10);
}

// =============================================================================
// REPL restart / --link cache reuse
// =============================================================================

// spec: design/backend/module-caching.md §10 — REPL restart cache hit (helper.meta.json mtime preserved)
#[test]
fn cache_repl_restart_cache_hit() {
    let first = project(&[
        (
            "main.cl",
            "(import [primitives [Pure]])\n(import [helper [add-one]])\n(defn main [] (Pure (add-one 41)))",
        ),
        (
            "helper.cl",
            "(import [primitives [add-i64]])\n(defn add-one [x] (add-i64 x 1))",
        ),
    ])
    .run("main.cl")
    .output()
    .assert_exit(42);

    assert!(first.tmp_exists(".cranelisp-cache/helper.meta.json"));
    let m1 = mtime(&first, ".cranelisp-cache/helper.meta.json");
    nap_for_mtime();

    let second = first.run_again().run("main.cl").output().assert_exit(42);

    let m2 = mtime(&second, ".cranelisp-cache/helper.meta.json");
    assert_eq!(
        m1, m2,
        "helper .meta.json must not be rewritten on REPL-restart cache hit"
    );
}

// spec: design/backend/module-caching.md §10 — incremental monomorphisation (cached dep usable)
#[test]
fn cache_repl_incremental_monomorphisation() {
    let first = project(&[
        (
            "main.cl",
            "(import [primitives [Pure]])\n(import [math [double]])\n(defn main [] (Pure (double 21)))",
        ),
        (
            "math.cl",
            "(import [primitives [add-i64]])\n(defn double [x] (add-i64 x x))",
        ),
    ])
    .run("main.cl")
    .output()
    .assert_exit(42);

    first
        .run_again()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(import [math [double]])\n(defn main [] (Pure (double 10)))",
        )
        .run("main.cl")
        .output()
        .assert_exit(20);
}

// spec: design/backend/module-caching.md §11 — quick-build links cached .o files (mtime preserved)
#[test]
fn cache_quick_build_links_cached_objects() {
    let first = project(&[
        (
            "main.cl",
            "(import [primitives [Pure]])\n(import [helper [double]])\n(defn main [] (Pure (double 21)))",
        ),
        (
            "helper.cl",
            "(import [primitives [add-i64]])\n(defn double [x] (add-i64 x x))",
        ),
    ])
    .run("main.cl")
    .output()
    .assert_exit(42);

    assert!(first.tmp_exists(".cranelisp-cache/helper.o"));
    let helper_obj_size = fs::metadata(first.tmpdir.join(".cranelisp-cache/helper.o"))
        .unwrap()
        .len();
    assert!(helper_obj_size > 0);

    let m1 = mtime(&first, ".cranelisp-cache/helper.o");
    nap_for_mtime();

    let second = first.run_again().run("main.cl").output().assert_exit(42);

    let m2 = mtime(&second, ".cranelisp-cache/helper.o");
    assert_eq!(m1, m2, "helper.o must not be rewritten on cache hit");
}

// spec: design/backend/module-caching.md §11 — cold-start (no cache present) produces correct result
#[test]
fn cache_quick_build_fallback_on_missing_cache() {
    let out = project(&[
        (
            "main.cl",
            "(import [primitives [Pure]])\n(import [helper [triple]])\n(defn main [] (Pure (triple 14)))",
        ),
        (
            "helper.cl",
            "(import [primitives [add-i64]])\n(defn triple [x] (add-i64 x (add-i64 x x)))",
        ),
    ])
    .run("main.cl")
    .output()
    .assert_exit(42);

    assert!(out.tmp_exists(".cranelisp-cache/manifest.json"));
    assert!(out.tmp_exists(".cranelisp-cache/helper.meta.json"));
}

// =============================================================================
// Round-trip observable equivalence (G.11 — runtime parity only; structural
// SymbolTable inspection is internal-API, quarantined.)
// =============================================================================

// spec: design/backend/module-caching.md §14 — single-module round-trip
#[test]
fn cache_round_trip_single_module_observable_equivalence() {
    let fresh = project(&[(
        "main.cl",
        "(import [primitives [Pure]])\n(defn main [] (Pure 99))",
    )])
    .run("main.cl")
    .output()
    .assert_exit(99);

    assert!(fresh.tmp_exists(".cranelisp-cache/main.meta.json"));

    fresh.run_again().run("main.cl").output().assert_exit(99);
}

// spec: design/backend/module-caching.md §14 — multi-module round-trip with cross-module call
#[test]
fn cache_round_trip_multi_module_observable_equivalence() {
    let fresh = project(&[
        (
            "main.cl",
            "(import [primitives [Pure]])\n(import [util [helper]])\n(defn main [] (Pure (helper 21)))",
        ),
        (
            "util.cl",
            "(import [primitives [add-i64]])\n(defn helper [x] (add-i64 x x))",
        ),
    ])
    .run("main.cl")
    .output()
    .assert_exit(42);

    assert!(fresh.tmp_exists(".cranelisp-cache/util.meta.json"));

    fresh.run_again().run("main.cl").output().assert_exit(42);
}

// spec: design/backend/module-caching.md §3 — cache invalidation on dep change is observable
#[test]
fn cache_invalidation_on_dep_change_e2e() {
    let first = project(&[
        (
            "main.cl",
            "(import [primitives [Pure]])\n(import [dep [val]])\n(defn main [] (Pure (val)))",
        ),
        ("dep.cl", "(defn val [] 11)"),
    ])
    .run("main.cl")
    .output()
    .assert_exit(11);

    assert!(first.tmp_exists(".cranelisp-cache/dep.meta.json"));

    first
        .run_again()
        .file("dep.cl", "(defn val [] 22)")
        .run("main.cl")
        .output()
        .assert_exit(22);
}

// =============================================================================
// REPL-mode cache integration — Wave 6 batch 2 Part A carry-forward
//
// Per the Wave 6 batch 2 audit: the existing
// `cache_repl_restart_cache_hit` and `cache_repl_incremental_monomorphisation`
// cover the *batch-mode* (`--run`) cache restart flow. The legacy
// `tests/sprint23.rs::cache_repl_*` cluster covers the *interactive REPL
// session* (stdin-driven) cache write/load/reset surface — a distinct
// angle preserved per Wave 5.5/5.6 multi-angle rule. `cache_writer_survives_reset`
// is the sole `/reset`-+-cache test in the codebase.
//
// SPRINT 78 NOTE — the three TestStandard-prelude tests below
// (`cache_repl_writes_manifest_on_prelude_load`,
//  `cache_repl_second_session_loads_prelude_from_cache`,
//  `cache_repl_writer_survives_slash_reset`) now PASS. They use the QA-owned
// `PreludeVariant::TestStandard` fixture
// (`tests/fixtures/preludes/test-standard.cl`), which loads NO real workspace
// stdlib, so there was never anything to decouple. They had been RED at the
// FIRST session on a genuine TRAIT-OPERATOR codegen defect: `(+ N M)` against a
// prelude that declares `Num`/`impl Num Int` raised `undefined function: +`
// ("codegen failed for /"). That SAME defect was the trait-operator prelude
// fallback gap tracked as FIXME 0315, RESOLVED in S78 — it had also red-ed ~12
// tests in `tests/spec_07_traits.rs` (`operator_plus_int`, `operator_plus_float`,
// `trait_impl_body_uses_operator`, `constrained_polymorphism_int_then_float`,
// …), which carried the minimal repro. The cache trio were downstream
// casualties: the empty-prelude / plain-fn cache siblings
// (`cache_repl_empty_prelude_session_2_evaluates_literal`,
//  `cache_repl_minimal_plain_fn_prelude_restored_on_session_2`) always PASSED,
// proving the cache-hit machinery was fine and the failure was the prelude's
// operator dispatch, not the cache. (Earlier mis-attribution to the stdlib glob
// collision, FIXME 0312, was incorrect — the real cause was the trait-operator
// fallback, FIXME 0315.)
// =============================================================================

// spec: design/int/repl-lifecycle.md §4.1 — Cache Write After Module Compilation.
//       repl/spec.md §14.7 — Interaction with Object Cache.
//   When the REPL compiles prelude modules at startup (here the
//   TestStandard fixture prelude), `.cranelisp-cache/manifest.json`
//   is materialised in the project_root (= per-test TempDir).
//
// (carry: legacy/sprint23.rs::cache_repl_writes_on_import)
#[test]
fn cache_repl_writes_manifest_on_prelude_load() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(helpers::e2e::PreludeVariant::TestStandard)
        .stdin("(+ 1 2)\n/quit\n")
        .output();

    assert!(
        out.stdout.contains("3"),
        "prelude operator should evaluate: stdout={:?}",
        out.stdout
    );
    assert!(
        out.tmp_exists(".cranelisp-cache/manifest.json"),
        "cache manifest should exist after REPL startup with prelude; tmpdir={}",
        out.tmpdir.display()
    );
}

// spec: design/int/repl-lifecycle.md §4.2 — Cache Load on Startup/Reset.
//       repl/spec.md §14.7 — Interaction with Object Cache.
//   Two REPL sessions in the same project root: first populates cache,
//   second loads prelude from cache. Both produce identical results.
//
//   Note: legacy header documents Sprint 59 Workstream A resolution —
//   the cache-hit arm of `inject_prelude_if_needed` now calls
//   `register_imports` on the user-module check state with an
//   `ImportNames::Glob` spec for `prelude`, matching the fresh-compile
//   arm. This test guards that resolution.
//
// (carry: legacy/sprint23.rs::cache_repl_loads_on_startup)
#[test]
fn cache_repl_second_session_loads_prelude_from_cache() {
    let first = Cranelisp::new()
        .repl()
        .with_prelude(helpers::e2e::PreludeVariant::TestStandard)
        .stdin("(+ 40 2)\n/quit\n")
        .output();

    assert!(
        first.stdout.contains("42"),
        "first session should evaluate via prelude: stdout={:?}",
        first.stdout
    );
    assert!(
        first.tmp_exists(".cranelisp-cache/manifest.json"),
        "cache must materialise after first session"
    );

    // Second session — same TempDir, prelude from cache.
    let second = first
        .run_again()
        .repl()
        .with_prelude(helpers::e2e::PreludeVariant::TestStandard)
        .stdin("(+ 40 2)\n/quit\n")
        .output();

    assert!(
        second.stdout.contains("42"),
        "second session (cache loaded) should also produce 42: stdout={:?}",
        second.stdout
    );
}

// spec: design/int/repl-lifecycle.md §2.3 — Prelude Reload After Reset.
//       design/int/repl-lifecycle.md §4.2 — Cache Load on Startup/Reset.
//   After `/reset`, the prelude reload still produces working state and
//   the cache survives across the reset. This is the ONLY `/reset`+cache
//   integration test in the suite.
//
// (carry: legacy/sprint23.rs::cache_writer_survives_reset)
#[test]
fn cache_repl_writer_survives_slash_reset() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(helpers::e2e::PreludeVariant::TestStandard)
        .stdin("(+ 3 4)\n/reset\n(+ 5 6)\n/quit\n")
        .output();

    assert!(
        out.stdout.contains("7"),
        "before /reset, (+ 3 4) should produce 7: stdout={:?}",
        out.stdout
    );
    assert!(
        out.stdout.contains("11"),
        "after /reset, (+ 5 6) should produce 11 (prelude reloaded): stdout={:?}",
        out.stdout
    );
    assert!(
        out.tmp_exists(".cranelisp-cache/manifest.json"),
        "cache manifest must survive /reset"
    );
}

// =============================================================================
// Sprint 59 Workstream A — cache-hit prelude-restoration regression guards.
//
// Sibling tests to `cache_repl_second_session_loads_prelude_from_cache` (which
// uses TestStandard prelude — operators + traits + ADTs). These two reductions
// partition the discrimination axis the original Sprint 59 bug investigation
// needed:
//
//   - Plain prelude (single defn, no operators / traits / impls): if session 2
//     fails to call it, the bug is universal across binding shapes.
//   - Empty prelude (no symbols at all): exercises only the cache-hit
//     module-load pathway. If session 2 fails on a literal, the bug is at the
//     module level, not the symbol-rebinding level.
//
// Carried from `tests/legacy/sprint59_cache_repro.rs` per the Sprint 64 Wave 6
// batch 3 audit. Headed by FIXME 0145.
// =============================================================================

// spec: design/int/repl-lifecycle.md §4.2 — Cache Load on Startup/Reset.
//       repl/spec.md §15.2 — session-persistence cache-hit symbol restoration.
//   Reduction A: smallest possible prelude — single plain `(defn f [] 42)`.
//   No traits, no impls, no operators. If session 2 cannot call `f`,
//   cache-hit prelude restoration is broken for EVERY binding type — not
//   just operator/trait machinery.
//
// A cache-restored prelude establishes the same fallback as a fresh one:
//   design/int/int.md §6.5.
//
// (carry: legacy/sprint59_cache_repro.rs::s59_cache_hit_plain_prelude_fn_not_restored)
#[test]
fn cache_repl_minimal_plain_fn_prelude_restored_on_session_2() {
    // Drop a single-defn prelude under a per-test lib dir; route CRANELISP_LIB
    // there so the binary auto-discovers it.
    let first = Cranelisp::new()
        .repl()
        .file("lib/prelude.cl", "(defn f [] 42)\n")
        .lib_dir("lib")
        .stdin("(f)\n/quit\n")
        .output();

    assert!(
        first.stdout.contains("42"),
        "session 1 should print 42 (fresh compile): stdout={:?}",
        first.stdout
    );
    assert!(
        first.tmp_exists(".cranelisp-cache/manifest.json"),
        "session 1 should populate cache manifest for a prelude with at least one export"
    );

    // Session 2 — same TempDir, prelude resolves via cache hit.
    let second = first
        .run_again()
        .repl()
        .lib_dir("lib")
        .stdin("(f)\n/quit\n")
        .output();

    assert!(
        second.stdout.contains("42"),
        "session 2 (cache hit) should also print 42; stdout={:?} stderr={:?}",
        second.stdout,
        second.stderr
    );
}

// spec: design/int/repl-lifecycle.md §4.2 — Cache Load on Startup/Reset.
//       repl/spec.md §15.2 — empty-prelude pathway (negative control).
//   Reduction B: empty prelude — no bindings to rebind. Exercises only the
//   cache-hit module-load pathway. If this fails, the bug is at the
//   module-load level (not symbol rebinding). Negative-control rung.
//
// REGRESSION-GUARD: Sprint 59 Workstream A — discriminator probe.
//
// (carry: legacy/sprint59_cache_repro.rs::s59_cache_hit_empty_prelude_basic_eval_works)
#[test]
fn cache_repl_empty_prelude_session_2_evaluates_literal() {
    let first = Cranelisp::new()
        .repl()
        .file("lib/prelude.cl", ";; empty\n")
        .lib_dir("lib")
        .stdin("42\n/quit\n")
        .output();

    assert!(
        first.stdout.contains("42"),
        "session 1 should print 42: stdout={:?}",
        first.stdout
    );

    // Session 2 — same TempDir, empty prelude reloaded from cache.
    let second = first
        .run_again()
        .repl()
        .lib_dir("lib")
        .stdin("42\n/quit\n")
        .output();

    assert!(
        second.stdout.contains("42"),
        "session 2 with empty prelude should also print 42; stdout={:?} stderr={:?}",
        second.stdout,
        second.stderr
    );
}

// =============================================================================
// Sprint 60 Workstream C — `.meta.json` build_id field
// =============================================================================
//
// Three regression guards covering the user-surface invariant of the
// build-id cache invalidation extension. Unit-tier coverage for the
// serialise/deserialise path lives in
// `crates/cranelisp-backend/src/cache/serialize.rs`
// (`build_id_round_trip_succeeds`, `stale_build_id_produces_build_id_mismatch`,
// `missing_build_id_field_routes_cache_stale`); these e2e tests prove
// the user-surface invariant fires through the binary subprocess.
// Carry from the Sprint 64 Wave 6 batch 4 audit.

/// Trivial single-file program used by the build_id tests below. `main`
/// returns 0 (spec §12.6) so `assert_ok()` is the right assertion.
const BUILD_ID_SRC: &str = "(import [primitives [add-i64 Pure]])\n(defn double [x] (add-i64 x x))\n(defn main [] (Pure (double 0)))";

/// Extract the `build_id` string from the raw `.meta.json` text. Returns
/// `None` if the field is absent. Narrow parser — looks for
/// `"build_id":"..."` as a top-level field; avoids a serde_json dep.
fn extract_build_id(meta_text: &str) -> Option<String> {
    let needle = "\"build_id\":";
    let idx = meta_text.find(needle)?;
    let after = &meta_text[idx + needle.len()..];
    let after = after.trim_start();
    let after = after.strip_prefix('"')?;
    let end = after.find('"')?;
    Some(after[..end].to_string())
}

/// Rewrite the `build_id` field's value in raw JSON text. Panics if the
/// field is absent — caller must ensure presence first.
fn set_build_id(meta_text: &str, new_value: &str) -> String {
    let needle = "\"build_id\":";
    let idx = meta_text
        .find(needle)
        .expect("meta text must contain build_id field for set_build_id");
    let before = &meta_text[..idx + needle.len()];
    let after = &meta_text[idx + needle.len()..];
    let after_trim = after.trim_start();
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

/// Remove the `build_id` field (and trailing comma if present) for the
/// pre-Sprint-60 shape simulation.
fn remove_build_id(meta_text: &str) -> String {
    let needle = "\"build_id\":";
    let idx = meta_text
        .find(needle)
        .expect("meta text must contain build_id field for remove_build_id");
    let after = &meta_text[idx + needle.len()..];
    let after_trim_offset = after.len() - after.trim_start().len();
    let val = &after[after_trim_offset + 1..]; // skip opening quote
    let end_quote = val
        .find('"')
        .expect("unterminated build_id value in meta.json");
    let mut end_idx = idx + needle.len() + after_trim_offset + 1 + end_quote + 1;
    let tail = &meta_text[end_idx..];
    if tail.trim_start().starts_with(',') {
        let ws = tail.len() - tail.trim_start().len();
        end_idx += ws + 1 /* the comma */;
        let after_comma = &meta_text[end_idx..];
        let ws2 = after_comma.len() - after_comma.trim_start().len();
        end_idx += ws2;
    }
    format!("{}{}", &meta_text[..idx], &meta_text[end_idx..])
}

// spec: design/backend/module-caching.md §4 — Serialization Format.
//   First compile populates `.meta.json` with a non-empty build_id, and
//   schema_version remains co-present (additive, not substitutive — Sprint
//   60 Architecture Review Condition 3).
//
// REGRESSION-GUARD: Sprint 60 Workstream C — write-side e2e wrapper
//   around unit `build_id_round_trip_succeeds` in
//   crates/cranelisp-backend/src/cache/serialize.rs.
//
// (carry: legacy/sprint60_cache_build_marker.rs::cache_meta_carries_build_id_after_first_compile)
#[test]
fn cache_meta_carries_build_id_after_first_compile() {
    let out = Cranelisp::new()
        .run("main.cl")
        .file("main.cl", BUILD_ID_SRC)
        .output()
        .assert_ok();

    let meta_path = out.tmpdir.join(".cranelisp-cache").join("main.meta.json");
    assert!(
        meta_path.exists(),
        "main.meta.json must be written under .cranelisp-cache/"
    );
    let text = fs::read_to_string(&meta_path).expect("read main.meta.json");
    let build_id = extract_build_id(&text)
        .unwrap_or_else(|| panic!("meta.json must carry a build_id field; got:\n{text}"));
    assert!(
        !build_id.is_empty(),
        "build_id must be non-empty; meta=\n{text}"
    );
    // Negative guard: schema_version must remain alongside build_id.
    // Additive (Sprint 60 Architecture Review Condition 3), not substitutive.
    assert!(
        text.contains("\"schema_version\":"),
        "schema_version must remain alongside build_id; meta=\n{text}"
    );
}

// spec: design/backend/module-caching.md §6 — Cache Invalidation Strategy.
//   Tampering with build_id forces a fresh build on the next compile:
//   second compile MUST succeed, and meta.build_id MUST be re-stamped to
//   the original (proving the cache miss + re-emit path ran rather than
//   silently honouring the stale meta).
//
// REGRESSION-GUARD: Sprint 60 Workstream C — invalidation-side e2e
//   wrapper around unit `stale_build_id_produces_build_id_mismatch`.
//
// (carry: legacy/sprint60_cache_build_marker.rs::cache_meta_with_stale_build_id_triggers_recompile)
#[test]
fn cache_meta_with_stale_build_id_triggers_recompile() {
    let first = Cranelisp::new()
        .run("main.cl")
        .file("main.cl", BUILD_ID_SRC)
        .output()
        .assert_ok();

    let meta_path = first.tmpdir.join(".cranelisp-cache").join("main.meta.json");
    let original_text = fs::read_to_string(&meta_path).expect("read main.meta.json");
    let original_build_id = extract_build_id(&original_text).expect("first compile wrote build_id");

    // Patch meta.build_id to a synthetic stale value.
    let patched_text = set_build_id(&original_text, "0.0.0+stale-synthetic");
    assert_eq!(
        extract_build_id(&patched_text).as_deref(),
        Some("0.0.0+stale-synthetic"),
        "patch must land before second compile"
    );
    fs::write(&meta_path, &patched_text).expect("write patched meta");

    // Second compile in the same TempDir — cache must miss and re-emit.
    let second = first.run_again().run("main.cl").output().assert_ok();

    let after_path = second
        .tmpdir
        .join(".cranelisp-cache")
        .join("main.meta.json");
    let after_text = fs::read_to_string(&after_path).expect("read meta after rebuild");
    let rewritten_build_id = extract_build_id(&after_text).expect("rebuild must restore build_id");
    // Negative: the stale sentinel MUST NOT survive — its survival would
    // mean the cache honoured the patched meta (i.e. invalidation didn't fire).
    assert_ne!(
        rewritten_build_id, "0.0.0+stale-synthetic",
        "stale build_id survived — cache did not invalidate on build_id mismatch"
    );
    assert_eq!(
        rewritten_build_id, original_build_id,
        "rebuild must stamp the current build_id (same as first compile)"
    );
}

// spec: design/backend/module-caching.md §6 — pre-Sprint-60 `.meta.json`
//   shape (no `build_id` field at all) MUST be treated as stale. Simulated
//   by removing the field from a freshly-written meta.
//
// REGRESSION-GUARD: Sprint 60 Workstream C — schema-evolution e2e wrapper
//   around unit `missing_build_id_field_routes_cache_stale`.
//
// (carry: legacy/sprint60_cache_build_marker.rs::cache_meta_without_build_id_field_triggers_recompile)
#[test]
fn cache_meta_without_build_id_field_triggers_recompile() {
    let first = Cranelisp::new()
        .run("main.cl")
        .file("main.cl", BUILD_ID_SRC)
        .output()
        .assert_ok();

    let meta_path = first.tmpdir.join(".cranelisp-cache").join("main.meta.json");
    let original_text = fs::read_to_string(&meta_path).expect("read main.meta.json");
    let original_build_id = extract_build_id(&original_text).expect("first compile wrote build_id");

    // Strip the build_id field entirely — pre-Sprint-60 cache shape.
    let patched_text = remove_build_id(&original_text);
    fs::write(&meta_path, &patched_text).expect("write patched meta");
    let verify = fs::read_to_string(&meta_path).expect("re-read patched meta");
    assert!(
        extract_build_id(&verify).is_none(),
        "patched meta must have no build_id field; got:\n{verify}"
    );

    // Second compile — cache must miss and rebuild.
    let second = first.run_again().run("main.cl").output().assert_ok();

    let after_path = second
        .tmpdir
        .join(".cranelisp-cache")
        .join("main.meta.json");
    let after_text = fs::read_to_string(&after_path).expect("read meta after rebuild");
    let restored = extract_build_id(&after_text).expect("rebuild must restore build_id");
    assert_eq!(
        restored, original_build_id,
        "rebuild must stamp the current build_id on pre-Sprint-60-shape caches"
    );
}

// =============================================================================
// L-B3(1)–(3) — CRANELISP_NO_OWNERSHIP cache-manifest key (S101 stage M)
// =============================================================================
//
// S101 Phase-5 stage 1 QA-first RED set (`tests/plan/s100-ownership-verification.md`
// §3.1 L-B3 / §6.1). The `CRANELISP_NO_OWNERSHIP` analysis-off toggle ships at
// stage M with its cache-manifest global key (`/arch` S101 Phase-2 ruling,
// `sprints/SPRINT.md` §Architecture review): flipping the toggle must
// invalidate the module cache WHOLESALE — mixed-ownership-ABI caches must be
// unrepresentable (`design/backend/ownership-codegen.md` §2.3). RED at draft
// (the env var was a no-op); RESOLVED S101 Wave 3 — the toggle + manifest key
// + `read_manifest` other-polarity-as-absent landed; both tests GREEN.
// Wave-5 amendment: every session pins its polarity EXPLICITLY (env_remove
// for OFF) so the tests hold under the L-B2(i) ambient-polarity lane.
//
// Observability: dep-module cache hits emit `module-trace: cache hit …` on
// stderr under CRANELISP_MODULE_TRACE=1 (tests/CLAUDE.md §Diagnostic Logging);
// recompilation is additionally pinned via the dep's `.o` mtime.

const LB3_MAIN: &str =
    "(import [primitives [Pure]])\n(import [util [helper]])\n(defn main [] (Pure (helper 21)))";
const LB3_UTIL: &str = "(import [primitives [add-i64]])\n(defn helper [x] (add-i64 x x))";

// spec: design/backend/ownership-codegen.md §2.3 — flipping the ownership
// toggle invalidates the cache wholesale: every module recompiles (zero cache
// hits — no stale `.o` of the other polarity is ever consumed) and output is
// identical. RED on HEAD (env var unknown ⇒ full cache hits on the flip run).
#[test]
fn cache_ownership_toggle_flip_invalidates_wholesale_no_stale_objects() {
    // Polarity-META test: every session pins its polarity EXPLICITLY
    // (`env_remove` for OFF — the toggle is presence-gated) so the flip legs
    // hold under the L-B2(i) lane, which runs the whole suite with
    // CRANELISP_NO_OWNERSHIP=1 in the ambient env (found at S101 Wave 5).
    let first = project(&[("main.cl", LB3_MAIN), ("util.cl", LB3_UTIL)])
        .env_remove("CRANELISP_NO_OWNERSHIP")
        .run("main.cl")
        .output()
        .assert_exit(42);
    let o_mtime1 = mtime(&first, ".cranelisp-cache/util.o");
    nap_for_mtime();

    let flipped = first
        .run_again()
        .env("CRANELISP_NO_OWNERSHIP", "1")
        .env("CRANELISP_MODULE_TRACE", "1")
        .run("main.cl")
        .output()
        .assert_exit(42); // identical observable output under the other polarity
    assert!(
        !flipped.stderr.contains("cache hit"),
        "toggle flip must invalidate wholesale — no module may cache-hit \
         (mixed-ABI caches unrepresentable); stderr:\n{}",
        flipped.stderr
    );
    let o_mtime2 = mtime(&flipped, ".cranelisp-cache/util.o");
    assert_ne!(
        o_mtime1, o_mtime2,
        "the dep's .o must be recompiled (rewritten) on the flipped run, \
         not served stale"
    );
}

// spec: design/backend/ownership-codegen.md §2.3 — round-trip: flipping back
// invalidates wholesale again (the key is part of the manifest, both
// directions), and a re-run at the SAME polarity serves full cache hits (the
// key is stable — guards against an always-miss implementation). RED on HEAD
// (the flip legs observe cache hits today).
#[test]
fn cache_ownership_toggle_round_trip_and_same_polarity_stability() {
    // Polarity-META test: every session pins its polarity EXPLICITLY (see the
    // sibling test's note — ambient-env robustness for the L-B2(i) lane).
    // Leg 1: populate at default polarity.
    let first = project(&[("main.cl", LB3_MAIN), ("util.cl", LB3_UTIL)])
        .env_remove("CRANELISP_NO_OWNERSHIP")
        .run("main.cl")
        .output()
        .assert_exit(42);

    // Leg 2: flip on ⇒ wholesale.
    let on = first
        .run_again()
        .env("CRANELISP_NO_OWNERSHIP", "1")
        .env("CRANELISP_MODULE_TRACE", "1")
        .run("main.cl")
        .output()
        .assert_exit(42);
    assert!(
        !on.stderr.contains("cache hit"),
        "flip ON must recompile wholesale; stderr:\n{}",
        on.stderr
    );

    // Leg 3: flip back off ⇒ wholesale again (round-trip), output identical.
    let off = on
        .run_again()
        .env_remove("CRANELISP_NO_OWNERSHIP")
        .env("CRANELISP_MODULE_TRACE", "1")
        .run("main.cl")
        .output()
        .assert_exit(42);
    assert!(
        !off.stderr.contains("cache hit"),
        "flip back OFF must recompile wholesale again; stderr:\n{}",
        off.stderr
    );

    // Leg 4: same polarity re-run ⇒ full cache hits (key stability — this leg
    // is green-at-draft by itself; the test is RED on the flip legs above).
    let stable = off
        .run_again()
        .env_remove("CRANELISP_NO_OWNERSHIP")
        .env("CRANELISP_MODULE_TRACE", "1")
        .run("main.cl")
        .output()
        .assert_exit(42);
    assert!(
        stable.stderr.contains("cache hit"),
        "same-polarity re-run must serve cache hits (the manifest key must be \
         stable, not always-miss); stderr:\n{}",
        stable.stderr
    );
}

// =============================================================================
// L-B3(4) — the CACHE_SCHEMA_VERSION 14→15 wholesale-invalidation lane
// (S103 increment-II; qa plan `tests/plan/s103-test-plan.md` §1.2 / §4).
// =============================================================================
//
// R5's value-flattening is a representation change: a post-R5 `.o` stores
// one-word single-ctor payloads BY VALUE where a pre-R5 `.o` boxed them, so a
// pre-R5 object is silently incompatible and MUST NOT be consumed after R5
// lands. Decision-34 handles this by bumping `CACHE_SCHEMA_VERSION`
// (`crates/cranelisp-backend/src/cache/mod.rs`) — the live value is **14**
// (verified at Phase-3), and R5 bumps it to **15** in the Wave-3 change-set. A
// cache stamped with the pre-R5 schema then routes through
// `CacheStale::SchemaMismatch` (cache-miss → recompute).
//
// Both tests below are RED at draft (schema is still 14) and flip GREEN with
// the bump.

const SCHEMA_MAIN: &str =
    "(import [primitives [Pure]])\n(import [util [helper]])\n(defn main [] (Pure (helper 21)))";
const SCHEMA_UTIL: &str = "(import [primitives [add-i64]])\n(defn helper [x] (add-i64 x x))";

/// The schema version the pre-R5 `.o` carries — the value R5's bump must reject.
/// (= the live `CACHE_SCHEMA_VERSION` at S103 Phase-3.)
const PRE_R5_SCHEMA: u32 = 14;

/// Extract the integer `schema_version` field from raw `.meta.json` text.
/// Narrow parser (avoids a serde_json dep), mirroring `extract_build_id`.
fn extract_schema_version(meta_text: &str) -> Option<u32> {
    let needle = "\"schema_version\":";
    let idx = meta_text.find(needle)?;
    let after = meta_text[idx + needle.len()..].trim_start();
    let end = after.find(|c: char| !c.is_ascii_digit())?;
    after[..end].parse().ok()
}

/// Rewrite an integer JSON field's value in raw text. Panics if the field is
/// absent. `needle` is the field key including the trailing colon
/// (e.g. `"\"cache_format_version\":"`).
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

/// Extract the manifest's global `cache_format_version` invalidation key.
fn extract_manifest_format_version(manifest_text: &str) -> Option<u32> {
    let needle = "\"cache_format_version\":";
    let idx = manifest_text.find(needle)?;
    let after = manifest_text[idx + needle.len()..].trim_start();
    let end = after.find(|c: char| !c.is_ascii_digit())?;
    after[..end].parse().ok()
}

fn extract_json_string_field<'a>(text: &'a str, field: &str) -> Option<&'a str> {
    let needle = format!("\"{field}\":");
    let after = text.get(text.find(&needle)? + needle.len()..)?.trim_start();
    let value = after.strip_prefix('"')?;
    Some(&value[..value.find('"')?])
}

// spec: design/backend/module-caching.md §4 — the schema version R5's
// representation change stamps MUST advance past the pre-R5 value (14→15), so
// no pre-R5 `.o` is schema-compatible. RED at draft (still 14); flips when R5
// bumps CACHE_SCHEMA_VERSION.
#[test]
fn cache_schema_version_bumped_for_r5_representation_change() {
    let out = project(&[("main.cl", SCHEMA_MAIN), ("util.cl", SCHEMA_UTIL)])
        .run("main.cl")
        .output()
        .assert_exit(42);
    let meta_path = out.tmpdir.join(".cranelisp-cache").join("util.meta.json");
    let text = fs::read_to_string(&meta_path).expect("read util.meta.json");
    let stamped = extract_schema_version(&text)
        .unwrap_or_else(|| panic!("meta.json must carry an integer schema_version; got:\n{text}"));
    assert!(
        stamped >= PRE_R5_SCHEMA + 1,
        "R5's value-flattening is a representation change and MUST bump \
         CACHE_SCHEMA_VERSION past the pre-R5 value {PRE_R5_SCHEMA} (Decision 34); \
         stamped schema_version={stamped}. RED until the Wave-3 R5 bump lands."
    );
}

// spec: design/backend/ownership-codegen.md §7.4 — a cache written before R5's
// representation change is wholesale-invalidated after R5 lands: every module
// recompiles (cache miss) rather than serving incompatible boxed-payload
// objects. The wholesale-invalidation gate is `check_manifest`
// (`crates/cranelisp-backend/src/cache/manifest.rs:150`), which keys on the
// MANIFEST's global `cache_format_version` (== `CACHE_SCHEMA_VERSION`), NOT the
// per-module `.meta.json schema_version` (that is a belt-and-suspenders
// secondary guard checked later in `deserialise_meta`, after the "cache hit"
// trace has already printed — FIXME 0527). So a faithful pre-R5-cache
// simulation patches the manifest key, which is what a pre-bump binary would
// have stamped. Uses a dep module (`util`) as the observable cache-hit surface
// (a single top-level module always rewrites its own `.o`; mirrors the L-B3
// legs above). GREEN once R5 has bumped the live schema past PRE_R5_SCHEMA: the
// patched-to-14 manifest then mismatches the live 15 and every module recomputes.
#[test]
fn cache_pre_r5_schema_object_invalidated_wholesale() {
    let first = project(&[("main.cl", SCHEMA_MAIN), ("util.cl", SCHEMA_UTIL)])
        .run("main.cl")
        .output()
        .assert_exit(42);
    // Patch the MANIFEST's global format key to the pre-R5 value — simulate a
    // cache written by a pre-bump binary (which stamps the manifest AND every
    // .meta.json with the old schema together; the manifest key is the gate).
    let manifest_path = first.tmpdir.join(".cranelisp-cache").join("manifest.json");
    let original = fs::read_to_string(&manifest_path).expect("read manifest.json");
    let patched = set_json_u32(&original, "\"cache_format_version\":", PRE_R5_SCHEMA);
    fs::write(&manifest_path, &patched).expect("write patched manifest");
    assert_eq!(
        extract_manifest_format_version(&fs::read_to_string(&manifest_path).unwrap()),
        Some(PRE_R5_SCHEMA),
        "patched manifest must carry the pre-R5 format version"
    );
    nap_for_mtime();
    let m1 = mtime(&first, ".cranelisp-cache/util.o");

    let second = first
        .run_again()
        .env("CRANELISP_MODULE_TRACE", "1")
        .run("main.cl")
        .output()
        .assert_exit(42);
    assert!(
        !second.stderr.contains("cache hit"),
        "a pre-R5 ({PRE_R5_SCHEMA}) manifest MUST be wholesale-invalidated once R5 \
         bumps the live schema — util must recompute, not cache-hit; stderr:\n{}",
        second.stderr
    );
    let m2 = mtime(&second, ".cranelisp-cache/util.o");
    assert_ne!(
        m1, m2,
        "util.o must be recompiled (rewritten) after a pre-R5 manifest-format \
         mismatch, not served stale"
    );
}

// =============================================================================
// Sprint 109 — DC-9 (dotted-ctor warm-cache round-trip) + AL-8 warm-cache leg
// (FQ auto-load from cache). See the [historical QA allocation](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/tests/plan/PLAN.md), S109 A/D.
// =============================================================================

// spec: design/arch/dotted-ctor-canonical-keys.md §2 — a
// dotted-ctor program resolves identically cold and warm: the canonical-key /
// `type_ctor_names` mapping round-trips through `.meta.json` so the warm run
// resolves the dotted constructor exactly as the cold run does. RED today (the
// dotted value-position constructor path does not resolve yet); after the
// registration change this is a permanent cold≡warm round-trip guard.
// defect: class=enumeration-miss locus=crates/cranelisp-typecheck/src/checker.rs::resolve_dotted_field_accessor found=S108 owner=/dev
#[test]
fn dotted_ctor_resolves_from_warm_cache() {
    let src = "(import [primitives [Pure Int add-i64]])\n\
               (deftype (Maybe a) Nil (Some [:a v]))\n\
               (deftype (Option a) Nil (Some [:a v]))\n\
               (defn main [] (Pure\n\
                 (add-i64 (match (Maybe.Some 7) [(Maybe.Some x) x Maybe.Nil 0])\n\
                          (match (Option.Some 3) [(Option.Some x) x Option.Nil 0]))))\n";
    // Cold run — builds the cache (RED until dotted ctors resolve); then the
    // warm run served from the `.meta.json` cache gives the identical result.
    project(&[("main.cl", src)])
        .run("main.cl")
        .output()
        .assert_exit(10)
        .run_again()
        .run("main.cl")
        .output()
        .assert_exit(10);
}

// spec: spec/08-modules.md §8.5.4 edge 8 — an auto-loaded module's resolution
// MAY be satisfied from the warm cache: a FQ reference resolves identically on a
// cold run (auto-load + compile) and a warm run (cache hit). GREEN — the
// cache-hit leg of AL-8 idempotence.
#[test]
fn fq_ref_resolves_from_warm_cache() {
    let files = &[
        (
            "mathx.cl",
            "(import [primitives [Int mul-i64]])\n(defn square [:Int x] :Int (mul-i64 x x))\n",
        ),
        (
            "main.cl",
            "(import [primitives [Pure]])\n(defn main [] (Pure (mathx/square 5)))\n",
        ),
    ];
    // Cold: auto-load + compile; then the warm run (same TempDir) is a cache hit.
    project(files)
        .run("main.cl")
        .output()
        .assert_exit(25)
        .run_again()
        .run("main.cl")
        .output()
        .assert_exit(25);
}

// =============================================================================
// Sprint 109 W1.2 — DC-14: CACHE_SCHEMA_VERSION 17→18 (arch §10.2/§10.8).
// `MonoMatchArm.resolved_ctor` serializes into the cached codegen_view; a pre-18
// meta lacks it (serde default `None`) and would hard-error at the backend, so a
// pre-18 `.meta.json` MUST be rejected wholesale (recompiled), never silently
// read; a warm schema-18 rerun of the DC-12 differing-layout twin stays green.
// [Historical QA allocation](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/tests/plan/PLAN.md),
// S109 D.3 DC-14. RED today — this rides the §10
// sidecar-transport change-set (the DC-12 twin itself is the Blocker), and the
// 17→18 bump lands with it; the pre-18-specific reject fully materialises once
// /dev bumps the binary to schema 18.
// =============================================================================

// spec: design/backend/module-caching.md §14.2 — schema 17→18 bump: warm
// cache of the DC-12 differing-layout twin stays green + a pre-current-schema
// meta is rejected wholesale (recompiled to the correct result).
#[test]
fn pre_schema_18_cache_rejected_and_warm_18_green() {
    // The DC-12 differing-layout twin (order A) — a single entry file.
    let twin = "(import [primitives [Pure add-i64 Int]])\n\
                (deftype (Maybe a) None (Some [:a v]))\n\
                (deftype Opt2 (Some [:Int a :Int b]) None2)\n\
                (defn main [] (Pure\n\
                  (add-i64 (match (Maybe.Some 5) [(Some x) x None 0])\n\
                           (match (Opt2.Some 10 20) [(Some x y) (add-i64 x y) None2 0]))))\n";
    // Cold compile (RED today — the wrong-ctor Blocker); then the WARM cache hit
    // MUST give the same correct result 35.
    let warm = project(&[("main.cl", twin)])
        .run("main.cl")
        .output()
        .assert_exit(35)
        .run_again()
        .run("main.cl")
        .output()
        .assert_exit(35);

    // Pre-(current-schema) meta is rejected WHOLESALE: patch schema_version to a
    // stale sentinel, rerun — the cache MUST reject it and recompile to the
    // correct result (never silently read a stale/None-armed codegen view).
    let meta_path = warm.tmpdir.join(".cranelisp-cache").join("main.meta.json");
    let text = fs::read_to_string(&meta_path).expect("meta exists after successful compile");
    let stale = regex::Regex::new(r#""schema_version"\s*:\s*\d+"#)
        .unwrap()
        .replace(&text, "\"schema_version\":1")
        .into_owned();
    assert!(
        stale.contains("\"schema_version\":1"),
        "the schema_version patch must land; meta:\n{text}"
    );
    fs::write(&meta_path, &stale).expect("write stale-schema meta");
    warm.run_again().run("main.cl").output().assert_exit(35);
}

// =============================================================================
// Sprint 112 (0628/I-C wave) — AG-1 leg-(a) stale-cache cell (plan §4; /arch
// FIXME 0644 addition). A schema-20 `.meta.json` from the OLD compiler can carry
// B-2-era multi-sig overload state — `register_mangled_variants` force-installed
// a bogus `Concrete{got_slot}` entry over a `Var` param (a `$Var` mangle) for a
// wrong-accept shape like `lf2` (`([:a p] p)`, ACCEPTED by the old compiler in
// all modes). Under the settled §5.1.2 model no `$Var` concrete entry survives
// (§11.3(B)); a schema-20 cache-hit typecheck bypass on an unchanged source file
// would otherwise resurrect it — the CS-2/P25 cache-trust class A4 names. The
// 20→21 bump (leg (a) carries it, plan §7.4) MUST refuse such a cache WHOLESALE.
//
// Stage-1 state: RED at HEAD (schema IS 20, so a schema-20 meta is honoured — a
// cache hit, no refusal). GREEN once leg (a) bumps `CACHE_SCHEMA_VERSION` 20→21:
// the patched schema-20 meta then mismatches and the module recompiles (its
// schema_version is re-stamped away from 20).
// =============================================================================

// spec: design/backend/module-caching.md §14.7 — a pre-current-schema
// `.meta.json` is refused WHOLESALE (recompiled), never partially deserialized.
// A cached `$Var`-Concrete multi-sig module (schema-20 era) cannot resurrect via
// a cache-hit typecheck bypass under schema 21.
#[test]
fn stale_schema20_multi_sig_var_concrete_cache_refused_wholesale_neg() {
    // A B-2-era wrong-accept shape (the `lf2` leaf-poly clause /arch 0644 names)
    // whose schema-20 cache carries the bogus `$Var` overload state. Compiles at
    // HEAD (wrong-accept) and post-leg-(a) (legitimate poly) alike; `(lf2 42)` =
    // 42 ⇒ exit 42.
    let src = "(import [primitives [Pure]])\n\
               (defn lf2 ([:a p] p))\n\
               (defn main [] (Pure (lf2 42)))\n";
    let warm = project(&[("main.cl", src)])
        .run("main.cl")
        .output()
        .assert_exit(42);

    // Doctor the meta to the PRE-BUMP schema (20) — simulating the old-compiler
    // cache. Under the 20→21 bump this MUST be refused wholesale.
    let meta_path = warm.tmpdir.join(".cranelisp-cache").join("main.meta.json");
    let text = fs::read_to_string(&meta_path).expect("meta exists after successful compile");
    let stale = set_json_u32(&text, "\"schema_version\":", 20);
    fs::write(&meta_path, &stale).expect("write schema-20 meta");

    let rerun = warm
        .run_again()
        .run("main.cl")
        .output()
        // Correctness preserved: whether via honoured hit (HEAD) or recompile
        // (post-bump), the result is still 42.
        .assert_exit(42);

    // The load-bearing REFUSAL facet: a schema-20 cache MUST be refused wholesale
    // — the module recompiles and its schema_version is re-stamped to the
    // current (bumped) value, NOT left at the honoured stale 20. RED at HEAD
    // (schema IS 20 ⇒ the patched meta is a cache HIT ⇒ stays 20); GREEN once
    // leg (a) bumps 20→21.
    let after_path = rerun.tmpdir.join(".cranelisp-cache").join("main.meta.json");
    let after_text = fs::read_to_string(&after_path).expect("meta after rerun");
    let after_schema = extract_schema_version(&after_text)
        .unwrap_or_else(|| panic!("meta must carry schema_version:\n{after_text}"));
    assert_ne!(
        after_schema, 20,
        "a schema-20 cache carrying the `$Var`-Concrete multi-sig wrong-accept \
         state MUST be refused WHOLESALE and recompiled (schema re-stamped away \
         from 20), NOT honoured via a cache-hit typecheck bypass (the CS-2/P25 \
         class; §11.3(B) 'no $Var concrete entry survives'). schema stayed {after_schema}."
    );
}

// =============================================================================
// Dependency change under an unchanged, cache-restored intermediate importer
//
// Shape `main → a → b`, two runs in one project. The second run edits only
// `b`, so the only reason not to serve `a` from cache is its dependency on `b`
// (design/backend/module-caching.md §3, secondary key). The CLI target `main`
// is always compiled fresh, so `a` is the importer under test. The oracle is
// the edited sources compiled without cache use: `--run --no-cache` in the same
// project, and a cold `--link` in a fresh project because `--link` refuses
// `--no-cache`. Each cell first shows that the unchanged `a` really is restored
// from cache, so agreement is not agreement through the fresh path.
// =============================================================================

const DEP_CHANGE_MAIN: &str = "(import [primitives [Pure]])\n\
                               (import [a [g]])\n\
                               (defn main [] (Pure (g)))\n";

/// Signature leg: `f`'s parameter changes from Int to String, so `a`'s
/// unchanged call `(f 5)` becomes ill-typed.
const DEP_CHANGE_SIG_A: &str = "(import [primitives [add-i64]])\n\
                                (import [b [f]])\n\
                                (defn g [] (add-i64 (f 5) 100))\n";
const DEP_CHANGE_SIG_B_BEFORE: &str = "(import [primitives [Int add-i64]])\n\
                                       (defn f [:Int x] :Int (add-i64 x 1))\n";
const DEP_CHANGE_SIG_B_AFTER: &str = "(import [primitives [Int String]])\n\
                                      (defn f [:String s] :Int 7)\n";

/// Layout leg: a compatible edit inserts a concrete `e` ahead of the called
/// `f`. The return values tell `f` (11) from `e` (99).
const DEP_CHANGE_LAYOUT_A: &str = "(import [b [f]])\n(defn g [] (f))\n";
const DEP_CHANGE_LAYOUT_B_BEFORE: &str = "(defn f [] 11)\n";
const DEP_CHANGE_LAYOUT_B_AFTER: &str = "(defn e [] 99)\n(defn f [] 11)\n";

#[derive(Clone, Copy)]
enum DepChangeMode {
    Run,
    Link,
}

impl DepChangeMode {
    fn select(self, c: Cranelisp) -> Cranelisp {
        let c = c.env("CRANELISP_MODULE_TRACE", "1");
        match self {
            DepChangeMode::Run => c.run("main.cl"),
            DepChangeMode::Link => c.link_then_run("main.cl"),
        }
    }
}

struct Observed {
    exit: Option<i32>,
    stdout: String,
    stderr: String,
}

impl Observed {
    fn of(out: &helpers::e2e::CrOutput) -> Self {
        Observed {
            exit: out.status.code(),
            stdout: out.stdout.clone(),
            stderr: out.stderr.clone(),
        }
    }
}

/// Compiles `main → a → b`, restores it warm, edits `b`, and returns the
/// uncached oracle and the cached run for the edited sources.
fn dep_change_under_cached_importer(
    mode: DepChangeMode,
    a_src: &str,
    (b_before, before_exit): (&str, i32),
    b_after: &str,
) -> (Observed, Observed) {
    let files_before = [
        ("main.cl", DEP_CHANGE_MAIN),
        ("a.cl", a_src),
        ("b.cl", b_before),
    ];
    let cold = mode
        .select(project(&files_before))
        .output()
        .assert_exit(before_exit);
    let a_object = cold.tmpdir.join(".cranelisp-cache/a.o");
    let a_bytes = fs::read(&a_object).expect("the cold run writes a.o");

    let warm = mode
        .select(cold.run_again())
        .output()
        .assert_exit(before_exit);
    assert!(
        warm.stderr.contains("cache hit (.meta valid) for a"),
        "with nothing changed, `a` must be restored from cache:\n{}",
        warm.stderr
    );

    let edited = warm.run_again().file("b.cl", b_after);
    let (control, edited) = match mode {
        DepChangeMode::Run => {
            let control = edited.run("main.cl").cli_flag("--no-cache").output();
            (Observed::of(&control), control.run_again())
        }
        DepChangeMode::Link => {
            let files_after = [
                ("main.cl", DEP_CHANGE_MAIN),
                ("a.cl", a_src),
                ("b.cl", b_after),
            ];
            let control = mode.select(project(&files_after)).output();
            (Observed::of(&control), edited)
        }
    };
    assert_eq!(
        fs::read(&a_object).expect("a.o is still cached"),
        a_bytes,
        "the uncached control must leave the cached a.o untouched"
    );

    let cached = Observed::of(&mode.select(edited).output());
    (control, cached)
}

fn assert_cached_matches_uncached(control: &Observed, cached: &Observed) {
    assert!(
        cached.exit == control.exit && cached.stdout == control.stdout,
        "after `b` changed, the cached run must behave as the uncached run\n\
         uncached: exit={:?} stdout={:?}\ncached:   exit={:?} stdout={:?}\n\
         uncached stderr:\n{}\ncached stderr:\n{}",
        control.exit,
        control.stdout,
        cached.exit,
        cached.stdout,
        control.stderr,
        cached.stderr
    );
}

fn assert_uncached_rejects_int_argument(control: &Observed) {
    assert!(
        control.exit != Some(0) && control.exit != Some(107) && control.stderr.contains("String"),
        "the uncached compile must reject `a`'s Int argument to a String parameter:\n\
         exit={:?}\nstdout:\n{}\nstderr:\n{}",
        control.exit,
        control.stdout,
        control.stderr
    );
}

// spec: design/backend/module-caching.md §3 — Secondary key: transitive
// dependency hashes; §8 cache-load/fresh-compile equivalence under `--run`.
// defect: class=artifact-underkey locus=src/process_form/cache_restore.rs::cache_validity_check found=S122 owner=/dev
#[test]
fn cache_dep_signature_change_under_cached_importer_matches_uncached_run() {
    let (control, cached) = dep_change_under_cached_importer(
        DepChangeMode::Run,
        DEP_CHANGE_SIG_A,
        (DEP_CHANGE_SIG_B_BEFORE, 106),
        DEP_CHANGE_SIG_B_AFTER,
    );
    assert_uncached_rejects_int_argument(&control);
    assert_cached_matches_uncached(&control, &cached);
}

// spec: design/backend/module-caching.md §3 — Secondary key: transitive
// dependency hashes; §11 quick build links cached objects.
// defect: class=artifact-underkey locus=src/process_form/cache_restore.rs::cache_validity_check found=S122 owner=/dev
#[test]
fn cache_dep_signature_change_under_cached_importer_matches_uncached_link() {
    let (control, cached) = dep_change_under_cached_importer(
        DepChangeMode::Link,
        DEP_CHANGE_SIG_A,
        (DEP_CHANGE_SIG_B_BEFORE, 106),
        DEP_CHANGE_SIG_B_AFTER,
    );
    assert_uncached_rejects_int_argument(&control);
    assert_cached_matches_uncached(&control, &cached);
}

// spec: design/backend/module-caching.md §3 — Secondary key: transitive
// dependency hashes (GOT layout); §8 equivalence under `--run`.
// defect: class=artifact-underkey locus=src/process_form/cache_restore.rs::cache_validity_check found=S122 owner=/dev
#[test]
fn cache_dep_layout_change_under_cached_importer_matches_uncached_run() {
    let (control, cached) = dep_change_under_cached_importer(
        DepChangeMode::Run,
        DEP_CHANGE_LAYOUT_A,
        (DEP_CHANGE_LAYOUT_B_BEFORE, 11),
        DEP_CHANGE_LAYOUT_B_AFTER,
    );
    assert_eq!(
        control.exit,
        Some(11),
        "uncached `a` calls `f`: {}",
        control.stderr
    );
    assert_cached_matches_uncached(&control, &cached);
}

// spec: design/backend/module-caching.md §3 — Secondary key: transitive
// dependency hashes (GOT layout); §11 quick build links cached objects.
// defect: class=artifact-underkey locus=src/process_form/cache_restore.rs::cache_validity_check found=S122 owner=/dev
#[test]
fn cache_dep_layout_change_under_cached_importer_matches_uncached_link() {
    let (control, cached) = dep_change_under_cached_importer(
        DepChangeMode::Link,
        DEP_CHANGE_LAYOUT_A,
        (DEP_CHANGE_LAYOUT_B_BEFORE, 11),
        DEP_CHANGE_LAYOUT_B_AFTER,
    );
    assert_eq!(
        control.exit,
        Some(11),
        "uncached `a` calls `f`: {}",
        control.stderr
    );
    assert_cached_matches_uncached(&control, &cached);
}

// Shape `main → c → a → b`: `a` only re-exports `b`'s `f`, so a change to `b`
// reaches `c` only through `a`, whose own source never changes. A record of
// `c`'s direct imports alone (`{a}`) would restore `c` stale
// (design/int/int.md §7.6: the record is the transitive closure).
const CLOSURE_MAIN: &str = "(import [primitives [Pure]])\n\
                            (import [c [g]])\n\
                            (defn main [] (Pure (g)))\n";
const CLOSURE_C: &str = "(import [primitives [add-i64]])\n\
                         (import [a [f]])\n\
                         (defn g [] (add-i64 (f 5) 100))\n";
const CLOSURE_A: &str = "(export [b [f]])\n";

fn trace_hit(out: &helpers::e2e::CrOutput, module: &str) -> bool {
    let hit = format!("cache hit (.meta valid) for {module}");
    out.stderr.lines().any(|line| line.ends_with(&hit))
}

/// Compiles `main → c → a → b` cold, then either restores it warm with nothing
/// changed (`rebuild_c == false`) or edits only `c` so that `c` is rebuilt over
/// a restored `a`. Then edits `b` and returns the uncached oracle and the
/// cached run for the edited sources.
fn closure_change_under_cached_importer(rebuild_c: bool) -> (Observed, Observed) {
    let run = |c: Cranelisp| c.env("CRANELISP_MODULE_TRACE", "1").run("main.cl");
    let cold = run(project(&[
        ("main.cl", CLOSURE_MAIN),
        ("c.cl", CLOSURE_C),
        ("a.cl", CLOSURE_A),
        ("b.cl", DEP_CHANGE_SIG_B_BEFORE),
    ]))
    .output()
    .assert_exit(106);

    let second = if rebuild_c {
        // A trailing comment changes `c`'s source hash and nothing else.
        let touched_c = format!("{CLOSURE_C};; touched\n");
        let out = run(cold.run_again().file("c.cl", &touched_c))
            .output()
            .assert_exit(106);
        assert!(
            trace_hit(&out, "a") && !trace_hit(&out, "c"),
            "with only `c` edited, `a` must restore from cache and `c` must rebuild:\n{}",
            out.stderr
        );
        out
    } else {
        let out = run(cold.run_again()).output().assert_exit(106);
        assert!(
            trace_hit(&out, "a") && trace_hit(&out, "c"),
            "with nothing changed, `a` and `c` must both restore from cache:\n{}",
            out.stderr
        );
        out
    };
    let c_object = second.tmpdir.join(".cranelisp-cache/c.o");
    let c_bytes = fs::read(&c_object).expect("c.o is cached");

    let control = run(second.run_again().file("b.cl", DEP_CHANGE_SIG_B_AFTER))
        .cli_flag("--no-cache")
        .output();
    assert_eq!(
        fs::read(&c_object).expect("c.o is still cached"),
        c_bytes,
        "the uncached control must leave the cached c.o untouched"
    );
    let observed_control = Observed::of(&control);
    let cached = Observed::of(&run(control.run_again()).output());
    (observed_control, cached)
}

// spec: design/int/int.md §7.6 — Dependency record and validity (the record is
// the transitive closure; a re-export target is an edge).
// defect: class=artifact-underkey locus=src/process_form/cache_restore.rs::cache_validity_check found=S122 owner=/dev
#[test]
fn cache_dep_change_through_unchanged_reexporter_matches_uncached_run() {
    let (control, cached) = closure_change_under_cached_importer(false);
    assert_uncached_rejects_int_argument(&control);
    assert_cached_matches_uncached(&control, &cached);
}

// spec: design/int/int.md §7.6 — Dependency record and validity (a restored
// member contributes its own validated record to a rebuilt importer's record).
// defect: class=artifact-underkey locus=src/process_form/cache_restore.rs::cache_validity_check found=S122 owner=/dev
#[test]
fn cache_dep_change_after_importer_rebuilt_over_restored_reexporter_matches_uncached_run() {
    let (control, cached) = closure_change_under_cached_importer(true);
    assert_uncached_rejects_int_argument(&control);
    assert_cached_matches_uncached(&control, &cached);
}

/// Every file under the project's cache directory, keyed by relative path.
fn cache_snapshot(tmpdir: &std::path::Path) -> std::collections::BTreeMap<String, Vec<u8>> {
    fn walk(
        root: &std::path::Path,
        dir: &std::path::Path,
        out: &mut std::collections::BTreeMap<String, Vec<u8>>,
    ) {
        for entry in fs::read_dir(dir).expect("read cache dir") {
            let path = entry.expect("cache dir entry").path();
            if path.is_dir() {
                walk(root, &path, out);
            } else {
                let rel = path.strip_prefix(root).expect("under root");
                out.insert(rel.display().to_string(), fs::read(&path).expect("read"));
            }
        }
    }
    let root = tmpdir.join(".cranelisp-cache");
    let mut out = std::collections::BTreeMap::new();
    walk(&root, &root, &mut out);
    out
}

impl Observed {
    fn hit(&self, module: &str) -> bool {
        let hit = format!("cache hit (.meta valid) for {module}");
        self.stderr.lines().any(|line| line.ends_with(&hit))
    }
}

/// `--run main.cl` with the module trace and every `env` pair set.
fn run_main(c: Cranelisp, env: &[(&str, &str)]) -> Cranelisp {
    env.iter()
        .fold(c.env("CRANELISP_MODULE_TRACE", "1"), |c, (k, v)| {
            c.env(k, v)
        })
        .run("main.cl")
}

/// Runs `files` cold, then warm with nothing changed, asserting that the warm
/// run behaves as the cold one and that every module in `restored` is served
/// from cache. Returns the cold observation and the warm output.
fn warm_restore(
    files: &[(&str, &str)],
    before_exit: i32,
    restored: &[&str],
    env: &[(&str, &str)],
) -> (Observed, helpers::e2e::CrOutput) {
    let cold = run_main(project(files), env)
        .output()
        .assert_exit(before_exit);
    let cold_observed = Observed::of(&cold);
    let warm = run_main(cold.run_again(), env).output();
    assert!(
        warm.status.code() == Some(before_exit) && warm.stdout == cold_observed.stdout,
        "with nothing changed, the warm run must behave as the cold run\n\
         cold: exit={before_exit} stdout={:?}\nwarm: exit={:?} stdout={:?}\n\
         warm stderr:\n{}",
        cold_observed.stdout,
        warm.status.code(),
        warm.stdout,
        warm.stderr
    );
    for module in restored {
        assert!(
            trace_hit(&warm, module),
            "with nothing changed, `{module}` must be restored from cache:\n{}",
            warm.stderr
        );
    }
    (cold_observed, warm)
}

struct EditLegs {
    cold: Observed,
    warm: Observed,
    /// `--run --no-cache` on the edited sources.
    control: Observed,
    /// `--run` on the edited sources over the warm cache.
    cached: Observed,
}

/// [`warm_restore`], then replaces one file and runs the uncached oracle and
/// the cached `--run` for the edited sources.
fn edit_after_warm_restore(
    files: &[(&str, &str)],
    before_exit: i32,
    restored: &[&str],
    (edited_path, edited_src): (&str, &str),
    env: &[(&str, &str)],
) -> EditLegs {
    let (cold, warm) = warm_restore(files, before_exit, restored, env);
    let warm_observed = Observed::of(&warm);
    let cache_before = cache_snapshot(&warm.tmpdir);

    let control = run_main(warm.run_again().file(edited_path, edited_src), env)
        .cli_flag("--no-cache")
        .output();
    assert!(
        cache_snapshot(&control.tmpdir) == cache_before,
        "the uncached control must leave the cache untouched"
    );
    let observed_control = Observed::of(&control);
    let cached = Observed::of(&run_main(control.run_again(), env).output());
    EditLegs {
        cold,
        warm: warm_observed,
        control: observed_control,
        cached,
    }
}

// F1: `a` reaches `b` only through the qualified reference `b/f`, which
// spec/08-modules.md §8.5.4 admits without an import of `b`. The layout edit
// inserts `e` (99) ahead of the called `f` (11).
const FQ_ONLY_A: &str = "(defn g [] (b/f))\n";

fn fq_only_dependency_change(main_src: &str) -> (Observed, Observed) {
    let EditLegs {
        control, cached, ..
    } = edit_after_warm_restore(
        &[
            ("main.cl", main_src),
            ("a.cl", FQ_ONLY_A),
            ("b.cl", DEP_CHANGE_LAYOUT_B_BEFORE),
        ],
        11,
        &["a"],
        ("b.cl", DEP_CHANGE_LAYOUT_B_AFTER),
        &[],
    );
    assert_eq!(
        control.exit,
        Some(11),
        "uncached `a` calls `f`: {}",
        control.stderr
    );
    (control, cached)
}

// spec: design/int/int.md §7.6 — Dependency record and validity (a dependency
// reached only through a qualified reference, spec/08-modules.md §8.5.4).
// defect: class=artifact-underkey locus=src/cache/dependency_record.rs::ModuleEdges found=S122 owner=/dev
#[test]
fn cache_fq_only_dependency_change_under_cached_importer_matches_uncached_run() {
    let (control, cached) = fq_only_dependency_change(
        "(import [primitives [Pure]])\n\
         (import [a [g]])\n\
         (import [b [f]])\n\
         (defn main [] (Pure (g)))\n",
    );
    assert_cached_matches_uncached(&control, &cached);
}

// spec: design/int/int.md §7.6 — Dependency record and validity (a dependency
// reached only through a qualified reference, spec/08-modules.md §8.5.4, that
// no other module imports). Nothing but `a`'s qualified reference loads `b`,
// so the restored `a.o` is observed before any edit.
// defect: class=enumeration-miss locus=src/process_form/cache_restore.rs::try_cache_hit_load found=S122 owner=/dev
#[test]
fn cache_fq_only_dependency_change_not_imported_by_entry_matches_uncached_run() {
    let (control, cached) = fq_only_dependency_change(
        "(import [primitives [Pure]])\n\
         (import [a [g]])\n\
         (defn main [] (Pure (g)))\n",
    );
    assert_cached_matches_uncached(&control, &cached);
}

// Remaining qualified-reference kinds. In each subject `a` reaches the module
// under test only through a qualified reference that is not a call, so `a`'s
// callees cannot name that module. The module under test defines an unused
// `anchor` in both versions. The edge-supplied sibling differs from the subject
// only in `a` importing `anchor`, which gives `a` an ordinary edge; it runs
// first, and its agreement leaves the missing edge as the subject's only stale
// mechanism.

/// Runs `check` over the edge-supplied sibling's legs, then over the
/// subject's. `files` holds `a.cl`; `module` is the module under test.
fn qualified_reference_change(
    module: &str,
    files: &[(&str, &str)],
    before_exit: i32,
    edit: (&str, &str),
    env: &[(&str, &str)],
    check: impl Fn(&str, &EditLegs),
) {
    let sibling_a = files
        .iter()
        .find(|(path, _)| *path == "a.cl")
        .map(|(_, src)| format!("(import [{module} [anchor]])\n{src}"))
        .expect("the fixture defines a.cl");
    let sibling: Vec<(&str, &str)> = files
        .iter()
        .map(|&(path, src)| {
            (
                path,
                if path == "a.cl" {
                    sibling_a.as_str()
                } else {
                    src
                },
            )
        })
        .collect();
    let restored = ["a"];
    check(
        "edge-supplied sibling",
        &edit_after_warm_restore(&sibling, before_exit, &restored, edit, env),
    );
    check(
        "qualified-only subject",
        &edit_after_warm_restore(files, before_exit, &restored, edit, env),
    );
}

/// The uncached run on the edited sources exits `expected`, and the cached run
/// behaves as it does.
fn matches_uncached(expected: i32) -> impl Fn(&str, &EditLegs) {
    move |leg: &str, legs: &EditLegs| {
        assert_eq!(
            legs.control.exit,
            Some(expected),
            "{leg}: uncached oracle:\n{}",
            legs.control.stderr
        );
        assert!(
            legs.cached.exit == legs.control.exit && legs.cached.stdout == legs.control.stdout,
            "{leg}: after the edit, the cached run must behave as the uncached run\n\
             uncached: exit={:?} stdout={:?}\ncached:   exit={:?} stdout={:?}\n\
             cached stderr:\n{}",
            legs.control.exit,
            legs.control.stdout,
            legs.cached.exit,
            legs.cached.stdout,
            legs.cached.stderr
        );
    }
}

// spec: design/int/int.md §7.6 — Dependency record and validity (first hop of a
// qualified re-export; spec/08-modules.md §8.5.4 edge 1)
// defect: class=artifact-underkey locus=src/cache/dependency_record.rs::ModuleEdges found=S122 owner=/dev
#[test]
fn cache_qualified_reexport_first_hop_change_matches_uncached_run() {
    // `r` re-exports `f` from `c` (11), then from `d` (99). `main` loads `c`
    // so that an `a.o` still bound to `c/f` links.
    qualified_reference_change(
        "r",
        &[
            (
                "main.cl",
                "(import [primitives [Pure]])\n\
                 (import [a [g]])\n\
                 (import [c [f]])\n\
                 (defn main [] (Pure (g)))\n",
            ),
            ("a.cl", "(defn g [] (r/f))\n"),
            ("r.cl", "(export [c [f]])\n(defn anchor [] 0)\n"),
            ("c.cl", "(defn f [] 11)\n"),
            ("d.cl", "(defn f [] 99)\n"),
        ],
        11,
        ("r.cl", "(export [d [f]])\n(defn anchor [] 0)\n"),
        &[],
        matches_uncached(99),
    );
}

// spec: design/int/int.md §7.6 — Dependency record and validity (constructor
// tag in value and pattern position; spec/08-modules.md §8.5.4 edge 1)
// defect: class=artifact-underkey locus=src/cache/dependency_record.rs::ModuleEdges found=S122 owner=/dev
#[test]
fn cache_qualified_constructor_tag_change_matches_uncached_run() {
    // `b` swaps its nullary variants' order, and so their tags. The result is
    // `classify(mk-hi) + 10 × code(make)` = 22. A stale `a` shows which of its
    // positions is stale: 11 both, 12 the value `b/Hi`, 21 the patterns.
    let b = |variants: &str| {
        format!(
            "(deftype T {variants})\n\
             (defn mk-hi [] Hi)\n\
             (defn code [t] (match t [Lo 1 Hi 2]))\n\
             (defn anchor [] 0)\n"
        )
    };
    qualified_reference_change(
        "b",
        &[
            (
                "main.cl",
                "(import [primitives [Pure add-i64 mul-i64]])\n\
                 (import [a [make classify]])\n\
                 (import [b [mk-hi code]])\n\
                 (defn main [] (Pure (add-i64 (classify (mk-hi)) (mul-i64 10 (code (make))))))\n",
            ),
            (
                "a.cl",
                "(defn make [] b/Hi)\n\
                 (defn classify [t] (match t [b/Lo 1 b/Hi 2]))\n",
            ),
            ("b.cl", b("Lo Hi").as_str()),
        ],
        22,
        ("b.cl", b("Hi Lo").as_str()),
        &[],
        matches_uncached(22),
    );
}

// spec: design/int/int.md §7.6 — Dependency record and validity (dotted field
// accessor; spec/08-modules.md §8.5.4 edge 1)
// defect: class=artifact-underkey locus=src/cache/dependency_record.rs::ModuleEdges found=S122 owner=/dev
#[test]
fn cache_qualified_accessor_field_order_change_matches_uncached_run() {
    // `b` swaps `Box`'s scalar fields; `v` stays 11 and `w` 99.
    qualified_reference_change(
        "b",
        &[
            (
                "main.cl",
                "(import [primitives [Pure]])\n\
                 (import [a [g]])\n\
                 (import [b [mk]])\n\
                 (defn main [] (Pure (g (mk))))\n",
            ),
            ("a.cl", "(defn g [bx] (b/Box.v bx))\n"),
            (
                "b.cl",
                "(import [primitives [Int]])\n\
                 (deftype Box [:Int v :Int w])\n\
                 (defn mk [] (Box 11 99))\n\
                 (defn anchor [] 0)\n",
            ),
        ],
        11,
        (
            "b.cl",
            "(import [primitives [Int]])\n\
             (deftype Box [:Int w :Int v])\n\
             (defn mk [] (Box 99 11))\n\
             (defn anchor [] 0)\n",
        ),
        &[],
        matches_uncached(11),
    );
}

/// `(allocs, deallocs)` from the run's `[RC_STATS]` line.
fn alloc_pair(observed: &Observed) -> (u64, u64) {
    let line = observed
        .stderr
        .lines()
        .find(|line| line.starts_with("[RC_STATS]"))
        .unwrap_or_else(|| panic!("no [RC_STATS] line:\n{}", observed.stderr));
    let field = |name: &str| -> u64 {
        line.split_whitespace()
            .find_map(|kv| kv.strip_prefix(name)?.strip_prefix('='))
            .and_then(|v| v.parse().ok())
            .unwrap_or_else(|| panic!("no `{name}` in {line}"))
    };
    (field("allocs"), field("deallocs"))
}

// spec: design/int/int.md §7.6 — Dependency record and validity (type-only
// reference; `a` mints its own drop glue for `b/T`; spec/08-modules.md §8.5.4
// edge 1)
// defect: class=artifact-underkey locus=src/cache/dependency_record.rs::ModuleEdges found=S122 owner=/dev
#[test]
fn cache_qualified_type_only_field_change_matches_uncached_allocator_counts() {
    // `T`'s field changes from `Int` to a heap `String`. Both runs exit 7; the
    // observable is the allocation pair, compared between two runs that differ
    // only in cache use. `main` imports `b` ahead of `a` because a type-only
    // reference does not yet load `b`; see the fresh-compile cell below.
    qualified_reference_change(
        "b",
        &[
            (
                "main.cl",
                "(import [primitives [Pure]])\n\
                 (import [b [mk]])\n\
                 (import [a [g]])\n\
                 (defn main [] (Pure (g (mk))))\n",
            ),
            (
                "a.cl",
                "(import [primitives [Int]])\n\
                 (deftype W [:b/T inner])\n\
                 (defn g [:b/T t] :Int (match (W t) [(W _) 7]))\n",
            ),
            (
                "b.cl",
                "(import [primitives [Int]])\n\
                 (deftype T [:Int n])\n\
                 (defn mk [] (T 7))\n\
                 (defn anchor [] 0)\n",
            ),
        ],
        7,
        (
            "b.cl",
            "(import [primitives [String str-concat]])\n\
             (deftype T [:String s])\n\
             (defn mk [] (T (str-concat \"ab\" \"cd\")))\n\
             (defn anchor [] 0)\n",
        ),
        &[("CRANELISP_RC_STATS", "1")],
        |leg, legs| {
            let cold = alloc_pair(&legs.cold);
            assert_eq!(
                alloc_pair(&legs.warm),
                cold,
                "{leg}: with nothing changed, the warm counts must equal the cold counts"
            );
            let control = alloc_pair(&legs.control);
            assert!(
                control.0 > cold.0,
                "{leg}: the edited `mk` must allocate its String: uncached {control:?}, before {cold:?}"
            );
            assert_eq!(legs.control.exit, Some(7), "{leg}: {}", legs.control.stderr);
            assert_eq!(
                legs.cached.exit, legs.control.exit,
                "{leg}: {}",
                legs.cached.stderr
            );
            assert_eq!(
                alloc_pair(&legs.cached),
                control,
                "{leg}: (allocs, deallocs) of the cached run must equal the uncached run's"
            );
        },
    );
}

// spec: spec/08-modules.md §8.5.4 edge 1 — a fully-qualified type name in an
// annotation loads its module, whatever loaded it before
// defect: class=wrong-reject locus=cranelisp-typecheck::fq-type-reference-resolution found=S122 owner=/dev
#[test]
fn fq_type_only_reference_loads_its_module_on_a_fresh_compile() {
    // Found arming the type-only cache cell, whose allocated shape (`main`
    // importing `a` before `b`) fails before any cache use. In each module
    // below `b` is named only in a type position; compiled fresh, the program
    // is rejected with "module `b` referenced by `b/T` is not loaded". Loading
    // `b` first (an earlier import, or a value reference such as `b/mk` in `a`)
    // makes it compile. The locus is provisional: which layer should turn the
    // unloaded type home into a load is not yet attributed.
    let b = "(import [primitives [Int]])\n(deftype T [:Int n])\n";
    let mut rejected = Vec::new();
    for (position, a) in [
        ("deftype field", "(deftype W [:b/T inner])\n(defn g [] 7)\n"),
        (
            "defn parameter annotation",
            "(import [primitives [Int]])\n(defn h [:b/T t] :Int 7)\n(defn g [] 7)\n",
        ),
    ] {
        let out = project(&[
            (
                "main.cl",
                "(import [primitives [Pure]])\n(import [a [g]])\n(defn main [] (Pure (g)))\n",
            ),
            ("a.cl", a),
            ("b.cl", b),
        ])
        .run("main.cl")
        .cli_flag("--no-cache")
        .output();
        if out.status.code() != Some(7) {
            rejected.push(format!(
                "{position}: exit={:?}\n{}",
                out.status.code(),
                out.stderr
            ));
        }
    }
    assert!(
        rejected.is_empty(),
        "`b/T` must load `b`:\n{}",
        rejected.join("\n")
    );
}

// spec: design/int/int.md §7.6 — Dependency record and validity (qualified
// macro head; spec/08-modules.md §8.5.4 edge 1)
// defect: class=artifact-underkey locus=src/cache/dependency_record.rs::ModuleEdges found=S122 owner=/dev
#[test]
fn cache_qualified_macro_head_expansion_change_matches_uncached_run() {
    qualified_reference_change(
        "b",
        &[
            (
                "main.cl",
                "(import [primitives [Pure]])\n\
                 (import [a [g]])\n\
                 (defn main [] (Pure (g)))\n",
            ),
            ("a.cl", "(defn g [] (b/m))\n"),
            ("b.cl", "(defmacro m [] `11)\n(defn anchor [] 0)\n"),
        ],
        11,
        ("b.cl", "(defmacro m [] `99)\n(defn anchor [] 0)\n"),
        &[],
        matches_uncached(99),
    );
}

// spec: design/int/int.md §7.6 — Dependency record and validity (constructor-only
// home that nothing else loads; spec/08-modules.md §8.5.4 edge 1)
#[test]
fn cache_qualified_constructor_only_home_restores_warm() {
    // Restoring `a` loads only its edges, and `a` names `d` only through the
    // constructor `d/K`. The warm run must still behave as the cold run.
    warm_restore(
        &[
            (
                "main.cl",
                "(import [primitives [Pure]])\n\
                 (import [a [g]])\n\
                 (defn main [] (Pure (g)))\n",
            ),
            ("a.cl", "(defn g [] (match (d/K 7) [(d/K n) n]))\n"),
            (
                "d.cl",
                "(import [primitives [Int]])\n(deftype K [:Int n])\n",
            ),
        ],
        7,
        &["a"],
        &[],
    );
}

// DV3: a declared test child `lib.test` imports from `grp.asserts`, itself a
// declared child. Editing only `lib.test` re-typechecks it over a restored
// `grp.asserts`.
const DV3_MAIN: &str = "(import [primitives [Pure]])\n\
                        (import [lib [v]])\n\
                        (defn main [] (Pure (v)))\n";
const DV3_LIB: &str = "(mod- test)\n(defn v [] 7)\n";

fn fresh_test_child_over_restored_declared_child(lib_test: &str) {
    let touched = format!("{lib_test};; touched\n");
    let EditLegs {
        control, cached, ..
    } = edit_after_warm_restore(
        &[
            ("main.cl", DV3_MAIN),
            ("lib.cl", DV3_LIB),
            ("lib/test.cl", lib_test),
            ("grp.cl", "(mod asserts)\n"),
            ("grp/asserts.cl", "(defn one [] 1)\n"),
        ],
        7,
        &["grp.asserts", "lib.test"],
        ("lib/test.cl", &touched),
        &[],
    );
    assert_eq!(control.exit, Some(7), "uncached: {}", control.stderr);
    assert!(
        cached.hit("grp.asserts") && !cached.hit("lib.test"),
        "with only `lib.test` edited, `grp.asserts` must restore and `lib.test` rebuild:\n{}",
        cached.stderr
    );
    assert_cached_matches_uncached(&control, &cached);
}

// spec: design/int/int.md §7.6 — Dependency record and validity (a fresh
// module typechecked over a restored declared child, spec/08-modules.md §8.2.3).
#[test]
fn cache_fresh_test_child_over_restored_declared_child_matches_uncached_run() {
    fresh_test_child_over_restored_declared_child(
        "(import [grp.asserts [one]])\n(defn check [] (one))\n",
    );
}

// spec: design/int/int.md §7.6 — Dependency record and validity (as above, the
// child also importing its parent, spec/08-modules.md §8.3.8).
#[test]
fn cache_fresh_super_importing_test_child_over_restored_declared_child_matches_uncached_run() {
    fresh_test_child_over_restored_declared_child(
        "(import [super [v]])\n\
         (import [grp.asserts [one]])\n\
         (defn check [] (one))\n\
         (defn parent-value [] (v))\n",
    );
}
