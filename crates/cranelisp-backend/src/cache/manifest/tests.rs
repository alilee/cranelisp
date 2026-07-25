use super::*;

// spec: design/backend/module-caching.md §3 — SHA-256 source hashing
#[test]
fn test_hash_source_deterministic() {
    let h1 = hash_source("(defn foo [x] x)");
    let h2 = hash_source("(defn foo [x] x)");
    assert_eq!(h1, h2);
}

// spec: design/backend/module-caching.md §3 — different source produces different hash
#[test]
fn test_hash_source_different_input() {
    let h1 = hash_source("(defn foo [x] x)");
    let h2 = hash_source("(defn bar [x] x)");
    assert_ne!(h1, h2);
}

// spec: design/backend/module-caching.md §3 — hash is 64 hex chars (SHA-256)
#[test]
fn test_hash_source_length() {
    let h = hash_source("hello");
    assert_eq!(h.len(), 64);
    assert!(h.chars().all(|c| c.is_ascii_hexdigit()));
}

// spec: design/backend/module-caching.md §3 — empty source produces valid hash
#[test]
fn test_hash_source_empty() {
    let h = hash_source("");
    assert_eq!(h.len(), 64);
}

// spec: design/backend/module-caching.md §3 — binary fingerprint is memoized
#[test]
fn test_binary_fingerprint_stable() {
    let fp1 = binary_fingerprint();
    let fp2 = binary_fingerprint();
    assert_eq!(fp1, fp2);
}

// spec: design/backend/module-caching.md §3 — manifest round-trip
#[test]
fn test_manifest_round_trip() {
    let dir = tempfile::tempdir().unwrap();
    let mut manifest = CacheManifest::new("aarch64-apple-darwin");
    let mp = ModuleFullPath::from("core.numerics");
    let mut deps = HashMap::new();
    deps.insert("prelude".to_string(), hash_source("prelude source"));
    manifest.upsert_module(&mp, hash_source("source"), deps);

    write_manifest(dir.path(), &manifest).unwrap();
    let loaded = read_manifest(dir.path()).unwrap();

    assert_eq!(loaded.cache_format_version, CACHE_FORMAT_VERSION);
    assert_eq!(loaded.target_triple, "aarch64-apple-darwin");
    let entry = loaded.get_module(&mp).unwrap();
    assert_eq!(entry.source_hash, hash_source("source"));
    assert_eq!(
        entry.dependency_hashes.get("prelude").unwrap(),
        &hash_source("prelude source")
    );
}

// spec: design/backend/module-caching.md §3 — check_manifest with valid cache
#[test]
fn test_check_manifest_valid() {
    let triple = target_lexicon::Triple::host().to_string();
    let mut manifest = CacheManifest::new(&triple);
    let mp = ModuleFullPath::from("user");
    let source_hash = hash_source("(defn main [] 42)");
    manifest.upsert_module(&mp, source_hash.clone(), HashMap::new());

    let result = check_manifest(&manifest, &mp, &source_hash, &HashMap::new());
    assert!(result.unwrap());
}

// spec: design/backend/module-caching.md §3 — check_manifest with changed source
#[test]
fn test_check_manifest_source_changed() {
    let triple = target_lexicon::Triple::host().to_string();
    let mut manifest = CacheManifest::new(&triple);
    let mp = ModuleFullPath::from("user");
    manifest.upsert_module(&mp, hash_source("old source"), HashMap::new());

    let result = check_manifest(&manifest, &mp, &hash_source("new source"), &HashMap::new());
    assert!(!result.unwrap());
}

// spec: design/backend/module-caching.md §3 — check_manifest with changed dependency
#[test]
fn test_check_manifest_dependency_changed() {
    let triple = target_lexicon::Triple::host().to_string();
    let mut manifest = CacheManifest::new(&triple);
    let mp = ModuleFullPath::from("user");
    let source_hash = hash_source("user source");
    let mut dep_hashes = HashMap::new();
    dep_hashes.insert("prelude".to_string(), hash_source("old prelude"));
    manifest.upsert_module(&mp, source_hash.clone(), dep_hashes);

    let mut current_deps = HashMap::new();
    current_deps.insert(ModuleFullPath::from("prelude"), hash_source("new prelude"));
    let result = check_manifest(&manifest, &mp, &source_hash, &current_deps);
    assert!(!result.unwrap());
}

// spec: design/backend/module-caching.md §3 — check_manifest with format version mismatch
#[test]
fn test_check_manifest_format_version_mismatch() {
    let triple = target_lexicon::Triple::host().to_string();
    let mut manifest = CacheManifest::new(&triple);
    manifest.cache_format_version = 999;
    let mp = ModuleFullPath::from("user");

    let result = check_manifest(&manifest, &mp, "hash", &HashMap::new());
    assert!(result.is_err());
}

// spec: design/backend/module-caching.md §3 — check_manifest with uncached module
#[test]
fn test_check_manifest_uncached_module() {
    let triple = target_lexicon::Triple::host().to_string();
    let manifest = CacheManifest::new(&triple);
    let mp = ModuleFullPath::from("unknown");

    let result = check_manifest(&manifest, &mp, "hash", &HashMap::new());
    assert!(!result.unwrap());
}

// spec: design/backend/module-caching.md §3 — manifest upsert replaces existing
#[test]
fn test_manifest_upsert_replaces() {
    let mut manifest = CacheManifest::new("test");
    let mp = ModuleFullPath::from("mod");
    manifest.upsert_module(&mp, "hash1".to_string(), HashMap::new());
    manifest.upsert_module(&mp, "hash2".to_string(), HashMap::new());
    assert_eq!(manifest.get_module(&mp).unwrap().source_hash, "hash2");
}

// ===== FIXME 0120 harvest: backend-internal manifest invalidation
// assertions from the quarantined `tests/legacy/cache.rs`. The
// pipeline/runtime-value parity is already covered e2e in
// `tests/cache.rs`; these are the crate-internal field-tamper and
// transitive/negative-guard assertions that have no e2e equivalent
// (per `memory/project_test_strategy.md` two-tier strategy). =====

// spec: design/backend/module-caching.md §6 — compiler-mtime change globally invalidates
//
// Harvest of legacy `cache_invalidation_compiler_mtime_change`: a
// manifest whose `compiler_mtime` differs from the running binary's
// fingerprint must yield `Err(CompilerChanged)`, not a per-module
// false. Tamper the field directly (the field is `pub`).
#[test]
fn check_manifest_compiler_mtime_change_errors() {
    let triple = target_lexicon::Triple::host().to_string();
    let mut manifest = CacheManifest::new(&triple);
    let mp = ModuleFullPath::from("user");
    let source_hash = hash_source("(defn main [] 42)");
    manifest.upsert_module(&mp, source_hash.clone(), HashMap::new());
    // Force a non-empty, definitely-stale fingerprint so the guard fires
    // regardless of the test binary's actual mtime.
    manifest.compiler_mtime = "mtime-0.0".to_string();

    let result = check_manifest(&manifest, &mp, &source_hash, &HashMap::new());
    assert!(
        matches!(result, Err(CacheInvalidReason::CompilerChanged)),
        "stale compiler_mtime must yield CompilerChanged, got {result:?}"
    );
}

// spec: design/backend/module-caching.md §6 — target-triple change globally invalidates
//
// Harvest of legacy `cache_invalidation_target_triple_change`: a
// manifest built for a foreign triple must yield `Err(TargetTriple)`.
// A definitely-foreign triple is chosen so the guard fires on every host.
#[test]
fn check_manifest_target_triple_change_errors() {
    let mut manifest = CacheManifest::new("sparc64-unknown-cranelisp-elf");
    let mp = ModuleFullPath::from("user");
    let source_hash = hash_source("(defn main [] 42)");
    manifest.upsert_module(&mp, source_hash.clone(), HashMap::new());

    let result = check_manifest(&manifest, &mp, &source_hash, &HashMap::new());
    assert!(
        matches!(result, Err(CacheInvalidReason::TargetTriple { .. })),
        "foreign target_triple must yield TargetTriple, got {result:?}"
    );
}

// spec: design/backend/module-caching.md §6 — Cranelift-version change globally invalidates
//
// Harvest of legacy `cache_invalidation_cranelift_version_change`: a
// manifest tagged with a stale Cranelift version must yield
// `Err(CraneliftVersion)`.
#[test]
fn check_manifest_cranelift_version_change_errors() {
    let triple = target_lexicon::Triple::host().to_string();
    let mut manifest = CacheManifest::new(&triple);
    let mp = ModuleFullPath::from("user");
    let source_hash = hash_source("(defn main [] 42)");
    manifest.upsert_module(&mp, source_hash.clone(), HashMap::new());
    manifest.cranelift_version = "cranelift-0.0.0-stale".to_string();

    let result = check_manifest(&manifest, &mp, &source_hash, &HashMap::new());
    assert!(
        matches!(result, Err(CacheInvalidReason::CraneliftVersion { .. })),
        "stale cranelift_version must yield CraneliftVersion, got {result:?}"
    );
}

// spec: design/backend/module-caching.md §3 — transitive dependency invalidation
//
// Harvest of legacy `cache_invalidation_transitive_dependency`: a chain
// A→B→C where C changes. A's manifest entry records B as its direct
// dependency; presenting a changed hash for B (B recompiled because C
// changed) invalidates A. This exercises the per-module
// `dependency_hashes` check independently of the global guards.
#[test]
fn check_manifest_transitive_dependency_change_invalidates() {
    let triple = target_lexicon::Triple::host().to_string();
    let mut manifest = CacheManifest::new(&triple);

    let module_a = ModuleFullPath::from("a");
    let a_hash = hash_source("(defn a [] (b))");
    let mut a_deps = HashMap::new();
    a_deps.insert("b".to_string(), hash_source("b@v1"));
    manifest.upsert_module(&module_a, a_hash.clone(), a_deps);

    // B was recompiled (its own dep C changed) → B's hash is now v2.
    // A's cached record still expects b@v1, so A is invalid.
    let mut current_deps = HashMap::new();
    current_deps.insert(ModuleFullPath::from("b"), hash_source("b@v2"));
    let result = check_manifest(&manifest, &module_a, &a_hash, &current_deps);
    assert!(
        !result.unwrap(),
        "A must be invalid when its dependency B changed transitively"
    );
}

// spec: design/backend/module-caching.md §3 — unrelated module change does NOT invalidate
//
// Harvest of legacy `cache_not_invalidated_by_unrelated_module_change`
// (negative guard): two modules in the manifest; A has no dependency on
// B. Changing B's source must leave A's check valid — the per-module
// dependency_hashes scope must not leak across unrelated modules.
#[test]
fn check_manifest_unrelated_module_change_does_not_invalidate() {
    let triple = target_lexicon::Triple::host().to_string();
    let mut manifest = CacheManifest::new(&triple);

    let module_a = ModuleFullPath::from("a");
    let a_hash = hash_source("(defn a [] 1)");
    manifest.upsert_module(&module_a, a_hash.clone(), HashMap::new());

    let module_b = ModuleFullPath::from("b");
    manifest.upsert_module(&module_b, hash_source("(defn b [] 2)"), HashMap::new());

    // B changes (not reflected in A's empty dep set). A stays valid:
    // A is checked with its own unchanged hash and no dependencies.
    let result = check_manifest(&manifest, &module_a, &a_hash, &HashMap::new());
    assert!(
        result.unwrap(),
        "A must remain valid when unrelated module B changes"
    );
}

// spec: design/backend/module-caching.md §3 — prelude change invalidates all dependents
//
// Harvest of legacy `cache_prelude_change_invalidates_all_user_modules`:
// two user modules both depend on `prelude`. A prelude source change must
// invalidate BOTH — the fan-out is per-module but every dependent records
// the prelude hash, so each independently detects the mismatch.
#[test]
fn check_manifest_prelude_change_invalidates_all_dependents() {
    let triple = target_lexicon::Triple::host().to_string();
    let mut manifest = CacheManifest::new(&triple);

    let old_prelude = hash_source("(defn p [] 0)");
    for name in ["user1", "user2"] {
        let mp = ModuleFullPath::from(name);
        let mut deps = HashMap::new();
        deps.insert("prelude".to_string(), old_prelude.clone());
        manifest.upsert_module(&mp, hash_source(name), deps);
    }

    let mut current_deps = HashMap::new();
    current_deps.insert(
        ModuleFullPath::from("prelude"),
        hash_source("(defn p [] 1)"),
    );

    for name in ["user1", "user2"] {
        let mp = ModuleFullPath::from(name);
        let result = check_manifest(&manifest, &mp, &hash_source(name), &current_deps);
        assert!(
            !result.unwrap(),
            "{name} must be invalidated by the prelude change"
        );
    }
}

// spec: design/backend/module-caching.md §3 — unchanged module keeps cache when sibling changes
//
// Harvest of legacy `watch_unchanged_modules_keep_cache` (the final
// `tests/legacy/sprint23.rs` GAP, FIXME 0144). The §14.7 watch invariant
// "unchanged modules keep their cached .o" reduces to a cache-manifest
// property: with two modules in one manifest, presenting a *changed* hash
// for A must make A NOT a cache hit while B, presented with its *unchanged*
// hash, must remain a cache hit. This is the paired same-manifest assertion
// (the prior `..._unrelated_module_change_does_not_invalidate` harvest only
// asserts the unchanged-sibling half; this pins both halves together — the
// exact discrimination the watcher relies on to recompile A while reusing
// B's cached object).
#[test]
fn check_manifest_changed_module_misses_unchanged_sibling_hits() {
    let triple = target_lexicon::Triple::host().to_string();
    let mut manifest = CacheManifest::new(&triple);

    let mp_a = ModuleFullPath::from("mod_a");
    let mp_b = ModuleFullPath::from("mod_b");
    let hash_a = hash_source("(defn val-a [] 1)");
    let hash_b = hash_source("(defn val-b [] 2)");
    manifest.upsert_module(&mp_a, hash_a, HashMap::new());
    manifest.upsert_module(&mp_b, hash_b.clone(), HashMap::new());

    // A "changes" — present a new hash. Must NOT be a cache hit.
    let new_hash_a = hash_source("(defn val-a [] 999)");
    let a_valid = check_manifest(&manifest, &mp_a, &new_hash_a, &HashMap::new());
    assert!(
        !a_valid.unwrap(),
        "module A with changed source must NOT be a cache hit"
    );

    // B is unchanged — present the original hash. Must STILL be a cache hit.
    let b_valid = check_manifest(&manifest, &mp_b, &hash_b, &HashMap::new());
    assert!(
        b_valid.unwrap(),
        "module B with unchanged source must still be a cache hit"
    );
}

// spec: design/backend/module-caching.md §3 — empty hash is not a wildcard
//
// Harvest of legacy `cache_neg_empty_hash_not_wildcard` (negative guard):
// a real cached source hash must NOT match an empty presented hash. The
// empty string is not a "match anything" sentinel.
#[test]
fn check_manifest_empty_hash_not_wildcard() {
    let triple = target_lexicon::Triple::host().to_string();
    let mut manifest = CacheManifest::new(&triple);
    let mp = ModuleFullPath::from("user");
    manifest.upsert_module(&mp, hash_source("(defn main [] 42)"), HashMap::new());

    let result = check_manifest(&manifest, &mp, "", &HashMap::new());
    assert!(
        !result.unwrap(),
        "empty presented hash must not match a real cached hash"
    );
}

// =========================================================================
// S101 item 6 — CRANELISP_NO_OWNERSHIP cache-manifest global key
// (design/backend/ownership-codegen.md §2.3, stage M).
// =========================================================================

// spec: design/backend/ownership-codegen.md §2.3 — a manifest written under
// the OTHER toggle polarity is globally invalid (wholesale invalidation), and
// the reason is the typed OwnershipToggle variant.
#[test]
fn check_manifest_ownership_toggle_flip_is_globally_invalid() {
    let triple = target_lexicon::Triple::host().to_string();
    let mut manifest = CacheManifest::new(&triple);
    let mp = ModuleFullPath::from("user");
    let source_hash = hash_source("(defn main [] 42)");
    manifest.upsert_module(&mp, source_hash.clone(), HashMap::new());

    // Simulate the cache having been written under the OTHER polarity.
    manifest.ownership_disabled = !no_ownership_enabled();

    let result = check_manifest(&manifest, &mp, &source_hash, &HashMap::new());
    match result {
        Err(CacheInvalidReason::OwnershipToggle { cached, current }) => {
            assert_ne!(cached, current, "the flip is what invalidates");
        }
        other => panic!(
            "polarity flip must be a GLOBAL invalidation with the typed \
             OwnershipToggle reason; got {other:?}"
        ),
    }
}

// spec: design/backend/ownership-codegen.md §2.3 — key STABILITY (the L-B3
// leg-4 guard against an always-miss implementation): a fresh manifest stamps
// the current polarity, so a same-polarity check passes.
#[test]
fn check_manifest_same_ownership_polarity_is_stable() {
    let triple = target_lexicon::Triple::host().to_string();
    let mut manifest = CacheManifest::new(&triple);
    assert_eq!(
        manifest.ownership_disabled,
        no_ownership_enabled(),
        "CacheManifest::new must stamp the current toggle polarity"
    );
    let mp = ModuleFullPath::from("user");
    let source_hash = hash_source("(defn main [] 42)");
    manifest.upsert_module(&mp, source_hash.clone(), HashMap::new());

    let result = check_manifest(&manifest, &mp, &source_hash, &HashMap::new());
    assert!(
        result.unwrap(),
        "same-polarity manifest must remain a cache hit (key stability)"
    );
}

// spec: design/backend/ownership-codegen.md §2.3 — a PRE-KEY manifest (no
// `ownership_disabled` field in the JSON) deserializes to the serde default
// `false` — sound because pre-key caches were written pre-analysis where both
// polarities are byte-identical; it invalidates iff the session sets the env.
#[test]
fn manifest_missing_ownership_field_defaults_to_analysis_on() {
    let json = r#"{
        "cache_format_version": 11,
        "compiler_mtime": "",
        "target_triple": "aarch64-unknown-linux-gnu",
        "cranelift_version": "0.116.1",
        "modules": {}
    }"#;
    let manifest: CacheManifest =
        serde_json::from_str(json).expect("pre-key manifest must deserialize");
    assert!(
        !manifest.ownership_disabled,
        "absent field must default to ownership_disabled: false"
    );
}

// spec: design/backend/ownership-codegen.md §2.3 — CONVERGENCE: a manifest on
// disk written under the OTHER polarity does not load (`read_manifest` treats
// it as absent), so the session starts from a fresh manifest stamped with the
// current polarity — the flip run recompiles wholesale AND the next
// same-polarity run serves hits again (the session rewrites the loaded
// manifest object, so a surviving stale-polarity manifest would never
// converge).
#[test]
fn read_manifest_rejects_other_polarity_manifest() {
    let dir = tempfile::tempdir().unwrap();
    let triple = target_lexicon::Triple::host().to_string();

    // Same-polarity manifest round-trips.
    let manifest = CacheManifest::new(&triple);
    write_manifest(dir.path(), &manifest).unwrap();
    assert!(
        read_manifest(dir.path()).is_some(),
        "same-polarity manifest must load"
    );

    // Other-polarity manifest is treated as absent.
    let mut flipped = CacheManifest::new(&triple);
    flipped.ownership_disabled = !no_ownership_enabled();
    write_manifest(dir.path(), &flipped).unwrap();
    assert!(
        read_manifest(dir.path()).is_none(),
        "an other-polarity manifest must not load (wholesale invalidation + \
         convergence — the fresh replacement stamps the current polarity)"
    );
}
