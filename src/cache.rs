// ObjectCache — thin wrapper around the on-disk `.o` + sidecar pair owned
// by `CompilerSession`.
//
// Sprint 67 Cluster B sub-fire 3 per `design/arch/facades/int.md` L519-549:
// the int-side facade entry point that the rest of the crate goes through
// for cache reads + writes. The interior holds the three pre-S67 SharedState
// fields (`cache_dir`, `cache_state`, `compiled_o_paths`) as
// `Mutex<>`-wrapped private state; callers depend on the method surface
// (`source_hash`, `record_cache_hit`, `record_compiled`, `is_cache_valid`,
// `cache_dir`, `flush_manifest`, `append_o_path`, `all_paths`,
// `is_enabled`) — S68 may reshape internals freely without changing call
// sites.
//
// Per the user discipline: this is the method-surface landing, not an
// internal restructure. The interior data shape is the existing
// `CacheState` (in `crate::session`) plus two siblings, hoisted under one
// owner. The same pre-S67 IO paths apply; what changes is the call-site
// dispatch.
//
// Facade-prescribed signatures (`open`, `lookup_sidecar`, `load_object`,
// `write`) are sketched as additional methods that wrap the existing
// `cranelisp-backend` cache primitives — S68 will be the wave that fully
// consolidates per Decision-43 + the BC §"Object cache" alignment. The
// minimum-this-sprint surface is the ones that have actual callers
// (everything in `crate::session_v4` + `crate::worker`).

use std::path::PathBuf;
use std::sync::Mutex;

use cranelisp_types::ModuleFullPath;

use crate::session_setup::CacheState;

/// The on-disk object cache, owned by `SharedState`.
///
/// Wraps the three pre-S67 SharedState cache fields (`cache_dir`,
/// `cache_state`, `compiled_o_paths`) into a single facade. Constructed
/// once per session by `CompilerSession::new` via `ObjectCache::new` —
/// the simpler entry point that takes the already-resolved `cache_dir`
/// plus initial `CacheState`. `ObjectCache::open` is the facade-prescribed
/// constructor that would do the resolution itself; that variant is
/// deferred to S68 when the full cohesion lands.
pub struct ObjectCache {
    /// Cache directory for `.o` + sidecar pairs. `None` when caching is
    /// disabled (e.g. `--run` without `--link`, or `--no-cache`).
    dir: Option<PathBuf>,

    /// Mutable cache state — manifest + source hashes + recompiled set.
    /// `None` when caching is disabled. Behind `Mutex` because both
    /// the initiator thread (publish source hash, flush manifest) and
    /// nice workers (record compiled module after `.o` write) mutate
    /// it from multiple threads.
    state: Mutex<Option<CacheState>>,

    /// Collected `.o` file paths written by nice workers. Used by
    /// `--link` to pass all `.o` files to the system linker. Behind
    /// `Mutex` because nice workers append from multiple threads while
    /// the initiator may iterate at link-time.
    compiled_o_paths: Mutex<Vec<PathBuf>>,
}

impl ObjectCache {
    /// Construct an `ObjectCache` from already-resolved cache state.
    ///
    /// `dir` is the cache directory (`None` to disable caching) and
    /// `state` is the loaded/initial `CacheState`. `CompilerSession::new`
    /// calls this with the result of `CacheState::new(cache_dir.clone())`
    /// after creating the directory. The facade-prescribed
    /// `ObjectCache::open(project_root)` constructor is deferred to S68
    /// — it would fold the path resolution + dir creation in here too.
    pub fn new(dir: Option<PathBuf>, state: Option<CacheState>) -> Self {
        Self {
            dir,
            state: Mutex::new(state),
            compiled_o_paths: Mutex::new(Vec::new()),
        }
    }

    /// Whether caching is enabled for this session.
    ///
    /// Returns `true` iff both `dir` is set AND `state` is loaded.
    /// `--no-cache` and `--run`-without-`--link` produce `false`.
    pub fn is_enabled(&self) -> bool {
        self.dir.is_some()
            && self.state.lock()
                .unwrap_or_else(|e| e.into_inner())
                .is_some()
    }

    /// The cache directory, or `None` when caching is disabled.
    ///
    /// Used by `link_by_name` to write `__startup.o` and the `_main`
    /// alias `.o` alongside the nice-worker output.
    pub fn cache_dir(&self) -> Option<PathBuf> {
        self.dir.clone()
    }

    /// Record a module's source hash for downstream dependency tracking.
    ///
    /// Called by `register_module_with_source` (initiator) and
    /// `try_cache_hit_load` (worker, for transitive deps). Used as the
    /// dep hash by downstream modules when computing their cache
    /// validity. No-op if caching is disabled.
    pub fn record_source_hash(&self, module: &ModuleFullPath, hash: String) {
        let mut guard = self.state.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(cs) = guard.as_mut() {
            cs.source_hashes_mut().insert(module.clone(), hash);
        }
    }

    /// Check whether a module has a valid cache entry.
    ///
    /// Returns `true` iff caching is enabled AND the manifest has a
    /// record matching `current_source_hash` + all `dep_hashes`.
    /// Returns `false` on cache miss, on disabled caching, and on
    /// global invalidation (compiler version mismatch, etc.).
    pub fn is_cache_valid(
        &self,
        module: &ModuleFullPath,
        current_source_hash: &str,
        dep_hashes: &std::collections::HashMap<ModuleFullPath, String>,
    ) -> bool {
        let guard = self.state.lock().unwrap_or_else(|e| e.into_inner());
        match guard.as_ref() {
            Some(cs) => cs.is_cache_valid(module, current_source_hash, dep_hashes),
            None => false,
        }
    }

    /// Record a cache hit for `module` — stores its source hash for
    /// downstream dependency tracking without marking it as recompiled.
    ///
    /// Called by `try_cache_hit_load` after a successful cache load.
    pub fn record_cache_hit(&self, module: &ModuleFullPath, source_hash: String) {
        let mut guard = self.state.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(cs) = guard.as_mut() {
            cs.record_cache_hit(module, source_hash);
        }
    }

    /// Record that a module was recompiled (cache miss) and write its
    /// manifest entry. Called by the nice worker after a successful
    /// `.o` write.
    pub fn record_compiled(
        &self,
        module: &ModuleFullPath,
        source_hash: String,
        dep_hashes: std::collections::HashMap<String, String>,
    ) {
        let mut guard = self.state.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(cs) = guard.as_mut() {
            cs.record_module(module, source_hash, dep_hashes);
        }
    }

    /// Get a snapshot of stored source hashes for the in-flight session.
    /// Used by `compile_module_object` to look up the dep's hash when
    /// recording its manifest entry.
    pub fn source_hash(&self, module: &ModuleFullPath) -> Option<String> {
        let guard = self.state.lock().unwrap_or_else(|e| e.into_inner());
        guard.as_ref()
            .and_then(|cs| cs.source_hashes().get(module).cloned())
    }

    /// Flush the cache manifest to disk. No-op when caching is disabled.
    pub fn flush_manifest(&self) {
        let guard = self.state.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(cs) = guard.as_ref() {
            cs.flush_manifest();
        }
    }

    /// Append a `.o` path to the linker collection (idempotent).
    ///
    /// Two distinct writers feed this set and can name the SAME module's
    /// `.o`: `compile_module_object` (the nice worker, for a freshly
    /// compiled module — `session_v4.rs`) and `load_cached_module_via_linker`
    /// (the cache-hit restore path, registering `cached.object_path` so a
    /// later `--link` includes cross-module objects that were restored from a
    /// prior `--run`'s cache — `worker.rs`, S86 D5b). A module that is first
    /// cache-restored and later re-appended (or any double-call) must not
    /// double-list in `all_paths()` — a duplicated `.o` on the `cc` link line
    /// risks duplicate-symbol link errors. Dedup at this single chokepoint
    /// keeps `all_paths()` clean for both writers (Principle 18 — enforce the
    /// no-duplicate invariant structurally at the one mutation site).
    pub fn append_o_path(&self, path: PathBuf) {
        let mut guard = self.compiled_o_paths.lock()
            .unwrap_or_else(|e| e.into_inner());
        if !guard.contains(&path) {
            guard.push(path);
        }
    }

    /// Snapshot the collected `.o` paths for `--link`. Returns a clone.
    pub fn all_paths(&self) -> Vec<PathBuf> {
        self.compiled_o_paths.lock()
            .unwrap_or_else(|e| e.into_inner())
            .clone()
    }
}

// Sprint 67 Cluster B sub-fire 3c — unit tests per
// `feedback_unit_tests_with_dev.md`. Tests cover the method-surface
// invariants the rest of the crate depends on: cache-enabled detection,
// path round-trip, source-hash storage, manifest flush, and disabled-mode
// safety.
#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    fn cache_state_for(dir: &Path) -> CacheState {
        CacheState::new(dir.to_path_buf())
    }

    #[test]
    fn new_with_some_dir_and_state_is_enabled() {
        let tmp = tempfile::tempdir().unwrap();
        let cs = cache_state_for(tmp.path());
        let cache = ObjectCache::new(Some(tmp.path().to_path_buf()), Some(cs));
        assert!(cache.is_enabled(), "ObjectCache with dir + state must report enabled");
    }

    #[test]
    fn new_with_none_dir_is_disabled() {
        let cache = ObjectCache::new(None, None);
        assert!(!cache.is_enabled(), "ObjectCache with no dir must report disabled");
    }

    #[test]
    fn cache_dir_round_trips() {
        let tmp = tempfile::tempdir().unwrap();
        let cs = cache_state_for(tmp.path());
        let cache = ObjectCache::new(Some(tmp.path().to_path_buf()), Some(cs));
        assert_eq!(cache.cache_dir(), Some(tmp.path().to_path_buf()));
    }

    #[test]
    fn record_source_hash_stores_for_lookup() {
        let tmp = tempfile::tempdir().unwrap();
        let cs = cache_state_for(tmp.path());
        let cache = ObjectCache::new(Some(tmp.path().to_path_buf()), Some(cs));
        let m = ModuleFullPath::from("user");
        cache.record_source_hash(&m, "abc123".to_string());
        assert_eq!(cache.source_hash(&m).as_deref(), Some("abc123"));
    }

    #[test]
    fn source_hash_returns_none_when_disabled() {
        let cache = ObjectCache::new(None, None);
        let m = ModuleFullPath::from("user");
        cache.record_source_hash(&m, "abc123".to_string());
        assert_eq!(cache.source_hash(&m), None,
            "disabled cache must not retain source hashes");
    }

    #[test]
    fn append_o_path_then_all_paths_returns_in_order() {
        let cache = ObjectCache::new(None, None);
        cache.append_o_path(PathBuf::from("/tmp/a.o"));
        cache.append_o_path(PathBuf::from("/tmp/b.o"));
        let paths = cache.all_paths();
        assert_eq!(paths, vec![PathBuf::from("/tmp/a.o"), PathBuf::from("/tmp/b.o")]);
    }

    #[test]
    fn is_cache_valid_returns_false_when_disabled() {
        let cache = ObjectCache::new(None, None);
        let m = ModuleFullPath::from("user");
        let dep_hashes = std::collections::HashMap::new();
        assert!(!cache.is_cache_valid(&m, "anyhash", &dep_hashes),
            "disabled cache must always miss");
    }

    #[test]
    fn flush_manifest_is_noop_when_disabled() {
        let cache = ObjectCache::new(None, None);
        // Should not panic.
        cache.flush_manifest();
    }

    // S86 D5b: the cache-HIT restore path (`load_cached_module_via_linker`)
    // registers its `cached.object_path` via `append_o_path` so a later
    // `--link` includes cross-module objects restored from a prior `--run`'s
    // cache. Before the fix, only `compile_module_object` (the cache-MISS
    // path) appended, so a restored dep `.o` was missing from `all_paths()`
    // and `cc` linked without it (undefined `__cranelisp_got_{dep}`). This
    // test asserts a restore-path append shows up in the link set, and that
    // the same `.o` named by BOTH the cache-restore and a later fresh
    // recompile is listed exactly once (dedup — no duplicate-symbol risk on
    // the `cc` line).
    #[test]
    fn cache_restored_o_path_joins_link_set_and_dedups() {
        let cache = ObjectCache::new(None, None);
        let dep_o = PathBuf::from("/tmp/.cache/helper.o");
        let user_o = PathBuf::from("/tmp/.cache/user.o");

        // Cache-HIT restore of `helper` registers its restored object.
        cache.append_o_path(dep_o.clone());
        // Fresh compile of `user` (cache-MISS) appends its object.
        cache.append_o_path(user_o.clone());

        let paths = cache.all_paths();
        assert!(paths.contains(&dep_o),
            "cache-restored dep .o must be in the --link set, got {paths:?}");
        assert!(paths.contains(&user_o));

        // A module that is both cache-restored AND later freshly recompiled
        // (or any double-append) must not double-list.
        cache.append_o_path(dep_o.clone());
        let after = cache.all_paths();
        assert_eq!(after.iter().filter(|p| **p == dep_o).count(), 1,
            "append_o_path must dedup — a duplicated .o on the cc line risks \
             duplicate-symbol link errors; got {after:?}");
        assert_eq!(after.len(), 2, "exactly two distinct objects, got {after:?}");
    }

    #[test]
    fn record_cache_hit_stores_source_hash_for_downstream() {
        let tmp = tempfile::tempdir().unwrap();
        let cs = cache_state_for(tmp.path());
        let cache = ObjectCache::new(Some(tmp.path().to_path_buf()), Some(cs));
        let m = ModuleFullPath::from("dep");
        cache.record_cache_hit(&m, "depHash".to_string());
        assert_eq!(cache.source_hash(&m).as_deref(), Some("depHash"));
    }
}
