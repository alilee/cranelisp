// ObjectCache — thin wrapper around the on-disk `.o` + sidecar pair owned
// by `CompilerSession`.
//
// Sprint 67 Cluster B sub-fire 3 per `design/arch/facades/int.md` L519-549:
// the int-side facade entry point that the rest of the crate goes through
// for cache reads + writes. The interior holds the three pre-S67 SharedState
// fields (`cache_dir`, `cache_state`, `compiled_o_paths`) as
// `Mutex<>`-wrapped private state; callers depend on the method surface
// (`source_hash`, `record_cache_hit`, `record_compiled`, `validate`,
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

use std::collections::BTreeMap;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use cranelisp_types::ModuleFullPath;

use crate::session_setup::{CacheState, CacheValidity, FileAgreement};

pub(crate) mod dependency_record;

use dependency_record::{
    AuthoredSlotLayout, DeferredEntry, DependencyRecord, LoadedSource, ModuleSources,
};

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

    /// Each stored `.meta` decoded for validation, held for the member's
    /// restore so the file is decoded once (`design/int/int.md` §7.6.3);
    /// `None` records that no valid `.meta` is stored. An entry lives only
    /// while the session holds no table for the member: the restore takes it,
    /// and the restore's install and a fresh registration end it. Every
    /// session writer of a `.meta` goes through [`Self::write_meta`], which
    /// ends the entry under its shard lock, so a decode cannot outlive the
    /// file it read. Correctness never depends on an entry: a missing one is
    /// decoded from the file.
    stored: dashmap::DashMap<ModuleFullPath, Option<StoredMeta>>,

    /// Each module whose latest object pass stopped without publishing its
    /// object (`design/int/int.md` §7.7). `--link` refuses while any stands.
    stopped_passes: Mutex<BTreeMap<ModuleFullPath, StoppedPass>>,

    /// The session's hold on `dir`: the project directory's owner lock, or the
    /// private directory it removes at its end. `None` for a cache built
    /// without a session's directory decision.
    directory: Mutex<Option<CacheDirectory>>,
}

/// The lock file whose exclusive advisory lock makes a session the owner of
/// its project's cache directory.
const OWNER_LOCK_FILE: &str = "owner.lock";

/// The directory a session's cache reads and writes (`design/int/int.md` §7.7,
/// *One cache owner per project directory*).
#[derive(Debug)]
pub(crate) enum CacheDirectory {
    /// The project's cache directory, held under its owner lock for the
    /// session's life. The operating system releases the lock when the
    /// process ends, a panic or a kill included.
    Owned { dir: PathBuf, _lock: std::fs::File },
    /// A private directory outside the project, used because the project's
    /// cache has another owner or cannot be locked. Removed at the session's
    /// end; nothing in the project's cache is read or written.
    Private { dir: PathBuf },
}

impl CacheDirectory {
    /// Take ownership of `project_cache`, never waiting; fall back to a fresh
    /// private directory when the lock is not taken, for any reason.
    pub(crate) fn open(project_cache: &Path) -> Self {
        match Self::take_owner_lock(project_cache) {
            Ok(lock) => CacheDirectory::Owned {
                dir: project_cache.to_path_buf(),
                _lock: lock,
            },
            Err(cause) => {
                let dir = Self::fresh_private_dir();
                if std::env::var("CRANELISP_MODULE_TRACE").is_ok() {
                    eprintln!(
                        "cache: '{}' is not owned by this session ({cause}); using private '{}'",
                        project_cache.display(),
                        dir.display()
                    );
                }
                CacheDirectory::Private { dir }
            }
        }
    }

    fn take_owner_lock(project_cache: &Path) -> Result<std::fs::File, String> {
        std::fs::create_dir_all(project_cache).map_err(|e| format!("create: {e}"))?;
        let lock = std::fs::OpenOptions::new()
            .create(true)
            .truncate(false)
            .write(true)
            .open(project_cache.join(OWNER_LOCK_FILE))
            .map_err(|e| format!("open lock file: {e}"))?;
        lock.try_lock().map_err(|e| format!("lock: {e}"))?;
        Ok(lock)
    }

    /// A new, empty directory under the system temporary directory.
    fn fresh_private_dir() -> PathBuf {
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let base = std::env::temp_dir();
        loop {
            let n = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let dir = base.join(format!("cranelisp-cache-{}-{n}", std::process::id()));
            match std::fs::create_dir(&dir) {
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                // A directory that cannot be created leaves every cache write
                // to fail as a stopped pass, never in the project's cache.
                _ => return dir,
            }
        }
    }

    pub(crate) fn path(&self) -> &Path {
        match self {
            CacheDirectory::Owned { dir, .. } | CacheDirectory::Private { dir } => dir,
        }
    }
}

impl Drop for CacheDirectory {
    fn drop(&mut self) {
        if let CacheDirectory::Private { dir } = self {
            let _ = std::fs::remove_dir_all(dir);
        }
    }
}

/// Where an object pass stopped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PassStage {
    /// The cache directory, the old object's retirement or the `.meta` write.
    Metadata,
    /// The object's codegen, emission or publication.
    Object,
}

/// An object pass that stopped at `stage` for `cause`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StoppedPass {
    pub(crate) stage: PassStage,
    pub(crate) cause: String,
}

impl std::fmt::Display for StoppedPass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let stage = match self.stage {
            PassStage::Metadata => "its metadata",
            PassStage::Object => "its object",
        };
        write!(f, "stopped at {stage}: {}", self.cause)
    }
}

/// What a restore loads for a decoded stored module (`design/int/int.md`
/// §7.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StoredObject {
    /// The module's `.o` is loaded.
    Load,
    /// The module codegens nothing, so it has no `.o` to load.
    NothingToLoad,
    /// The module has codegen targets and no `.o`: a miss.
    Missing,
}

impl StoredObject {
    pub(crate) fn of(cached: &cranelisp_backend::cache::CachedModule) -> Self {
        if cached.has_object {
            StoredObject::Load
        } else if cached.symbol_table.codegen_targets().next().is_some() {
            StoredObject::Missing
        } else {
            StoredObject::NothingToLoad
        }
    }
}

/// Publish `bytes` as the module object at `object_path`, so a file at that
/// path is always a complete object (`design/int/int.md` §7.7). On failure
/// nothing new stands at `object_path`.
pub(crate) fn publish_object(object_path: &Path, bytes: &[u8]) -> std::io::Result<()> {
    publish_object_with(object_path, |file| file.write_all(bytes))
}

/// Run `write` into a temporary beside `object_path`, flush it to disk and
/// rename it onto `object_path`. A failed step removes the temporary.
pub(crate) fn publish_object_with(
    object_path: &Path,
    write: impl FnOnce(&mut std::fs::File) -> std::io::Result<()>,
) -> std::io::Result<()> {
    let temporary = publication_temporary(object_path);
    let mut file = std::fs::File::create_new(&temporary)?;
    let written = write(&mut file).and_then(|()| file.sync_all());
    drop(file);
    let published = written.and_then(|()| std::fs::rename(&temporary, object_path));
    if published.is_err() {
        // Best effort: restore reads only the object path, never a temporary.
        let _ = std::fs::remove_file(&temporary);
    }
    published
}

/// A name beside `object_path` that no other write, in this process or
/// another, uses.
fn publication_temporary(object_path: &Path) -> PathBuf {
    static NEXT_PUBLICATION: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let publication = NEXT_PUBLICATION.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let mut name = object_path.file_name().unwrap_or_default().to_os_string();
    name.push(format!(".{}.{publication}.tmp", std::process::id()));
    object_path.with_file_name(name)
}

fn cache_write_error(message: String) -> cranelisp_types::CranelispError {
    cranelisp_types::CranelispError::CodegenError {
        message,
        location: cranelisp_types::ErrorLocation::from_span(cranelisp_types::Span::SYNTHETIC),
    }
}

/// What a `.meta` write did.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MetaWrite {
    /// The `.meta` now holds the table, its earlier object retired.
    Written,
    /// Nothing was written: the module's table is ahead of its file
    /// (`design/int/s125-binary-clean.md` §4.3).
    Diverged,
}

/// A decoded stored `.meta` and the authored slot layout read from it.
struct StoredMeta {
    layout: AuthoredSlotLayout,
    module: cranelisp_backend::cache::CachedModule,
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
            stored: dashmap::DashMap::new(),
            stopped_passes: Mutex::new(BTreeMap::new()),
            directory: Mutex::new(None),
        }
    }

    /// The session's cache over `directory` (`None` under `--no-cache`): the
    /// one construction that decides which directory a session reads and
    /// writes (`design/int/int.md` §7.7, *One cache owner*).
    pub(crate) fn for_session(directory: Option<CacheDirectory>) -> Self {
        let dir = directory.as_ref().map(|d| d.path().to_path_buf());
        let state = dir.clone().map(CacheState::new);
        let cache = Self::new(dir, state);
        *cache.directory.lock().unwrap_or_else(|e| e.into_inner()) = directory;
        cache
    }

    /// End the session's hold on its directory: release the owner lock, or
    /// remove the private directory. Called once the session's workers have
    /// stopped writing.
    pub(crate) fn end_session(&self) {
        self.directory
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .take();
    }

    /// The authored slot layout of `module`'s stored `.meta`; `None` when
    /// caching is disabled or no valid `.meta` is stored. The decode is held
    /// for the member's restore.
    pub(crate) fn stored_layout(&self, module: &ModuleFullPath) -> Option<AuthoredSlotLayout> {
        if let Some(held) = self.stored.get(module) {
            return held.as_ref().map(|stored| stored.layout.clone());
        }
        self.stored
            .entry(module.clone())
            .or_insert_with(|| {
                let module = self.decode(module)?;
                Some(StoredMeta {
                    layout: AuthoredSlotLayout::of(&module.symbol_table),
                    module,
                })
            })
            .as_ref()
            .map(|stored| stored.layout.clone())
    }

    /// `module`'s stored module for its metadata restore: the decode
    /// validation holds, taken, or else a decode of the file.
    pub(crate) fn stored_module(
        &self,
        module: &ModuleFullPath,
    ) -> Option<cranelisp_backend::cache::CachedModule> {
        match self.stored.remove(module) {
            Some((_, held)) => held.map(|stored| stored.module),
            None => self.decode(module),
        }
    }

    /// End any decode held for `module`: the session now holds its table.
    pub(crate) fn end_stored_hold(&self, module: &ModuleFullPath) {
        self.stored.remove(module);
    }

    fn decode(&self, module: &ModuleFullPath) -> Option<cranelisp_backend::cache::CachedModule> {
        let dir = self.dir.as_deref()?;
        cranelisp_backend::cache::try_load_cached_module(dir, module)
            .ok()
            .flatten()
    }

    /// Write `table` as `module`'s stored `.meta`, ending the decode held from
    /// the `.meta` it replaces.
    ///
    /// The module's existing `.o` is removed first, so the new `.meta` never
    /// stands beside an object built from another table (`design/int/int.md`
    /// §7.7). If the object cannot be removed, nothing is written and the
    /// earlier pair stands; the caller must then record no manifest entry.
    ///
    /// While the module's table is ahead of its file nothing is written
    /// (`design/int/s125-binary-clean.md` §4.3). The agreement is read under
    /// the lock a divergence retires the module's files under, so a `.meta`
    /// is never written after its retirement.
    pub(crate) fn write_meta(
        &self,
        module: &ModuleFullPath,
        table: &crate::code::SessionSymbolTable,
    ) -> Result<MetaWrite, cranelisp_types::CranelispError> {
        let Some(dir) = self.dir.as_deref() else {
            return Err(cache_write_error(format!(
                "cannot write cache metadata for {module}: caching is disabled"
            )));
        };
        let state = self.state.lock().unwrap_or_else(|e| e.into_inner());
        if state
            .as_ref()
            .is_some_and(|cs| cs.agreement(module) == FileAgreement::Diverged)
        {
            return Ok(MetaWrite::Diverged);
        }
        let (meta_path, object_path) = cranelisp_backend::cache::module_cache_path(dir, module);
        let held = self.stored.entry(module.clone());
        match std::fs::remove_file(&object_path) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                return Err(cache_write_error(format!(
                    "cannot retire cached object {} before rewriting its metadata: {error}",
                    object_path.display()
                )));
            }
        }
        let written = cranelisp_backend::cache::serialize::write_meta(
            &meta_path,
            table,
            cranelisp_backend::cache::CACHE_SCHEMA_VERSION,
        );
        if let dashmap::Entry::Occupied(decoded) = held {
            decoded.remove();
        }
        drop(state);
        written.map(|()| MetaWrite::Written)
    }

    /// Record that `module`'s live table is ahead of its source file: a
    /// definition turn's regeneration did not write it
    /// (`design/int/s125-binary-clean.md` §4.3). The module's `.o` and `.meta`
    /// are retired, so the next session cannot restore a definition the file
    /// lacks, and no cache entry is written for it until a load, reload or
    /// regeneration makes the file agree again.
    pub(crate) fn record_divergence(&self, module: &ModuleFullPath) {
        let mut state = self.state.lock().unwrap_or_else(|e| e.into_inner());
        let Some(cs) = state.as_mut() else {
            return;
        };
        cs.record_divergence(module);
        self.stored.remove(module);
        let Some(dir) = self.dir.as_deref() else {
            return;
        };
        let (meta_path, object_path) = cranelisp_backend::cache::module_cache_path(dir, module);
        for path in [&object_path, &meta_path] {
            match std::fs::remove_file(path) {
                Ok(()) => {}
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                Err(error) => eprintln!(
                    "Warning: cannot retire cached {} of {module}, whose session holds \
                     definitions its file lacks: {error}",
                    path.display()
                ),
            }
        }
    }

    /// Whether `module`'s table agrees with its file; it agrees when caching
    /// is disabled.
    #[cfg(test)]
    pub(crate) fn agreement(&self, module: &ModuleFullPath) -> FileAgreement {
        let state = self.state.lock().unwrap_or_else(|e| e.into_inner());
        state
            .as_ref()
            .map_or(FileAgreement::Agrees, |cs| cs.agreement(module))
    }

    /// Whether caching is enabled for this session.
    ///
    /// Returns `true` iff both `dir` is set AND `state` is loaded.
    /// `--no-cache` and `--run`-without-`--link` produce `false`.
    pub fn is_enabled(&self) -> bool {
        self.dir.is_some()
            && self
                .state
                .lock()
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

    /// Record the source hash a fresh registration of `module` loaded. It
    /// supersedes a restored version and ends any held decode, since the
    /// session now holds the module's table. Records nothing if caching is
    /// disabled.
    pub fn record_source_hash(&self, module: &ModuleFullPath, hash: String) {
        self.end_stored_hold(module);
        let mut guard = self.state.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(cs) = guard.as_mut() {
            cs.record_fresh_source(module, hash);
        }
    }

    /// Validate `module`'s manifest entry against the current sources.
    /// Always stale when caching is disabled.
    pub(crate) fn validate(
        &self,
        module: &ModuleFullPath,
        current_source_hash: &str,
        sources: &ModuleSources<'_>,
    ) -> CacheValidity {
        let guard = self.state.lock().unwrap_or_else(|e| e.into_inner());
        match guard.as_ref() {
            Some(cs) => cs.validate(module, current_source_hash, sources),
            None => CacheValidity::Stale,
        }
    }

    /// Record that `module` was restored from the cache under its validated
    /// `record`, without marking it recompiled.
    pub(crate) fn record_cache_hit(
        &self,
        module: &ModuleFullPath,
        source_hash: String,
        record: DependencyRecord,
    ) {
        let mut guard = self.state.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(cs) = guard.as_mut() {
            cs.record_cache_hit(module, source_hash, record);
        }
    }

    /// Write `module`'s manifest entry. Called by the cache writers once
    /// `record` has been built from settled state.
    pub(crate) fn record_compiled(
        &self,
        module: &ModuleFullPath,
        source_hash: String,
        record: DependencyRecord,
    ) {
        let mut guard = self.state.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(cs) = guard.as_mut() {
            cs.record_module(module, source_hash, record);
        }
    }

    /// Hold `entry` until its record settles; a later write of the same module
    /// supersedes it.
    pub(crate) fn defer_entry(&self, entry: DeferredEntry) {
        let mut guard = self.state.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(cs) = guard.as_mut() {
            cs.defer_entry(entry);
        }
    }

    pub(crate) fn take_deferred_entries(&self) -> Vec<DeferredEntry> {
        let mut guard = self.state.lock().unwrap_or_else(|e| e.into_inner());
        guard
            .as_mut()
            .map(CacheState::take_deferred_entries)
            .unwrap_or_default()
    }

    /// The source hash this session loaded for `module`.
    pub fn source_hash(&self, module: &ModuleFullPath) -> Option<String> {
        let guard = self.state.lock().unwrap_or_else(|e| e.into_inner());
        guard
            .as_ref()
            .and_then(|cs| cs.loaded_source(module))
            .map(|loaded| loaded.source_hash().to_string())
    }

    /// The source version this session loaded for `module`.
    pub(crate) fn loaded_source(&self, module: &ModuleFullPath) -> Option<LoadedSource> {
        let guard = self.state.lock().unwrap_or_else(|e| e.into_inner());
        guard
            .as_ref()
            .and_then(|cs| cs.loaded_source(module))
            .cloned()
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
        let mut guard = self
            .compiled_o_paths
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        if !guard.contains(&path) {
            guard.push(path);
        }
    }

    /// Record how `module`'s object pass ended: a stop stands until a later
    /// pass for the module succeeds.
    pub(crate) fn settle_object_pass(
        &self,
        module: &ModuleFullPath,
        outcome: Result<(), StoppedPass>,
    ) {
        let mut stopped = self
            .stopped_passes
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        match outcome {
            Ok(()) => {
                stopped.remove(module);
            }
            Err(stop) => {
                stopped.insert(module.clone(), stop);
            }
        }
    }

    /// The modules whose latest object pass stopped, with how it stopped.
    pub(crate) fn stopped_passes(&self) -> BTreeMap<ModuleFullPath, StoppedPass> {
        self.stopped_passes
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .clone()
    }

    /// Snapshot the collected `.o` paths for `--link`. Returns a clone.
    pub fn all_paths(&self) -> Vec<PathBuf> {
        self.compiled_o_paths
            .lock()
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
        assert!(
            cache.is_enabled(),
            "ObjectCache with dir + state must report enabled"
        );
    }

    #[test]
    fn new_with_none_dir_is_disabled() {
        let cache = ObjectCache::new(None, None);
        assert!(
            !cache.is_enabled(),
            "ObjectCache with no dir must report disabled"
        );
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
        assert_eq!(
            cache.source_hash(&m),
            None,
            "disabled cache must not retain source hashes"
        );
    }

    #[test]
    fn append_o_path_then_all_paths_returns_in_order() {
        let cache = ObjectCache::new(None, None);
        cache.append_o_path(PathBuf::from("/tmp/a.o"));
        cache.append_o_path(PathBuf::from("/tmp/b.o"));
        let paths = cache.all_paths();
        assert_eq!(
            paths,
            vec![PathBuf::from("/tmp/a.o"), PathBuf::from("/tmp/b.o")]
        );
    }

    // spec: design/int/int.md §7.7 — a completed publication leaves exactly
    // the emitted bytes at the object path and no temporary beside it.
    #[test]
    fn a_published_object_holds_its_bytes_alone_in_the_directory() {
        let dir = tempfile::tempdir().unwrap();
        let object_path = dir.path().join("lib.o");
        std::fs::write(&object_path, "the earlier generation's object").unwrap();

        publish_object(&object_path, b"the emitted object").unwrap();

        assert_eq!(std::fs::read(&object_path).unwrap(), b"the emitted object");
        let names: Vec<_> = std::fs::read_dir(dir.path())
            .unwrap()
            .map(|entry| entry.unwrap().file_name())
            .collect();
        assert_eq!(names, ["lib.o"]);
    }

    // ---------------------------------------------------------------------
    // S125 §4.3 — the cache is never ahead of the file (ACT-1102)
    // ---------------------------------------------------------------------

    /// A cache over `dir` holding a written `.meta` and `.o` for `m`.
    fn cache_with_generation(dir: &Path, m: &ModuleFullPath) -> ObjectCache {
        let cache = ObjectCache::new(Some(dir.to_path_buf()), Some(cache_state_for(dir)));
        cache.record_source_hash(m, "loaded".to_string());
        let table = crate::code::SessionSymbolTable::new_with_params(m.clone());
        assert_eq!(cache.write_meta(m, &table).unwrap(), MetaWrite::Written);
        let (_, object) = cranelisp_backend::cache::module_cache_path(dir, m);
        std::fs::write(object, b"object").unwrap();
        cache
    }

    // spec: design/int/s125-binary-clean.md §4.3 — a divergence retires the
    // module's `.o` and `.meta` and refuses every write until the file agrees.
    #[test]
    fn a_divergence_retires_the_generation_and_refuses_writes() {
        let tmp = tempfile::tempdir().unwrap();
        let m = ModuleFullPath::from("user");
        let cache = cache_with_generation(tmp.path(), &m);
        let (meta, object) = cranelisp_backend::cache::module_cache_path(tmp.path(), &m);

        cache.record_divergence(&m);

        assert_eq!(cache.agreement(&m), FileAgreement::Diverged);
        assert!(
            !meta.exists() && !object.exists(),
            "the generation is retired"
        );
        let table = crate::code::SessionSymbolTable::new_with_params(m.clone());
        assert_eq!(cache.write_meta(&m, &table).unwrap(), MetaWrite::Diverged);
        assert!(!meta.exists(), "no `.meta` is written while diverged");
        cache.record_compiled(&m, "loaded".to_string(), DependencyRecord::default());
        let guard = cache.state.lock().unwrap();
        let cs = guard.as_ref().unwrap();
        assert!(
            cs.manifest_entry(&m).is_none(),
            "no manifest entry is written while diverged"
        );
    }

    // spec: design/int/s125-binary-clean.md §4.3 — a read or written file
    // (the recorded source hash) makes the table agree again, and writes
    // resume; a cache hit agrees too. Control: an agreeing module writes.
    #[test]
    fn a_recorded_source_ends_the_divergence() {
        let tmp = tempfile::tempdir().unwrap();
        let m = ModuleFullPath::from("user");
        let cache = cache_with_generation(tmp.path(), &m);
        assert_eq!(cache.agreement(&m), FileAgreement::Agrees);

        cache.record_divergence(&m);
        cache.record_source_hash(&m, "written".to_string());
        assert_eq!(cache.agreement(&m), FileAgreement::Agrees);
        let table = crate::code::SessionSymbolTable::new_with_params(m.clone());
        assert_eq!(cache.write_meta(&m, &table).unwrap(), MetaWrite::Written);

        cache.record_divergence(&m);
        cache.record_cache_hit(&m, "restored".to_string(), DependencyRecord::default());
        assert_eq!(cache.agreement(&m), FileAgreement::Agrees);
    }

    #[test]
    fn validate_is_stale_when_disabled() {
        let tmp = tempfile::tempdir().unwrap();
        let cache = ObjectCache::new(None, None);
        let m = ModuleFullPath::from("user");
        assert_eq!(
            cache.validate(
                &m,
                "anyhash",
                &ModuleSources::new(tmp.path(), &[], &dashmap::DashMap::new(), &cache)
            ),
            CacheValidity::Stale,
            "disabled cache must always miss"
        );
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
        assert!(
            paths.contains(&dep_o),
            "cache-restored dep .o must be in the --link set, got {paths:?}"
        );
        assert!(paths.contains(&user_o));

        // A module that is both cache-restored AND later freshly recompiled
        // (or any double-append) must not double-list.
        cache.append_o_path(dep_o.clone());
        let after = cache.all_paths();
        assert_eq!(
            after.iter().filter(|p| **p == dep_o).count(),
            1,
            "append_o_path must dedup — a duplicated .o on the cc line risks \
             duplicate-symbol link errors; got {after:?}"
        );
        assert_eq!(
            after.len(),
            2,
            "exactly two distinct objects, got {after:?}"
        );
    }

    #[test]
    fn record_cache_hit_stores_source_hash_for_downstream() {
        let tmp = tempfile::tempdir().unwrap();
        let cs = cache_state_for(tmp.path());
        let cache = ObjectCache::new(Some(tmp.path().to_path_buf()), Some(cs));
        let m = ModuleFullPath::from("dep");
        cache.record_cache_hit(&m, "depHash".to_string(), DependencyRecord::default());
        assert_eq!(cache.source_hash(&m).as_deref(), Some("depHash"));
    }

    #[test]
    fn fresh_registration_supersedes_a_restored_version() {
        let tmp = tempfile::tempdir().unwrap();
        let cache = ObjectCache::new(
            Some(tmp.path().to_path_buf()),
            Some(cache_state_for(tmp.path())),
        );
        let m = ModuleFullPath::from("dep");
        cache.record_cache_hit(&m, "restored".to_string(), DependencyRecord::default());
        cache.record_source_hash(&m, "fresh".to_string());
        assert_eq!(
            cache.loaded_source(&m),
            Some(LoadedSource::Fresh {
                source_hash: "fresh".to_string()
            })
        );
    }

    // Validity seam (`design/int/int.md` §7.6; S122 CL-E). An importer `user`
    // is cached against dependency `dep` and the prelude; each case changes
    // what the loading handler would read now.
    mod validity_seam {
        use super::*;
        use cranelisp_backend::cache::manifest::{self, CacheManifest};
        use std::collections::HashMap;

        const USER_SOURCE: &str = "(defn main [] 1)";
        const DEP_SOURCE: &str = "(defn f [] 1)";
        const PRELUDE_SOURCE: &str = "(defn p [] 1)";

        struct Fixture {
            project: tempfile::TempDir,
            lib: tempfile::TempDir,
            cache_dir: tempfile::TempDir,
            /// The live tables of `dep` and the prelude, which assign no slot.
            tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
        }

        /// The derivation key of a member whose live table assigns no slot.
        fn key(source: &str) -> String {
            let table = crate::code::SessionSymbolTable::new_with_params(ModuleFullPath::from("m"));
            crate::cache::dependency_record::AuthoredSlotLayout::of(&table)
                .derivation_key(&manifest::hash_source(source))
        }

        impl Fixture {
            /// A project whose sources are those `user`'s entry recorded; the
            /// prelude lives in a lib dir.
            fn cached() -> Self {
                Self::recorded_as(key(DEP_SOURCE), key(PRELUDE_SOURCE))
            }

            /// A project whose `user` entry recorded `dep` and the prelude
            /// under `dep_key` and `prelude_key`.
            fn recorded_as(dep_key: String, prelude_key: String) -> Self {
                let fixture = Fixture {
                    project: tempfile::tempdir().unwrap(),
                    lib: tempfile::tempdir().unwrap(),
                    cache_dir: tempfile::tempdir().unwrap(),
                    tables: dashmap::DashMap::new(),
                };
                for module in ["dep", "prelude"] {
                    let module = ModuleFullPath::from(module);
                    fixture.tables.insert(
                        module.clone(),
                        crate::code::SessionSymbolTable::new_with_params(module),
                    );
                }
                fixture.write("dep.cl", DEP_SOURCE);
                std::fs::write(fixture.lib.path().join("prelude.cl"), PRELUDE_SOURCE).unwrap();
                let mut entry = CacheManifest::new_for_host();
                entry.upsert_module(
                    &ModuleFullPath::from("user"),
                    manifest::hash_source(USER_SOURCE),
                    HashMap::from([
                        ("dep".to_string(), dep_key),
                        ("prelude".to_string(), prelude_key),
                    ]),
                );
                manifest::write_manifest(fixture.cache_dir.path(), &entry).unwrap();
                fixture
            }

            fn write(&self, relative: &str, source: &str) {
                std::fs::write(self.project.path().join(relative), source).unwrap();
            }

            fn validate_user(&self) -> CacheValidity {
                let cache = ObjectCache::new(
                    Some(self.cache_dir.path().to_path_buf()),
                    Some(cache_state_for(self.cache_dir.path())),
                );
                let lib_dirs = [self.lib.path().to_path_buf()];
                cache.validate(
                    &ModuleFullPath::from("user"),
                    &manifest::hash_source(USER_SOURCE),
                    &ModuleSources::new(self.project.path(), &lib_dirs, &self.tables, &cache),
                )
            }
        }

        #[test]
        fn unchanged_recorded_members_hit_with_their_record() {
            let CacheValidity::Valid { record } = Fixture::cached().validate_user() else {
                panic!("unchanged sources must hit");
            };
            let members: Vec<&str> = record.members().map(|(m, _)| m.as_ref()).collect();
            assert_eq!(members, ["dep", "prelude"]);
        }

        // spec: design/int/int.md §7.6.3 — a record written before keys
        // carried the slot layout (S123 and earlier: bare source hashes) is a
        // miss even with every source unchanged.
        #[test]
        fn a_record_of_bare_source_hashes_is_stale() {
            let fixture = Fixture::recorded_as(
                manifest::hash_source(DEP_SOURCE),
                manifest::hash_source(PRELUDE_SOURCE),
            );
            assert_eq!(fixture.validate_user(), CacheValidity::Stale);
        }

        #[test]
        fn changed_recorded_member_is_stale() {
            let fixture = Fixture::cached();
            fixture.write("dep.cl", "(defn f [] 2)");
            assert_eq!(fixture.validate_user(), CacheValidity::Stale);
        }

        #[test]
        fn unresolvable_recorded_member_is_stale() {
            let fixture = Fixture::cached();
            std::fs::remove_file(fixture.project.path().join("dep.cl")).unwrap();
            assert_eq!(fixture.validate_user(), CacheValidity::Stale);
        }

        #[test]
        fn changed_prelude_in_lib_dir_is_stale() {
            let fixture = Fixture::cached();
            std::fs::write(fixture.lib.path().join("prelude.cl"), "(defn p [] 2)").unwrap();
            assert_eq!(fixture.validate_user(), CacheValidity::Stale);
        }

        #[test]
        fn project_prelude_shadowing_the_lib_prelude_is_stale() {
            let fixture = Fixture::cached();
            // `resolve_prelude` prefers the project root, so the loading
            // handler would now read this file instead.
            fixture.write("prelude.cl", "(defn p [] 2)");
            assert_eq!(fixture.validate_user(), CacheValidity::Stale);
        }
    }
}
