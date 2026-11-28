// session_v4::nice_worker — nice-worker object-codegen subsystem (S87 §2.1).
//
// The low-priority thread loop + the single-module `.o`/`.meta.json` writer.
// One concern (cache-write side codegen), runs on its own threads, touches
// only `&SharedState`. The `compile_module_object` god-function is split into
// named phase-helpers (S87 §3.3); the orchestrator preserves every early
// `return` and the load-bearing ordering. Moved verbatim from `session_v4.rs`
// (S87 §2.1 / §3.3).

use std::path::Path;
#[cfg(test)]
use std::sync::Arc;

use cranelisp_types::ModuleFullPath;

use super::SharedState;
use crate::cache::dependency_record::{
    Covered, CoveredBatch, ModuleEdges, UnpublishedPrelude, record_manifest_entry,
};
use crate::cache::{PassStage, StoppedPass};
use crate::scheduler::ObjectHold;

// ---------------------------------------------------------------------------
// Nice worker spawning + loop (Step 10)
// ---------------------------------------------------------------------------

/// Spawn nice (low-priority) worker threads inside a `std::thread::scope`.
///
/// Test-only helper kept for `nice_worker_lifecycle_spawn_and_shutdown` in
/// `src/scheduler.rs` tests. Production code uses the persistent
/// `nice_worker_handles` pool spawned in `CompilerSession::new` (Sprint 46).
/// `cfg(test)` gates this so `thread::scope` does not appear in any
/// non-test build per `design/int/persistent-workers.md` §11 acceptance
/// criterion 2.
///
/// # Panics
///
/// Panics if the OS fails to spawn a thread. Tests rely on this invariant.
#[cfg(test)]
pub fn spawn_nice_workers<'scope, 'env>(
    scope: &'scope std::thread::Scope<'scope, 'env>,
    shared: &'env Arc<SharedState>,
    n: usize,
) {
    for i in 0..n {
        let worker_shared = Arc::clone(shared);
        std::thread::Builder::new()
            .name(format!("nice-worker-{}", i))
            .spawn_scoped(scope, move || {
                nice_worker_loop(&worker_shared);
            })
            .expect("failed to spawn nice worker thread");
    }
}

/// Main loop for nice (low-priority) worker threads.
///
/// Runs at reduced OS scheduling priority. Claims TypecheckDone modules
/// from the scheduler, compiles them to `.o` files via Cranelift
/// ObjectModule, writes the `.o` to the cache directory, and appends
/// the path to the `ObjectCache` facade (`shared.cache.append_o_path`)
/// for the linker.
///
/// When caching is disabled (`shared.cache.cache_dir()` is None) or no
/// program is available for a module, the worker skips
/// `.o` compilation and just marks the module as object-complete.
///
/// The loop parks on `scheduler.take_object_codegen()` (condvar-based)
/// when no work is available, and exits on shutdown.
pub(crate) fn nice_worker_loop(shared: &SharedState) {
    // Set below-normal OS scheduling priority (best-effort).
    crate::thread_util::set_nice_priority();

    loop {
        // Check for priority promotion (hot flush before --link).
        let promoted = shared
            .promote_nice_workers
            .load(std::sync::atomic::Ordering::Relaxed);
        if promoted {
            crate::thread_util::set_normal_priority();
        }

        // Object codegen FIRST (the correctness path), index work in the slack
        // (S91 §25.5 / R17 — object codegen first, index warm-up yields to it).
        // Non-blocking claim so the loop can fall through to index work when no
        // object work is pending, rather than parking forever.
        if let Some(module) = shared.scheduler.try_take_object_codegen() {
            // Attempt .o compilation if caching is enabled. Sprint 67 Cluster B
            // sub-fire 3: cache dir via ObjectCache facade.
            let outcome = match shared.cache.cache_dir() {
                Some(cache_dir) => compile_module_object(shared, &module, &cache_dir),
                None => PassOutcome::Settled,
            };
            // A held pass reports no completion (`design/int/int.md` §7.6.4).
            if outcome == PassOutcome::Settled {
                shared.scheduler.notify_object_codegen_complete(&module);
            }
            continue;
        }

        // No object work pending. S91 — the index burn-down (R18:
        // abandon-on-flush). A PROMOTED nice worker (pre-`--link` hot flush) is
        // object-codegen-scoped: it does NOT drain index work — the link needs
        // no index, and the index worklist yields entirely (the flush-time face
        // of R17's yield-to-codegen). It parks (re-checking object work) instead.
        if !promoted {
            // R18 abandon-on-shutdown: check the shutdown flag BETWEEN
            // `IndexModule` tasks (here, before claiming the next one) and exit
            // promptly — never "finish the whole burn-down first". A task
            // already claimed runs to completion (atomic `.meta` ⇒ no corrupt
            // file even if the next task is abandoned).
            if shared.scheduler.is_shutdown() {
                break;
            }
            if crate::session_v4::index_worker::run_one_index_task(shared) {
                continue;
            }
        }

        // No object work AND (promoted OR no index work) — park until woken by a
        // new TypecheckDone module, an index-worklist arm, or shutdown.
        if !shared.scheduler.park_nice_worker() {
            // Observability: publish this nice-worker thread's scheduler-trace
            // ring buffer so the main thread's `flush_to_stderr` can merge it
            // into the dump (design/int/observability.md §7). No-op when
            // disabled.
            crate::observability::publish_thread_buffer();
            // GOT trace events (FIXME 0099) — nice workers also emit GOT events
            // (LinkerWrite during cache-hit load).
            crate::got_trace::publish_thread_buffer();
            return; // Shutdown signaled.
        }
    }

    // Promoted-path shutdown break exits here (after the `break` above).
    crate::observability::publish_thread_buffer();
    crate::got_trace::publish_thread_buffer();
}

/// Compile a single module to `.o` and `.meta.json` files in the cache directory.
///
/// Sprint 58 Step 5b: reads `SymbolTable` directly via the shared
/// `defined_symbols()` predicate (Decision 22).
///
/// Errors are logged to stderr and do not halt the worker — the module is still
/// marked object-complete so the scheduler lifecycle proceeds. A pass that
/// stops is recorded with its cause for `--link`, and a later successful pass
/// for the module clears the record (`design/int/int.md` §7.7).
fn compile_module_object(
    shared: &SharedState,
    module: &ModuleFullPath,
    cache_dir: &Path,
) -> PassOutcome {
    run_object_pass(shared, module, cache_dir, crate::cache::publish_object)
}

/// Writes a module's emitted object bytes to its object path.
type PublishObject = fn(&Path, &[u8]) -> std::io::Result<()>;

/// Whether an object pass settled, or went back on the object queue held on
/// an unpublished member (`design/int/int.md` §7.6.4, *Deferral*).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PassOutcome {
    Settled,
    Held,
}

/// How an object pass ended short of its object.
#[derive(Debug, PartialEq, Eq)]
enum PassEnd {
    Stopped(StoppedPass),
    Held,
}

impl From<StoppedPass> for PassEnd {
    fn from(stop: StoppedPass) -> Self {
        PassEnd::Stopped(stop)
    }
}

fn run_object_pass(
    shared: &SharedState,
    module: &ModuleFullPath,
    cache_dir: &Path,
    publish: PublishObject,
) -> PassOutcome {
    let settled = match object_pass(shared, module, cache_dir, publish) {
        Ok(()) => Ok(()),
        Err(PassEnd::Stopped(stop)) => Err(stop),
        Err(PassEnd::Held) => return PassOutcome::Held,
    };
    shared.cache.settle_object_pass(module, settled);
    PassOutcome::Settled
}

/// The stop of an object pass whose covered member had not published when
/// objects came to be awaited (`design/int/int.md` §7.6.4, *No deadlock*).
pub(crate) fn unpublished_member_stop(member: &ModuleFullPath) -> StoppedPass {
    StoppedPass {
        stage: PassStage::Object,
        cause: format!("covered module '{member}' had not published when objects were awaited"),
    }
}

/// S87 §3.3: the pass's phases in their load-bearing order — the `.meta.json`
/// is DECOUPLED from `.o` output and persists whenever the module
/// type-checked.
fn object_pass(
    shared: &SharedState,
    module: &ModuleFullPath,
    cache_dir: &Path,
    publish: PublishObject,
) -> Result<(), PassEnd> {
    use cranelisp_backend::cache;

    // Resolve cache paths up front — `.meta.json` persistence is DECOUPLED from
    // `.o` output (S84 Phase 4B, FIXME 0387). A module that type-checked but
    // codegens nothing (a generic-only module whose sole defn is a slot-less
    // `Polymorphic` template — excluded from `defined_symbols()` since Phase 4B)
    // still persists its scheme/symbol-table snapshot so a downstream module can
    // monomorphise it on a later cold-load.
    let (meta_path, o_path) = cache::module_cache_path(cache_dir, module);

    // Phase 1: write `.meta.json` (typecheck-driven; ensures the parent dir;
    // retires the earlier `.o`). A failure stops the whole pass. A module
    // whose table is ahead of its file writes nothing: its files were
    // retired, and no entry is recorded (`design/int/s125-binary-clean.md`
    // §4.3).
    if write_module_meta(shared, module, &meta_path)? == crate::cache::MetaWrite::Diverged {
        return Ok(());
    }

    // Phase 2: enumerate codegen-compilable symbols. A generic-only,
    // types-only or imports-only module emits no `.o` but is still recorded in
    // the manifest, so the next session restores it rather than rewriting its
    // `.meta.json` (FIXME 0387); the cache-hit loader tolerates the absent `.o`.
    let targets = enumerate_codegen_targets(shared, module);
    if targets.is_empty() {
        record_loaded_module(shared, module);
        return Ok(());
    }

    // Phase 3: build + emit the `.o` bytes.
    let obj_bytes = emit_object(shared, module, targets)?;

    // Phase 4: write the `.o` + record in manifest + append for the linker.
    Ok(write_object_and_record(
        shared, module, &o_path, &obj_bytes, publish,
    )?)
}

/// Phase 1 (S87 §3.3): write `.meta.json` for cache-hit restoration via the
/// unified `cache::write_meta` API (Sprint 58 Step 5b / Decision 33+34). This
/// is TYPECHECK-DRIVEN: it persists whenever the module type-checked,
/// independent of whether codegen produces an `.o` (FIXME 0387). The .meta.json
/// IS a serialised SymbolTable; `write_meta` stamps `schema_version =
/// CACHE_SCHEMA_VERSION` on the cloned table before serialising. Per Decision
/// 33, structural decls (imports/exports/platforms/submodules) are fields on
/// the SymbolTable itself, so the serialised table carries the user-authored
/// structural specifications inline (cache-hit derives transitive deps from
/// `imports` directly).
///
/// A meta-dir create failure or a failed `.meta` write stops the pass: an
/// `.o` or manifest entry written after it would pair with whichever `.meta`
/// the failed write left (`design/int/int.md` §7.7).
fn write_module_meta(
    shared: &SharedState,
    module: &ModuleFullPath,
    meta_path: &Path,
) -> Result<crate::cache::MetaWrite, StoppedPass> {
    // Ensure parent directory exists (used by both the `.meta.json` and `.o`
    // writes below).
    if let Some(parent) = meta_path.parent()
        && let Err(e) = std::fs::create_dir_all(parent)
    {
        let cause = format!("cannot create cache dir '{}': {e}", parent.display());
        eprintln!("nice-worker: {cause}");
        return Err(StoppedPass {
            stage: PassStage::Metadata,
            cause,
        });
    }

    let symbol_table = shared
        .symbol_tables
        .get(module)
        .map(|guard| guard.clone())
        .unwrap_or_else(|| crate::code::SessionSymbolTable::new_with_params(module.clone()));

    shared.cache.write_meta(module, &symbol_table).map_err(|e| {
        eprintln!(
            "nice-worker: .meta.json write failed for {}: {}",
            module,
            e.message()
        );
        StoppedPass {
            stage: PassStage::Metadata,
            cause: e.message().to_string(),
        }
    })
}

/// Phase 2 (S87 §3.3): enumerate codegen-compilable symbols via the shared
/// predicate (Decision 22). Empty result → no compilable defns (types-only,
/// imports-only, OR a generic-only `Polymorphic` module post-Phase-4B) → no
/// `.o`, which is the correct new state (FIXME 0387). The `.meta.json` above
/// has already persisted; we just emit no object.
fn enumerate_codegen_targets(
    shared: &SharedState,
    module: &ModuleFullPath,
) -> Vec<cranelisp_types::CallableTarget> {
    shared
        .symbol_tables
        .get(module)
        .map(|t| t.codegen_targets().map(|(target, _)| target).collect())
        .unwrap_or_default()
}

/// Write the manifest entry of a module this session loaded, keyed by the
/// source version it loaded and its live table's dependency closure
/// (`design/int/int.md` §7.6). A module with no stashed source hash gets none.
fn record_loaded_module(shared: &SharedState, module: &ModuleFullPath) {
    let Some(source_hash) = shared.cache.source_hash(module) else {
        return;
    };
    let Some(edges) = shared.symbol_tables.get(module).map(|table| {
        let fallback = shared.prelude_fallback.get(module).is_some_and(|bit| *bit);
        ModuleEdges::of_table(module, &table, fallback)
    }) else {
        return;
    };
    record_manifest_entry(shared, module, source_hash, edges);
}

/// A stop in the object's codegen. Logged only under
/// `CRANELISP_CODEGEN_TRACE`: the in-memory compilation may have succeeded,
/// so only `--link` reads it, through the record.
fn codegen_stop(module: &ModuleFullPath, cause: String) -> StoppedPass {
    if std::env::var("CRANELISP_CODEGEN_TRACE").is_ok() {
        eprintln!("nice-worker: {cause} for {module}");
    }
    StoppedPass {
        stage: PassStage::Object,
        cause,
    }
}

/// Phase 3b (S87 §3.3): build the ObjectModule with PIC ISA and emit the `.o`
/// bytes via the unified `compile_to_module` path. Intrinsics are declared on
/// the module internally; cross-module refs resolve from `symbol_tables`.
fn emit_object(
    shared: &SharedState,
    module: &ModuleFullPath,
    targets: Vec<cranelisp_types::CallableTarget>,
) -> Result<Vec<u8>, PassEnd> {
    let isa = cranelisp_backend::build_isa(true)
        .map_err(|e| codegen_stop(module, format!("ISA build failed: {}", e.message())))?;
    let obj_builder = cranelisp_backend::cranelift_object::ObjectBuilder::new(
        isa,
        format!("cranelisp_{}", module),
        cranelisp_backend::cranelift_module::default_libcall_names(),
    )
    .map_err(|e| codegen_stop(module, format!("ObjectBuilder failed: {e}")))?;
    let mut obj_module = cranelisp_backend::cranelift_object::ObjectModule::new(obj_builder);
    let batch = object_batch(
        module,
        targets,
        &shared.symbol_tables,
        &shared.prelude_fallback,
        &shared.scheduler,
    )?;

    cranelisp_backend::compile_to_module(
        module.clone(),
        &batch.codegen_targets(),
        &shared.symbol_tables,
        &mut obj_module,
        // FIXME 0325: nice-worker `.o` codegen is always batch (cache-write
        // side) — never consumed by introspection, so skip CLIF rendering.
        false,
    )
    .map_err(|e| codegen_stop(module, format!(".o compilation failed: {e}")))?;
    Ok(obj_module
        .finish()
        .emit()
        .map_err(|e| codegen_stop(module, format!(".o emit failed: {e}")))?)
}

/// `module`'s object targets, each paired with the covered set of its module
/// of origin (`design/int/int.md` §7.6.4, *The object pass waits* and *The
/// form's home*). Every member, the prelude included, is read through the
/// published predicate commit planning uses; an unpublished member holds the
/// pass on it.
fn object_batch(
    module: &ModuleFullPath,
    targets: Vec<cranelisp_types::CallableTarget>,
    tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    prelude_fallback: &cranelisp_typecheck::PreludeFallback,
    scheduler: &crate::scheduler::CompileScheduler,
) -> Result<CoveredBatch, PassEnd> {
    let member = match CoveredBatch::derive(
        module,
        targets,
        tables,
        prelude_fallback,
        UnpublishedPrelude::Answer,
        |member| scheduler.has_published(member),
    ) {
        Covered::Covered(batch) => return Ok(batch),
        Covered::Unpublished(member) => member,
    };
    // A published member the walk answered has no table, and will not get one.
    if !tables.contains_key(&member) && scheduler.has_published(&member) {
        return Err(codegen_stop(
            module,
            format!("covered module '{member}' has no symbol table"),
        )
        .into());
    }
    match scheduler.hold_object_pass(module, &member) {
        ObjectHold::Held => Err(PassEnd::Held),
        ObjectHold::Stop => Err(unpublished_member_stop(&member).into()),
    }
}

/// Phase 4 (S87 §3.3): publish the `.o` file, then record the module in the
/// manifest for cache-hit detection on the next session and append the `.o`
/// path for the linker. A failed publication is logged and stops the pass
/// with no entry recorded.
fn write_object_and_record(
    shared: &SharedState,
    module: &ModuleFullPath,
    o_path: &Path,
    obj_bytes: &[u8],
    publish: PublishObject,
) -> Result<(), StoppedPass> {
    // The parent dir was ensured for the `.meta.json` write, which shares it.
    if let Err(e) = publish(o_path, obj_bytes) {
        let cause = format!("cannot write '{}': {e}", o_path.display());
        eprintln!("nice-worker: {cause}");
        return Err(StoppedPass {
            stage: PassStage::Object,
            cause,
        });
    }

    record_loaded_module(shared, module);
    shared.cache.append_o_path(o_path.to_path_buf());
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use cranelisp_types::{CodegenBehaviour, ModuleFullPath};

    use crate::cache::dependency_record::ModuleSources;
    use crate::cache::{PassStage, StoredObject};
    use crate::session_setup::CacheValidity;
    use crate::session_v4::{CompilerSession, RunMode, SessionSettings};

    /// What one cached launch of `lib` left: its entry's validity against the
    /// source it compiled, and what a restore would load.
    #[derive(Debug, PartialEq, Eq)]
    struct Generation {
        entry_valid: bool,
        object: StoredObject,
    }

    /// A cached `--run` session over `lib` whose object work has drained.
    fn compiled_session(root: &Path, source: &str) -> CompilerSession {
        std::fs::write(root.join("lib.cl"), source).unwrap();
        let mut s = CompilerSession::new(
            SessionSettings {
                no_color: true,
                no_cache: false,
                codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
                priority_workers: 1,
                nice_workers: 1,
                run_mode: RunMode::Run,
            },
            root.to_path_buf(),
            "lib",
        )
        .expect("test session bootstrap");
        s.set_lib_dirs(Vec::new());
        s.register_module("lib").unwrap();
        s.wait_object_complete().unwrap();
        s
    }

    fn launch(root: &Path, source: &str) -> Generation {
        let mut s = compiled_session(root, source);
        let lib = ModuleFullPath::from("lib");
        let shared = &s.shared;
        let sources = ModuleSources::new(root, &[], &shared.symbol_tables, &shared.cache);
        let validity = shared.cache.validate(
            &lib,
            &cranelisp_backend::cache::manifest::hash_source(source),
            &sources,
        );
        let cache_dir = shared.cache.cache_dir().expect("cache enabled");
        let cached = cranelisp_backend::cache::try_load_cached_module(&cache_dir, &lib)
            .unwrap()
            .expect("the launch persists `lib`");
        let generation = Generation {
            entry_valid: matches!(validity, CacheValidity::Valid { .. }),
            object: StoredObject::of(&cached),
        };
        s.shutdown();
        generation
    }

    fn stopped_publication(object_path: &Path, bytes: &[u8]) -> std::io::Result<()> {
        crate::cache::publish_object_with(object_path, |file| {
            std::io::Write::write_all(file, &bytes[..bytes.len() / 2])?;
            Err(std::io::Error::other("the write stops part-way"))
        })
    }

    /// The stage at which each module's latest object pass stopped.
    fn stopped_stages(s: &CompilerSession) -> Vec<(ModuleFullPath, PassStage)> {
        s.shared
            .cache
            .stopped_passes()
            .into_iter()
            .map(|(module, stop)| (module, stop.stage))
            .collect()
    }

    // spec: design/int/int.md §7.7 — a pass stopped at the `.meta` write
    // records the module, and a later successful pass clears the record.
    #[test]
    fn a_pass_stopped_at_its_metadata_stands_until_a_later_pass_succeeds() {
        let root = tempfile::tempdir().unwrap();
        let mut s = compiled_session(root.path(), "(defn g [] 41)\n");
        let lib = ModuleFullPath::from("lib");
        let cache_dir = s.shared.cache.cache_dir().expect("cache enabled");
        assert_eq!(stopped_stages(&s), [], "a clean pass leaves no record");
        let object_path = cranelisp_backend::cache::module_cache_path(&cache_dir, &lib).1;
        std::fs::remove_file(&object_path).unwrap();
        std::fs::create_dir(&object_path).unwrap();

        super::run_object_pass(&s.shared, &lib, &cache_dir, crate::cache::publish_object);
        assert_eq!(stopped_stages(&s), [(lib.clone(), PassStage::Metadata)]);

        std::fs::remove_dir(&object_path).unwrap();
        super::run_object_pass(&s.shared, &lib, &cache_dir, crate::cache::publish_object);
        assert_eq!(stopped_stages(&s), []);
        s.shutdown();
    }

    // spec: design/int/int.md §7.7 — a pass stopped at the object write
    // records the module with its cause, and a later successful pass clears
    // the record.
    #[test]
    fn a_pass_stopped_at_its_object_stands_until_a_later_pass_succeeds() {
        let root = tempfile::tempdir().unwrap();
        let mut s = compiled_session(root.path(), "(defn g [] 41)\n");
        let lib = ModuleFullPath::from("lib");
        let cache_dir = s.shared.cache.cache_dir().expect("cache enabled");

        super::run_object_pass(&s.shared, &lib, &cache_dir, stopped_publication);
        assert_eq!(stopped_stages(&s), [(lib.clone(), PassStage::Object)]);
        let stop = &s.shared.cache.stopped_passes()[&lib];
        assert!(stop.cause.contains("the write stops part-way"), "{stop}");

        super::run_object_pass(&s.shared, &lib, &cache_dir, crate::cache::publish_object);
        assert_eq!(stopped_stages(&s), []);
        s.shutdown();
    }

    // spec: design/int/int.md §7.7 — an object publication that stops after
    // writing part of the bytes leaves no file at the object path, nor its
    // temporary, so the next restore is a miss rather than a truncated load.
    #[test]
    fn a_stopped_object_publication_leaves_a_miss() {
        let root = tempfile::tempdir().unwrap();
        let mut s = compiled_session(root.path(), "(defn g [] 41)\n");
        let lib = ModuleFullPath::from("lib");
        let cache_dir = s.shared.cache.cache_dir().expect("cache enabled");
        let restored = || {
            let cached = cranelisp_backend::cache::try_load_cached_module(&cache_dir, &lib)
                .unwrap()
                .expect("the pass persists `lib`");
            StoredObject::of(&cached)
        };
        assert_eq!(restored(), StoredObject::Load);

        super::run_object_pass(&s.shared, &lib, &cache_dir, stopped_publication);

        let leftovers: Vec<_> = std::fs::read_dir(&cache_dir)
            .unwrap()
            .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
            .filter(|name| name.starts_with("lib.o"))
            .collect();
        assert_eq!(leftovers, Vec::<String>::new());
        assert_eq!(restored(), StoredObject::Missing);
        s.shutdown();
    }

    // spec: design/int/int.md §7.7 — a successful object pass leaves its new
    // `.o` and records its entry; a later pass whose table has no codegen
    // targets leaves no `.o`, so the restore registers the module with nothing
    // to load instead of the earlier generation's object.
    #[test]
    fn an_object_pass_with_no_codegen_targets_retires_the_earlier_object() {
        let root = tempfile::tempdir().unwrap();
        assert_eq!(
            launch(root.path(), "(defn g [] 41)\n"),
            Generation {
                entry_valid: true,
                object: StoredObject::Load,
            }
        );
        assert_eq!(
            launch(root.path(), "(defn id [x] x)\n"),
            Generation {
                entry_valid: true,
                object: StoredObject::NothingToLoad,
            }
        );
    }

    // spec: design/int/int.md §7.6.4 *Pairing* — the object pass derives the
    // sets commit planning derives and pairs each target with its module of
    // origin's set: `m/run`'s instance in `main` with `m`'s.
    #[test]
    fn the_object_pass_pairs_an_instance_with_its_templates_set() {
        let root = tempfile::tempdir().unwrap();
        let mut s = CompilerSession::new(
            SessionSettings {
                no_color: true,
                no_cache: true,
                codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
                priority_workers: 1,
                nice_workers: 0,
                run_mode: RunMode::Run,
            },
            root.path().to_path_buf(),
            "main",
        )
        .unwrap();
        s.set_lib_dirs(Vec::new());
        let sources = [
            (
                "x",
                "(import [primitives [Int add-i64]])\n(defn f [:Int n] (add-i64 n 1))\n",
            ),
            (
                "m",
                "(import [primitives [Int]])\n(defn run [h] (trace (h 1)))\n",
            ),
            ("main", "(defn g [] (m/run x/f))\n"),
        ];
        for (module, source) in sources {
            let path = root.path().join(format!("{module}.cl"));
            s.register_module_with_source(module, source, &path)
                .unwrap();
        }
        let main = ModuleFullPath::from("main");
        let shared = &s.shared;
        let batch = super::object_batch(
            &main,
            super::enumerate_codegen_targets(shared, &main),
            &shared.symbol_tables,
            &shared.prelude_fallback,
            &shared.scheduler,
        )
        .unwrap();
        let set = |modules: &[&str]| -> std::collections::BTreeSet<ModuleFullPath> {
            modules.iter().copied().map(ModuleFullPath::from).collect()
        };
        let m_set = set(&["m", "primitives"]);
        let main_set = set(&["m", "main", "primitives", "x"]);
        assert_eq!(batch.set_of(&ModuleFullPath::from("m")), Some(&m_set));
        assert_eq!(batch.set_of(&main), Some(&main_set));
        let table = shared.symbol_tables.get(&main).unwrap();
        let mut instances = 0;
        for (target, paired) in batch.paired() {
            let is_instance = table
                .callable_target(target)
                .and_then(|arm| arm.template_module())
                .is_some();
            instances += usize::from(is_instance);
            let expected = if is_instance { &m_set } else { &main_set };
            assert_eq!(paired, expected, "{target:?}");
        }
        assert_eq!(instances, 1, "main holds `m/run`'s instance");
        drop(table);
        s.shutdown();
    }

    /// The modules of ACT-1087's fixture: `prelude` re-exports `m`, whose
    /// declared child `m.c` takes the implicit prelude import; `p` is the
    /// module the prelude re-exports once its Pass 0 finishes.
    mod prelude_child {
        use std::collections::BTreeSet;

        use cranelisp_types::{ExportSpec, ImportNames, ModuleFullPath, Span};

        use crate::code::SessionSymbolTable;
        use crate::scheduler::{CompileScheduler, HeldObjectPass, ObjectHold};

        use super::super::{PassEnd, object_batch};

        fn m(path: &str) -> ModuleFullPath {
            ModuleFullPath::from(path)
        }

        fn reexport(target: &str) -> ExportSpec {
            ExportSpec {
                module_path: m(target),
                alias: None,
                names: ImportNames::Glob,
                span: Span::SYNTHETIC,
            }
        }

        /// The tables as they stand while the prelude is blocked in Pass 0
        /// after recording its `export` of `m`.
        fn in_flight_tables() -> dashmap::DashMap<ModuleFullPath, SessionSymbolTable> {
            let tables = dashmap::DashMap::new();
            for module in ["m", "m.c", "p", "primitives"] {
                tables.insert(m(module), SessionSymbolTable::new_with_params(m(module)));
            }
            let mut prelude = SessionSymbolTable::new_with_params(m("prelude"));
            prelude.exports = vec![reexport("m")];
            tables.insert(m("prelude"), prelude);
            tables
        }

        /// `m.c` typechecked, its object pass claimed, the prelude still in
        /// flight.
        /// The covered set `m.c`'s object pass derives for `m.c`'s own
        /// bodies, or how the pass ended.
        fn object_set(
            tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
            fallback: &cranelisp_typecheck::PreludeFallback,
            sched: &CompileScheduler,
        ) -> Result<BTreeSet<ModuleFullPath>, PassEnd> {
            object_batch(&m("m.c"), Vec::new(), tables, fallback, sched)
                .map(|batch| batch.set_of(&m("m.c")).cloned().unwrap())
        }

        fn scheduler() -> CompileScheduler {
            let sched = CompileScheduler::new();
            sched.register_module(m("prelude"), std::sync::Arc::from(Vec::new()), true);
            sched.register_module(m("m.c"), std::sync::Arc::from(Vec::new()), false);
            sched.notify_typecheck_done(&m("m.c"));
            assert_eq!(sched.try_take_object_codegen(), Some(m("m.c")));
            sched
        }

        // spec: design/int/int.md §7.6.4 *The object pass waits* — a child of
        // a prelude dependency, reached before the prelude publishes, holds
        // its object pass; once the prelude publishes, the object's set holds
        // the module the prelude re-exports.
        #[test]
        fn a_child_built_before_the_prelude_publishes_covers_its_reexport() {
            let tables = in_flight_tables();
            let fallback = cranelisp_typecheck::PreludeFallback::default();
            fallback.insert(m("m.c"), true);
            let sched = scheduler();
            assert_eq!(object_set(&tables, &fallback, &sched), Err(PassEnd::Held));

            tables
                .get_mut(&m("prelude"))
                .unwrap()
                .exports
                .push(reexport("p"));
            sched.notify_typecheck_done(&m("prelude"));
            let claimed: BTreeSet<_> =
                std::iter::from_fn(|| sched.try_take_object_codegen()).collect();
            assert!(claimed.contains(&m("m.c")), "{claimed:?}");
            assert_eq!(
                object_set(&tables, &fallback, &sched),
                Ok(["m", "m.c", "p", "prelude", "primitives"].map(m).into())
            );
        }

        // spec: design/int/int.md §7.6.4 *No deadlock* — a pass that meets an
        // unpublished member while objects are awaited stops, naming it.
        #[test]
        fn a_pass_reaching_an_unpublished_prelude_while_objects_are_awaited_stops() {
            let tables = in_flight_tables();
            let fallback = cranelisp_typecheck::PreludeFallback::default();
            fallback.insert(m("m.c"), true);
            let sched = scheduler();
            assert_eq!(sched.begin_object_wait(), Vec::<HeldObjectPass>::new());
            let Err(PassEnd::Stopped(stop)) = object_set(&tables, &fallback, &sched) else {
                panic!("the pass must stop while objects are awaited");
            };
            assert!(stop.cause.contains("'prelude'"), "{stop}");
            assert_eq!(
                sched.hold_object_pass(&m("m.c"), &m("prelude")),
                ObjectHold::Stop
            );
        }
    }
}
