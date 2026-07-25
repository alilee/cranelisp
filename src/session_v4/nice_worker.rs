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
            if let Some(cache_dir) = shared.cache.cache_dir() {
                compile_module_object(shared, &module, &cache_dir);
            }
            // Notify scheduler that object codegen is done for this module.
            shared.scheduler.notify_object_codegen_complete(&module);
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
/// `defined_symbols()` predicate (Decision 22). The transitional
/// `codegen_programs` stash is gone — the backend never read from it, and
/// the "had compilable defns" presence signal collapses to "did
/// `defined_symbols()` return anything".
///
/// Errors are logged to stderr and do not halt the worker — the module is still
/// marked object-complete so the scheduler lifecycle proceeds.
///
/// S87 §3.3: decomposed into phase-helpers (`write_module_meta`,
/// `enumerate_codegen_names`, `record_empty_codegen`, `emit_object`,
/// `write_object_and_record`). The orchestrator preserves every early `return`
/// and the load-bearing ordering (.meta.json is DECOUPLED from `.o` output —
/// persists whenever the module type-checked).
fn compile_module_object(shared: &SharedState, module: &ModuleFullPath, cache_dir: &Path) {
    use cranelisp_backend::cache;

    // S101 cache-write poisoning (repl/spec.md §18.8; design/int/
    // session-transaction.md §8.3): a module holding a BROKEN symbol at write
    // time persists NOTHING — a cache snapshot would capture trap-stub GOT
    // state as the module's compiled truth, letting a restart serve stale
    // code for a definition whose source no longer typechecks. Skipping is
    // cheap (the source hash has diverged anyway) and self-heals: the first
    // fully-green turn re-enqueues (`mark_object_stale`) and persists
    // normally. The caller still marks the module object-complete, so
    // `wait_object_complete` never hangs on a poisoned module.
    if shared.broken.iter().any(|r| r.key().module == *module) {
        return;
    }

    // Resolve cache paths up front — `.meta.json` persistence is DECOUPLED from
    // `.o` output (S84 Phase 4B, FIXME 0387). A module that type-checked but
    // codegens nothing (a generic-only module whose sole defn is a slot-less
    // `Polymorphic` template — excluded from `defined_symbols()` since Phase 4B)
    // still persists its scheme/symbol-table snapshot so a downstream module can
    // monomorphise it on a later cold-load.
    let (meta_path, o_path) = cache::module_cache_path(cache_dir, module);

    // Phase 1: write `.meta.json` (typecheck-driven; ensures the parent dir).
    // A meta-dir create failure aborts the whole pass (matches prior behaviour).
    if !write_module_meta(shared, module, &meta_path) {
        return;
    }

    // Phase 2: enumerate codegen-compilable symbols. Empty → no `.o`, but the
    // module is still recorded in the manifest (Phase 3).
    let names = enumerate_codegen_names(shared, module);
    if names.is_empty() {
        record_empty_codegen(shared, module);
        return;
    }

    // Phase 3: build + emit the `.o` bytes. `None` on any non-fatal codegen
    // failure (the caller returns — the module is still marked object-complete
    // by `nice_worker_loop`).
    let obj_bytes = match emit_object(shared, module, &names) {
        Some(bytes) => bytes,
        None => return,
    };

    // Phase 4: write the `.o` + record in manifest + append for the linker.
    write_object_and_record(shared, module, &o_path, &obj_bytes);
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
/// Returns `false` (caller aborts the pass) only on a meta-dir create failure;
/// a `write_meta` error is logged and tolerated (it does not block `.o`
/// codegen).
fn write_module_meta(shared: &SharedState, module: &ModuleFullPath, meta_path: &Path) -> bool {
    use cranelisp_backend::cache;

    // Ensure parent directory exists (used by both the `.meta.json` and `.o`
    // writes below).
    if let Some(parent) = meta_path.parent()
        && let Err(e) = std::fs::create_dir_all(parent)
    {
        eprintln!(
            "nice-worker: cannot create cache dir '{}': {}",
            parent.display(),
            e
        );
        return false;
    }

    let symbol_table = shared
        .symbol_tables
        .get(module)
        .map(|guard| guard.clone())
        .unwrap_or_else(|| crate::code::SessionSymbolTable::new_with_params(module.clone()));

    if let Err(e) =
        cache::serialize::write_meta(meta_path, &symbol_table, cache::CACHE_SCHEMA_VERSION)
    {
        eprintln!(
            "nice-worker: .meta.json write failed for {}: {}",
            module,
            e.message()
        );
        // Continue — the meta failure does not block `.o` codegen below.
    }
    true
}

/// Phase 2 (S87 §3.3): enumerate codegen-compilable symbols via the shared
/// predicate (Decision 22). Empty result → no compilable defns (types-only,
/// imports-only, OR a generic-only `Polymorphic` module post-Phase-4B) → no
/// `.o`, which is the correct new state (FIXME 0387). The `.meta.json` above
/// has already persisted; we just emit no object.
fn enumerate_codegen_names(
    shared: &SharedState,
    module: &ModuleFullPath,
) -> Vec<cranelisp_types::Symbol> {
    shared
        .symbol_tables
        .get(module)
        .map(|t| t.defined_symbols().map(|(name, _)| name.clone()).collect())
        .unwrap_or_default()
}

/// Phase 3a (S87 §3.3): generic-only / types-only / imports-only module — no
/// `.o` is emitted, but the module MUST still be recorded in the manifest so
/// the next session recognises it as a cache hit (FIXME 0387). Without this the
/// module is absent from the manifest, `is_cache_valid` returns false on the
/// next run, and the module is needlessly recompiled — rewriting its
/// `.meta.json`. The cache-hit loader (`try_cache_hit_load`) tolerates the
/// absent `.o` for a module whose codegen batch is empty.
fn record_empty_codegen(shared: &SharedState, module: &ModuleFullPath) {
    let source_hash = shared.cache.source_hash(module).unwrap_or_default();
    shared
        .cache
        .record_compiled(module, source_hash, std::collections::HashMap::new());
}

/// Phase 3b (S87 §3.3): build the ObjectModule with PIC ISA and emit the `.o`
/// bytes via the unified `compile_to_module` path. Returns `None` on any
/// non-fatal codegen failure (ISA build / ObjectBuilder / compile / emit) — the
/// `CRANELISP_CODEGEN_TRACE`-gated `eprintln!`s stay verbatim. Intrinsics are
/// declared on the module internally; cross-module refs resolve from
/// `symbol_tables`.
fn emit_object(
    shared: &SharedState,
    module: &ModuleFullPath,
    names: &[cranelisp_types::Symbol],
) -> Option<Vec<u8>> {
    // Build ObjectModule with PIC ISA.
    let isa = match cranelisp_backend::build_isa(true) {
        Ok(isa) => isa,
        Err(e) => {
            if std::env::var("CRANELISP_CODEGEN_TRACE").is_ok() {
                eprintln!(
                    "nice-worker: ISA build failed for {}: {}",
                    module,
                    e.message()
                );
            }
            return None;
        }
    };
    let obj_builder = match cranelisp_backend::cranelift_object::ObjectBuilder::new(
        isa,
        format!("cranelisp_{}", module),
        cranelisp_backend::cranelift_module::default_libcall_names(),
    ) {
        Ok(b) => b,
        Err(e) => {
            if std::env::var("CRANELISP_CODEGEN_TRACE").is_ok() {
                eprintln!("nice-worker: ObjectBuilder failed for {}: {e}", module);
            }
            return None;
        }
    };
    let mut obj_module = cranelisp_backend::cranelift_object::ObjectModule::new(obj_builder);

    // Compile using the unified compile_to_module path. Intrinsics are declared
    // on the module internally; cross-module refs resolve from `symbol_tables`.
    match cranelisp_backend::compile_to_module(
        module.clone(),
        names,
        &shared.symbol_tables,
        &mut obj_module,
        // FIXME 0325: nice-worker `.o` codegen is always batch (cache-write
        // side) — never consumed by introspection, so skip CLIF rendering.
        false,
    ) {
        Ok(_result) => {
            // Emit .o bytes from the ObjectModule.
            match obj_module.finish().emit() {
                Ok(bytes) => Some(bytes),
                Err(e) => {
                    if std::env::var("CRANELISP_CODEGEN_TRACE").is_ok() {
                        eprintln!("nice-worker: .o emit failed for {}: {e}", module);
                    }
                    None
                }
            }
        }
        Err(e) => {
            // Log .o compilation errors only when CRANELISP_CODEGEN_TRACE is set.
            // These are non-fatal (in-memory compilation may have succeeded).
            if std::env::var("CRANELISP_CODEGEN_TRACE").is_ok() {
                eprintln!("nice-worker: .o compilation failed for {}: {}", module, e);
            }
            None
        }
    }
}

/// Phase 4 (S87 §3.3): write the `.o` file, record the module in the manifest
/// for cache-hit detection on the next session, and append the `.o` path for
/// the linker (all via the `ObjectCache` facade — Sprint 67 Cluster B
/// sub-fire 3). The parent dir was ensured by `write_module_meta` (shared
/// parent). A `.o` write failure is logged and returns (the module stays
/// object-complete via `nice_worker_loop`).
fn write_object_and_record(
    shared: &SharedState,
    module: &ModuleFullPath,
    o_path: &Path,
    obj_bytes: &[u8],
) {
    // Write the .o file to cache directory (the parent dir was ensured above for
    // the `.meta.json` write, which shares the same parent).
    if let Err(e) = std::fs::write(o_path, obj_bytes) {
        eprintln!("nice-worker: cannot write '{}': {}", o_path.display(), e);
        return;
    }

    // Record module in manifest for cache-hit detection on next session.
    // Sprint 67 Cluster B sub-fire 3: ObjectCache facade — `source_hash` +
    // `record_compiled` replace the manual cache_state lock + record_module.
    {
        let source_hash = shared.cache.source_hash(module).unwrap_or_default();
        // dep_hashes: empty for now — full dependency tracking is a future enhancement.
        shared
            .cache
            .record_compiled(module, source_hash, std::collections::HashMap::new());
    }

    // Append the .o path for the linker. Sprint 67 Cluster B sub-fire 3:
    // ObjectCache facade.
    shared.cache.append_o_path(o_path.to_path_buf());
}
