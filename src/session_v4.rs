// CompilerSession: v4 pipeline session (pipeline-v4.md §5, roadmap Steps 0-7).
//
// Wraps the existing CompilationSession. Batch compilation goes through the v4
// scheduler-driven path with lazy dependency discovery (Step 5). REPL eval
// routes through process_module_forms(Additive) with serial per-form processing
// (Step 7).

use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, AtomicU32};
use std::sync::{Arc, Mutex};

use cranelisp_types::{CranelispError, FQSymbol, ModuleFullPath, Sexp, Warning};
// Re-exported for the `#[cfg(test)] mod *_tests` siblings that reach it via
// `use super::*` (they construct `SessionSettings`). The parent itself no
// longer names it directly (the `SessionSettings` field moved to `types.rs`).
#[cfg(test)]
pub(crate) use cranelisp_types::CodegenBehaviour;

use cranelisp_typecheck::CheckState;

use crate::code::SessionSymbolTable;
use crate::platform::LoadedPlatform;
use crate::scheduler::CompileScheduler;

// Re-export display functions so tests can import from session_v4 instead of repl.
pub use crate::display::format_result_value;
// QUIT_SENTINEL relocated to `repl.rs` (FIXME 0109 Wave D); re-exported here to
// preserve its former `session_v4::QUIT_SENTINEL` path + public reachability.
pub use crate::repl::QUIT_SENTINEL;

// S87 §2 decomposition — submodules. The `CompilerSession`/`SharedState` struct
// definitions stay in this parent (single definition site for the sibling
// `impl CompilerSession` blocks); the free fns, DTOs, and lifecycle impls move
// into the submodules below and are re-exported here so external paths
// (`crate::session_v4::X`) resolve unchanged (the compatibility membrane).
mod types;

// types.rs — DTOs + leaf pure helpers (S87 §2.1). Re-exported to preserve
// `session_v4::X` paths used by main.rs / eval.rs / repl.rs / worker.rs /
// cluster.rs / platform.rs.
pub use self::types::{
    CommandResult, EvalResult, Introspection, ModuleIntroductionOutcome, RunMode,
    SessionSettings, SymbolCategory, SymbolDescription, SymbolInfo, TypecheckProduct,
    parens_balanced_pub,
};
pub(crate) use self::types::{
    dedup_platform_names_preserving_order, extract_def_name_from_sexp, intrinsic_type_from_name,
    is_comment_only, parens_balanced, resolve_priority_worker_count,
};

// test_runner.rs — the `discover-tests` host-promised extern + `TestRunnerState`
// + the late-bound wrapper-closure machinery (S87 §2.1). Re-exported to preserve
// `session_v4::X` paths used by eval.rs / repl.rs / worker.rs / scheduler tests.
mod test_runner;
pub use self::test_runner::TestRunnerState;
pub(crate) use self::test_runner::{
    discover_test_names, discover_tests_extern, run_test_by_name, set_test_runner_state,
    TestOutcome,
};

// nice_worker.rs — the nice-worker object-codegen subsystem (S87 §2.1 / §3.3).
// `nice_worker_loop` is called by `CompilerSession::new`; `spawn_nice_workers`
// is a test-only helper referenced from `scheduler/tests.rs` as
// `session_v4::spawn_nice_workers` — re-exported to preserve that path.
mod nice_worker;
pub(crate) use self::nice_worker::nice_worker_loop;
#[cfg(test)]
pub use self::nice_worker::spawn_nice_workers;

// shared_state.rs — `ReadOnlyMacroResolver` (the `/expand` read-only recognizer),
// the one `SharedState`-adjacent behavior that is neither a `CompilerSession`
// method nor a DTO (S87 §2.1). The `SharedState` struct definition itself stays
// in this parent (§2.0). Re-exported to preserve the `session_v4::X` path used
// by repl.rs.
mod shared_state;
pub(crate) use self::shared_state::ReadOnlyMacroResolver;

// lifecycle.rs — the big `impl CompilerSession` blocks (`new`, accessors, module
// registration, watcher reload, link, shutdown) + `impl Drop` +
// `populate_ring0_got_slots` (S87 §2.1). A sibling `impl CompilerSession`
// module; the struct defs stay in this parent (§2.0). `populate_ring0_got_slots`
// is module-internal to `lifecycle` (only `new` calls it), so no re-export.
mod lifecycle;

// ---------------------------------------------------------------------------
// CompilerSession (pipeline-v4.md §5)
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// SharedState (thread-safe state for priority + nice workers)
// ---------------------------------------------------------------------------

/// Thread-safe state shared between the main thread and nice worker threads.
///
/// Separated from `CompilerSession` so that nice workers can hold `&SharedState`
/// while the main thread retains `&mut CompilerSession` for priority worker
/// operations. All fields are inherently thread-safe (Mutex, AtomicBool,
/// read-only after construction).
pub struct SharedState {
    /// Compilation scheduler. Tracks module lifecycle and coordinates
    /// work items. Internal Mutex + condvars for thread-safe access.
    pub scheduler: CompileScheduler,

    /// Project root directory (read-only after construction). Sprint 57
    /// Wave 4 G9: moved here from `CompilerSession` so persistent priority
    /// workers can access it without borrow glue.
    pub project_root: PathBuf,

    /// Lib directories for module resolution (§8.11.2 tier 3). Wrapped in
    /// `Mutex` so tests (and future runtime reconfiguration) can update the
    /// set after workers have spawned; workers hold the lock only for the
    /// duration of a single read (rare per compile). Sprint 57 Wave 4 G9:
    /// moved here from `CompilerSession` for persistent-worker access.
    pub lib_dirs: Mutex<Vec<PathBuf>>,

    /// Extra platform DLL search directories (§8.11.3 tier 3). Same Mutex
    /// rationale as `lib_dirs`. Sprint 57 Wave 4 G9: moved here from
    /// `CompilerSession` for persistent-worker access.
    pub platform_dirs: Mutex<Vec<PathBuf>>,

    // S78 in-call-stack restructure: `module_sexps` and `suspend_states` are
    // DELETED. The cluster sexps now ride the scheduler work packet
    // (`PriorityWork::Typecheck { module, sexps }`, stored on `ModuleState`);
    // the half-finished suspend state is gone (retry-from-top rebuilds it from
    // the packet sexps each pass). These two cross-thread in-progress parking
    // maps were the S60–S62 heisenbug substrate (state externalized into a
    // shared map and re-read by a different thread after an unblock); removing
    // them removes the substrate. `SharedState` drops 16 → 14 pub fields.

    /// Object cache — on-disk `.o` + sidecar pair facade per
    /// `design/arch/facades/int.md` L166 + L519-549. Sprint 67 Cluster B
    /// sub-fire 3 replaces the three pre-S67 SharedState fields
    /// (`cache_dir: Option<PathBuf>`, `cache_state: Mutex<Option<CacheState>>`,
    /// `compiled_o_paths: Mutex<Vec<PathBuf>>`) with this single facade
    /// owner. Workers and the initiator dispatch through `ObjectCache`
    /// methods (`is_enabled`, `cache_dir`, `record_source_hash`,
    /// `is_cache_valid`, `record_cache_hit`, `record_compiled`,
    /// `source_hash`, `flush_manifest`, `append_o_path`, `all_paths`) —
    /// the method surface is the load-bearing facade landing.
    pub cache: std::sync::Arc<crate::cache::ObjectCache>,

    /// Flag for nice worker priority promotion during hot flush (Step 10).
    /// When set to true, nice workers self-promote to normal OS priority.
    ///
    /// **Sprint 67 Cluster B investigation verified LIVE.** Atomic flag is
    /// read by `spawn_nice_workers` per-iteration to detect hot-flush priority
    /// boost requests; written by `wait_object_complete` when the initiator
    /// thread requests a flush. Facade-plan `PFR — facade widens` (S67 W1
    /// row) holds. Deferred to S68 facade refresh per FIXME 0208.
    pub promote_nice_workers: AtomicBool,

    // Sprint 67 Cluster B sub-fire 2e: `cached_modules: Mutex<HashSet<...>>`
    // deleted. The scheduler's per-module `cached_modules` set is the single
    // source of truth, accessed via `CompileScheduler::cached_module_insert /
    // contains / remove` (formerly only `is_cached_module` was public). The
    // SharedState duplicate was redundant — every write to it was paired
    // with a `scheduler.register_module_cached` call that already populated
    // the scheduler-side set.

    /// File path to module path mapping. Populated during handle_import
    /// when modules are first discovered. Used by the file watcher to
    /// identify which module changed.
    pub file_to_module: Mutex<HashMap<PathBuf, ModuleFullPath>>,

    // Sprint 67 Cluster B sub-fire 3: `cache_state: Mutex<Option<CacheState>>`
    // was here. Folded into `ObjectCache` (above) as interior state — callers
    // now dispatch through `shared.cache.*` methods.

    // Sprint 67 Wave 4 follow-up: `codegen_behaviour: CodegenBehaviour` was
    // here. Retired. The frontend `build_form` / `build_expr` boundary is
    // mode-agnostic; `(trace ...)` in `--link` standalone-binary mode fails at
    // link time via the architecture's natural missing-symbol detection (the
    // trace runtime is not bundled into the staticlib produced by exe-bundle).
    // The session-construction value still lives on `SessionSettings` for
    // potential future consumers; no projection onto `SharedState` is needed.
    // See spec/04-expressions.md §4.12.9.

    // -- Stateless TC: shared state (Sprint 51) --
    // The single source of truth for per-module symbol data. Formerly owned
    // by TypeChecker; now on SharedState for direct access by all workers.

    /// Per-module symbol tables. The single source of truth for per-module
    /// symbol data. Workers and session methods access this directly.
    ///
    /// Sprint 58 Wave 3b (Decision 35): the integration layer's concrete
    /// `C = Code` (an enum unifying `Code::Jit { Arc<Jit>, ptr }` and
    /// `Code::Linker { Arc<Linker>, ptr }`); `L = ()` (per-symbol Linker
    /// retention via `Code::Linker.linker` covers every case where a
    /// Linker needs to outlive its construction). See `src/code.rs` for
    /// the `Code` enum definition + reclaim contract; `SessionSymbolTable`
    /// is the alias.
    pub symbol_tables: dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,

    /// Monotonic counter for fresh type variable IDs. Shared across all
    /// TypeCheckEnv instances for concurrent workers.
    pub next_type_id: AtomicU32,

    /// Session-scoped module-path aliases (§8.6.6). int owns alias
    /// installation (BC §2 invariant 2 — import/export registration is an
    /// int-side concern, struck from typecheck in S76). typecheck reads this
    /// read-only via `TypeCheckEnv`/`check_forms`; the resolution primitive
    /// (`cranelisp_types::resolve`) consults it for qualified-name longest-
    /// prefix substitution. Populated by the int-side alias installer at
    /// parse-time (`process_cluster` pre-`check_forms`).
    pub module_aliases: cranelisp_types::ModuleAliases,

    /// Per-module prelude-outer-scope fallback flags (S78 §2.7 — prelude as
    /// an OUTER SCOPE, not flattened into each table). `module_path → true`
    /// ⇒ a bare-name inner-table miss falls back to the `prelude` module's
    /// own table (chain-following its `(export [primitives [*]])` re-exports
    /// to the canonical primitive entries). Absent OR `false` ⇒ no fallback.
    /// int populates this in `inject_prelude_if_needed` (the one site that
    /// decides the ON/OFF condition via `sexps_reference_prelude`); typecheck
    /// reads it read-only via `TypeCheckEnv`/`check_forms` (the 5th param) at
    /// its two bare-name resolution chokepoints. The synthetic `prelude`
    /// module itself, and any module that references/refuses prelude, are
    /// simply never inserted (absence-is-OFF). Session-side and unserialized
    /// — recomputed per session from source, never cached.
    pub prelude_fallback: cranelisp_typecheck::PreludeFallback,

    // Sprint 67 Cluster B sub-fire 2d: `current_module: Mutex<ModuleFullPath>`
    // was here. Relocated (PIF) to `CompilerSession::current_repl_module` per
    // `design/arch/facades/int.md` L23 + L222. REPL is single-threaded
    // against this state; the Mutex was vestigial. Workers receive their
    // module per `PriorityWork` / `NiceWork` work item and never need to
    // read the REPL's current namespace.

    // Sprint 77 W-SharedState (FIXME 0176/0179): `repl_check_state:
    // Mutex<Option<CheckState>>` was here. PIF-relocated to
    // `CompilerSession.repl_check_state` per `facades/int.md` §408. The S67
    // investigation flagged it `PIF — relocate to CompilerSession`; the S77
    // source walk confirmed every access is on the single-threaded initiator
    // (REPL `&mut self` methods, `take()`/restore around a stack-local
    // `ModuleCompiler`) — workers never touch it, so the relocation is
    // race-free. (S78 then deleted `module_sexps` / `suspend_states` outright —
    // the cluster sexps ride the scheduler work packet; no worker-shared
    // in-progress map remains.)

    // -- Target data model (session-restructure.md) --
    // DashMaps are inherently concurrent and accessible to both priority
    // and nice workers via Arc<SharedState>.

    /// Per-module typecheck products (replaces TC-internal storage).
    pub typecheck_products: dashmap::DashMap<ModuleFullPath, TypecheckProduct>,
    // Sprint 58 Step 5b (Decision 22): the `codegen_programs` transient
    // stash is gone — the nice worker walks `symbol_tables[module]
    // .defined_symbols()` directly to enumerate codegen targets, the same
    // predicate the priority worker uses, so no parallel store is needed.

    // Sprint 57 Wave 2 G6: `codegen_products: DashMap<ModuleFullPath, CodegenProduct>`
    // was here. Deleted. Compiled code is read from
    // `symbol_tables[module].get(name).code`.
    //
    // Sprint 58 Wave 3b (Decision 35): `kept_jits: Mutex<Vec<KeptJit>>` and
    // `kept_linkers: Mutex<Vec<Linker>>` retention pools dissolved. The
    // `Arc<Jit>` retention root moved per-entry onto `Code::Jit { jit, ptr }`
    // on each `ModuleEntry::Def.code`; the `Arc<Linker>` retention root
    // moved per-entry onto `Code::Linker { linker, ptr }`. When a REPL
    // user redefines a defn, the prior `ModuleEntry::Def` value drops; if
    // no other entry references the same `Arc<Jit>`, the count hits zero
    // and `Jit::Drop` calls `unsafe JITModule::free_memory()` — the
    // Decision 31 Scenario 2 per-redefinition reclaim primitive. See
    // `src/code.rs` for the `Code` enum; `design/int/symbol-table-generics.md`
    // §2.3 for the dissolution rationale.
    /// Platform DLL retention pool (Sprint 57 Wave 3 G8). Holds
    /// `LoadedPlatform` handles for the session lifetime so that every
    /// platform-fn pointer in a per-module GOT (referenced by an entry's
    /// `ModuleEntry::Def.got_slot`) remains valid for as long as any code on
    /// the symbol tables might dispatch through it. (Sprint 66 Wave 0
    /// amendment — the prior `ModuleEntry::Def.fn_ptr` field has been
    /// replaced by GOT-as-single-source-of-truth.)
    ///
    /// # Safety invariant
    ///
    /// Each platform-fn GOT entry is valid for as long as the owning DLL
    /// handle is in `SharedState::kept_dlls`. Sessions retain these handles
    /// for their full lifetime; the pool is never drained. Pushing a
    /// `LoadedPlatform` is the write that makes its GOT pointers safe to
    /// call; dropping a `LoadedPlatform` invalidates its pointers. On drop
    /// (end of session) all pointers are simultaneously invalidated, which
    /// is fine because nothing can still be calling them after drop.
    pub kept_dlls: Mutex<Vec<LoadedPlatform>>,
    /// Per-symbol introspection data, **REPL-only** (D1/D1b). `Some(map)` only
    /// under `RunMode::Repl`; `None` in `--run`/`--link` — the store does not
    /// exist in batch (it is not merely unpopulated). The compile pipeline reads
    /// nothing from it (macro `sexp`, the one compile datum, lives on the symbol
    /// table per D1). Slash commands (`/sig`,`/doc`,`/source`,`/sexp`,`/clif`)
    /// read it; absent ⇒ they no-op. (`/disasm` re-derives on demand via
    /// `produce_disasm` — it does NOT read this store.)
    pub introspection: Option<dashmap::DashMap<FQSymbol, Introspection>>,

    /// Which CLI verb launched this session (D1 ruling §4). The explicit
    /// REPL-vs-batch signal: `run_mode.populates_introspection()` gates
    /// introspection population to `Repl` only (`cluster::process_cluster`);
    /// `run_mode.is_repl()` drives the platform layout-hash gate
    /// (`worker.rs` `handle_platform`). Replaces the former
    /// `introspection.is_some()` proxy.
    pub run_mode: RunMode,

    /// Test runner state used by the `run-test` / `discover-tests` intrinsics
    /// (Sprint 66 Wave 3a-γ).
    ///
    /// Boxed so the pointer is stable for the session's lifetime. The
    /// `TEST_RUNNER` thread-local stores `*const TestRunnerState` derived from
    /// this Box; because the Box owns the allocation for the full session and
    /// the pointed-at `current_module` field is wrapped in `Mutex`, the
    /// thread-local pointer is always safe to dereference while
    /// `CompilerSession` is alive.
    ///
    /// Lifted from per-compilation init to session-wide init so that the test
    /// intrinsics may be registered unconditionally at JIT setup (the
    /// architectural answer to FIXME 0177's "conditionally-registered
    /// intrinsics" wart).
    pub test_runner_state: Box<TestRunnerState>,
    // Sprint 58 Step 5a (Decision 33): `module_structures` was a parallel
    // store for `(import …)`/`(export …)`/`(platform …)`/`(mod …)` decls in
    // source order. Those are now fields on `SymbolTable` itself
    // (populated by `src/worker.rs` form-handlers, read by `src/save.rs`
    // and the file-watcher cascade in `try_pop_changes`).
}

// `EvalInFlightGuard` — deleted in S78 Step 3 (OQ-3). The RAII guard that set
// `ModuleState::eval_in_flight` across `register_dep_for_eval` to suppress a
// worker claiming the caller module is gone with the flag it managed. The
// in-call-stack model keeps the caller's cluster state on the eval thread's
// stack frame, so no worker can observe it mid-wait — there is no race to
// suppress. The observable parity is guarded by the H5-replay gate.

/// The compiler session — scheduler-driven concurrent compilation.
///
/// One session per process. Owns the TypeChecker, codegen state, and
/// scheduler. Persistent priority + nice worker threads are spawned in
/// `new()` and joined in `shutdown()` / `Drop` (Sprint 57 Wave 4 G9).
pub struct CompilerSession {
    /// Thread-safe state shared with nice + priority worker threads. Wrapped
    /// in Arc so workers get an independent clone. Sprint 57 Wave 4 G9
    /// moved `project_root`, `lib_dirs`, `platform_dirs` here so persistent
    /// priority workers can access them without borrow glue. Convenience
    /// accessors (`project_root()`, `lib_dirs()`, `platform_dirs()`) are
    /// provided below for call sites that previously held direct fields.
    pub shared: Arc<SharedState>,

    // -- REPL-specific state (pipeline-v4.md §6) --

    /// Modules that failed reload (file watcher). While non-empty, expression
    /// evaluation is blocked.
    pub error_modules: HashSet<ModuleFullPath>,

    /// File watcher for REPL mode. Initialized via `init_watcher()` after
    /// construction. None in batch/link modes or if OS watcher unavailable.
    pub watcher: Option<crate::watch::FileWatcher>,

    /// Worker thread pool — priority + nice handles + nice-worker count.
    /// Sprint 67 Cluster B sub-fire 2a/2b per `design/arch/facades/int.md`
    /// L25 + L201. Replaces the three pre-S67 fields
    /// (`priority_worker_handles`, `nice_worker_handles`, `nice_workers`).
    /// Joined in `shutdown()` / `Drop`. The facade method surface
    /// (`WorkerPool::shutdown`, `WorkerPool::nice_worker_count`) is the
    /// stable touch-point for the rest of `int`; internal data shape is
    /// free to evolve in S68.
    ///
    /// `pub(crate)` (FIXME 0109 Wave D): the slash-command `handle_*` /
    /// prompt methods relocated to `repl.rs` reach this field; Rust field
    /// privacy is module-scoped, so the sibling-module `impl CompilerSession`
    /// blocks require crate visibility.
    pub(crate) worker_pool: crate::worker_pool::WorkerPool,

    /// REPL active module — per `/mod` (Sprint 67 Cluster B sub-fire 2d).
    /// PIF-relocated from `SharedState.current_module` per
    /// `design/arch/facades/int.md` L23 + L222. Plain `ModuleFullPath` (no
    /// Mutex) — initiator-only state; the REPL is single-threaded against
    /// it. Workers don't read it — they receive their module via
    /// `PriorityWork` / `NiceWork`.
    ///
    /// `pub(crate)` (FIXME 0109 Wave D) — reached by relocated `eval.rs` /
    /// `repl.rs` methods (module-scoped field privacy).
    pub(crate) current_repl_module: ModuleFullPath,

    /// REPL carry-forward: CheckState that persists across REPL evals
    /// (substitution, scope stack, overloads, module aliases). `None` in
    /// batch mode — CheckState is stack-local per worker there.
    ///
    /// **Sprint 77 W-SharedState (FIXME 0176/0179): PIF-relocated from
    /// `SharedState.repl_check_state` per `design/arch/facades/int.md` §408.**
    /// REPL-only carry-forward; every access is on the single-threaded
    /// initiator (REPL `&mut self` methods use a `take()`/restore pattern
    /// around a stack-local `ModuleCompiler`). Workers never touch it.
    /// `Mutex` retained so the inner `take()`/restore keeps the same shape as
    /// the former `SharedState` field; the `Mutex` is vestigial against
    /// `&mut self` access and may be unwrapped in a follow-up.
    ///
    /// `pub(crate)` (FIXME 0109 Wave D) — reached by relocated `eval.rs` /
    /// `repl.rs` methods (module-scoped field privacy).
    pub(crate) repl_check_state: Mutex<Option<CheckState>>,

    /// REPL input-active flag — per `repl/spec.md §14` / exec-flow-repl
    /// STEP 1 / STEP 3. Shared with the watcher event handler via `Arc`
    /// clone so the watcher can skip cascade reloads while the user is
    /// mid-input. Sprint 67 Cluster B sub-fire 2c per
    /// `design/arch/facades/int.md` L24 + L102.
    ///
    /// Today the field is the facade-prescribed home but the watcher event
    /// handler does not yet consult it — the flag landing here is the
    /// load-bearing structural change; wiring the watcher to read it is
    /// FIXME 0205's broader scope (S68 facade refresh).
    ///
    /// `pub(crate)` (FIXME 0109 Wave D) — reached by relocated `eval.rs` /
    /// `repl.rs` methods (module-scoped field privacy).
    pub(crate) repl_input_active: std::sync::Arc<AtomicBool>,

    /// Accumulated warnings — initiator-collected. Sprint 67 Cluster B
    /// sub-fire 2c per `design/arch/facades/int.md` L26 + L140.
    ///
    /// Workers route warnings through the work-completion notification path
    /// where they merge into this Vec; the field landing here gives the
    /// facade-prescribed `warnings()` accessor a real backing store. The
    /// worker → session warning merge wiring is FIXME 0205's broader scope.
    ///
    /// `pub(crate)` (FIXME 0109 Wave D) — reached by relocated `eval.rs` /
    /// `repl.rs` methods (module-scoped field privacy).
    pub(crate) warnings: Vec<Warning>,

    /// The session's ENTRY module — the `main`-bearing / REPL-target module
    /// the session was asked to compile (S78 §1). Named by the CLI target,
    /// defaulting to `"user"` only when no target is given. It is the "home"
    /// module: `/mod` with no argument returns the REPL cursor here. `"user"`
    /// is ONLY its default name, never a privileged identity — every program
    /// has an entry module, but most have NO `user` module at all.
    ///
    /// `pub(crate)` (FIXME 0109 Wave D) — reached by relocated `eval.rs` /
    /// `repl.rs` methods (module-scoped field privacy).
    pub(crate) entry_module: ModuleFullPath,
}

impl CompilerSession {
    /// Re-register a module for typechecking (file-watcher path).
    ///
    /// Sprint 67 Wave 3 (FIXME 0176 closure scope) — facade-prescribed
    /// `CompilerSession` thin forward to `CompileScheduler::re_register_module`
    /// per `design/arch/facades/int.md` §"CompilerSession". Returns
    /// `Ok(true)` if the module was re-registered, `Ok(false)` if the
    /// scheduler skipped it (unknown module, mid-typecheck, or its backing
    /// source could not be read).
    ///
    /// S78: re-register now requires the module's cluster sexps (they ride the
    /// work packet). This forward sources them from the module's backing file
    /// (the file-watcher's `reload_module` is the primary path and already
    /// carries the on-disk source; this thin forward reads + parses the file
    /// recorded on the typecheck product). If no backing file or the source
    /// cannot be read/parsed, the re-register is skipped (`Ok(false)`).
    ///
    /// S87 §2: kept on the parent (the struct's home) as the facade thin-forward
    /// — the bulk of the lifecycle impl moved to `lifecycle.rs`, but this one
    /// stays here so the `session_v4.rs` facade surface (and the row-45 guard)
    /// is preserved.
    pub fn re_register_module(
        &mut self,
        module: &ModuleFullPath,
    ) -> Result<bool, CranelispError> {
        let Some(file_path) = self.shared.typecheck_products.get(module)
            .and_then(|tp| tp.file_path.clone())
        else {
            return Ok(false);
        };
        let Ok(source) = std::fs::read_to_string(&file_path) else {
            return Ok(false);
        };
        let sexps: std::sync::Arc<[Sexp]> =
            std::sync::Arc::from(cranelisp_frontend::parse(&source)?);
        // Module-preamble wiring (§8.16.5; design/frontend/module-preamble.md §5):
        // a watcher-triggered re-register re-reads fresh source from disk, so the
        // preamble is re-captured (the on-disk file is the source of truth here,
        // not a cache).
        crate::save::apply_module_preamble(&self.shared.symbol_tables, module, &source);
        Ok(self.shared.scheduler.re_register_module(module, sexps))
    }
}


#[cfg(test)]
mod platform_enumeration_dedup_tests;


// ---------------------------------------------------------------------------
// Trace format support (repl/spec.md §4.12)
// ---------------------------------------------------------------------------


// ---------------------------------------------------------------------------
// Trace display support (repl/spec.md §4.12)
// ---------------------------------------------------------------------------

// `TraceDisplayState` / `TRACE_DISPLAY` / `set_trace_display_state` /
// `clear_trace_display_state` / `repl_trace_format` — DELETED S76 (FIXME 0256,
// trace ruling 2026-06-04). The trace value-formatter is now the pure
// descriptor-driven `cranelisp_intrinsics::trace::cranelisp_trace_format`
// (codegen bakes a self-contained `DisplayDescriptor`; no session state). int
// hosts no trace-display state. `src/display.rs::format_result_value` (REPL
// result display) is untouched and stays.

// ---------------------------------------------------------------------------
// Sprint 57 Wave 4 G9 — persistent worker lifecycle tests
// ---------------------------------------------------------------------------
//
// Covers the four scenarios from `design/int/persistent-workers.md` §9.1:
//   1. park + wake (enqueue → worker processes)
//   2. shutdown under load (Drop while work enqueued, no panic, no leak)
//   3. concurrent register_module (two modules at once, both complete)
//   4. reload-during-compile race (reload while register_module is mid-flight)
//
// These are end-to-end session tests that use trivial source so they do not
// rely on a prelude or stdlib; they validate the worker lifecycle only.

#[cfg(test)]
mod persistent_worker_tests;


// ---------------------------------------------------------------------------
// Sprint 61 Slice 1 — bare-primitive-name value path (Defect 4)
// ---------------------------------------------------------------------------
//
// Unit tests for the bare-value resolution path in
// `check_bare_symbol_introspection` and `resolve_entry_for_display`.
// The fix under test: the one-hop display resolver was replaced by a
// bounded-depth recursive walk so user → prelude → primitives chains
// terminate on the defining `ModuleEntry::Def` — matching the typechecker's
// existing recursive `resolve_to_terminal_entry_owned`. See
// `design/int/bare-primitive-value-path.md` (candidate 2).
#[cfg(test)]
mod bare_primitive_value_path_tests;

#[cfg(test)]
mod list_classification_tests;


