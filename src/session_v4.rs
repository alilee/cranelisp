// CompilerSession: v4 pipeline session (pipeline-v4.md §5, roadmap Steps 0-7).
//
// Wraps the existing CompilationSession. Batch compilation goes through the v4
// scheduler-driven path with lazy dependency discovery (Step 5). REPL eval
// routes through process_module_forms(Additive) with serial per-form processing
// (Step 7).

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU32};
use std::sync::{Arc, Mutex};

use cranelisp_types::{ErrorLocation,
    CodegenBehaviour, CranelispError,
    DefKind, FQSymbol, ModuleEntry, ModuleFullPath,
    Sexp, Span, Symbol,
    Type, Warning,
};

use cranelisp_typecheck::CheckState;

use crate::code::{Code, SessionSymbolTable};
use crate::platform::LoadedPlatform;
use crate::scheduler::CompileScheduler;

// Re-export display functions so tests can import from session_v4 instead of repl.
pub use crate::display::format_result_value;
// QUIT_SENTINEL relocated to `repl.rs` (FIXME 0109 Wave D); re-exported here to
// preserve its former `session_v4::QUIT_SENTINEL` path + public reachability.
pub use crate::repl::QUIT_SENTINEL;

// ---------------------------------------------------------------------------
// ReadOnlyMacroResolver — for /expand slash command
// ---------------------------------------------------------------------------

/// Read-only macro resolver for the /expand slash command.
///
/// Same lookup logic as `SymbolTableMacroResolver` (follows Import/Reexport
/// chains) but never triggers compilation. If a macro's clauses are not
/// compiled, returns `Ok(None)` (silently skipped).
pub(crate) struct ReadOnlyMacroResolver<'a> {
    pub(crate) symbol_tables: &'a dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    pub(crate) module_aliases: &'a cranelisp_types::ModuleAliases,
    /// Per-module prelude-fallback bits — so `/expand` recognizes a
    /// prelude-provided macro from a user module via the implicit outer scope
    /// (S78 §2; public-only per I-1), matching the live compile-time path.
    pub(crate) prelude_fallback: &'a cranelisp_typecheck::PreludeFallback,
    pub(crate) current_module: ModuleFullPath,
}

impl crate::expander::MacroResolver for ReadOnlyMacroResolver<'_> {
    fn symbol_tables(
        &self,
    ) -> &dashmap::DashMap<ModuleFullPath, SessionSymbolTable> {
        self.symbol_tables
    }

    fn recognize(
        &mut self,
        name: &str,
        span: Span,
    ) -> Result<Option<FQSymbol>, CranelispError> {
        // RECOGNITION via the LOCKED types primitive (committed `View`,
        // `macro-availability-model.md` §0.7) — same path as the live
        // compile-time recognition; no second chain-walk copy. Read-only:
        // no on-demand compilation. If the macro's clauses are not already in
        // memory, the executor (`JitMacroExpander::invoke`) surfaces a clear
        // `Aborted` — `/expand` is only meaningful after the macro is defined
        // and compiled, which the REPL flow guarantees for a prior input.
        crate::expander::recognize_macro_head(
            self.symbol_tables,
            self.module_aliases,
            self.prelude_fallback,
            &self.current_module,
            name,
            span,
        )
    }
}

// ---------------------------------------------------------------------------
// RunMode (D1 ruling — design/arch/d1-introspection-repl-only.md §4)
// ---------------------------------------------------------------------------

/// Which CLI verb launched this session — the explicit run-mode carrier that
/// replaces the `introspection.is_some()` proxy (D1 ruling §4).
///
/// `RunMode` is an **int-internal** property of the running session; it is NOT
/// a `cranelisp-types` boundary type (frontend / typecheck / backend never see
/// it). It is deliberately **distinct** from backend's
/// `CompileMode::{Interactive, Batch, Release}` codegen-strategy axis (which
/// governs GOT-indirect-vs-direct codegen, not REPL-vs-batch session
/// behaviour). Do not conflate the two.
///
/// Two consumers:
/// - `populates_introspection()` — introspection is a REPL slash-command
///   facility (`/sig`, `/doc`, `/source`, `/clif`) and is populated ONLY in
///   `Repl` mode. The compile pipeline reads nothing from it; compile-necessary
///   data (macro `sexp`) lives on the symbol table.
/// - `is_repl()` — the platform layout-hash gate's REPL discriminator (REPL
///   warns-and-loads on drift; `--run`/`--link` refuse).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RunMode {
    /// `cranelisp` with no/REPL target — interactive prompt; populates
    /// introspection; layout-hash drift WARNS-AND-LOADS.
    Repl,
    /// `cranelisp --run <file>` — batch execute then `process::exit`;
    /// no introspection; layout-hash drift REFUSES.
    Run,
    /// `cranelisp --link <file>` — produce a standalone executable;
    /// no introspection; layout-hash drift REFUSES.
    Link,
}

impl RunMode {
    /// Introspection is REPL-only.
    pub fn populates_introspection(self) -> bool {
        matches!(self, RunMode::Repl)
    }

    /// The layout-hash gate's `is_repl` discriminator (REPL warns; Run/Link
    /// refuse).
    pub fn is_repl(self) -> bool {
        matches!(self, RunMode::Repl)
    }
}

// ---------------------------------------------------------------------------
// SessionSettings (pipeline-v4.md §10)
// ---------------------------------------------------------------------------

/// Session configuration. CLI flags override cranelisp.toml values.
pub struct SessionSettings {
    pub no_color: bool,
    pub no_cache: bool,
    pub codegen_behaviour: CodegenBehaviour,
    pub priority_workers: usize,
    pub nice_workers: usize,
    /// Which CLI verb launched the session (D1 ruling §4). Threaded onto
    /// `SharedState.run_mode`; the explicit REPL-vs-batch signal replacing the
    /// `introspection.is_some()` proxy.
    pub run_mode: RunMode,
}

// ---------------------------------------------------------------------------
// CommandResult (pipeline-v4.md §6.1)
// ---------------------------------------------------------------------------

/// Result of processing a REPL input line through `process_commands`.
pub enum CommandResult {
    /// Blank line, comment, or side-effect-only command.
    Nothing,
    /// Session should exit.
    Quit,
    /// Command that produces displayable output (e.g., /sig, /list).
    Final(String),
    /// Raw source text to submit for compilation.
    Compile(String),
}

// ---------------------------------------------------------------------------
// EvalResult (pipeline-v4.md §6.2)
// ---------------------------------------------------------------------------

/// Result of evaluating one input via `CompilerSession::eval()`.
///
/// Either a definition (which introduced a symbol) or a value (which
/// was computed). Both carry zero or more warnings.
pub enum EvalResult {
    /// A definition was processed (defn, deftype, deftrait, impl, defmacro).
    Def {
        symbol: FQSymbol,
        ty: Type,
        warnings: Vec<Warning>,
    },
    /// An expression was evaluated to a value.
    Val {
        value: i64,
        ty: Type,
        warnings: Vec<Warning>,
    },
}

impl EvalResult {
    pub fn warnings(&self) -> &[Warning] {
        match self {
            EvalResult::Def { warnings, .. } => warnings,
            EvalResult::Val { warnings, .. } => warnings,
        }
    }

    pub fn warnings_mut(&mut self) -> &mut Vec<Warning> {
        match self {
            EvalResult::Def { warnings, .. } => warnings,
            EvalResult::Val { warnings, .. } => warnings,
        }
    }

    /// The raw i64 value. Returns 0 for `Def`.
    pub fn value(&self) -> i64 {
        match self {
            EvalResult::Val { value, .. } => *value,
            EvalResult::Def { .. } => 0,
        }
    }

    /// The inferred type.
    pub fn ty(&self) -> &Type {
        match self {
            EvalResult::Val { ty, .. } => ty,
            EvalResult::Def { ty, .. } => ty,
        }
    }

    /// Whether this is a definition.
    pub fn is_def(&self) -> bool {
        matches!(self, EvalResult::Def { .. })
    }
}

// ---------------------------------------------------------------------------
// Slash command types (pipeline-v4.md §6.1)
// ---------------------------------------------------------------------------


/// Check if parentheses are balanced in input (for multi-line continuation).
/// Exposed as `parens_balanced_pub` for use by the REPL loop in main.rs.
pub fn parens_balanced_pub(input: &str) -> bool {
    parens_balanced(input)
}

pub(crate) fn parens_balanced(input: &str) -> bool {
    let mut depth: i32 = 0;
    let mut in_string = false;
    let mut in_comment = false;
    let mut prev_char = '\0';

    for ch in input.chars() {
        if in_comment {
            if ch == '\n' {
                in_comment = false;
            }
            prev_char = ch;
            continue;
        }
        if in_string {
            if ch == '"' && prev_char != '\\' {
                in_string = false;
            }
            prev_char = ch;
            continue;
        }
        match ch {
            ';' => in_comment = true,
            '"' => in_string = true,
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            _ => {}
        }
        prev_char = ch;
    }
    depth <= 0
}

// ---------------------------------------------------------------------------
// Target data model types (session-restructure.md)
// ---------------------------------------------------------------------------

/// TARGET STATE: per-module typecheck product. Replaces TC-internal storage.
/// Populated by typecheck or deserialized from .meta.json on cache hit.
/// Permanent for session lifetime. See session-restructure.md.
///
/// Sprint 56 Wave 0 (§9.8 G7 pull-forward): the per-module GOT table moved
/// onto `SymbolTable.got`. Readers who previously read `tp.got` now read
/// `symbol_tables[m].got` directly. The `got` field is deleted from this
/// struct. Sprint 56 Wave 2 retired `SessionCompilationEnv` entirely — the
/// only survivors on this struct are `file_path` (used by `/source`) and
/// `source_text` (used for sexp-span slicing in introspection).
pub struct TypecheckProduct {
    pub file_path: Option<PathBuf>,
    /// Module source text, retained in --repl mode for /source introspection.
    /// Sexp spans index into this string. None for cache-hit modules and batch mode.
    pub source_text: Option<String>,
}

// Sprint 58 Wave 3b (Decision 35): the `KeptJit` wrapper struct (Sprint 57
// Wave 2 G6) was deleted along with the `kept_jits` retention pool it served.
// Its `Send + Sync` rationale lives on at `src/code.rs` for the `Code` enum
// that subsumed its role (per-entry `Arc<Jit>` retention on `ModuleEntry::Def
// .code`).

/// REPL-only per-symbol introspection data.
/// Not populated during batch. See session-restructure.md.
#[derive(Debug, Clone, Default)]
pub struct Introspection {
    pub source: Option<String>,
    pub sexp: Option<Sexp>,
    pub expanded: Option<Sexp>,
    pub ast: Option<cranelisp_types::Defn>,
    pub clif_ir: Option<String>,
    pub disasm: Option<String>,
    pub code_size: Option<usize>,
}

// ---------------------------------------------------------------------------
// Sprint 67 W3 — Facade-prescribed introspection record types
// (FIXME 0176 partial close; `facades/int.md` §"Introspection records")
// ---------------------------------------------------------------------------

/// Symbol category for facade-level introspection. A coarser classification
/// than `ModuleEntry` itself — used by `describe_symbol` /
/// `list_user_definitions` to bucket symbols for REPL display.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolCategory {
    Module,
    Macro,
    Trait,
    Type,
    Fn,
    SpecialForm,
    Constructor,
}

/// Brief symbol record — name + category + optional scheme + optional doc.
/// Returned by `CompilerSession::list_user_definitions()`.
#[non_exhaustive]
#[derive(Debug, Clone)]
pub struct SymbolInfo {
    pub name: Symbol,
    pub category: SymbolCategory,
    pub scheme: Option<cranelisp_types::Scheme>,
    pub docstring: Option<String>,
}

/// Full symbol description — `SymbolInfo` plus source text + FQ symbol.
/// Returned by `CompilerSession::describe_symbol(name)`.
///
/// The `related` field carries cross-reference FQSymbols (defn, impl, match
/// arms, etc.) per `facades/int.md` L403 + `repl/spec.md` §3.6's
/// related-symbol comment lines. Populated as an empty Vec at first wiring
/// (Sprint 67 Wave 4) — full population is tracked by FIXME 0194.
#[non_exhaustive]
#[derive(Debug, Clone)]
pub struct SymbolDescription {
    pub fq: FQSymbol,
    pub category: SymbolCategory,
    pub scheme: Option<cranelisp_types::Scheme>,
    pub docstring: Option<String>,
    pub source: Option<String>,
    pub related: Vec<FQSymbol>,
}

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
    /// table per D1). Slash commands (`/sig`,`/doc`,`/source`,`/sexp`,`/clif`,
    /// `/disasm`) read it; absent ⇒ they no-op.
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

/// Resolve the effective priority-worker count from a `SessionSettings`
/// request. `0` → auto-detect (`available_parallelism()-1`, clamped to
/// `[1, 8]`); any non-zero value is clamped to `[1, 8]`. Per
/// `persistent-workers.md` §5.1.
pub(crate) fn resolve_priority_worker_count(requested: usize) -> usize {
    if requested == 0 {
        std::thread::available_parallelism()
            .map(|n| n.get().saturating_sub(1))
            .unwrap_or(1)
            .clamp(1, 8)
    } else {
        requested.clamp(1, 8)
    }
}

// `EvalInFlightGuard` — deleted in S78 Step 3 (OQ-3). The RAII guard that set
// `ModuleState::eval_in_flight` across `register_dep_for_eval` to suppress a
// worker claiming the caller module is gone with the flag it managed. The
// in-call-stack model keeps the caller's cluster state on the eval thread's
// stack frame, so no worker can observe it mid-wait — there is no race to
// suppress. The observable parity is guarded by the H5-replay gate.

/// The outcome of `CompilerSession::introduce_module` (FIXME 0192 Residual
/// Task 2 — 4-branch lifecycle).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleIntroductionOutcome {
    /// The module was already present; no change.
    AlreadyPresent,
    /// The cached metadata + `.o` was decoded and installed atomically.
    CachedLoad,
    /// No cache entry but a source file is registered; caller should
    /// schedule compilation (the orchestrator does not invoke the scheduler).
    SourceLoad,
    /// Neither cache nor source — an empty symbol table was created.
    Blank,
}

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
    /// Create a new compiler session (pipeline-v4.md §5).
    ///
    /// Spawns `priority_workers` persistent priority worker threads and
    /// `nice_workers` persistent nice worker threads. Workers park on the
    /// scheduler's condvars and process work for the session lifetime;
    /// `shutdown()` (called from `Drop`) joins them all. Sprint 57 Wave 4
    /// G9 per `design/int/persistent-workers.md` §4.1.
    ///
    /// The effective priority worker count is derived from
    /// `settings.priority_workers`: values of 0 are interpreted as
    /// "auto-detect" (`available_parallelism()-1`, clamped to `[1, 8]`);
    /// explicit values are clamped to `[1, 8]`. Tests pass
    /// `priority_workers: 1` for determinism.
    pub fn new(
        settings: SessionSettings,
        project_root: PathBuf,
        entry_module_name: &str,
    ) -> Self {
        // Lib dirs: stdlib location(s), NOT including project_root.
        // Project root is tier 2 in §8.11.2, searched separately.
        let lib_dirs = crate::session_setup::assemble_lib_dirs(&project_root);

        // Platform dirs: extra search locations from env var (§8.11.5).
        let platform_dirs = crate::session_setup::assemble_platform_dirs();

        // Sprint 67 Cluster B sub-fire 3: cache directory + state are folded
        // into the `ObjectCache` facade. `Some(_)` when caching is enabled;
        // `None` under `--no-cache`. The directory is created eagerly because
        // the worker writes happen on the hot path.
        let cache_dir_opt = if settings.no_cache {
            None
        } else {
            let dir = project_root.join(".cranelisp-cache");
            let _ = std::fs::create_dir_all(&dir);
            Some(dir)
        };
        let cache_state = cache_dir_opt.as_ref()
            .map(|d| crate::session_setup::CacheState::new(d.clone()));
        let object_cache = std::sync::Arc::new(
            crate::cache::ObjectCache::new(cache_dir_opt, cache_state),
        );

        // Priority-worker count: 0 = auto-detect, else explicit. Clamp to
        // [1, 8] per `persistent-workers.md` §5.1.
        let priority_workers = resolve_priority_worker_count(settings.priority_workers);

        let nice_workers = settings.nice_workers;

        // D1 ruling §4: capture the run-mode before `settings` is consumed
        // below; it is carried on `SharedState` as the explicit REPL-vs-batch
        // signal (introspection gating + layout-hash gate).
        let run_mode = settings.run_mode;

        let symbol_tables: dashmap::DashMap<ModuleFullPath, SessionSymbolTable> =
            dashmap::DashMap::new();
        let next_type_id = AtomicU32::new(0);
        // S78 §1: the ENTRY module is an ordinary module. `"user"` is only its
        // default NAME (passed by `main.rs` when no CLI target is given); it is
        // NOT a privileged identity. The session seeds the REPL cursor /
        // check-state / test-runner state off this name (below), and lazily
        // creates the entry module's symbol table by its real name so any
        // pre-first-input REPL introspection (`/list`, `/imports` on an empty
        // session) finds a table. The real entry registration (`register_module`
        // → `register_entry_module`) is name-agnostic and runs later; this seed
        // is just the create-by-real-name table the cursor points at.
        let entry_module = ModuleFullPath::from(entry_module_name);

        // S78 §1: create the entry module's table by its REAL name (never a
        // hardcoded "user" literal). Special forms mount at root "" and
        // synthetic modules mount in `mount_synthetic_modules` — neither needs
        // a pre-seeded entry table; this exists only so pre-first-input REPL
        // introspection has a table for the cursor's module.
        cranelisp_types::ensure_module_exists(&symbol_tables, &entry_module);

        // S68 Wave 4 (Decision 0048): Arc-clone the statically-constructed
        // `PRIMITIVES_TABLE` into the session's symbol tables at
        // `ModuleFullPath::from("primitives")`. The session's primitives
        // module then *shares* the static `Arc<GotTable>` with every other
        // session in the process. `(*PRIMITIVES_TABLE).clone()` clones the
        // `SymbolTable<Code, ()>` by value; the inner `got: Arc<GotTable>`
        // field is an Arc-clone, so the underlying GotTable is shared with
        // the static. From this point on, primitives dispatch is functionally
        // equivalent to any other module via the standard cross-module
        // GOT-indirect call path.
        //
        // `mount_synthetic_modules` (next call) short-circuits the primitives-
        // module creation (its `if !contains_key` check finds the entry).
        // Subsequent `register_primitives` / `register_ring1_primitives` /
        // etc. `get_mut` the same module and *overwrite* the Symbol entries
        // by name — the typecheck-side metadata (scheme, docstring) reflects
        // the typecheck registry's view. The shared `Arc<GotTable>` carries
        // through unchanged because `register_primitives` mutates only the
        // session-local `next_got_slot` counter, allocating fresh slots that
        // `populate_ring0_got_slots` (called below) populates from the
        // static table's slot ↔ fn-ptr mapping. The dispatch invariant is
        // preserved: every primitive call lands on a GOT slot that holds
        // the static `extern "C" fn` ptr.
        // S76 (FIXME 0242-i): `PRIMITIVES_TABLE` is now `SymbolTable<(), ()>`;
        // concretise to the session `<Code, ()>` flavour via `into_concrete`
        // at the mount. The inner `got: Arc<GotTable>` is Arc-cloned, so the
        // session's primitives module shares the static GOT (slots already
        // populated with the Ring-0 shim addresses).
        symbol_tables.insert(
            ModuleFullPath::from("primitives"),
            (*cranelisp_primitives::PRIMITIVES_TABLE)
                .as_ref()
                .clone()
                .into_concrete::<Code, ()>(),
        );

        // S76 (FIXME 0242): the synthetic-module mount — int's reconstruction
        // of the deleted `cranelisp_typecheck::register_builtins` body. Seeds
        // special forms (root ""), intrinsic type names + Vec, the `macros`
        // module (Sexp/SList + sconcat), Option, IO (+ bind), Trace, and the
        // test infrastructure into the session tables. `primitives` is already
        // mounted above; this adds to it + the root "" + creates `macros`. It
        // does NOT touch the entry module (it is an ordinary module, seeded by
        // its real name above and registered name-agnostically later — S78 §1).
        // Fresh type vars for the polymorphic ADTs/primitive are allocated
        // from `next_type_id`, advancing the high-water mark monotonically.
        crate::bootstrap::mount_synthetic_modules(&symbol_tables, &next_type_id);

        // Per FIXME 0174 + Decision 43: Ring 0 primitives (`add-i64`, `not`,
        // …) are now ordinary `ModuleEntry::Def` entries with `got_slot:
        // Some(_)`. Pair each name with its Rust shim address and write the
        // pointer into the primitives module's GOT slot so the standard
        // GOT-indirect dispatch path (and the mappable-path
        // `(let [f not] (f true))`) resolves correctly. Inline substitution
        // in backend remains a separate optimisation.
        populate_ring0_got_slots(&symbol_tables);

        // Sprint 66 Wave 3a-γ: build the session-wide TestRunnerState. The
        // `tc_modules` pointer is derived from the `symbol_tables` DashMap
        // owned by the Arc<SharedState> we're about to construct. Since
        // `SharedState` is held behind `Arc` for the session lifetime and
        // never moved, the pointer is stable. The `current_module` field is
        // a `Mutex` so `/mod` may update it without rebuilding the state.
        let test_runner_state = Box::new(TestRunnerState {
            tc_modules: std::ptr::null(), // patched immediately after Arc construction
            // S78 §1: seed off the ENTRY module name, not a hardcoded "user".
            current_module: Mutex::new(entry_module.clone()),
        });

        let shared = Arc::new(SharedState {
            scheduler: CompileScheduler::new(),
            project_root,
            lib_dirs: Mutex::new(lib_dirs),
            platform_dirs: Mutex::new(platform_dirs),
            cache: object_cache,
            promote_nice_workers: AtomicBool::new(false),
            file_to_module: Mutex::new(HashMap::new()),
            symbol_tables,
            next_type_id,
            module_aliases: cranelisp_types::ModuleAliases::default(),
            prelude_fallback: cranelisp_typecheck::PreludeFallback::default(),
            typecheck_products: dashmap::DashMap::new(),
            // Sprint 58 Wave 3b: kept_jits / kept_linkers dissolved per
            // Decision 35; Arc retention now lives on each Code::Jit /
            // Code::Linker on `ModuleEntry::Def.code`.
            kept_dlls: Mutex::new(Vec::new()),
            // D1b: the introspection STORE is REPL-only — `Some(empty map)`
            // under `RunMode::Repl`, `None` in `--run`/`--link` (no allocation
            // in batch). Same `run_mode` carrier that gates population (D1 §4).
            introspection: run_mode.populates_introspection().then(dashmap::DashMap::new),
            run_mode,
            test_runner_state,
        });

        // Patch the `tc_modules` pointer inside `test_runner_state` to point
        // at `shared.symbol_tables`. Safe: `shared` is `Arc<SharedState>`,
        // never moved; the `symbol_tables` field has a stable address for
        // the session lifetime. The `Box<TestRunnerState>` itself sits inside
        // the `SharedState` struct, so a `&mut` through `Arc` would alias
        // shared state — instead we cast through a raw pointer to flip the
        // single `*const` field. This write happens exactly once, before any
        // worker thread is spawned (so before any reader observes the field).
        // SAFETY: single-writer, pre-spawn; no concurrent reader exists yet.
        unsafe {
            let trs_ptr = &*shared.test_runner_state as *const TestRunnerState
                as *mut TestRunnerState;
            (*trs_ptr).tc_modules = &shared.symbol_tables as *const _;
        }

        // Spawn persistent priority worker threads (Sprint 57 Wave 4 G9).
        // Workers park on `scheduler.priority_work_available` and process
        // modules until shutdown. Joined in `shutdown()` / `Drop`.
        let mut priority_worker_handles = Vec::with_capacity(priority_workers);
        for i in 0..priority_workers {
            let worker_shared = Arc::clone(&shared);
            let handle = std::thread::Builder::new()
                .name(format!("priority-worker-{}", i))
                .spawn(move || {
                    crate::worker::priority_worker_loop_shared(&worker_shared);
                })
                .expect("failed to spawn priority worker thread");
            priority_worker_handles.push(handle);
        }

        // Spawn persistent nice worker threads for object codegen (.o files).
        // Workers park on scheduler condvar and wake when modules reach
        // TypecheckDone. They run for the session lifetime and are joined
        // in shutdown().
        let mut nice_worker_handles = Vec::with_capacity(nice_workers);
        for i in 0..nice_workers {
            let worker_shared = Arc::clone(&shared);
            let handle = std::thread::Builder::new()
                .name(format!("nice-worker-{}", i))
                .spawn(move || {
                    nice_worker_loop(&worker_shared);
                })
                .expect("failed to spawn nice worker thread");
            nice_worker_handles.push(handle);
        }

        CompilerSession {
            shared,
            error_modules: HashSet::new(),
            watcher: None,
            worker_pool: crate::worker_pool::WorkerPool::new(
                priority_worker_handles, nice_worker_handles, nice_workers,
            ),
            // S78 §1: the REPL cursor + carry-forward CheckState start at the
            // ENTRY module (its real name), not a hardcoded "user".
            current_repl_module: entry_module.clone(),
            repl_check_state: Mutex::new(Some(CheckState::new(entry_module.clone()))),
            repl_input_active: std::sync::Arc::new(AtomicBool::new(false)),
            warnings: Vec::new(),
            entry_module,
        }
    }

    /// Convenience accessor: project root.
    pub fn project_root(&self) -> &Path {
        &self.shared.project_root
    }

    /// Convenience accessor: lib search directories (snapshot clone).
    pub fn lib_dirs(&self) -> Vec<PathBuf> {
        self.shared.lib_dirs.lock()
            .unwrap_or_else(|e| e.into_inner())
            .clone()
    }

    /// Convenience accessor: platform DLL search directories (snapshot clone).
    pub fn platform_dirs(&self) -> Vec<PathBuf> {
        self.shared.platform_dirs.lock()
            .unwrap_or_else(|e| e.into_inner())
            .clone()
    }

    /// Update the lib directory set. Sprint 57 Wave 4 G9: tests and the
    /// CLI call this after `new()` to override defaults; workers take a
    /// fresh clone for each file-resolution call, so the change is
    /// observed by subsequent typechecks.
    pub fn set_lib_dirs(&mut self, dirs: Vec<PathBuf>) {
        *self.shared.lib_dirs.lock()
            .unwrap_or_else(|e| e.into_inner()) = dirs;
    }

    /// Update the platform search directory set. Same semantics as
    /// `set_lib_dirs`.
    pub fn set_platform_dirs(&mut self, dirs: Vec<PathBuf>) {
        *self.shared.platform_dirs.lock()
            .unwrap_or_else(|e| e.into_inner()) = dirs;
    }

    /// Append a single platform search directory to the current set.
    /// Convenience wrapper around `set_platform_dirs` for tests/CLI.
    pub fn push_platform_dir(&mut self, dir: PathBuf) {
        let mut guard = self.shared.platform_dirs.lock()
            .unwrap_or_else(|e| e.into_inner());
        guard.push(dir);
    }

    // -- Convenience accessors for shared TC state --

    // `tc_env` deleted (W-Absorb): all former callers switched to the
    // types-crate `ensure_module_exists` free fn; no remaining use for a
    // session-built `TypeCheckEnv`.

    /// Get the current module path (REPL carry-forward).
    ///
    /// Sprint 67 Cluster B sub-fire 2d: reads the CompilerSession-owned
    /// `current_repl_module` field (PIF-relocated from
    /// `SharedState.current_module` per facade L222 — REPL is single-threaded
    /// against this state).
    pub(crate) fn current_module_path(&self) -> ModuleFullPath {
        self.current_repl_module.clone()
    }

    /// Set the current module path (REPL carry-forward).
    ///
    /// Sprint 67 Cluster B sub-fire 2d: writes the CompilerSession-owned
    /// `current_repl_module` field and mirrors the change into the
    /// session-stable `test_runner_state.current_module` (still on
    /// `SharedState` because the JIT-emitted test intrinsics dereference
    /// it via a raw pointer that must outlive the session). Also resets
    /// `shared.repl_check_state` to a fresh `CheckState` for the new
    /// module — REPL carry-forward state (subst, env, overloads) is lost
    /// on module switch, matching the prior behaviour.
    pub(crate) fn set_current_module(&mut self, path: ModuleFullPath) {
        cranelisp_types::ensure_module_exists(&self.shared.symbol_tables, &path);
        self.current_repl_module = path.clone();
        // Sprint 66 Wave 3a-γ: keep the test-runner state's `current_module`
        // in sync so `discover-tests` (with empty module arg) targets the
        // active REPL namespace after a `/mod` switch. The
        // `test_runner_state` lives behind the `Arc<SharedState>` so the
        // JIT-emitted intrinsics may dereference a stable pointer; only
        // the inner `Mutex<ModuleFullPath>` needs updating here.
        *self.shared.test_runner_state.current_module.lock()
            .unwrap_or_else(|e| e.into_inner()) = path.clone();
        // Create a new CheckState for the new module.
        *self.repl_check_state.lock()
            .unwrap_or_else(|e| e.into_inner()) = Some(CheckState::new(path));
    }

    /// Get a read guard for the current module's symbol table.
    pub(crate) fn current_symbol_table(&self) -> dashmap::mapref::one::Ref<'_, ModuleFullPath, SessionSymbolTable> {
        let module = self.current_module_path();
        self.shared.symbol_tables.get(&module)
            .unwrap_or_else(|| unreachable!("invariant: current_module always exists in symbol_tables"))
    }

    /// Get a read guard for any module's symbol table.
    pub(crate) fn module_table(&self, path: &ModuleFullPath) -> Option<dashmap::mapref::one::Ref<'_, ModuleFullPath, SessionSymbolTable>> {
        self.shared.symbol_tables.get(path)
    }

    /// Introduce a module into the session — the 4-branch lifecycle gate.
    ///
    /// Sprint 67 hack-back (FIXME 0192 Residual Task 2): the single
    /// orchestration entry point for module introduction. Routes to one of
    /// four outcomes:
    ///   1. **AlreadyPresent** — `path` already has a symbol table; no change.
    ///   2. **CachedLoad** — cache reports a valid metadata + `.o` for `path`;
    ///      decode the cached `SymbolTable`, advance the typecheck `next_id`
    ///      past any cached TypeId vars (the consistency invariant from the
    ///      old `restore_cached_module`), and atomically install the table
    ///      via `cranelisp_types::install_module`.
    ///   3. **SourceLoad** — no cache hit but a source file is registered for
    ///      `path`; signal the caller (scheduler) to enqueue compilation.
    ///   4. **Blank** — neither cache nor source is available; create an empty
    ///      symbol table at `path` via `cranelisp_types::ensure_module_exists`.
    ///
    /// The cache-hit branch shares its install primitive with `worker.rs`'s
    /// `try_cache_hit_load` (which retains the surrounding logic for transitive
    /// dep walking + platform re-resolution that the worker context owns).
    /// The source-load branch returns the outcome variant so the caller can
    /// decide whether/how to schedule — the orchestrator does not directly
    /// drive the scheduler (which has tighter shared-state contracts the
    /// session does not own).
    pub fn introduce_module(
        &self,
        path: &ModuleFullPath,
    ) -> Result<ModuleIntroductionOutcome, CranelispError> {
        // Branch 1 — already present.
        if self.shared.symbol_tables.contains_key(path) {
            return Ok(ModuleIntroductionOutcome::AlreadyPresent);
        }

        // Branch 2 — cache hit. Probe the backend cache for a valid entry;
        // if present, decode and install atomically.
        if let Some(decoded) = self.try_load_cached_for_introduction(path)? {
            cranelisp_typecheck::advance_next_id_past_table(
                &self.shared.next_type_id, &decoded,
            );
            cranelisp_types::install_module(
                &self.shared.symbol_tables, path.clone(), decoded,
            );
            return Ok(ModuleIntroductionOutcome::CachedLoad);
        }

        // Branch 3 — source hit. The session has no scheduler in hand here;
        // signal the caller. Source presence is determined by inspecting the
        // worker's `file_to_module` reverse-mapping or by attempting source
        // lookup via cache_state's known paths.
        if self.find_module_source(path).is_some() {
            return Ok(ModuleIntroductionOutcome::SourceLoad);
        }

        // Branch 4 — blank create-if-absent.
        let _ = cranelisp_types::ensure_module_exists(
            &self.shared.symbol_tables, path,
        );
        Ok(ModuleIntroductionOutcome::Blank)
    }

    /// Backwards-compatible alias for the Blank branch only. Kept for callers
    /// that want create-if-absent semantics without inspecting the outcome.
    #[allow(dead_code)]
    pub fn introduce_module_blank(&self, path: &ModuleFullPath) {
        let _ = cranelisp_types::ensure_module_exists(&self.shared.symbol_tables, path);
    }

    /// Cache probe for `introduce_module`'s branch 2. Returns
    /// `Some(decoded_table)` iff cache reports a valid entry with an `.o`
    /// file present. Errors (cache read failures) bubble up as
    /// `CranelispError::Internal` strings; absent entries return `Ok(None)`.
    pub(crate) fn try_load_cached_for_introduction(
        &self,
        path: &ModuleFullPath,
    ) -> Result<Option<cranelisp_types::SymbolTable<Code, ()>>, CranelispError> {
        use cranelisp_backend::cache;
        // Sprint 67 Cluster B sub-fire 3: read cache directory via the
        // ObjectCache facade method (was: locking `shared.cache_state`).
        let cache_dir = match self.shared.cache.cache_dir() {
            Some(d) => d,
            None => return Ok(None),
        };
        let cached = match cache::try_load_cached_module(&cache_dir, path) {
            Ok(Some(c)) => c,
            _ => return Ok(None),
        };
        if !cached.has_object {
            return Ok(None);
        }
        Ok(Some(
            cached.metadata.symbol_table.into_concrete::<Code, ()>(),
        ))
    }

    /// Branch-3 probe: returns the source file path for `module` if one is
    /// known to the session (registered in `file_to_module`'s reverse map).
    pub(crate) fn find_module_source(&self, module: &ModuleFullPath) -> Option<std::path::PathBuf> {
        let guard = self.shared.file_to_module.lock()
            .unwrap_or_else(|e| e.into_inner());
        guard.iter()
            .find_map(|(file, mp)| if mp == module { Some(file.clone()) } else { None })
    }

    /// Resolve a module by name (for /exports command).
    ///
    /// Sprint 67 hack-back (FIXME 0192 method 7): the `TypeCheckEnv` method
    /// was deleted; the body relocated to `cranelisp_types` as a free fn.
    /// The session passes its `current_module_path()` as the scope root
    /// (replacing the prior `state.current_module` access).
    pub(crate) fn resolve_module_by_name(&self, name: &str) -> Option<ModuleFullPath> {
        cranelisp_types::resolve_module_by_name_chain(
            &self.shared.symbol_tables,
            &self.current_module_path(),
            name,
        )
    }

    /// Initialize the file watcher for REPL mode (repl/spec.md §14).
    ///
    /// Creates an OS-level file watcher and registers all currently known
    /// module source files. Call once after `wait_inmem_complete()` so
    /// that `file_to_module` is populated.
    pub fn init_watcher(&mut self) {
        let mut fw = match crate::watch::FileWatcher::new() {
            Some(fw) => fw,
            None => return,
        };

        // Register all source files already loaded (prelude + its deps).
        let file_to_mod = self.shared.file_to_module
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        for path in file_to_mod.keys() {
            fw.watch_file(path);
        }
        drop(file_to_mod);

        self.watcher = Some(fw);
    }

    // -----------------------------------------------------------------------
    // Sprint 67 W3 — Facade-prescribed introspection accessors
    // (FIXME 0176 partial close; `facades/int.md` §"Introspection accessors")
    //
    // Pure read-side projections over `shared.symbol_tables` + `shared.introspection`.
    // No `&mut self` required for reads; the two mutating REPL-state methods
    // (`set_current_repl_module`, `set_repl_input_active`) write to
    // `CompilerSession`-side state per the SharedState alignment plan.
    //
    // Today these forward to the existing slash-command handler internals
    // (`handle_source`, `get_introspection`, etc.); subsequent /dev (int) fires
    // will pivot the slash-command handlers to call these new accessors first
    // so the accessors become the canonical entry points.
    // -----------------------------------------------------------------------

    /// REPL `/source` — original source text of a symbol, or `None` if the
    /// symbol has no introspection record (production batch mode) or no
    /// captured source. Reads `shared.introspection[fq]`.
    pub fn symbol_source(&self, fq: &FQSymbol) -> Option<String> {
        self.shared.introspection.as_ref()
            .and_then(|m| m.get(fq))
            .and_then(|intr| intr.source.clone())
    }

    /// REPL `/sexp` — parsed s-expression of a symbol's defining form, or
    /// `None`. Reads `shared.introspection[fq]`.
    pub fn symbol_sexp(&self, fq: &FQSymbol) -> Option<Sexp> {
        self.shared.introspection.as_ref()
            .and_then(|m| m.get(fq))
            .and_then(|intr| intr.sexp.clone())
    }

    /// REPL `/clif` — CLIF IR text of a symbol's compiled body, or `None`.
    /// Populated only when `CRANELISP_CODEGEN_TRACE` or REPL-trace mode is
    /// active. Reads `shared.introspection[fq]`.
    pub fn symbol_clif(&self, fq: &FQSymbol) -> Option<String> {
        self.shared.introspection.as_ref()
            .and_then(|m| m.get(fq))
            .and_then(|intr| intr.clif_ir.clone())
    }

    /// REPL `/disasm` — disassembled native code of a symbol, or `None`.
    /// Same trace-mode gating as `symbol_clif`. Reads `shared.introspection[fq]`.
    pub fn symbol_disasm(&self, fq: &FQSymbol) -> Option<String> {
        self.shared.introspection.as_ref()
            .and_then(|m| m.get(fq))
            .and_then(|intr| intr.disasm.clone())
    }

}


impl CompilerSession {
    /// REPL `/list` — user-defined symbols in the current REPL module (excludes
    /// imports + special forms). Returns a `Vec<SymbolInfo>` per facade
    /// §"Introspection records".
    pub fn list_user_definitions(&self) -> Vec<SymbolInfo> {
        let current = self.current_module_path();
        let mut out = Vec::new();
        if let Some(table) = self.shared.symbol_tables.get(&current) {
            for (name, entry) in table.all_symbols() {
                // Skip imports / reexports + special forms — those are surfaced
                // by `/imports` separately.
                let (category, scheme, docstring) = match entry {
                    ModuleEntry::Def { scheme, docstring, kind, .. } => {
                        let cat = match kind.as_ref() {
                            DefKind::Constructor { .. } => SymbolCategory::Constructor,
                            DefKind::Macro { .. } => SymbolCategory::Macro,
                            _ => SymbolCategory::Fn,
                        };
                        (cat, Some(scheme.clone()), docstring.clone())
                    }
                    ModuleEntry::TypeDef { .. } =>
                        (SymbolCategory::Type, None, None),
                    ModuleEntry::TraitDecl { docstring, .. } =>
                        (SymbolCategory::Trait, None, docstring.clone()),
                    // Special forms + imports are surfaced by `/imports`.
                    _ => continue,
                };
                out.push(SymbolInfo {
                    name: name.clone(),
                    category,
                    scheme,
                    docstring,
                });
            }
        }
        out
    }

    /// REPL `/imports [MODULE]` — list the import declarations in a target
    /// module. Returns one `ImportSpec` per `ModuleEntry::Import`, carrying
    /// the source module + the local binding name (per
    /// `cranelisp_types::ImportSpec`). Reexports are listed separately by
    /// `module_exports` when the module publishes them.
    ///
    /// Per-binding reconstruction shape: `ModuleEntry::Import` stores only
    /// the source `FQSymbol` per binding; the parse-time `ImportSpec` is not
    /// retained on the symbol table. Each returned spec is therefore a
    /// single-name `Specific([local_name])` against the source module, with
    /// `alias = None` and `span = Span::SYNTHETIC`. Aliased imports (local
    /// != source.symbol) collapse to the local name on the binding side —
    /// the source.symbol distinction is recoverable from the
    /// `module_exports` of the source module. Threading the original
    /// parse-time `ImportSpec` through to here is tracked by FIXME 0194.
    pub fn module_imports(&self, module: &ModuleFullPath) -> Vec<cranelisp_types::ImportSpec> {
        use cranelisp_types::{ImportNames, ImportSpec};
        let mut out = Vec::new();
        if let Some(table) = self.shared.symbol_tables.get(module) {
            for (name, entry) in table.all_symbols() {
                if let ModuleEntry::Import { source, .. } = entry {
                    out.push(ImportSpec {
                        module_path: source.module.clone(),
                        alias: None,
                        names: ImportNames::Specific(vec![name.clone()]),
                        span: Span::SYNTHETIC,
                    });
                }
            }
        }
        out
    }

    /// REPL `/exports MODULE` — list the publicly-visible symbols of a module.
    /// A symbol is public iff its `ModuleEntry` carries `Visibility::Public`
    /// (Def / TypeDef / TraitDecl / Macro / Constructor / Reexport).
    pub fn module_exports(&self, module: &ModuleFullPath) -> Vec<(Symbol, ModuleEntry<Code>)> {
        let mut out = Vec::new();
        if let Some(table) = self.shared.symbol_tables.get(module) {
            for (name, entry) in table.all_symbols() {
                // Uniform per-entry visibility accessor (S70 — covers Def
                // [incl. macro/constructor kinds], TypeDef, TraitDecl,
                // SpecialForm, and public-visibility Import re-export edges).
                if entry.is_public() {
                    out.push((name.clone(), entry.clone()));
                }
            }
        }
        out
    }

    /// Current REPL module (per facade §"CompilerSession.current_repl_module").
    ///
    /// Sprint 67 Cluster B sub-fire 2d: now reads the CompilerSession-owned
    /// field directly (PIF-relocate landed). Returns a `&ModuleFullPath` per
    /// facade L125 — no clone needed at the accessor boundary.
    pub fn current_repl_module(&self) -> &ModuleFullPath {
        &self.current_repl_module
    }

    /// Switch the REPL's active module (per `/mod NAME`). Writes
    /// `shared.current_module` + `shared.test_runner_state.current_module` +
    /// resets `shared.repl_check_state` to a fresh `CheckState` for the new
    /// module.
    pub fn set_current_repl_module(&mut self, module: ModuleFullPath) {
        self.set_current_module(module);
    }

    /// Update the watcher-input-active flag (per exec-flow-repl STEP 1 / STEP 3).
    ///
    /// Sprint 67 Cluster B sub-fire 2c: now writes the
    /// CompilerSession-owned `repl_input_active: Arc<AtomicBool>` field
    /// (PIF-relocate landed). The watcher event handler holds an
    /// `Arc::clone` of this atomic and consults it before triggering
    /// cascade reloads — wiring the watcher to actually consult the flag
    /// is FIXME 0205's broader scope (S68 facade refresh); landing the
    /// field + accessor here is the load-bearing structural change.
    pub fn set_repl_input_active(&self, active: bool) {
        self.repl_input_active.store(active, std::sync::atomic::Ordering::Release);
    }

    /// Accumulated session warnings (per facade L140).
    ///
    /// Sprint 67 Cluster B sub-fire 2c: returns the CompilerSession-owned
    /// `warnings` accumulator. Workers route warnings through this Vec via
    /// the eventual `warnings_mut()` / work-completion merge path
    /// (FIXME 0205); landing the accessor here is the facade method-surface
    /// landing — S68 wires workers without changing this call site.
    pub fn warnings(&self) -> &[Warning] {
        &self.warnings
    }

    /// Mutable accessor for the warnings accumulator. Used by the eventual
    /// worker → session warning merge path; for now the public method
    /// surface is the load-bearing change.
    #[allow(dead_code)]
    pub fn warnings_mut(&mut self) -> &mut Vec<Warning> {
        &mut self.warnings
    }

    /// Register any newly-loaded module source files with the watcher.
    ///
    /// Called after eval/import so that newly discovered modules get watched.
    /// The watcher internally deduplicates already-watched directories.
    pub fn sync_watcher(&mut self) {
        let watcher = match &mut self.watcher {
            Some(w) => w,
            None => return,
        };
        let file_to_mod = self.shared.file_to_module
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        for path in file_to_mod.keys() {
            watcher.watch_file(path);
        }
    }

    /// Poll the file watcher for changed source files and reload them.
    ///
    /// Returns a list of user-visible messages (one per reloaded module).
    /// On success, removes the module from `error_modules`. On failure,
    /// adds it to `error_modules` to block subsequent evals.
    ///
    /// Per repl/spec.md §14: notification format is `[updated: file.cl]`
    /// on success, `[errors: file.cl]` on failure. Cascade invalidation
    /// reloads modules that depend on changed modules.
    pub fn poll_and_reload(&mut self) -> Vec<String> {
        let watcher = match &mut self.watcher {
            Some(w) => w,
            None => return Vec::new(),
        };

        let changed_paths = match watcher.poll_changes() {
            Some(paths) => paths,
            None => return Vec::new(),
        };

        // Map file paths → module paths via SharedState.file_to_module.
        let file_to_mod = self.shared.file_to_module
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let mut modules_to_reload: Vec<(ModuleFullPath, PathBuf)> = Vec::new();
        for path in &changed_paths {
            if let Some(module_path) = file_to_mod.get(path)
                && !modules_to_reload.iter().any(|(mp, _)| mp == module_path) {
                    modules_to_reload.push((module_path.clone(), path.clone()));
                }
        }
        // Cascade invalidation: find modules that import any changed module
        // and add them to the reload list. Sprint 58 Step 5a: read `imports`
        // off the per-module SymbolTable directly (was: parallel
        // `module_structures.import_specs`).
        let changed_modules: HashSet<ModuleFullPath> = modules_to_reload
            .iter()
            .map(|(mp, _)| mp.clone())
            .collect();
        for entry in self.shared.symbol_tables.iter() {
            let dependent_module = entry.key().clone();
            if changed_modules.contains(&dependent_module) {
                continue; // Already being reloaded directly.
            }
            let depends_on_changed = entry.value().imports.iter().any(|spec| {
                let import_mod = ModuleFullPath::from(spec.module_path.as_ref());
                changed_modules.contains(&import_mod)
            });
            if depends_on_changed {
                // Find the file path for this dependent module.
                if let Some(dep_path) = file_to_mod.iter()
                    .find(|(_, mp)| **mp == dependent_module)
                    .map(|(p, _)| p.clone())
                {
                    modules_to_reload.push((dependent_module, dep_path));
                }
            }
        }
        drop(file_to_mod);

        let mut messages = Vec::new();
        for (module_path, file_path) in modules_to_reload {
            // Extract just the filename for the notification message.
            let file_name = file_path.file_name()
                .and_then(|n| n.to_str())
                .unwrap_or_else(|| module_path.as_ref());
            match self.reload_module(&module_path, &file_path) {
                Ok(()) => {
                    self.error_modules.remove(&module_path);
                    messages.push(format!("[updated: {}]", file_name));
                }
                Err(e) => {
                    self.error_modules.insert(module_path.clone());
                    messages.push(format!("[errors: {}]\n  {e}", file_name));
                }
            }
        }
        messages
    }

    /// Regenerate the backing .cl file for the current module.
    ///
    /// Called after successful eval of a definition (defn, deftype, deftrait,
    /// impl, defmacro) or structural change (import, mod, platform).
    /// Reads the current module's symbol table and structural metadata,
    /// generates source text, and writes atomically.
    ///
    /// On write failure, prints a warning and continues — in-memory state
    /// is the ground truth (design/int/session-persistence.md §3.3).
    ///
    /// S78: the former post-write republish into `SharedState::module_sexps`
    /// is gone — that cross-thread parking map is deleted. A persistent worker
    /// only typechecks a module from sexps that ride its scheduler work packet
    /// (`register_module` / `re_register_module`), so there is no shared sexps
    /// entry to keep current and no "no parsed sexps for module" residue to
    /// guard against.
    pub fn regenerate_backing_file(&mut self) {
        let module = self.current_module_path();

        // Get the backing file path from typecheck product.
        let file_path = match self.shared.typecheck_products.get(&module) {
            Some(tp) => match &tp.file_path {
                Some(p) => p.clone(),
                None => {
                    // Entry module may not have a file path yet (fresh session).
                    // Default to {project_root}/{module}.cl.
                    self.shared.project_root.join(format!("{}.cl", module))
                }
            },
            None => self.shared.project_root.join(format!("{}.cl", module)),
        };

        // Read the symbol table for this module. Sprint 58 Step 5a: structural
        // decls (imports/exports/platforms/submodules) are now fields on the
        // SymbolTable itself; no separate read is needed.
        let st = match self.shared.symbol_tables.get(&module) {
            Some(st) => st.clone(),
            None => return, // No symbol table — nothing to save.
        };

        // FIXME 0343: submodule-body-preservation guard. A module whose backing
        // file holds an authored inline `(mod child form…)` block (the ModDecl
        // still carries `inline_body`) MUST NOT be regenerated from the parent's
        // table alone — the child's defns live in the child's table, so regen
        // would emit a bare `(mod child)` and DROP the body from disk (data
        // corruption). Preserve the file verbatim in that case.
        if !crate::save::should_regenerate(&st) {
            return;
        }

        // FIXME 0220 (/arch ruling S81): lazy on-demand introspection
        // rehydration for cache-loaded symbols. A module restored from the
        // compile cache has no REPL-only Introspection records, so a
        // cache-restored `UserFn` would be silently dropped from the
        // regenerated `.cl` (its source rides neither introspection nor
        // `macro_sexp`). Re-read the backing `.cl` (the cache key — always
        // present) and populate the missing UserFn records before regen.
        if let Some(intro) = self.shared.introspection.as_ref()
            && let Ok(backing_source) = std::fs::read_to_string(&file_path)
        {
            crate::save::rehydrate_userfn_introspection_from_source(
                &st,
                intro,
                &module,
                &backing_source,
            );
        }

        // Generate source text.
        let source = crate::save::generate_module_source(
            &st,
            self.shared.introspection.as_ref(),
            &module,
        );

        // Skip writing empty source (no user-defined content).
        if source.trim().is_empty() {
            return;
        }

        // Compute content hash for watcher suppression.
        let hash = cranelisp_backend::cache::manifest::hash_source(&source);

        // Atomic write.
        if let Err(e) = crate::save::atomic_write(&file_path, &source) {
            eprintln!("Warning: failed to save {}: {e}", file_path.display());
            return;
        }

        // Update watcher content hash so the self-write is suppressed
        // (design/int/session-persistence.md §4).
        if let Some(ref mut watcher) = self.watcher {
            let canonical = file_path.canonicalize().unwrap_or_else(|_| file_path.clone());
            watcher.update_content_hash(canonical.clone(), hash);
        }

        // Register the file in file_to_module so the watcher can find it.
        if let Ok(canonical) = file_path.canonicalize() {
            self.shared.file_to_module
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .insert(canonical, module.clone());
        }

        // S78: the former `module_sexps[module]` republish is gone — there is
        // no shared sexps map to keep current. A persistent worker only
        // typechecks `module` from sexps that ride its scheduler work packet
        // (`register_module` / `re_register_module`), and the REPL eval path
        // re-derives from the form it is processing; neither reads a shared
        // map. The H5 "no parsed sexps for module" residue this republish
        // guarded cannot occur (the map it republished into is deleted).
    }

    /// Reload a single module from its source file.
    ///
    /// Clears the module's stale products, re-parses, and re-registers with
    /// the scheduler (the fresh sexps ride the re-register work packet — S78).
    /// The persistent priority workers pick up the re-registration and
    /// re-typecheck + re-codegen. Sprint 57 Wave 4 G11 per
    /// `persistent-workers.md` §4.6 — reload via scheduler falls out of
    /// persistent workers (same path as `register_module_with_source`).
    pub(crate) fn reload_module(
        &mut self,
        module_path: &ModuleFullPath,
        file_path: &Path,
    ) -> Result<(), CranelispError> {
        crate::observability::record_module_event(
            crate::observability::SchedulerTraceTag::RecompileModule,
            module_path.as_ref(),
        );
        let source = std::fs::read_to_string(file_path).map_err(|e| {
            CranelispError::ModuleError {
                message: format!("cannot read {}: {e}", file_path.display()),
                location: ErrorLocation::from_span_file(Span::new(0, 0), Some(file_path.to_path_buf())),
            }
        })?;

        // Remove stale products before recompilation.
        // Sprint 57 Wave 2 G6: `codegen_products` was deleted; compiled code
        // lives on `ModuleEntry::Def.code`. Walk the module's symbols and
        // clear each `code` field so stale pointers are not callable during
        // recompilation. The `Arc<Jit>` handles in `kept_jits` keep the old
        // mmap'd pages alive until the session ends (preserves the Phase-2
        // redefinition policy of "old code stays callable for in-flight
        // calls" — same behaviour as before, just via a different store).
        crate::observability::record_module_event(
            crate::observability::SchedulerTraceTag::ClearModuleState,
            module_path.as_ref(),
        );
        self.shared.typecheck_products.remove(module_path);
        if let Some(mut st) = self.shared.symbol_tables.get_mut(module_path) {
            for entry in st.symbols.values_mut() {
                if let ModuleEntry::Def { code, .. } = entry {
                    *code = None;
                }
            }
        }

        // Parse the new source; the sexps ride the re-register work packet
        // (S78 — no shared `module_sexps` map). Persistent workers parked on
        // the priority-work condvar wake and process it (G11 per §4.6).
        let sexps: std::sync::Arc<[Sexp]> =
            std::sync::Arc::from(cranelisp_frontend::parse(&source)?);

        // S82 reload-during-compile race: a worker sets `inmem_done = true`
        // partway through its codegen pass, BEFORE it reaches
        // `notify_typecheck_done` (the TypecheckWorking → TypecheckDone
        // transition). The initial `register_module_with_source` returns as
        // soon as `wait_inmem_complete_blocking` observes `inmem_done`, so the
        // worker may still be mid-pass when we get here. If it is,
        // `re_register_module` hits its "mid-typecheck — skip" guard, returns
        // false, and the `register_module` fallback below is a no-op (the
        // module already exists) — the reload would be silently dropped and the
        // stale table survives. Wait for the in-flight pass to settle so the
        // re-register reliably takes.
        self.shared.scheduler.wait_module_typecheck_settled(module_path);

        // `re_register_module` clears `inmem_done` and re-queues the module
        // for typecheck with the fresh sexps. `register_module` would be a
        // no-op because the module is already in `scheduler.modules`.
        let re_registered = self.shared.scheduler.re_register_module(module_path, sexps.clone());
        if !re_registered {
            // Module isn't known to the scheduler yet (first-time seed from
            // file watcher) — fall back to register_module.
            self.shared.scheduler.register_module(module_path.clone(), sexps, false);
        }

        // Block until inmem-done for every registered module. The workers
        // do the typecheck + in-memory codegen.
        self.shared.scheduler.wait_inmem_complete_blocking()?;

        // Check if the module ended up in Failed state (wait_inmem_complete_blocking
        // would have returned Err in that case, but double-check explicitly).
        if self.shared.scheduler.is_failed(module_path) {
            return Err(CranelispError::ModuleError {
                message: format!("module '{}' failed to compile", module_path.as_ref()),
                location: ErrorLocation::from_span_file(Span::new(0, 0), None),
            });
        }

        Ok(())
    }

    /// Register a module by name (pipeline-v4.md §3.1).
    ///
    /// Resolves source file, parses, enqueues for typechecking.
    /// TODO: currently runs inline worker loop. Will just enqueue
    /// once persistent workers are wired.
    pub fn register_module(
        &mut self,
        module_name: &str,
    ) -> Result<(), CranelispError> {
        self.register_entry_module(module_name)?;
        Ok(())
    }

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
        Ok(self.shared.scheduler.re_register_module(module, sexps))
    }

    /// Register a module with explicit source (internal + test helpers).
    ///
    /// Parses the source and registers the module with the scheduler (the
    /// sexps ride the work packet — S78); the persistent priority workers
    /// parked on `priority_work_available` wake and process it. The caller
    /// blocks on `wait_inmem_complete_blocking` until every registered module
    /// reaches inmem_done or failure. Sprint 57 Wave 4 G9 per
    /// `persistent-workers.md` §4.3.
    pub fn register_module_with_source(
        &mut self,
        module_name: &str,
        source: &str,
        _entry_module_path: &Path,
    ) -> Result<Vec<Warning>, CranelispError> {
        let module = ModuleFullPath::from(module_name);
        let sexps: std::sync::Arc<[Sexp]> =
            std::sync::Arc::from(cranelisp_frontend::parse(source)?);

        // Record source hash for manifest generation. Sprint 67 Cluster B
        // sub-fire 3: dispatch via the `ObjectCache` facade method.
        {
            let hash = cranelisp_backend::cache::manifest::hash_source(source);
            self.shared.cache.record_source_hash(&module, hash);
        }

        // Register module with scheduler (entry module, not delaying others).
        // The sexps ride the work packet (S78 — no shared `module_sexps` map);
        // a worker that wakes on the scheduler notify reads them off the
        // packet. Wakes parked priority workers via
        // `priority_work_available.notify_all()`.
        self.shared.scheduler.register_module(module.clone(), sexps, false);

        // Block until every registered module reaches inmem_done (or a
        // module fails). The persistent priority workers do the typecheck
        // + in-memory codegen and call `notify_inmem_codegen_complete` /
        // `notify_typecheck_done`, which wakes the scheduler's completion
        // condvar.
        self.shared.scheduler.wait_inmem_complete_blocking()?;

        Ok(Vec::new())
    }




    /// Execute the entry module's main function via the trampoline.
    ///
    /// For the v4 scheduler path: GOT is already populated by the worker
    /// loop. For the old path: flushes codegen queue first.
    ///
    /// Looks up `main` in the GOT, calls it, and runs the IO trampoline
    /// if the return type is IO.
    pub fn trampoline(
        &mut self,
        module_name: &str,
    ) -> Result<(i64, Type), CranelispError> {
        // Enforce the batch-mode signature `(Fn [] (IO _))` before running
        // (spec §10.6 / §12.6). `--run` reaches `main` through this seam (NOT
        // `link_by_name`), so the same `validate_main` gate the `--link` path
        // applies must be applied here — otherwise a bare-`Int`/`Bool` main
        // would be leniently accepted under `--run`. The REPL never calls
        // `trampoline`, so it stays exempt (§10.6.2).
        let module_path = ModuleFullPath::from(module_name);
        if let Some(table) = self.module_table(&module_path) {
            crate::exe::validate_main(&table)?;
        }
        // (If the entry table is absent, the code-ptr lookup below produces the
        // "no `main`" diagnostic — no separate handling needed here.)

        // Look up main's compiled code on its symbol-table entry (G6).
        let main_sym = cranelisp_types::Symbol::from("main");
        let code_ptr = self.lookup_main_code_ptr(module_name, &main_sym)?;
        let result_type = self.lookup_main_return_type(module_name);

        // Clear any stale runtime error.
        let _ = cranelisp_intrinsics::panic::take_runtime_error();

        // Call main.
        // SAFETY: `code_ptr` is non-null — returned from `lookup_main_code_ptr`
        // which errors on None. It points to finalized JIT code compiled by
        // Cranelift via `compile_and_register_defn`. The compiled function uses
        // the `extern "C" fn() -> i64` calling convention (zero-arg defn with
        // i64 return), matching the transmute target type.
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
        let raw_value = func();

        // Check for runtime panics.
        if let Some(err) = cranelisp_intrinsics::panic::take_runtime_error() {
            return Err(CranelispError::CodegenError {
                message: format!("runtime panic: {}", err),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            });
        }

        // IO trampoline.
        if result_type.is_io() {
            let inner_value = cranelisp_intrinsics::run_io_trampoline(raw_value);
            // Decision 24 (consuming convention): `run_io_trampoline` is
            // non-consuming of its input tree. The caller-tree outer nodes
            // (Bind/Pure + continuation closures) must be released via
            // `drop::consume_io_tree` — without this, every batch-mode
            // `(defn main ...)` that returns IO leaks its outer IO nodes.
            // Mirrors the pipeline path's `unwrap_io_inline` in pipeline.rs
            // and the extern `cranelisp_run_io` entry in runtime::io.
            cranelisp_intrinsics::drop::consume_io_tree(raw_value);

            // A platform Effect forced during the trampoline may have faulted
            // under the intrinsics fault guard (FIXME 0327, the dispatch
            // funnel). int composes the structured `PlatformError::DispatchError`
            // from the intrinsics-captured `(fn_name, cause)` slot (BC §4b
            // invariant 14 / §5 invariant 9 — two-layer split).
            if let Some(fault) = cranelisp_intrinsics::panic::take_dispatch_fault() {
                return Err(CranelispError::Platform(
                    cranelisp_types::PlatformError::DispatchError {
                        fn_name: cranelisp_types::Symbol::from(fault.fn_name),
                        cause: fault.cause,
                        location: ErrorLocation::from_span(Span::SYNTHETIC),
                    },
                ));
            }

            let inner_type = result_type.unwrap_io().clone();
            Ok((inner_value, inner_type))
        } else {
            Ok((raw_value, result_type))
        }
    }

    /// Look up the code pointer for `main` on its `ModuleEntry::Def.code`
    /// (Sprint 57 Wave 2 G6 — replaces the deleted `codegen_products` lookup).
    pub(crate) fn lookup_main_code_ptr(
        &self,
        module_name: &str,
        main_sym: &cranelisp_types::Symbol,
    ) -> Result<*const u8, CranelispError> {
        let module_path = ModuleFullPath::from(module_name);

        // GOT is the single source of callable addresses (D41/D35); read
        // `main`'s pointer from its GOT slot rather than a `Code::ptr`.
        // The callable slot now rides on the `DefKind` variant (S83 reshape,
        // FIXME 0356/0357) — read it via the `callable_got_slot()` chokepoint.
        if let Some(table) = self.shared.symbol_tables.get(&module_path)
            && let Some(entry @ ModuleEntry::Def { code: Some(_), .. }) =
                table.get(main_sym.as_ref())
            && let Some(slot) = entry.callable_got_slot()
        {
            let ptr = table.got.load_slot(slot);
            if !ptr.is_null() {
                return Ok(ptr);
            }
        }

        Err(CranelispError::ModuleError {
            message: "entry module has no `main` function — batch mode requires (defn main [] ...)"
                .into(),
            location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
        })
    }

    /// Look up the return type of `main` from the typechecker.
    pub(crate) fn lookup_main_return_type(&self, module_name: &str) -> Type {
        let module_path = ModuleFullPath::from(module_name);
        let main_sym = Symbol::from("main");

        if let Some(table) = self.module_table(&module_path)
            && let Some(cranelisp_types::ModuleEntry::Def { scheme, .. }) =
                table.get(main_sym.as_ref())
            && let Type::Fn(_, ret) = &scheme.ty
        {
            return *ret.clone();
        }
        Type::Int
    }

    /// Wait until all registered modules have object codegen complete.
    ///
    /// Block until all in-memory codegen (JIT) is complete.
    pub fn wait_inmem_complete(
        &self,
    ) -> Result<(), crate::scheduler::SchedulerError> {
        self.shared.scheduler.wait_inmem_complete()
    }

    /// Transfer orchestration ownership of the ENTRY module to the eval thread
    /// (S78 §3 / B1). Called by the REPL driver (`main.rs`) once startup
    /// typecheck has completed and the eval loop is about to take over.
    ///
    /// After this, the eval thread is the entry module's *sole* orchestrator:
    /// a dependency gap the eval thread hits during a REPL form is driven by
    /// the eval thread's own wait+retry (`register_dep_for_eval`), and the
    /// scheduler will NOT requeue the entry onto the pool for a concurrent
    /// re-typecheck of its own sexps. This closes the B1 dual-orchestration —
    /// keyed on the entry module's orchestration role (`eval_owned`), carried
    /// as data on its `ModuleState`, never on the name `"user"`.
    pub fn mark_entry_eval_owned(&self) {
        self.shared.scheduler.mark_eval_owned(&self.entry_module);
    }

    /// Promotes nice workers to normal priority before blocking, ensuring
    /// object codegen completes promptly (e.g., before linking). Wakes
    /// the `object_work_available` condvar so workers observe the promotion
    /// flag on their next loop iteration.
    pub fn wait_object_complete(
        &self,
    ) -> Result<(), crate::scheduler::SchedulerError> {
        // When no nice workers are running (e.g., tests with nice_workers: 0),
        // no .o files will be produced. Skip the wait to avoid blocking
        // forever. Sprint 67 Cluster B sub-fire 2a/2b: nice-worker count
        // read via the `WorkerPool` facade method.
        if self.worker_pool.nice_worker_count() == 0 {
            return Ok(());
        }

        // Promote nice workers so object codegen runs at full speed.
        self.shared.promote_nice_workers.store(
            true,
            std::sync::atomic::Ordering::Release,
        );
        // Wake workers so they observe the promotion flag.
        self.shared.scheduler.wake_object_workers();

        let result = self.shared.scheduler.wait_object_complete();

        // Flush the cache manifest to disk so the next session can detect
        // cache hits. Sprint 67 Cluster B sub-fire 3: ObjectCache facade.
        self.shared.cache.flush_manifest();

        result
    }

    /// Shut down the session: signal workers to drain and exit.
    ///
    /// Sets the scheduler shutdown flag (wakes all condvars) and joins
    /// both the persistent priority and nice worker pools. Workers
    /// observe the shutdown flag via `take_priority_work_blocking` /
    /// `take_object_codegen` returning `None` and exit their loops.
    ///
    /// Idempotent: safe to call twice; the second call joins no
    /// additional handles. Called automatically by `Drop` as a safety net
    /// for tests that never call `shutdown()` explicitly.
    /// Sprint 57 Wave 4 G9 per `persistent-workers.md` §5.2.
    pub fn shutdown(&mut self) {
        self.shared.scheduler.shutdown();
        // Sprint 67 Cluster B sub-fire 2a/2b: join routing migrated through
        // `WorkerPool::shutdown` (the facade method-surface landing). The
        // priority + nice handle drains live inside `WorkerPool`; this call
        // is the load-bearing entry point — S68 may reshape internals
        // freely without changing this call site.
        self.worker_pool.shutdown();
    }

    /// §3.1: Register entry module by name. Session resolves the source
    /// file from project_root + lib_dirs, reads it, and registers with
    /// the scheduler.
    pub fn register_entry_module(
        &mut self,
        module_name: &str,
    ) -> Result<Vec<Warning>, CranelispError> {
        let module = ModuleFullPath::from(module_name);
        // Resolve source file: project_root (tier 2) then lib_dirs (tier 3).
        let lib_dirs = self.lib_dirs();
        let file_path = crate::pipeline::resolve_module_file(&module, &self.shared.project_root, &lib_dirs);
        let (source, entry_path) = match file_path {
            Some(path) => {
                let src = std::fs::read_to_string(&path).unwrap_or_default();
                (src, path)
            }
            None => {
                // No file found — empty module (e.g., fresh REPL).
                let default_path = self.shared.project_root.join(format!("{module_name}.cl"));
                (String::new(), default_path)
            }
        };

        // Register the entry module's own file in file_to_module so the
        // file watcher can detect changes to it (not just its dependencies).
        if let Ok(canonical) = entry_path.canonicalize() {
            self.shared.file_to_module
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .insert(canonical, module);
        }

        self.register_module_with_source(module_name, &source, &entry_path)
    }

    /// §8: Link by module name. Collects .o files produced by nice workers,
    /// generates a startup stub, and invokes the system linker.
    ///
    /// Must be called after `wait_object_complete()` — all .o files must
    /// be ready.
    pub fn link_by_name(
        &mut self,
        module_name: &str,
    ) -> Result<(), CranelispError> {
        let module = ModuleFullPath::from(module_name);

        // Validate main exists and determine return kind (Int vs IO).
        let entry_table = self.module_table(&module).ok_or_else(|| {
            CranelispError::ModuleError {
                message: format!("entry module '{}' not found in typechecker", module_name),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            }
        })?;
        // Enforce the batch-mode signature `(Fn [] (IO _))` (spec §10.6 /
        // §12.6). A valid `main` always returns `IO _` after this gate — the
        // startup stub therefore always trampolines the IO result.
        crate::exe::validate_main(&entry_table)?;
        // Sprint 58 Wave 2 / Decision 36: read the entry module's `main`
        // GOT slot index now (before dropping the table guard). The alias
        // `.o` (emitted below) routes the system linker's `_main` import
        // through this slot via `__cranelisp_got_{entry_module}`.
        let main_got_slot = crate::exe::entry_main_got_slot(&entry_table)?;
        drop(entry_table);

        // Every main accepted by `validate_main` returns `IO _`, so the startup
        // stub always includes the IO trampoline.
        let main_returns_io = true;

        // Collect .o paths from nice workers. Sprint 67 Cluster B sub-fire 3:
        // ObjectCache facade.
        let o_paths = self.shared.cache.all_paths();

        if o_paths.is_empty() {
            return Err(CranelispError::ModuleError {
                message: "no .o files produced — cannot link".into(),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            });
        }

        // Source the platforms the program loaded at compile time (via
        // `(platform "…")` → `load_and_register_platform`, retained on
        // `kept_dlls`) and derive the three `--link` inputs from them
        // (platform-interface.md §7.3): the rlib paths the linker force-loads,
        // the manifest symbol names the startup stub calls, and the per-platform
        // layout-hash checks the startup stub bakes.
        let (platform_manifest_names, platform_rlib_paths, platform_layout_checks) =
            self.linked_platform_link_data()?;

        // Sprint 58 Wave 2 / Decision 36: every user-defined function is
        // declared bare-`Linkage::Local` by `compile_to_module` (no
        // module-qualified naming). The startup stub references the user-main
        // symbol as `Linkage::Import`; the linker resolves it against the alias
        // `.o` we emit below, which exports that symbol and tail-calls through
        // the entry module's GOT.
        //
        // FIXME 0324 (§11.3): the entry-stub and user-main symbol names are
        // host-dependent. macOS keeps `start` / `main` (custom crt-bypassing
        // entry). Linux routes through crt by emitting the stub as C `main`, so
        // the user-main alias is renamed `cranelisp_user_main` to avoid
        // colliding with the C `main`. Both come from `host_entry_symbols()`.
        let (stub_entry_symbol, entry_fn_name) = crate::exe::host_entry_symbols()?;

        // Generate startup .o stub. The per-platform layout-hash checks
        // (platform-interface.md §5.5.4 `--link` gate) are derived above from the
        // linked platforms (`linked_platform_link_data`): for each platform that
        // exported a layout hash, the compiler regenerates the schema from the
        // live `platform.<name>` table and bakes the resulting expected hash, so
        // a stale platform builds but aborts at process start. Empty when no
        // platform is linked (the as-built no-platform path).
        let startup_bytes = crate::exe::generate_startup_object(
            &platform_manifest_names,
            main_returns_io,
            entry_fn_name,
            stub_entry_symbol,
            &platform_layout_checks,
        )?;

        // Sprint 67 Cluster B sub-fire 3: cache dir via ObjectCache facade.
        let cache_dir = self.shared.cache.cache_dir().ok_or_else(|| {
            CranelispError::ModuleError {
                message: "cache directory not configured — cannot write startup .o".into(),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            }
        })?;
        let startup_o_path = cache_dir.join("__startup.o");
        std::fs::write(&startup_o_path, &startup_bytes).map_err(|e| {
            CranelispError::ModuleError {
                message: format!("failed to write startup .o: {e}"),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, Some(startup_o_path.clone())),
            }
        })?;

        // Sprint 58 Wave 2 / Decision 36 `--link` exception: emit the
        // `_main` Export alias `.o` that tail-calls into the entry
        // module's GOT slot for `main`. Without this alias the system
        // linker has no `_main` symbol to resolve (the entry module's
        // bare `main` is `Linkage::Local`), and link fails with
        // "undefined symbol _main".
        let alias_bytes =
            crate::exe::generate_main_alias_object(&module, main_got_slot, entry_fn_name)?;
        let alias_o_path = cache_dir.join("__main_alias.o");
        std::fs::write(&alias_o_path, &alias_bytes).map_err(|e| {
            CranelispError::ModuleError {
                message: format!("failed to write main alias .o: {e}"),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, Some(alias_o_path.clone())),
            }
        })?;

        // Find the runtime bundle library.
        let bundle_lib = crate::exe::find_bundle_lib()?;

        // Output path: entry module stem in CWD (not project root).
        // E.g., `cranelisp --link examples/hello.cl` produces `./hello`.
        let output_path = PathBuf::from(module_name.replace(".cl", ""));

        // Compose the final .o list: nice-worker module .o files +
        // the `_main` alias .o. The alias is appended last so its Export
        // `_main` resolves the startup stub's Import.
        let mut all_o_paths = o_paths;
        all_o_paths.push(alias_o_path);

        // Link.
        crate::exe::link_executable(
            &output_path,
            &all_o_paths,
            &startup_o_path,
            &bundle_lib,
            &platform_rlib_paths,
        )
    }

    /// Derive the three `--link` platform inputs from the loaded-platform
    /// registry (`SharedState::kept_dlls`) — platform-interface.md §7.3.
    ///
    /// Each `(platform "<name>")` declaration in the entry program loaded a DLL
    /// at compile time, retained on `kept_dlls`. For the standalone binary the
    /// linker must statically link those platforms instead. Returns, in order:
    ///
    /// - **manifest names** — the symbol the startup stub calls to populate each
    ///   platform's GOT (`collect_platform_manifest_names`);
    /// - **rlib paths** — the static archives the linker `-force_load`s
    ///   (`find_platform_rlibs`), so the platform's `#[export_name]` GOT +
    ///   manifest + layout-hash symbols resolve in the produced binary;
    /// - **layout-hash checks** — for each platform that exported a layout hash
    ///   (i.e. marshals ADTs), the compiler regenerates the schema from the live
    ///   `platform.<name>` table (the same backend generator the load-time gate
    ///   runs) and bakes the expected hash into the startup stub, so a stale
    ///   statically-linked platform aborts at process start (§5.5.4 `--link`
    ///   gate).
    pub(crate) fn linked_platform_link_data(
        &self,
    ) -> Result<
        (
            Vec<String>,
            Vec<PathBuf>,
            Vec<cranelisp_backend::exe::PlatformLayoutCheck>,
        ),
        CranelispError,
    > {
        let platform_names: Vec<String> = {
            let guard = self
                .shared
                .kept_dlls
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            guard.iter().map(|p| p.name.clone()).collect()
        };

        let manifest_names =
            crate::exe::collect_platform_manifest_names(platform_names.len());

        let rlib_paths = crate::exe::find_platform_rlibs(
            &platform_names,
            &self.shared.project_root,
            &self.lib_dirs(),
            &self.platform_dirs(),
        )?;

        // Per-platform layout-hash checks: only for platforms that exported a
        // layout hash. The expected hash is regenerated from the live tables (NOT
        // read from the DLL) — the `--link` gate compares the compiler's
        // freshly-computed hash against the statically-linked
        // `__cranelisp_layout_hash_<name>`, so a drifted platform refuses.
        let mut layout_checks = Vec::new();
        {
            let guard = self
                .shared
                .kept_dlls
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            for platform in guard.iter() {
                if platform.layout_hash.is_none() {
                    // Scalar-only platform (no ADTs) exports no hash — no gate.
                    continue;
                }
                let module_path =
                    ModuleFullPath::from(format!("platform.{}", platform.name));
                let roots = self
                    .shared
                    .symbol_tables
                    .get(&module_path)
                    .map(|t| cranelisp_backend::schema::platform_effect_roots(&t))
                    .unwrap_or_default();
                let expected_hash = cranelisp_backend::schema::compute_layout_hash(
                    &self.shared.symbol_tables,
                    &roots,
                );
                layout_checks.push(cranelisp_backend::exe::PlatformLayoutCheck {
                    name: platform.name.clone(),
                    expected_hash,
                });
            }
        }

        Ok((manifest_names, rlib_paths, layout_checks))
    }

}

pub(crate) fn extract_def_name_from_sexp(sexp: &Sexp) -> Option<String> {
    if let Sexp::List(items, _) = sexp
        && items.len() >= 2
            && let Sexp::Symbol(head, _) = &items[0] {
                match head.as_str() {
                    "defmacro" => {
                        if let Sexp::Symbol(name, _) = &items[1] {
                            return Some(name.to_string());
                        }
                    }
                    "import" | "platform" | "mod" => {
                        // These don't define a named symbol in the usual sense.
                        return None;
                    }
                    _ => {}
                }
            }
    None
}

impl Drop for CompilerSession {
    fn drop(&mut self) {
        // Defensive: ensure workers are signalled and joined before this
        // session is destroyed. Prevents hangs (and mmap'd JIT pages going
        // out of scope while a worker still dereferences them) if the
        // session is dropped without an explicit `shutdown()` call — e.g.
        // during test teardown or panic unwinding. Sprint 57 Wave 4 G9
        // per `persistent-workers.md` §5.2.
        //
        // `shutdown()` is idempotent; calling it in Drop is safe even if
        // the caller already called it.
        self.shutdown();
    }
}

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
fn nice_worker_loop(shared: &SharedState) {
    // Set below-normal OS scheduling priority (best-effort).
    crate::thread_util::set_nice_priority();

    loop {
        // Check for priority promotion (hot flush before --link).
        if shared.promote_nice_workers.load(
            std::sync::atomic::Ordering::Relaxed,
        ) {
            crate::thread_util::set_normal_priority();
        }

        // Park until a TypecheckDone module with object_done == false
        // is available, or shutdown is signaled.
        let module = match shared.scheduler.take_object_codegen() {
            Some(m) => m,
            None => {
                // Observability: publish this nice-worker thread's
                // scheduler-trace ring buffer so the main thread's
                // `flush_to_stderr` can merge it into the dump
                // (design/int/observability.md §7). No-op when disabled.
                crate::observability::publish_thread_buffer();
                // GOT trace events (FIXME 0099) — nice workers also emit
                // GOT events (LinkerWrite during cache-hit load).
                crate::got_trace::publish_thread_buffer();
                return; // Shutdown signaled.
            }
        };

        // Attempt .o compilation if caching is enabled. Sprint 67 Cluster B
        // sub-fire 3: cache dir via ObjectCache facade.
        if let Some(cache_dir) = shared.cache.cache_dir() {
            compile_module_object(shared, &module, &cache_dir);
        }

        // Notify scheduler that object codegen is done for this module.
        shared.scheduler.notify_object_codegen_complete(&module);
    }
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
fn compile_module_object(
    shared: &SharedState,
    module: &ModuleFullPath,
    cache_dir: &Path,
) {
    use cranelisp_backend::cache;

    // Enumerate codegen-compilable symbols via the shared predicate (Decision 22).
    // Empty result → no compilable defns (types-only, imports-only) → skip.
    let names: Vec<cranelisp_types::Symbol> = shared
        .symbol_tables
        .get(module)
        .map(|t| {
            t.defined_symbols()
                .map(|(name, _)| name.clone())
                .collect()
        })
        .unwrap_or_default();
    if names.is_empty() {
        return;
    }

    // Build ObjectModule with PIC ISA.
    let isa = match cranelisp_backend::build_isa(true) {
        Ok(isa) => isa,
        Err(e) => {
            if std::env::var("CRANELISP_CODEGEN_TRACE").is_ok() {
                eprintln!("nice-worker: ISA build failed for {}: {}", module, e.message());
            }
            return;
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
            return;
        }
    };
    let mut obj_module = cranelisp_backend::cranelift_object::ObjectModule::new(obj_builder);

    // Compile using the unified compile_to_module path. Intrinsics are declared
    // on the module internally; cross-module refs resolve from `symbol_tables`.
    let obj_bytes = match cranelisp_backend::compile_to_module(
        module.clone(),
        &names,
        &shared.symbol_tables,
        &shared.module_aliases,
        &mut obj_module,
        // FIXME 0325: nice-worker `.o` codegen is always batch (cache-write
        // side) — never consumed by introspection, so skip CLIF rendering.
        false,
    ) {
        Ok(_result) => {
            // Emit .o bytes from the ObjectModule.
            match obj_module.finish().emit() {
                Ok(bytes) => bytes,
                Err(e) => {
                    if std::env::var("CRANELISP_CODEGEN_TRACE").is_ok() {
                        eprintln!("nice-worker: .o emit failed for {}: {e}", module);
                    }
                    return;
                }
            }
        }
        Err(e) => {
            // Log .o compilation errors only when CRANELISP_CODEGEN_TRACE is set.
            // These are non-fatal (in-memory compilation may have succeeded).
            if std::env::var("CRANELISP_CODEGEN_TRACE").is_ok() {
                eprintln!("nice-worker: .o compilation failed for {}: {}", module, e);
            }
            return;
        }
    };

    // Write .o and .meta.json files to cache directory.
    let (meta_path, o_path) = cache::module_cache_path(cache_dir, module);

    // Ensure parent directory exists.
    if let Some(parent) = o_path.parent()
        && let Err(e) = std::fs::create_dir_all(parent)
    {
        eprintln!("nice-worker: cannot create cache dir '{}': {}", parent.display(), e);
        return;
    }

    if let Err(e) = std::fs::write(&o_path, &obj_bytes) {
        eprintln!("nice-worker: cannot write '{}': {}", o_path.display(), e);
        return;
    }

    // Write .meta.json for cache-hit restoration via the unified
    // `cache::write_meta` API (Sprint 58 Step 5b / Decision 33+34).
    // The .meta.json IS a serialised SymbolTable; `write_meta` stamps
    // `schema_version = CACHE_SCHEMA_VERSION` on the cloned table before
    // serialising. Per Decision 33, structural decls
    // (imports/exports/platforms/submodules) are now fields on the
    // SymbolTable itself — the worker form-handlers populate them in
    // `process_module_forms`, so the serialised table carries the
    // user-authored structural specifications inline (no separate
    // `dependencies` envelope needed; cache-hit derives transitive deps from
    // `imports` directly).
    let symbol_table = shared.symbol_tables
        .get(module)
        .map(|guard| guard.clone())
        .unwrap_or_else(|| crate::code::SessionSymbolTable::new_with_params(module.clone()));

    if let Err(e) = cache::serialize::write_meta(&meta_path, &symbol_table, cache::CACHE_SCHEMA_VERSION) {
        eprintln!("nice-worker: .meta.json write failed for {}: {}", module, e.message());
        // Continue — the .o file was written successfully.
    }

    // Record module in manifest for cache-hit detection on next session.
    // Sprint 67 Cluster B sub-fire 3: ObjectCache facade — `source_hash` +
    // `record_compiled` replace the manual cache_state lock + record_module.
    {
        let source_hash = shared.cache.source_hash(module).unwrap_or_default();
        // dep_hashes: empty for now — full dependency tracking is a future enhancement.
        shared.cache.record_compiled(module, source_hash, std::collections::HashMap::new());
    }

    // Append the .o path for the linker. Sprint 67 Cluster B sub-fire 3:
    // ObjectCache facade.
    shared.cache.append_o_path(o_path);
}

// ---------------------------------------------------------------------------
// Trace format support (repl/spec.md §4.12)
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Test infrastructure: core logic + JIT-callable externs
// ---------------------------------------------------------------------------

/// Result of running a single test (Rust-side, no heap allocation). Consumed by
/// the `/run-tests` slash-command formatter (`format_test_run`); the test name
/// is held by the caller (the FQ name being run) so it is not duplicated here.
pub(crate) enum TestOutcome {
    Pass,
    Fail { reason: String },
    Panic { reason: String },
}

/// Core: discover test-* function names in a module. No heap allocation.
///
/// Returns fully-qualified names ("module/test-name") sorted alphabetically.
///
/// Sprint 57 Wave 2 G6: reads `ModuleEntry::Def.code` (replaces the deleted
/// `CodegenProduct` DashMap).
pub(crate) fn discover_test_names(
    tc_modules: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    module: &ModuleFullPath,
) -> Vec<String> {
    let mut names = Vec::new();
    let symbols = match tc_modules.get(module) {
        Some(st) => st,
        None => return names,
    };
    for (name, entry) in symbols.all_symbols() {
        if !name.as_ref().starts_with("test-") {
            continue;
        }
        // The callable slot rides on the `DefKind` variant (S83 reshape,
        // FIXME 0356/0357) — read it via the `callable_got_slot()` chokepoint.
        match entry {
            ModuleEntry::Def {
                param_names,
                code: Some(_),
                ..
            } if param_names.is_empty()
                && entry
                    .callable_got_slot()
                    .is_some_and(|slot| !symbols.got.load_slot(slot).is_null()) =>
            {
                names.push(format!("{}/{}", module.as_ref(), name.as_ref()));
            }
            _ => continue,
        }
    }
    names.sort();
    names
}

/// Core: run a single test by fully-qualified name. No heap allocation.
///
/// Looks up the code pointer, calls it, interprets the (Option String) result.
///
/// Sprint 57 Wave 2 G6: reads `ModuleEntry::Def.code` (replaces the deleted
/// `CodegenProduct` DashMap).
pub(crate) fn run_test_by_name(
    tc_modules: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    fq_name: &str,
    default_module: &ModuleFullPath,
) -> TestOutcome {
    use cranelisp_types::NULLARY_TAG_THRESHOLD;

    // Parse "module/name" into module path and bare name. S78 §1.4: an
    // unqualified name defaults to the current/entry module, NOT a hardcoded
    // "user" — for a non-`user` entry program a hardcoded "user" mis-routes
    // the lookup to a non-existent table.
    let (module, bare_name) = match fq_name.rsplit_once('/') {
        Some((m, n)) => (ModuleFullPath::from(m), n),
        None => (default_module.clone(), fq_name),
    };

    // Look up the code pointer from the entry's GOT slot (D41/D35 — GOT is
    // the single source of callable addresses; no `Code::ptr`).
    let code_ptr = tc_modules.get(&module).and_then(|t| {
        // The callable slot rides on the `DefKind` variant (S83 reshape,
        // FIXME 0356/0357) — read it via the `callable_got_slot()` chokepoint.
        let entry = t.get(bare_name)?;
        let ModuleEntry::Def { code: Some(_), .. } = entry else {
            return None;
        };
        let slot = entry.callable_got_slot()?;
        let ptr = t.got.load_slot(slot);
        if ptr.is_null() {
            None
        } else {
            Some(ptr)
        }
    });

    let code_ptr = match code_ptr {
        Some(ptr) if !ptr.is_null() => ptr,
        _ => return TestOutcome::Fail {
            reason: "test function not found".to_string(),
        },
    };

    // Call the test function.
    let _ = cranelisp_intrinsics::panic::take_runtime_error();
    let value = unsafe {
        let func: extern "C" fn() -> i64 = std::mem::transmute(code_ptr);
        func()
    };

    if let Some(msg) = cranelisp_intrinsics::panic::take_runtime_error() {
        return TestOutcome::Panic { reason: msg };
    }

    if (value as usize) < NULLARY_TAG_THRESHOLD {
        TestOutcome::Pass
    } else {
        let reason = unsafe {
            let base = value as *const u8;
            let string_ptr = *(base.add(
                cranelisp_backend::heap::HeapAdt::field_offset(0) as usize,
            ) as *const i64);
            cranelisp_intrinsics::heap_string::read_string_as_str(string_ptr).to_string()
        };
        TestOutcome::Fail { reason }
    }
}

/// Session state for the `run-test` / `discover-tests` intrinsics.
///
/// Sprint 66 Wave 3a-γ: lifted from per-compilation construction to
/// session-wide construction (built once in `CompilerSession::new`, stored on
/// `SharedState`). The thread-local `TEST_RUNNER` cell holds a pointer derived
/// from `SharedState.test_runner_state` (a `Box`, so the address is stable for
/// the session lifetime); the REPL eval path sets it before invoking a
/// compiled expression. The `current_module` field is a `Mutex` so the REPL
/// `/mod` command may update it without re-allocating the state.
///
/// The intrinsics themselves dereference these pointers when JIT-emitted code
/// invokes `run-test` / `discover-tests` — see `run_test_extern` /
/// `discover_tests_extern` below. The state is only meaningful inside an
/// active REPL eval; absent that, the intrinsics return harmless empty
/// results (mirrors the prior null-pointer-guard behaviour).
pub struct TestRunnerState {
    /// TC modules for scanning symbol tables and reading compiled `code`.
    tc_modules: *const dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    /// Current module path (for discover-tests with empty module arg).
    /// Updated by `set_current_module` when the REPL `/mod` command switches.
    current_module: Mutex<ModuleFullPath>,
}

// Safety: the pointer-typed `tc_modules` field is read-only data; it points
// at a `DashMap` (itself Send + Sync) inside the same `SharedState` instance.
// `Mutex<ModuleFullPath>` is Send + Sync. The thread-local-pointer access is
// always read-via-Cell on the thread that called `set_test_runner_state`.
unsafe impl Send for TestRunnerState {}
unsafe impl Sync for TestRunnerState {}

impl TestRunnerState {
    /// Construct a stub TestRunnerState for unit tests that need to build a
    /// `SharedState` but don't exercise the test intrinsics. The
    /// `tc_modules` pointer is null; any extern call against this state
    /// returns the harmless null-pointer fallback (empty list / `?` name).
    pub fn stub() -> Self {
        Self {
            tc_modules: std::ptr::null(),
            current_module: Mutex::new(ModuleFullPath::from("user")),
        }
    }
}

thread_local! {
    static TEST_RUNNER: std::cell::Cell<*const TestRunnerState> =
        const { std::cell::Cell::new(std::ptr::null()) };
}

pub(crate) fn set_test_runner_state(state: &TestRunnerState) {
    TEST_RUNNER.with(|c| c.set(state as *const _));
}

// `int_intrinsics()` + `run_test_extern` + the SList/IO/TestResult marshalling
// helpers DELETED (S76 FIXME 0271). `run-test` is subsumed — running a test is
// invoking a discovered late-bound wrapper under `catch-runtime-error`. The
// surviving `discover-tests` extern is host-promised via `Jit::define_symbol`
// (registered in `worker::build_session_jit`), not a parked-table entry. The
// trace half of the old table left earlier (FIXME 0256); the table is now gone.

/// Allocate a heap ADT with the given tag and fields.
///
/// Layout: [alloc_size(8) | rc=1(8) | tag(8) | field0(8) | field1(8) | ...]
/// (mirrors `HeapAdt` in `cranelisp-backend::heap`). Returns the base pointer.
unsafe fn alloc_heap_adt(tag: i64, fields: &[i64]) -> i64 { unsafe {
    let payload_size = 8 + fields.len() * 8; // tag + fields
    let base = cranelisp_intrinsics::alloc::alloc_with_rc(payload_size);
    // Tag at offset 16 (HeapHeader::SIZE).
    *(base.add(16) as *mut i64) = tag;
    // Fields at offsets 24, 32, 40, ...
    for (i, &field) in fields.iter().enumerate() {
        *(base.add(24 + i * 8) as *mut i64) = field;
    }
    base as i64
}}

/// The late-bound test-wrapper closure body — `extern "C" fn(env_ptr) -> i64`.
///
/// The closure layout is `[header(16) | code_ptr=this(8) | drop_glue=0(8) |
/// slot_addr(8)]` (a `HeapClosure` with one capture). The single capture is the
/// **address of the test's GOT slot** (`GotTable::base_ptr() + slot*8`), which
/// is stable for the module's lifetime; its *contents* are the test's current
/// code pointer (updated in place on redefinition). So the wrapper:
///
/// 1. loads the captured slot-address from the closure env (capture offset 0 =
///    base + 32);
/// 2. loads the current code pointer from that slot-address (late-binding — a
///    redefined test runs its new body through the same wrapper);
/// 3. calls `extern "C" fn() -> i64` and returns the `(Option String)` result.
///
/// A null slot (test not yet compiled) returns the sentinel `0` (`None`).
extern "C" fn discovered_test_wrapper(env_ptr: i64) -> i64 {
    if env_ptr == 0 {
        return 0;
    }
    unsafe {
        // capture[0] at offset 32 (HeapClosure::CAPTURES_START).
        let slot_addr = *((env_ptr as *const u8).add(32) as *const i64);
        if slot_addr == 0 {
            return 0;
        }
        let code_ptr = (slot_addr as *const *const u8).read();
        if code_ptr.is_null() {
            return 0;
        }
        let func: extern "C" fn() -> i64 = std::mem::transmute(code_ptr);
        func()
    }
}

/// Allocate a late-bound test-wrapper closure capturing `slot_addr` (the stable
/// address of the test's GOT slot). Layout matches a zero-capture-shape
/// `compile_lambda` closure with one capture, so the language sees it as an
/// ordinary `(Fn [] (Option String))` value.
unsafe fn alloc_test_wrapper_closure(slot_addr: i64) -> i64 { unsafe {
    // payload = code_ptr(8) + drop_glue_ptr(8) + 1 capture(8) = 24 bytes.
    let base = cranelisp_intrinsics::alloc::alloc_with_rc(24);
    *(base.add(16) as *mut i64) = discovered_test_wrapper as *const u8 as i64; // code_ptr
    *(base.add(24) as *mut i64) = 0; // drop_glue_ptr (no heap captures)
    *(base.add(32) as *mut i64) = slot_addr; // capture[0] = GOT slot address
    base as i64
}}

/// An eligible test discovered for the fn-value return: the FQ name and the
/// stable address of its GOT slot (for the late-bound wrapper capture).
struct EligibleTest {
    fq_name: String,
    slot_addr: i64,
}

/// Scan a module for eligible `test-*` fns: prefix `test-` AND the EXACT scheme
/// `(Fn [] (Option String))` (test-discovery.md q-eligibility). A mis-typed
/// `test-*` is excluded; the warning is surfaced at the REPL/`--run` boundary
/// (the extern runs in compiled code and cannot push a Warning, so the warn is
/// the slash-command path's concern — here we silently exclude).
///
/// Returns the eligible tests sorted by FQ name. The slot address is
/// `got.base_ptr() + slot*8` — stable for the module lifetime, contents updated
/// in place on redefinition (late binding).
fn discover_eligible_tests(
    tc_modules: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    module: &ModuleFullPath,
) -> Vec<EligibleTest> {
    let mut out = Vec::new();
    let Some(symbols) = tc_modules.get(module) else {
        return out;
    };
    let got_base = symbols.got.base_ptr() as i64;
    for (name, entry) in symbols.all_symbols() {
        if !name.as_ref().starts_with("test-") {
            continue;
        }
        // The callable slot rides on the `DefKind` variant (S83 reshape,
        // FIXME 0356/0357) — read it via the `callable_got_slot()` chokepoint.
        let ModuleEntry::Def { scheme, .. } = entry else {
            continue;
        };
        let Some(slot) = entry.callable_got_slot() else {
            continue;
        };
        if !test_scheme_is_eligible(scheme) {
            continue; // mis-typed test-* — excluded (q-eligibility).
        }
        out.push(EligibleTest {
            fq_name: format!("{}/{}", module.as_ref(), name.as_ref()),
            // slot address = base + slot * size_of::<AtomicPtr<u8>>() (8).
            slot_addr: got_base + (slot as i64) * 8,
        });
    }
    out.sort_by(|a, b| a.fq_name.cmp(&b.fq_name));
    out
}


/// True iff `scheme` is exactly `(Fn [] (Option String))` — zero-arg returning
/// `(Option String)` (test-discovery.md q-eligibility). Quantified vars are
/// permitted only if they do not appear (a monomorphic test); the structural
/// shape is what matters.
fn test_scheme_is_eligible(scheme: &cranelisp_types::Scheme) -> bool {
    let cranelisp_types::Type::Fn(params, ret) = &scheme.ty else {
        return false;
    };
    if !params.is_empty() {
        return false;
    }
    let cranelisp_types::Type::ADT(fqtn, args) = ret.as_ref() else {
        return false;
    };
    fqtn.name.as_ref() == "Option"
        && fqtn.module.as_ref() == "primitives"
        && args.len() == 1
        && matches!(args[0], cranelisp_types::Type::String)
}

#[cfg(test)]
mod discover_tests_extern_tests {
    use super::*;
    use cranelisp_types::{FQTypeName, ModuleFullPath, Scheme, Type, TypeName};
    use std::collections::HashMap;

    fn option_string() -> Type {
        Type::ADT(
            FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Option")),
            vec![Type::String],
        )
    }

    fn mono_scheme(ty: Type) -> Scheme {
        Scheme { type_vars: vec![], constraints: HashMap::new(), ty }
    }

    // spec: design/arch/test-discovery.md §5 — eligibility = test- prefix AND
    // the EXACT scheme (Fn [] (Option String)).
    #[test]
    fn eligible_only_for_exact_zero_arg_option_string() {
        // The exact eligible shape.
        assert!(test_scheme_is_eligible(&mono_scheme(Type::Fn(
            vec![],
            Box::new(option_string())
        ))));
        // Wrong arity (one param) — excluded.
        assert!(!test_scheme_is_eligible(&mono_scheme(Type::Fn(
            vec![Type::Int],
            Box::new(option_string())
        ))));
        // Wrong return (Option Int) — excluded.
        assert!(!test_scheme_is_eligible(&mono_scheme(Type::Fn(
            vec![],
            Box::new(Type::ADT(
                FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Option")),
                vec![Type::Int],
            )),
        ))));
        // Not a function (a value) — excluded.
        assert!(!test_scheme_is_eligible(&mono_scheme(Type::Int)));
    }

    // spec: design/arch/test-discovery.md §6 — the wrapper closure reads its
    // captured GOT-slot address and indirects to the current code pointer.
    #[test]
    fn wrapper_indirects_through_captured_slot_and_is_late_bound() {
        // Stand up a slot (an AtomicPtr-shaped i64 cell) holding a code pointer.
        extern "C" fn test_a() -> i64 { 0 }   // None (pass)
        extern "C" fn test_b() -> i64 { 12345 } // some heap ptr sentinel

        let mut slot: i64 = test_a as *const u8 as i64;
        let slot_addr = (&raw mut slot) as i64;

        let closure = unsafe { alloc_test_wrapper_closure(slot_addr) };
        // The closure's code_ptr is the wrapper; capture[0] is the slot address.
        unsafe {
            assert_eq!(
                *((closure as *const u8).add(16) as *const i64),
                discovered_test_wrapper as *const u8 as i64
            );
            assert_eq!(*((closure as *const u8).add(32) as *const i64), slot_addr);
        }

        // Invoke the wrapper: indirects through the slot to test_a → 0.
        assert_eq!(discovered_test_wrapper(closure), 0);

        // Late binding: redefine the slot's contents (write THROUGH the slot
        // address, exactly as a redefinition's GOT store would) → the wrapper
        // runs the new body. Writing via the pointer (not the local) is also
        // what the wrapper reads, so there is no dead-store.
        unsafe { *(slot_addr as *mut i64) = test_b as *const u8 as i64; }
        assert_eq!(discovered_test_wrapper(closure), 12345);

        // Null env / null slot guard.
        assert_eq!(discovered_test_wrapper(0), 0);
    }

    // spec: design/arch/test-discovery.md §6 — null TEST_RUNNER → empty Vec.
    #[test]
    fn extern_returns_empty_vec_when_no_session() {
        // No TEST_RUNNER set on this thread.
        let v = discover_tests_extern(0);
        assert_ne!(v, 0, "should return a heap (Vec ...), even if empty");
        // len field at offset 16 must be 0.
        let len = unsafe { *((v as *const u8).add(16) as *const i64) };
        assert_eq!(len, 0);
    }
}

/// JIT-callable host-promised extern: discover eligible test functions across
/// the given module paths and return fn-value pairs.
///
/// Argument: a heap `(Vec String)` of module paths (the no-arg / single-String
/// sugar shapes are normalised to this by the stdlib macro — FIXME 0273). A
/// null/absent arg falls back to the current module.
///
/// Returns a heap `(Vec (Pair String (Fn [] (Option String))))`: each pair is a
/// heap `Pair` ADT (tag 0, fields `[name_string, callable_closure]`); the
/// callable is a late-bound wrapper closure (see `discovered_test_wrapper`).
///
/// Registered as `discover-tests` via `Jit::define_symbol` in
/// `worker::build_session_jit` (`DefKind::PrimitiveExtern`, test-discovery.md §6).
pub(crate) extern "C" fn discover_tests_extern(modules_vec: i64) -> i64 {
    TEST_RUNNER.with(|c| {
        let state_ptr = c.get();
        if state_ptr.is_null() {
            return unsafe { alloc_empty_vec() };
        }
        let state = unsafe { &*state_ptr };
        let tc_modules = unsafe { &*state.tc_modules };

        // Decode the (Vec String) argument into module paths. A null/empty Vec
        // falls back to the current module.
        let module_paths = unsafe { read_module_paths(modules_vec) };
        let module_paths = if module_paths.is_empty() {
            vec![state
                .current_module
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .clone()]
        } else {
            module_paths
        };

        // Union the eligible tests across the named modules.
        let mut eligible: Vec<EligibleTest> = Vec::new();
        for module in &module_paths {
            eligible.extend(discover_eligible_tests(tc_modules, module));
        }

        // Build the (Vec (Pair String callable)).
        let pair_ptrs: Vec<i64> = eligible
            .into_iter()
            .map(|t| unsafe {
                let name_str =
                    cranelisp_intrinsics::heap_string::alloc_string(t.fq_name.as_bytes()) as i64;
                let callable = alloc_test_wrapper_closure(t.slot_addr);
                // Pair ctor tag=0, fields [first=name, second=callable].
                alloc_heap_adt(0, &[name_str, callable])
            })
            .collect();
        unsafe { alloc_vec_from(&pair_ptrs) }
    })
}

/// Read a heap `(Vec String)` into owned `ModuleFullPath`s. A null pointer or a
/// zero-length vec yields an empty list.
unsafe fn read_module_paths(vec_ptr: i64) -> Vec<ModuleFullPath> { unsafe {
    if vec_ptr == 0 {
        return Vec::new();
    }
    // HeapVec layout: [header(16) | len(8)@16 | cap(8)@24 | data_ptr(8)@32].
    let base = vec_ptr as *const u8;
    let len = *(base.add(16) as *const i64);
    let data_ptr = *(base.add(32) as *const i64) as *const i64;
    if len <= 0 || data_ptr.is_null() {
        return Vec::new();
    }
    let mut out = Vec::with_capacity(len as usize);
    for i in 0..len as usize {
        let elem = *data_ptr.add(i); // heap String pointer
        if elem == 0 {
            continue;
        }
        let s = cranelisp_intrinsics::heap_string::read_string_as_str(elem);
        out.push(ModuleFullPath::from(s));
    }
    out
}}

/// Allocate an empty heap `Vec` (len=0, cap=0, data_ptr=null) via the runtime
/// `vec_new` so the layout + data-buffer allocation convention match exactly
/// what backend codegen and `vec_drop` expect.
unsafe fn alloc_empty_vec() -> i64 {
    cranelisp_intrinsics::vec_runtime::vec_new(0)
}

/// Allocate a heap `Vec` whose elements are the given i64 values, using the
/// runtime `vec_new(cap)` (which allocates the data buffer with the canonical
/// convention — a raw buffer pointed at by `data_ptr`) and then writing the
/// elements + len directly. This keeps the buffer reclaimable by `vec_drop`.
unsafe fn alloc_vec_from(elems: &[i64]) -> i64 { unsafe {
    let n = elems.len();
    let base = cranelisp_intrinsics::vec_runtime::vec_new(n as i64) as *mut u8;
    if n == 0 {
        return base as i64;
    }
    // HeapVec: len@16, cap@24, data_ptr@32; data buffer holds `cap` i64 slots.
    let data_ptr = *(base.add(32) as *const i64) as *mut i64;
    for (i, &e) in elems.iter().enumerate() {
        *data_ptr.add(i) = e;
    }
    *(base.add(16) as *mut i64) = n as i64; // len
    base as i64
}}

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
mod persistent_worker_tests {
    use super::*;

    fn test_session(priority_workers: usize) -> (CompilerSession, PathBuf) {
        // Use a unique temp dir per call as project_root so no stray
        // prelude.cl is found. The caller is responsible for removing
        // the dir after the test (or letting the OS reclaim /tmp).
        let stamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let pid = std::process::id();
        let tmp_root = std::env::temp_dir()
            .join(format!("cranelisp-wave4-{}-{}", pid, stamp));
        std::fs::create_dir_all(&tmp_root).expect("create test project_root");
        let settings = SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers,
            nice_workers: 0,
            run_mode: RunMode::Repl,
        };
        let mut s = CompilerSession::new(settings, tmp_root.clone(), "user");
        s.set_lib_dirs(vec![]);
        (s, tmp_root)
    }

    // spec: persistent-workers.md §4.2 — workers park on the priority-work
    // condvar and wake when register_module enqueues work.
    #[test]
    fn persistent_worker_park_and_wake() {
        let (mut s, root) = test_session(1);
        // Worker has been spawned in `new()` and is parked. Register a
        // trivial module — the notify_all on `priority_work_available`
        // wakes the worker.
        let p = root.join("wake.cl");
        s.register_module_with_source("wake", "(defn zero [] 0)", &p)
            .expect("register_module_with_source should succeed");
        // After return: wait_inmem_complete_blocking has observed inmem_done.
        assert!(
            !s.shared.scheduler.is_failed(&ModuleFullPath::from("wake")),
            "module must not have failed",
        );
        // The worker is parked again now (no more work). Shutdown joins it.
        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // spec: persistent-workers.md §5.2 — Drop while work is enqueued calls
    // shutdown() which signals + joins. No panic, no leak.
    #[test]
    fn shutdown_under_load_no_panic() {
        let (mut s, root) = test_session(2);
        // Register a module. workers begin processing.
        let p = root.join("load.cl");
        s.register_module_with_source("load", "(defn a [] 1) (defn b [] 2)", &p)
            .expect("register_module_with_source should succeed");
        // Immediately shutdown (workers may still be mid-loop).
        s.shutdown();
        // Calling shutdown a second time is idempotent.
        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // spec: persistent-workers.md §9.1 — concurrent module registrations
    // all complete; no lost updates.
    #[test]
    fn concurrent_register_module_two_modules_complete() {
        let (mut s, root) = test_session(2);

        // Register module A.
        s.register_module_with_source(
            "concA",
            "(defn a [] 10)",
            &root.join("concA.cl"),
        )
        .expect("register concA");

        // Register module B while A is complete but workers still parked.
        // The persistent pool handles the second registration without
        // respawning anything.
        s.register_module_with_source(
            "concB",
            "(defn b [] 20)",
            &root.join("concB.cl"),
        )
        .expect("register concB");

        // Both modules should be complete (inmem_done), neither failed.
        assert!(!s.shared.scheduler.is_failed(&ModuleFullPath::from("concA")));
        assert!(!s.shared.scheduler.is_failed(&ModuleFullPath::from("concB")));
        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // spec: persistent-workers.md §9.1 — reload_module through the same
    // persistent pool as register_module. Re-register → workers wake →
    // recompile → inmem_done.
    #[test]
    fn reload_during_compile_race_completes() {
        let (mut s, root) = test_session(2);

        // Write a real file so reload_module can read from disk.
        let file_path = root.join("reload_target.cl");
        std::fs::write(&file_path, "(defn original [] 1)\n")
            .expect("seed reload_target.cl");

        // Initial register via the source-explicit path.
        s.register_module_with_source(
            "reload_target",
            "(defn original [] 1)",
            &file_path,
        )
        .expect("initial register");

        // Overwrite with new content and trigger reload.
        std::fs::write(&file_path, "(defn updated [] 2)\n")
            .expect("rewrite reload_target.cl");
        let module = ModuleFullPath::from("reload_target");
        s.reload_module(&module, &file_path)
            .expect("reload should succeed via persistent workers");

        // Module must be in a non-failed state after reload. The post-reload
        // symbol table should carry `updated` (the new defn).
        assert!(!s.shared.scheduler.is_failed(&module));
        let has_updated = s.shared.symbol_tables
            .get(&module)
            .map(|t| t.get("updated").is_some())
            .unwrap_or(false);
        assert!(has_updated, "reloaded module must carry the new defn");

        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // S78 in-call-stack restructure: the former
    // `register_dep_for_eval_publish_then_register_is_observable_to_downstream`
    // test probed the deleted `module_sexps` publish-before-register mechanism
    // (the cross-thread parking map is gone — sexps ride the work packet). It
    // is retired; the dep-load behaviour it guarded is covered e2e by the
    // FQ-autoload / dep-chain suite and the H5-replay gate
    // (`tests/repl_persist_race.rs`).

    // spec: design/int/s77-int-restructure.md §3.3 — a dep-registration site
    // (caller blocked on the dep) uses `delays_other=true`, landing the dep in
    // `ModulePool::TypecheckFirst`. After S78 this is the `register_module`
    // call inside `drive_module_dep` / the structural form handlers (the
    // session-side `register_dep_for_eval` no longer registers — the gap-drive
    // already did). Asserts the scheduler contract the priority ordering
    // depends on, against the new packet-carrying `register_module` signature.
    #[test]
    fn dep_registration_uses_delays_other_true() {
        use crate::scheduler::{CompileScheduler, ModulePool};

        fn empty_sexps() -> std::sync::Arc<[Sexp]> {
            std::sync::Arc::from(Vec::new())
        }

        let scheduler = CompileScheduler::new();
        let dep = ModuleFullPath::from("sprint60_e2_dep_pool");

        scheduler.register_module(dep.clone(), empty_sexps(), true);

        let pool = scheduler.module_pool(&dep)
            .expect("dep must be registered");
        assert_eq!(
            pool,
            ModulePool::TypecheckFirst,
            "register_module(_, _, true) MUST land the dep in TypecheckFirst \
             (the scheduler contract the dep-drive priority depends on; \
             observed {:?})",
            pool,
        );

        // Negative: `false` lands the dep in TypecheckNext (entry-module
        // placement).
        let other = ModuleFullPath::from("sprint60_e2_dep_pool_neg");
        scheduler.register_module(other.clone(), empty_sexps(), false);
        let neg_pool = scheduler.module_pool(&other)
            .expect("neg dep must be registered");
        assert_eq!(
            neg_pool, ModulePool::TypecheckNext,
            "register_module(_, _, false) MUST land the dep in TypecheckNext \
             (observed {:?})",
            neg_pool,
        );
    }

    // ══════════════════════════════════════════════════════════════════════
    // Harvest from tests/legacy/wave4_g9.rs (FIXME 0119, S81 W-E /dev int).
    //
    // The legacy file's park/wake, shutdown-under-load, concurrent-register,
    // and reload-during-compile scenarios are ALREADY covered by the tests
    // above (`persistent_worker_park_and_wake`, `shutdown_under_load_no_panic`,
    // `concurrent_register_module_two_modules_complete`,
    // `reload_during_compile_race_completes`). These three harvest tests carry
    // the assertions the existing cluster does NOT: the N-module concurrent
    // register with per-defn `code.is_some()` codegen-population checks, the
    // per-worker JIT isolation across two live sessions (+ a two-thread
    // concurrency guard), and the `thread::scope`-absent close-gate grep.
    // ══════════════════════════════════════════════════════════════════════

    // spec: design/int/persistent-workers.md §4.3 — register enqueues; workers
    //       drain. Stronger than the 2-module check: every defn's `code` field
    //       must be populated after the persistent pool finalizes codegen.
    #[test]
    fn harvest_concurrent_register_many_modules_codegen_populated() {
        let (mut s, root) = test_session(4);
        const MODULE_COUNT: usize = 10;
        for i in 0..MODULE_COUNT {
            let name = format!("modA{i}");
            let file = root.join(format!("{name}.cl"));
            let src = format!("(defn f{i} [] {})", i as i64);
            s.register_module_with_source(&name, &src, &file)
                .unwrap_or_else(|e| panic!("register {name} failed: {e}"));
        }
        for i in 0..MODULE_COUNT {
            let mp = ModuleFullPath::from(format!("modA{i}").as_str());
            assert!(
                !s.shared.scheduler.is_failed(&mp),
                "modA{i} must not be Failed after concurrent register"
            );
            let table = s
                .shared
                .symbol_tables
                .get(&mp)
                .unwrap_or_else(|| panic!("symbol table missing for modA{i}"));
            match table.get(&format!("f{i}")) {
                Some(ModuleEntry::Def { code, .. }) => assert!(
                    code.is_some(),
                    "defn f{i} in modA{i}: code must be Some after persistent-worker codegen"
                ),
                other => panic!("expected Def for f{i} in modA{i}, got {other:?}"),
            }
        }
        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // spec: design/int/persistent-workers.md §4.5 — one JIT per priority worker
    //       (thread-local). Two live sessions with colliding defn names MUST
    //       not share a JIT or leak code pointers; A's shutdown MUST NOT
    //       invalidate B.
    #[test]
    fn harvest_per_worker_jit_isolation_across_sessions() {
        use std::sync::{Arc, Barrier};

        let (mut a, root_a) = test_session(1);
        let (mut b, root_b) = test_session(1);
        a.register_module_with_source("iso", "(defn f [] 111)", &root_a.join("iso.cl"))
            .expect("register into A");
        b.register_module_with_source("iso", "(defn f [] 222)", &root_b.join("iso.cl"))
            .expect("register into B");

        let mp = ModuleFullPath::from("iso");
        for (label, sess) in [("A", &a), ("B", &b)] {
            let tab = sess
                .shared
                .symbol_tables
                .get(&mp)
                .unwrap_or_else(|| panic!("{label}.iso symbol table must exist"));
            match tab.get("f") {
                Some(ModuleEntry::Def { code, .. }) => {
                    assert!(code.is_some(), "{label}.iso/f code must be populated")
                }
                other => panic!("expected Def for {label}.iso/f, got {other:?}"),
            }
        }

        // Shutdown A; B must remain operational.
        a.shutdown();
        let _ = std::fs::remove_dir_all(&root_a);
        b.register_module_with_source("post_a", "(defn g [] 333)", &root_b.join("post_a.cl"))
            .expect("B must still work after A is dropped");
        let post_mp = ModuleFullPath::from("post_a");
        assert!(!b.shared.scheduler.is_failed(&post_mp));
        {
            let b_tab = b
                .shared
                .symbol_tables
                .get(&post_mp)
                .expect("B.post_a symbol table must exist");
            match b_tab.get("g") {
                Some(ModuleEntry::Def { code, .. }) => {
                    assert!(code.is_some(), "B.post_a/g code must be populated after A shutdown")
                }
                other => panic!("expected Def for B.post_a/g, got {other:?}"),
            }
        }
        b.shutdown();
        let _ = std::fs::remove_dir_all(&root_b);

        // Concurrency guard: two sessions operated from their own threads must
        // not deadlock or race (no static/global JIT coupling).
        let barrier = Arc::new(Barrier::new(2));
        let b1 = Arc::clone(&barrier);
        let t1 = std::thread::spawn(move || {
            let (mut s, root) = test_session(1);
            b1.wait();
            s.register_module_with_source("p1", "(defn f [] 1)", &root.join("p1.cl"))
                .expect("p1 register");
            s.shutdown();
            let _ = std::fs::remove_dir_all(&root);
        });
        let t2 = std::thread::spawn(move || {
            let (mut s, root) = test_session(1);
            barrier.wait();
            s.register_module_with_source("p2", "(defn f [] 2)", &root.join("p2.cl"))
                .expect("p2 register");
            s.shutdown();
            let _ = std::fs::remove_dir_all(&root);
        });
        t1.join().expect("thread 1 must not panic");
        t2.join().expect("thread 2 must not panic");
    }

    // spec: design/int/persistent-workers.md §11 acceptance criterion 2 —
    //       `thread::scope` must appear zero times outside `#[cfg(test)]` in
    //       the worker lifecycle files (session_v4.rs / worker.rs / scheduler.rs).
    #[test]
    fn harvest_thread_scope_absent_outside_cfg_test() {
        let src_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
        let files = [
            src_root.join("session_v4.rs"),
            src_root.join("worker.rs"),
            src_root.join("scheduler.rs"),
        ];
        let mut offenders: Vec<String> = Vec::new();
        for path in &files {
            let content = std::fs::read_to_string(path)
                .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
            for (lineno, line) in strip_cfg_test_regions(&content) {
                let trimmed = line.trim_start();
                if trimmed.starts_with("//")
                    || trimmed.starts_with("///")
                    || trimmed.starts_with("//!")
                    || trimmed.starts_with("/*")
                    || trimmed.starts_with('*')
                {
                    continue;
                }
                if line.contains("thread::scope") {
                    offenders.push(format!("{}:{}: {}", path.display(), lineno, line.trim()));
                }
            }
        }
        assert!(
            offenders.is_empty(),
            "G9 close gate: `thread::scope` live references outside `#[cfg(test)]`:\n{}",
            offenders.join("\n")
        );
    }

    /// Brace-balanced scanner: return `(line_number, line)` pairs for live
    /// (non-`#[cfg(test)]`) code. Not a full parser — handles the
    /// attribute-on-its-own-line style used in this codebase.
    fn strip_cfg_test_regions(content: &str) -> Vec<(usize, String)> {
        let lines: Vec<&str> = content.lines().collect();
        let mut live: Vec<(usize, String)> = Vec::new();
        let mut i = 0;
        while i < lines.len() {
            let trimmed = lines[i].trim_start();
            if trimmed.starts_with("#[cfg(test)]") {
                i += 1;
                while i < lines.len() && lines[i].trim_start().starts_with("#[") {
                    i += 1;
                }
                if i >= lines.len() {
                    break;
                }
                let item_trim = lines[i].trim_end();
                let opens_block = lines[i].contains('{') && !item_trim.ends_with(';');
                if !opens_block && item_trim.ends_with(';') {
                    i += 1;
                    continue;
                }
                let mut depth: i32 = 0;
                let mut seen_open = false;
                while i < lines.len() {
                    for ch in lines[i].chars() {
                        match ch {
                            '{' => {
                                depth += 1;
                                seen_open = true;
                            }
                            '}' => depth -= 1,
                            _ => {}
                        }
                    }
                    i += 1;
                    if seen_open && depth <= 0 {
                        break;
                    }
                }
                continue;
            }
            live.push((i + 1, lines[i].to_string()));
            i += 1;
        }
        live
    }
}


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
mod bare_primitive_value_path_tests {
    use super::*;
    use cranelisp_types::{DefKind, ModuleEntry, Scheme, Symbol, Type, Visibility};
    use std::collections::HashMap as StdHashMap;

    /// Build a `ModuleEntry::Def` for a primitive (matches how
    /// `register_builtins` seeds `primitives/add-i64`).
    fn mk_primitive_def(ty: Type, docstring: Option<&str>) -> ModuleEntry<Code> {
        let mut builder = ModuleEntry::def(
            Scheme { type_vars: vec![], constraints: StdHashMap::new(), ty },
            DefKind::Primitive { got_slot: 0 },
        )
        .visibility(Visibility::Public);
        if let Some(doc) = docstring {
            builder = builder.docstring(doc);
        }
        builder.build()
    }

    /// Fresh session with empty lib_dirs and a temp project_root so no
    /// prelude.cl is auto-discovered. Caller populates `shared.symbol_tables`
    /// to stage the chain under test.
    fn isolated_session() -> (CompilerSession, PathBuf) {
        let stamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let pid = std::process::id();
        let tmp_root = std::env::temp_dir()
            .join(format!("cranelisp-s61-slice1-{}-{}", pid, stamp));
        std::fs::create_dir_all(&tmp_root).expect("create test project_root");
        let settings = SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers: 0,
            nice_workers: 0,
            run_mode: RunMode::Repl,
        };
        let mut s = CompilerSession::new(settings, tmp_root.clone(), "user");
        s.set_lib_dirs(vec![]);
        (s, tmp_root)
    }

    fn stage_primitive_reexport_chain(
        s: &CompilerSession,
        primitive_name: &str,
        primitive_ty: Type,
        docstring: Option<&str>,
    ) {
        let primitives = ModuleFullPath::from("primitives");
        let prelude = ModuleFullPath::from("prelude");
        let user = ModuleFullPath::from("user");

        // Ensure primitives table exists and holds the Def.
        s.shared.symbol_tables.entry(primitives.clone())
            .or_insert_with(|| SessionSymbolTable::new_with_params(primitives.clone()));
        if let Some(mut st) = s.shared.symbol_tables.get_mut(&primitives) {
            st.insert(
                Symbol::from(primitive_name),
                mk_primitive_def(primitive_ty, docstring),
            );
        }

        // prelude: Reexport → primitives/<name>.
        s.shared.symbol_tables.entry(prelude.clone())
            .or_insert_with(|| SessionSymbolTable::new_with_params(prelude.clone()));
        if let Some(mut st) = s.shared.symbol_tables.get_mut(&prelude) {
            st.insert(
                Symbol::from(primitive_name),
                ModuleEntry::Import {
                    source: FQSymbol {
                        module: primitives.clone(),
                        symbol: Symbol::from(primitive_name),
                    },
                    visibility: Visibility::Public,
                },
            );
        }

        // user: Import → prelude/<name> (implicit prelude glob effect).
        if let Some(mut st) = s.shared.symbol_tables.get_mut(&user) {
            st.insert(
                Symbol::from(primitive_name),
                ModuleEntry::Import {
                    source: FQSymbol {
                        module: prelude.clone(),
                        symbol: Symbol::from(primitive_name),
                    },
                    visibility: Visibility::Private,
                },
            );
        }
    }

    // spec: repl/spec.md §1.1 + spec/08-modules.md §8.9 — bare-value path
    //       MUST resolve a re-exported primitive to its terminal Def and
    //       echo the introspection card. Before the fix, the one-hop
    //       resolver terminated on the `Reexport` intermediate and the
    //       match dropped through `_ => None`.
    #[test]
    fn bare_reexported_primitive_resolves_to_terminal_def() {
        let (mut s, root) = isolated_session();
        let add_i64_ty = Type::Fn(
            vec![Type::Int, Type::Int],
            Box::new(Type::Int),
        );
        stage_primitive_reexport_chain(
            &s,
            "add-i64",
            add_i64_ty.clone(),
            Some("Add two i64 values."),
        );

        // Simulate the bare-value path: look up in user's table and
        // resolve. This is the exact sequence performed inside
        // `check_bare_symbol_introspection`.
        let user = ModuleFullPath::from("user");
        let entry = s.shared.symbol_tables.get(&user)
            .and_then(|st| st.get("add-i64").cloned())
            .expect("user module must carry Import for add-i64");
        let (resolved_entry, resolved_module) =
            s.resolve_entry_for_display(&entry, &user);

        match &resolved_entry {
            ModuleEntry::Def { scheme, kind, .. } => {
                assert_eq!(
                    scheme.ty, add_i64_ty,
                    "terminal Def must carry the primitive's own type",
                );
                assert!(
                    matches!(kind.as_ref(), DefKind::Primitive { .. }),
                    "terminal entry must be a Primitive Def, got: {:?}", kind,
                );
            }
            other => panic!(
                "expected terminal ModuleEntry::Def after resolve, got: {:?}",
                other,
            ),
        }
        assert_eq!(
            resolved_module,
            ModuleFullPath::from("primitives"),
            "resolved_module MUST be `primitives` (spec §8.9 re-export provenance)",
        );

        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // spec: repl/spec.md §1.1 — bare-value introspection output format
    //       `:Type name ; classification - docstring`. The `format_eval_result`
    //       pipeline must produce a qualified-module echo for a re-exported
    //       primitive; this is the user-visible string the REPL prints.
    #[test]
    fn bare_reexported_primitive_formats_as_primitives_qualified() {
        let (mut s, root) = isolated_session();
        let add_i64_ty = Type::Fn(
            vec![Type::Int, Type::Int],
            Box::new(Type::Int),
        );
        stage_primitive_reexport_chain(
            &s,
            "add-i64",
            add_i64_ty,
            Some("Add two i64 values."),
        );

        // Drive the bare-value introspection handler directly.
        let sexp = Sexp::Symbol("add-i64".to_string(), Span::SYNTHETIC);
        let result = s.check_bare_symbol_introspection(&sexp)
            .expect(
                "re-exported primitive MUST resolve on the bare-value path \
                 (S61 Slice 1 acceptance)",
            );

        let output = s.format_eval_result(&result);
        assert!(
            output.starts_with(":(Fn [primitives/Int primitives/Int] primitives/Int) primitives/add-i64"),
            "bare-value echo must carry the full qualified type + \
             `primitives/add-i64` name (spec §8.9 re-export provenance); got: {output}",
        );
        assert!(
            output.contains("; primitive"),
            "classification MUST be `; primitive` for a primitive Def \
             (spec §4.1.1); got: {output}",
        );
        assert!(
            output.contains(" - Add two i64 values."),
            "docstring first line MUST follow ` - ` after classification \
             (repl/spec.md §1.1); got: {output}",
        );

        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // spec: repl/spec.md §1.1 — genuinely unknown bare symbols MUST NOT
    //       produce an introspection card. The bare-value path returns
    //       None so the caller's fall-through (typecheck → codegen error)
    //       produces the expected `undefined variable` diagnostic. This
    //       is the negative case proving the fix didn't over-broaden the
    //       match to swallow lookup failures.
    #[test]
    fn bare_unknown_symbol_returns_none_for_introspection() {
        let (mut s, root) = isolated_session();
        // Stage `add-i64` but NOT `unknown-primitive-xyz`.
        stage_primitive_reexport_chain(
            &s,
            "add-i64",
            Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            None,
        );

        let sexp = Sexp::Symbol(
            "unknown-primitive-xyz".to_string(),
            Span::SYNTHETIC,
        );
        let result = s.check_bare_symbol_introspection(&sexp);
        assert!(
            result.is_none(),
            "unknown bare symbol MUST return None so the caller falls \
             through to the normal `undefined variable` typecheck error \
             (repl/spec.md §1.1 — no introspection card for unknown names); \
             got: is_some={}", result.is_some(),
        );

        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // Harvest T-S1-3 from tests/legacy/sprint61_bare_primitive.rs (FIXME 0147):
    // generalisation across the re-exported primitive surface. Every staged
    // primitive resolves identically through user → prelude → primitives to
    // its terminal Def attributed to `primitives`. The legacy test asserted
    // this over ≥5 primitives end-to-end; this is the int Rust-API equivalent.
    // spec: spec/08-modules.md §8.9 — re-export provenance; repl/spec.md §1.1
    #[test]
    fn bare_reexported_primitive_surface_resolves_identically_across_symbols() {
        let (mut s, root) = isolated_session();
        let int2_to_int = || Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int));
        let cases: &[(&str, Type)] = &[
            ("add-i64", int2_to_int()),
            ("mul-i64", int2_to_int()),
            ("sub-i64", int2_to_int()),
            ("eq-i64", Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool))),
            ("not", Type::Fn(vec![Type::Bool], Box::new(Type::Bool))),
            ("str-concat", Type::Fn(vec![Type::String, Type::String], Box::new(Type::String))),
        ];
        for (name, ty) in cases {
            stage_primitive_reexport_chain(&s, name, ty.clone(), None);
        }

        let user = ModuleFullPath::from("user");
        for (name, ty) in cases {
            let entry = s
                .shared
                .symbol_tables
                .get(&user)
                .and_then(|st| st.get(name).cloned())
                .unwrap_or_else(|| panic!("user must carry Import for {name}"));
            let (resolved_entry, resolved_module) = s.resolve_entry_for_display(&entry, &user);
            match &resolved_entry {
                ModuleEntry::Def { scheme, kind, .. } => {
                    assert_eq!(&scheme.ty, ty, "{name}: terminal Def carries its own type");
                    assert!(
                        matches!(kind.as_ref(), DefKind::Primitive { .. }),
                        "{name}: terminal entry must be a Primitive Def, got {kind:?}"
                    );
                }
                other => panic!("{name}: expected terminal Def, got {other:?}"),
            }
            assert_eq!(
                resolved_module,
                ModuleFullPath::from("primitives"),
                "{name}: MUST attribute to `primitives` (spec §8.9), not user/prelude"
            );
        }

        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }
}

#[cfg(test)]
mod list_classification_tests {
    use super::*;
    use cranelisp_types::{DefKind, FQTypeName, Scheme, Type, Visibility};
    use std::collections::HashMap as StdHashMap;

    // ══════════════════════════════════════════════════════════════════════
    // Harvest from tests/legacy/repl_negative_old.rs (FIXME 0124, S81 W-E
    // /dev int) — the `classify_entry` / `collect_list_categories` portion.
    //
    // The legacy helper replicated `handle_list`'s classification logic in
    // test code (reaching into `session.shared.symbol_tables`). The int-owned
    // surface is `CompilerSession::list_user_definitions`, which buckets a
    // module's symbols into `SymbolCategory`. This harvests the positive
    // classification AND the negatives the spec requires (repl/spec.md §3.3 /
    // tests/CLAUDE.md §Negative): a defmacro is a Macro NOT a Fn; an Import is
    // NOT listed (surfaced by `/imports`); a constructor is a Constructor.
    // The display-format + type-inference portions of repl_negative_old.rs
    // route to /backend (`display.rs`) + /typecheck (`checker.rs`), outside
    // int's narrow deployment.
    // ══════════════════════════════════════════════════════════════════════

    fn isolated_session() -> (CompilerSession, PathBuf) {
        let stamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let pid = std::process::id();
        let tmp_root = std::env::temp_dir()
            .join(format!("cranelisp-s64-list-{}-{}", pid, stamp));
        std::fs::create_dir_all(&tmp_root).expect("create test project_root");
        let settings = SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers: 0,
            nice_workers: 0,
            run_mode: RunMode::Repl,
        };
        let mut s = CompilerSession::new(settings, tmp_root.clone(), "user");
        s.set_lib_dirs(vec![]);
        (s, tmp_root)
    }

    fn mono(ty: Type) -> Scheme {
        Scheme { type_vars: vec![], constraints: StdHashMap::new(), ty }
    }

    // spec: repl/spec.md §3.3 — `/list` buckets symbols by category; a defmacro
    //       MUST classify as Macro (NOT Fn), a constructor as Constructor, and
    //       imports MUST NOT appear (they are surfaced by `/imports`).
    #[test]
    fn list_user_definitions_classifies_and_excludes_imports() {
        let (mut s, root) = isolated_session();
        let user = ModuleFullPath::from("user");

        if let Some(mut st) = s.shared.symbol_tables.get_mut(&user) {
            // A plain function.
            st.insert(
                Symbol::from("f"),
                ModuleEntry::def(
                    mono(Type::Fn(vec![Type::Int], Box::new(Type::Int))),
                    DefKind::UserFn {
                        fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0 },
                    },
                )
                .visibility(Visibility::Public)
                .build(),
            );
            // A macro.
            st.insert(
                Symbol::from("m"),
                ModuleEntry::def(
                    mono(Type::Int),
                    DefKind::Macro {
                        clauses_meta: vec![],
                        macro_sexp: Sexp::Symbol("m".to_string(), Span::SYNTHETIC),
                    },
                )
                .visibility(Visibility::Public)
                .build(),
            );
            // A constructor.
            st.insert(
                Symbol::from("Mk"),
                ModuleEntry::def(
                    mono(Type::Int),
                    DefKind::Constructor {
                        got_slot: 0,
                        type_name: FQTypeName {
                            module: user.clone(),
                            name: cranelisp_types::TypeName::from("T"),
                        },
                        tag: 0,
                        field_count: 0,
                        internal: false,
                        type_def: None,
                    },
                )
                .visibility(Visibility::Public)
                .build(),
            );
            // An import — MUST NOT be listed by `/list`.
            st.insert(
                Symbol::from("imported"),
                ModuleEntry::Import {
                    source: FQSymbol {
                        module: ModuleFullPath::from("other"),
                        symbol: Symbol::from("imported"),
                    },
                    visibility: Visibility::Private,
                },
            );
        }

        let defs = s.list_user_definitions();
        let cat = |name: &str| defs.iter().find(|d| d.name.as_ref() == name).map(|d| d.category);

        assert_eq!(cat("f"), Some(SymbolCategory::Fn), "plain defn is a Fn");
        assert_eq!(
            cat("m"),
            Some(SymbolCategory::Macro),
            "defmacro MUST classify as Macro, NOT Fn (repl/spec.md §3.3 negative)"
        );
        assert_ne!(
            cat("m"),
            Some(SymbolCategory::Fn),
            "negative: defmacro MUST NOT be bucketed as a Fn"
        );
        assert_eq!(
            cat("Mk"),
            Some(SymbolCategory::Constructor),
            "constructor MUST classify as Constructor"
        );
        assert!(
            cat("imported").is_none(),
            "negative: imports MUST NOT appear in /list (surfaced by /imports)"
        );

        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }
}

// --- relocated back from repl.rs (FIXME 0109 Wave D): session-lifecycle +
// shared helpers used by session_v4 / eval.rs / repl.rs ---

/// Populate the `primitives` synthetic module's GOT slots with Ring 0
/// shim-fn addresses.
///
/// Per FIXME 0174 + Decision 43, Ring 0 primitives (`add-i64`, …, `not`,
/// `eq-bool`) are registered in `typecheck::builtins::register_primitives`
/// with `got_slot: Some(_)` and `jit_name: Some(_)`. Their code pointers
/// are written here, immediately after `register_builtins` returns, by
/// reading them from `cranelisp_primitives::PRIMITIVES_TABLE` — the
/// post-FIXME-0159 single source of truth for primitive entries and
/// GOT-stored fn ptrs. The static table's GOT carries each Ring 0 shim's
/// address at its own slot index; this fn copies them across to the
/// session's `primitives` table at the session-allocated slot indices
/// (the two tables index slots independently).
///
/// The standard GOT-indirect dispatch (`compile_direct_call` →
/// `resolve_got_target` → `__cranelisp_got_primitives[slot]`) resolves the
/// call to these shim fn ptrs. The `primitives_inline.rs` inline-substitution
/// path is a separate code-size + dispatch-cost optimisation: identical
/// semantics, faster code. Mappable paths (`(let [f not] (f true))`)
/// always work via the GOT-stored shim ptr.
///
/// Idempotent — safe to call after every `register_builtins`; the shim
/// pointers are stable for the process lifetime.
pub(crate) fn populate_ring0_got_slots(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
) {
    let primitives_path = ModuleFullPath::from("primitives");
    let Some(table) = symbol_tables.get(&primitives_path) else {
        // primitives module not seeded — register_builtins ordering broken.
        // Quietly skip; the regular pipeline error path will surface the
        // missing-module condition when a Ring 0 call is compiled.
        return;
    };
    // PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<Code, ()>>>. Deref the
    // LazyLock to the Arc, then `.as_ref()` to get `&SymbolTable`.
    let static_table = (*cranelisp_primitives::PRIMITIVES_TABLE).as_ref();
    // The callable slot rides on the `DefKind` variant (S83 reshape, FIXME
    // 0356/0357) — read both the static-source and session-dest slots via the
    // `callable_got_slot()` chokepoint.
    for (name, static_entry) in static_table.symbols.iter() {
        let Some(src_slot) = static_entry.callable_got_slot() else {
            continue;
        };
        let ptr = static_table.got.load_slot(src_slot);
        let Some(session_entry) = table.get(name.as_ref()) else {
            continue;
        };
        let Some(dst_slot) = session_entry.callable_got_slot() else {
            continue;
        };
        table.got.store_slot(dst_slot, ptr);
    }
}

/// Check if input is a comment-only line.
pub(crate) fn is_comment_only(input: &str) -> bool {
    input.lines().all(|line| {
        let trimmed = line.trim();
        trimmed.is_empty() || trimmed.starts_with(';')
    })
}

pub(crate) fn intrinsic_type_from_name(name: &str) -> Option<Type> {
    match name {
        "Int" => Some(Type::Int),
        "Bool" => Some(Type::Bool),
        "Float" => Some(Type::Float),
        "String" => Some(Type::String),
        _ => None,
    }
}
