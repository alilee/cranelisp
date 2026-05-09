# Facade spec — Binary / int (`src/` + `crates/cranelisp-exe-bundle/`)

**Bounded context citation.** Pipeline orchestration, REPL session, CLI, slash-command dispatch, file watcher, and `--link` standalone executable generation (exe-bundle). The application layer that wires the other surfaces together and produces the deployable artefact. See `bounded-contexts.md` §6 — Binary / int.

This spec is **target-stating**. Drift detection between as-designed and as-built is the job of `cargo-public-api` (M4-pending) and `/review`'s per-PR audit, not this document.

This is the largest facade — `int` integrates everything. Most of the surface is `CompilerSession` methods (the high-level facade `::main` calls), with `CompileScheduler`, `ObjectCache`, and `worker` underneath. The Composed introspection flows and Link orchestration sub-sections at the end document multi-call patterns rather than new types.

---

## Public surface (as-designed)

### `CompilerSession` — the high-level facade

The single object that `::main` constructs and drives. Wraps an `Arc<SharedState>` (the worker-shareable subset — see next section) plus initiator-thread-only state (watcher channel, REPL eval cursor, worker pool handles, accumulated warnings). Exposes the orchestration methods every cli mode and the REPL share.

```rust
pub struct CompilerSession {
    pub shared: Arc<SharedState>,                                                  // worker-shareable subset — see next section

    // Initiator-thread-only state — never crosses thread boundary
    watcher: Option<WatcherChannel>,                                               // notify::Event receiver
    current_repl_module: ModuleFullPath,                                           // /mod state
    repl_input_active: Arc<AtomicBool>,                                            // shared with watcher event handler via Arc clone
    worker_pool: WorkerPool,                                                       // joins on Drop
    warnings: Vec<Warning>,                                                        // initiator-collected, never cross-thread
}

impl CompilerSession {
    // Construction
    pub fn new(settings: SessionSettings, project_root: PathBuf) -> CompilerSession;

    // Module registration (entry point — fire-and-forget per exec-flow-compilation)
    // Phase 0 (parse + write_structural_decls) runs synchronously here, before dispatching PriorityWork::Typecheck.
    pub fn register_module(&mut self, module: &ModuleFullPath) -> Result<(), CranelispError>;
    pub fn re_register_module(&mut self, module: &ModuleFullPath) -> Result<bool, CranelispError>;       // file watcher path

    // Shared form-processing entry — used by both compilation worker and eval (per exec-flow-compilation + exec-flow-repl)
    pub fn process_form(&mut self, form: Sexp, scope: &ModuleFullPath) -> Result<ProcessedForm, CranelispError>;
    pub fn insert_symbol(&mut self, processed: &ProcessedForm, target: &ModuleFullPath);

    // REPL eval — composes process_form + insert_symbol (defns) or process_form + temp-closure JIT (expressions)
    pub fn eval(&mut self, src: &str) -> Result<Option<EvalResult>, CranelispError>;

    // REPL slash-command dispatch
    pub fn process_commands(&mut self, input: &str, stdout: &mut impl Write) -> CommandResult;

    // Trampoline — the runtime cadence entry (per exec-flow-runtime)
    pub fn trampoline(&mut self, module_name: &str) -> Result<(i64, Type), CranelispError>;              // Run mode + REPL eval expression form

    // Cli pre-exit affordances (per exec-flow-run, exec-flow-link, exec-flow-repl)
    pub fn wait_for_inmem_codegen(&self) -> Result<(), CranelispError>;
    pub fn wait_for_object_codegen(&self) -> Result<(), CranelispError>;

    // Link mode entry
    pub fn link_by_name(&mut self, module_name: &str) -> Result<(), CranelispError>;

    // Lifecycle
    pub fn shutdown(&mut self);

    // REPL display + IO
    pub fn print_banner(&self, stdout: &mut impl Write);
    pub fn write_prompt(&self, stdout: &mut impl Write, compile_ms: u64, eval_ms: u64);
    pub fn write_continuation_prompt(&self, stdout: &mut impl Write, compile_ms: u64, eval_ms: u64);
    pub fn parens_balanced(&self, input: &str) -> bool;
    pub fn pretty_print(&self, text: &str, stdout: &mut impl Write);
    pub fn format_eval_result(&self, result: &EvalResult) -> String;
    pub fn format_command_result(&self, result: &CommandResult) -> String;
    pub fn format_error(&self, error: &CranelispError) -> String;                                        // resolves ErrorLocation + introspection.source for rich display

    // Watcher integration
    pub fn init_watcher(&mut self) -> Result<(), CranelispError>;
    pub fn sync_watcher(&mut self) -> Result<(), CranelispError>;
    pub fn set_repl_input_active(&self, active: bool);                                                   // per exec-flow-repl STEP 1 / STEP 3

    // Persistence
    pub fn regenerate_backing_file(&mut self, module: &ModuleFullPath) -> Result<(), CranelispError>;    // iterates SymbolTable::defn_order, emits introspection[fq].source per entry — per repl/spec.md §15

    // Introspection accessors (used by slash commands — see Composed introspection flows below)
    pub fn list_user_definitions(&self) -> Vec<SymbolInfo>;
    pub fn describe_symbol(&self, name: &str) -> Option<SymbolDescription>;
    pub fn module_imports(&self, module: &ModuleFullPath) -> Vec<ImportSpec>;
    pub fn module_exports(&self, module: &ModuleFullPath) -> Vec<(Symbol, ModuleEntry<Code>)>;
    pub fn current_repl_module(&self) -> &ModuleFullPath;
    pub fn set_current_repl_module(&mut self, module: ModuleFullPath);                                   // /mod implementation

    // Per-symbol introspection accessors — read from shared.introspection (None outside REPL/trace mode)
    pub fn symbol_source(&self, fq: &FQSymbol) -> Option<String>;                                        // /source — replaces module_source
    pub fn symbol_sexp(&self, fq: &FQSymbol) -> Option<Sexp>;                                            // /sexp
    pub fn symbol_clif(&self, fq: &FQSymbol) -> Option<String>;                                          // /clif
    pub fn symbol_disasm(&self, fq: &FQSymbol) -> Option<String>;                                        // /disasm
    pub fn symbol_code_size(&self, fq: &FQSymbol) -> Option<usize>;                                      // formatting for /clif and /disasm
    pub fn symbol_compile_duration(&self, fq: &FQSymbol) -> Option<Duration>;                            // /time

    // Settings + paths (delegates to shared.settings, shared.project_root, shared.lib_dirs, shared.platform_dirs)
    pub fn project_root(&self) -> &Path;
    pub fn lib_dirs(&self) -> Vec<PathBuf>;
    pub fn platform_dirs(&self) -> Vec<PathBuf>;
    pub fn warnings(&self) -> &[Warning];
}
```

### `SharedState` — the worker-shareable session subset

The `Arc<T>` workers hold across thread boundaries. Every field is interior-mutable (`DashMap`, `Atomic*`, `Arc<RwLock<_>>`) so that workers freely access via `&shared.field` without exclusive borrows. **No merge step** anywhere — writes go directly into shared structures under per-cell locks (per Decisions 25, 26, 31, 33 and the per-symbol mutability discipline of `SymbolTable`).

`CompilerSession` holds one `Arc<SharedState>`; workers each clone it on spawn. The split keeps initiator-thread state (watcher channel, REPL cursor, worker handles, accumulated warnings) out of the worker-reachable surface.

```rust
pub struct SharedState {
    // ──────────── The single store (Decisions 25, 26, 33) ────────────
    /// Per-module SymbolTables. Outer DashMap shard locks for module access;
    /// inner DashMap per-entry locks for symbol mutation.
    /// Phase 0 (parse-time) is the only [&mut SymbolTable] hold; everything
    /// after takes shared [&SymbolTable] + per-entry inner locks.
    pub symbol_tables: DashMap<ModuleFullPath, SymbolTable<Code, ()>>,

    // ──────────── Coordination ────────────
    /// Work dispatch + per-module/per-symbol readiness coordination.
    /// Workers call notify_* on completion and wait_for_* on dependencies.
    pub scheduler: Arc<CompileScheduler>,

    /// Object cache — workers read sidecars + .o on cache-hit, write on
    /// cache-miss codegen.
    pub cache: Arc<ObjectCache>,

    // ──────────── Long-lived runtime state ────────────
    /// Loaded platform DLLs — session-global, kept alive for the session's
    /// lifetime (per /platform addendum §A3). Indexed by manifest path.
    pub kept_dlls: DashMap<PathBuf, Arc<DllHandle>>,

    // ──────────── REPL / trace introspection (Decision 38) ────────────
    /// Per-symbol introspection metadata — sexp, source, clif_ir, disasm,
    /// code_size, compile_duration. Some(map) iff REPL mode OR trace mode
    /// (CRANELISP_CODEGEN_TRACE) is enabled; None in production batch
    /// (zero overhead — Run/Link batch carries no per-symbol metadata).
    /// Codegen and parse paths populate via .as_ref().map(|m| m.insert(...)).
    /// Per-defn source lives here per Decision 39 — there is no separate
    /// module_sources field.
    pub introspection: Option<DashMap<FQSymbol, Introspection>>,

    // ──────────── Read-only configuration ────────────
    pub settings: SessionSettings,
    pub project_root: PathBuf,
    pub lib_dirs: Vec<PathBuf>,
    pub platform_dirs: Vec<PathBuf>,
}

#[non_exhaustive]
pub struct WatcherChannel {
    /* opaque — receiver side of notify::Event mpsc */
}

#[non_exhaustive]
pub struct WorkerPool {
    /* opaque — JoinHandle vector + shutdown signal */
}

#[non_exhaustive]
pub struct DllHandle {
    /* opaque — wraps libloading::Library + manifest metadata */
}
```

**Initiator vs worker reach** — what's on each side and why:

| Field | On | Why |
|---|---|---|
| `symbol_tables` | SharedState | Per-symbol mutation by workers; per-entry locks via inner DashMap |
| `scheduler` | SharedState | Workers call `notify_*` and `wait_for_*` |
| `cache` | SharedState | Worker reads sidecars + writes `.o`; the underlying file IO is internally synchronised |
| `kept_dlls` | SharedState | Platform calls happen on workers (during JIT registration + IO trampoline) |
| `introspection` | SharedState | Codegen workers populate `clif_ir`/`disasm`/`compile_duration` |
| `settings` / `project_root` / `lib_dirs` / `platform_dirs` | SharedState | Read by workers (e.g., for cache path resolution); never mutated post-construction |
| `watcher` | CompilerSession | mpsc receiver — only the initiator thread reads from it |
| `current_repl_module` | CompilerSession | Mutated by `/mod` (initiator-only); workers don't need it |
| `repl_input_active` | CompilerSession (with `Arc<AtomicBool>` clone passed to watcher event handler) | Initiator-side coordination of watcher windowing |
| `worker_pool` | CompilerSession | Joining on shutdown is initiator's job |
| `warnings` | CompilerSession | Initiator-collected; workers route warnings back via the work-completion notification, where they merge into this Vec |

**Worker access pattern**: workers receive `Arc<SharedState>` at spawn time (one Arc clone per worker). All reads through `&shared.*` — never `&mut`. All mutations through interior mutability of the contained types. No worker-side merge step; mutations are immediately visible to other workers as soon as the per-cell lock releases.

### Settings and config

```rust
#[non_exhaustive]
pub struct SessionSettings {
    pub no_color: bool,
    pub no_cache: bool,
    pub codegen_behaviour: CodegenBehaviour,                                       // re-exported from cranelisp-types
    pub priority_workers: usize,
    pub nice_workers: usize,
}

#[non_exhaustive]
pub struct ProjectTarget {
    pub project_root: PathBuf,
    pub entry_module: ModuleFullPath,
}
```

### Eval results (returned by eval, displayed via format_eval_result)

```rust
#[non_exhaustive]
pub enum EvalResult {
    Def {
        symbol: FQSymbol,
        kind: DefKind,
        scheme: Scheme,
        warnings: Vec<Warning>,
    },
    Value {
        value: EvalValue,
        warnings: Vec<Warning>,
    },
    Import {
        module: ModuleFullPath,
        names: Vec<Symbol>,
        warnings: Vec<Warning>,
    },
}

impl EvalResult {
    pub fn is_def(&self) -> bool;                                                  // governs regenerate_backing_file
    pub fn warnings(&self) -> &[Warning];
}

#[non_exhaustive]
pub struct EvalValue {
    pub repr: i64,
    pub ty: Type,
    pub heap_root: Option<Arc<HeapRetention>>,                                     // keeps returned heap alloc alive until the caller drops the value
}

#[non_exhaustive]
pub struct HeapRetention {
    /* opaque — drops the held alloc per consuming convention */
}
```

### Slash-command dispatch result (per pipeline-v4.md §6.1)

```rust
#[non_exhaustive]
pub enum CommandResult {
    Nothing,                                                                       // blank, comment, or side-effect-only command
    Quit,                                                                          // /quit or EOF — break the REPL loop
    Final(String),                                                                 // displayable text (e.g. /sig output)
    Compile(String),                                                               // raw source — caller feeds to eval
}

#[non_exhaustive]
pub enum SlashCommand {
    Help, List, Imports, Exports(ModuleFullPath), Sig(Symbol), Doc(Symbol), Type(Symbol), Info(Symbol),
    Source(Symbol), Sexp(Symbol), Ast(Symbol), Clif(Symbol), Disasm(Symbol),
    Time(Symbol), Mem, RunTests, Mod(Option<ModuleFullPath>), Reload(Option<ModuleFullPath>),
    Expand(String), Quit,
    /* … */
}
```

### Introspection records (returned by accessor methods)

```rust
#[non_exhaustive]
pub struct SymbolInfo {
    pub name: Symbol,
    pub category: SymbolCategory,                                                  // Module | Macro | Trait | Type | Fn
    pub scheme: Option<Scheme>,
    pub docstring: Option<String>,
}

#[non_exhaustive]
pub enum SymbolCategory { Module, Macro, Trait, Type, Fn, SpecialForm, Constructor }

#[non_exhaustive]
pub struct SymbolDescription {
    pub fq: FQSymbol,
    pub category: SymbolCategory,
    pub scheme: Option<Scheme>,
    pub docstring: Option<String>,
    pub source: Option<String>,                                                    // mirrors Sess::symbol_source(fq) — convenience for one-shot describe
    pub related: Vec<FQSymbol>,                                                    // related symbols — defn, impl, match arms, etc.
}
```

### `Introspection` — per-symbol REPL/trace metadata (Decision 38, Decision 39)

The value type stored in `SharedState.introspection: Option<DashMap<FQSymbol, Introspection>>`. Populated ONLY when REPL mode or trace mode is enabled — production batch leaves the outer `Option` as `None` and pays zero overhead.

```rust
#[non_exhaustive]
pub struct Introspection {
    /// Per-defn source snippet — the text of `(defn foo ...)`. Populated by the
    /// parser at parse-time (slices the file `Arc<str>` against the defn's span,
    /// drops the file string after partitioning). For REPL evals, the source is
    /// the eval text itself. Used by `/source name` and `regenerate_backing_file`.
    /// Per Decision 39 — there is no module-global source store.
    pub source: Option<String>,

    /// Post-expansion s-expression. Populated by parse + macro expansion.
    /// Used by `/sexp name`.
    pub sexp: Option<Sexp>,

    /// CLIF IR text. Populated by JIT codegen iff `CRANELISP_CODEGEN_TRACE`
    /// or REPL-trace mode is active. Used by `/clif name`.
    pub clif_ir: Option<String>,

    /// Disassembly of compiled native code. Populated by JIT codegen iff trace
    /// mode is active. Used by `/disasm name`.
    pub disasm: Option<String>,

    /// Native code size in bytes. Populated by JIT codegen. Used by `/clif`
    /// and `/disasm` formatting headers.
    pub code_size: Option<usize>,

    /// Wall-clock duration of the codegen step. Populated by the codegen
    /// wrapper. Used by `/time name`.
    pub compile_duration: Option<Duration>,
}
```

**Population points** (all conditional on `shared.introspection.is_some()`):
- `process_form` after `parse`: write `source` + `sexp` for each defn form.
- `compile_to_module` per-symbol call (Decision 41): backend writes `clif_ir`, `disasm`, `code_size`, `compile_duration` directly into the introspection map via the `Option<&DashMap<FQSymbol, Introspection>>` parameter — no int-side post-processing. Per-symbol JIT cardinality means one `Introspection` write per `compile_to_module` call.

**Consistency with Decision 31 carry-forward.** REPL redefinition replaces the `ModuleEntry::Def` for the same FQSymbol; the corresponding `Introspection` entry is overwritten in the same `process_form` pass (`introspection.insert(fq, fresh_intro)`). The two stores share keying by FQSymbol and are mutated at the same orchestration points; no drift.

### `CompileScheduler` — work dispatch + per-symbol readiness coordination

The single coordination authority. Owns the priority + nice work queues, the per-module/per-symbol readiness state, and the worker park/wake primitives. Per the runtime/platform diagrams: the same Scheduler handles BOTH work dispatch AND wait/release (no separate DependencyService).

```rust
pub struct CompileScheduler {
    /* private */
}

impl CompileScheduler {
    pub fn new() -> Self;

    // Module-level registration
    pub fn register_module(&self, module: ModuleFullPath);
    pub fn register_module_cached(&self, module: ModuleFullPath, symbols: HashSet<Symbol>);
    pub fn re_register_module(&self, module: &ModuleFullPath) -> bool;

    // Worker dispatch
    pub fn take_priority_work_blocking(&self) -> Option<PriorityWork>;             // park until work or shutdown
    pub fn take_object_codegen(&self) -> Option<ModuleFullPath>;                   // nice-worker entry

    // Notification (called by workers on completion)
    pub fn notify_symbol_typechecked(&self, fq: &FQSymbol);
    pub fn notify_typecheck_done(&self, module: &ModuleFullPath);
    pub fn notify_typecheck_done_from_cache(&self, module: &ModuleFullPath);       // cache-hit-typecheck path; enqueues LoadObject not Jit
    pub fn notify_inmem_codegen_complete(&self, fq: &FQSymbol);
    pub fn notify_inmem_codegen_batch_complete(&self, module: &ModuleFullPath);    // LoadObject completion
    pub fn notify_object_codegen_complete(&self, module: &ModuleFullPath);

    // Enqueue (called by workers + Sess::eval)
    pub fn enqueue_jit(&self, fq: FQSymbol);                                       // per-symbol JIT work
    pub fn enqueue_object(&self, module: ModuleFullPath);
    pub fn append_form(&self, module: &ModuleFullPath, form: Sexp) -> Result<(), CranelispError>;   // REPL additive append per exec-flow-repl

    // Wait / block primitives (called by workers and by Sess::eval)
    pub fn wait_for_typecheck(&self, module: &ModuleFullPath) -> Result<(), SchedulerError>;       // block until module typecheck-done
    pub fn wait_for_typecheck_symbol(&self, fq: &FQSymbol) -> Result<(), SchedulerError>;          // FQ form retry path
    pub fn wait_for_typecheck_type(&self, fqt: &FQTypeName) -> Result<(), SchedulerError>;         // FQTypename retry path
    pub fn wait_for_inmem(&self, fq: &FQSymbol) -> Result<(), SchedulerError>;                     // expansion needs jitted macro
    pub fn priority_boost_jit(&self, fq: &FQSymbol);                                               // promote symbol's JIT to head of queue
    pub fn block_for_macro_codegen(&self, fq: &FQSymbol) -> Result<(), SchedulerError>;            // eval per-closure-dep wait

    // Global completion waits (called by Sess for cli pre-exit)
    pub fn wait_inmem_complete(&self) -> Result<(), SchedulerError>;
    pub fn wait_object_complete(&self) -> Result<(), SchedulerError>;
    pub fn wait_module_inmem_complete_blocking(&self, module: &ModuleFullPath) -> Result<(), SchedulerError>;

    // Lifecycle
    pub fn shutdown(&self);
    pub fn is_shutdown(&self) -> bool;
}

#[non_exhaustive]
pub enum PriorityWork {
    Typecheck(ModuleFullPath),
    Jit(FQSymbol),
    LoadObject(ModuleFullPath),                                                    // cache-hit-typecheck path enqueues this
}

#[non_exhaustive]
pub enum NiceWork {
    ObjectCodegen(ModuleFullPath),
}

#[non_exhaustive]
pub enum SchedulerError {
    Shutdown,
    ModuleFailed(ModuleFullPath),
    Cycle(Vec<ModuleFullPath>),                                                    // mutual import per Decision 30
}
```

### `ObjectCache` — on-disk `.o` + sidecar pair

```rust
pub struct ObjectCache {
    /* opens {project_root}/target/.cache or equivalent */
}

impl ObjectCache {
    pub fn open(project_root: &Path) -> Result<Self, CacheError>;
    pub fn lookup_sidecar<C: CodeStore, L: LinkerStore>(&self, module: &ModuleFullPath, source_hash: u64) -> CacheLookupResult<C, L>;
    pub fn load_object(&self, module: &ModuleFullPath) -> Result<Vec<u8>, CacheError>;
    pub fn write(&self, module: &ModuleFullPath, artefact: &ObjectArtefact) -> Result<(), CacheError>;
}

#[non_exhaustive]
pub enum CacheLookupResult<C: CodeStore, L: LinkerStore> {
    Hit(SymbolTable<C, L>),                                                        // deserialised; per Decision 25 paired with .o
    Miss,                                                                          // no sidecar, version mismatch, or source changed
}

#[non_exhaustive]
pub enum CacheError {
    NotFound,
    DeserializeFailed(String),
    SchemaVersionMismatch { found: u32, expected: u32 },                           // Decision 34
    Io(std::io::Error),
    /* … */
}
```

### `Code` — the per-entry retention root (Decisions 35 + 41)

Defined in `cranelisp-backend` per Decision 41 (which retracts Decision 35's Layer 2 Option B). Re-exported by int for session-boundary use:

```rust
pub use cranelisp_backend::Code;       // re-export for SymbolTable<Code, ()> instantiation at the session boundary
```

Backend is no longer C-blind — it constructs `Code::Jit(Arc<Jit>)` directly inside `compile_to_module` and writes via Decision 38's `write_code(&self, sym, code)`, and writes the resulting fn pointer to the same entry's `fn_ptr` field (S66 fn_ptr unification — `Code` carries lifecycle owner only). Int still names `Code` at the session-boundary instantiation `SymbolTable<Code, ()>`, but no longer wraps a backend return tuple — the previous post-loop in `worker.rs:2860-3018` (iterate-over-names + GOT-store + `Code::Jit`-construct + three error cascades) collapses into the per-symbol call-site loop:

```rust
for sym in defined_symbols(&shared.symbol_tables[scope]) {
    let jit = Jit::new_with_symbols(&extra)?;
    compile_to_module(scope, &[sym], &shared.symbol_tables, shared.introspection.as_ref(), jit.jit_module())?;
}
```

Decision 35 framing recap: the integration layer instantiates `SymbolTable<Code, ()>` at the session boundary (per Decision 32 — `L = ()` because per-symbol Linker retention via `Code::Linker.linker: Arc<Linker>` covers all needed lifetimes). Principle 3 protection (no `cranelisp-types → cranelisp-backend` dep) survives intact — `Code` lives in `cranelisp-backend`, not in `cranelisp-types`.

### `worker` — the priority + nice worker loops

```rust
pub fn priority_worker_loop(shared: Arc<SharedState>);                             // per pipeline-v4 §4.1
pub fn nice_worker_loop(shared: Arc<SharedState>);                                 // per pipeline-v4 §4.3
```

Workers are spawned by `CompilerSession::new`. Each takes its own `Arc<SharedState>` clone (refcount bump, not deep copy) and loops on `take_*_work_blocking` until `shutdown()`. All access to session state goes through `&shared.*` — no `&mut SharedState` ever exists. Mutation happens through interior mutability of the contained types (DashMap per-entry locks, atomics, etc.). The body is the typecheck-phase / object-codegen-phase shown in `exec-flow-compilation`.

### `LineEditor` — the REPL line-input layer

```rust
pub mod line_editor {
    pub fn read_line(prompt: &str, continuation_state: &mut ContinuationState) -> Result<InputState, ReplError>;
}

#[non_exhaustive]
pub enum InputState {
    Complete(String),
    NeedContinuation(String),
}

#[non_exhaustive]
pub struct ContinuationState {
    pub partial: String,
    pub paren_depth: i32,
}

#[non_exhaustive]
pub enum ReplError {
    Eof,
    Interrupted,
    IoError(std::io::Error),
}
```

### Watcher events

```rust
#[non_exhaustive]
pub struct FileChangeEvent {
    pub module: ModuleFullPath,
    pub content_hash: u64,
}
```

### CLI parsing

```rust
pub mod main {
    pub fn parse_args() -> Result<(Action, ProjectTarget, SessionSettings), CliError>;
    pub fn resolve_target(target: Option<&str>) -> (PathBuf, String);              // per repl/spec.md §0.5
}

#[non_exhaustive]
pub enum Action { Repl, Run, Link, Version, Help }

#[non_exhaustive]
pub enum CliError {
    UnknownFlag(String),
    UnexpectedArgument(String),
    Conflicting(&'static str),
    DirectoryNotFound(PathBuf),
    EntryFileMissing(PathBuf),
}
```

### Observability — `src/io_trace/`, `src/scheduler_trace/`, `src/got_trace/` (per Decision 40 + FIXME 0099 + FIXME 0103)

Per Decision 40, the consumer-side ring buffers and formatters that pre-S65 lived in `cranelisp-runtime` (`trace.rs`, `io_trace.rs`) relocate to int. Per Decision 43, the `IoObserver` registration API lives in `cranelisp-intrinsics`; int registers an observer at session init. Per FIXME 0099, the `GotObserver` registration API lives in `cranelisp-backend`; int registers similarly. All three follow the same shape — env-var-gated activation, per-thread `VecDeque` ring buffer with FIFO overflow, end-of-session flush formatter, RAII guards over the buffers.

```rust
pub mod io_trace {
    /// Registered with intrinsics via `cranelisp_intrinsics::register_io_observer(Some(record))`.
    /// Activates iff REPL/trace mode is on or `CRANELISP_IO_TRACE=1`. Production batch (`--link`,
    /// non-trace `--run`) does NOT register and pays one relaxed null-check load per IO call site.
    pub fn record(tag: cranelisp_intrinsics::IoEventTag, event: &cranelisp_intrinsics::IoEvent);

    /// End-of-session formatter — drains all per-thread ring buffers, merge-sorts by
    /// `cranelisp_intrinsics::trace_anchor()` monotonic origin, writes formatted text to stderr.
    pub fn flush_to_stderr();
}

pub mod scheduler_trace {
    /// Internal scheduler-cadence trace events (form-by-form scheduler dispatch + work
    /// completion + park/wake). Recorded directly by int's scheduler — no external observer
    /// contract because the producer and consumer both live in int. Same monotonic anchor as
    /// io_trace (`cranelisp_intrinsics::trace_anchor()`) so cross-trace merge-sort produces a
    /// coherent ordering.
    pub fn record_event(/* … */);
    pub fn flush_to_stderr();
}

pub mod got_trace {
    /// Registered with backend via `cranelisp_backend::register_got_observer(Some(record))`.
    /// Activates iff REPL/trace mode is on or `CRANELISP_GOT_TRACE=1`.
    pub fn record(tag: cranelisp_backend::GotEventTag, event: &cranelisp_backend::GotEvent);

    pub fn flush_to_stderr();
}

#[non_exhaustive]
pub struct IoTraceFlushGuard {
    /* opaque — RAII guard; on Drop, calls io_trace::flush_to_stderr() */
}

#[non_exhaustive]
pub struct SchedulerTraceFlushGuard {
    /* opaque — RAII guard; on Drop, calls scheduler_trace::flush_to_stderr() */
}

/// Installs a panic hook that flushes the IO and scheduler trace ring buffers
/// on panic so test failures and unexpected aborts surface the trace context.
/// Idempotent; called once at session init when trace mode is active.
pub fn install_panic_hook();
```

`IoTraceFlushGuard` and `SchedulerTraceFlushGuard` are int's own types (per Principle 15 they live where the consumer state lives — int's `src/io_trace/` and `src/scheduler_trace/`). They are NOT intrinsics surface (intrinsics owns only the `IoObserver` extension-point API per Decision 40 + 43). Tests that need to flush at end-of-test use these guards; production binaries activate them implicitly on session init when REPL/trace mode is on.

### Display surface — `src/display.rs` (per FIXME 0108)

Per FIXME 0108, the value/type display formatting (831 LOC pre-relocation in `cranelisp-backend/src/display.rs`) belongs in int — REPL display orchestration is downstream of execution and is an integration-layer concern, not a backend concern. The backend bounded context is "typed AST → executable"; nothing about REPL display crosses boundaries backend exposes. Post-relocation, these helpers live in `src/display.rs`:

```rust
/// Formats a `Type` with FQTypeName module prefixes (e.g. `:primitives/Int`).
/// Used by `format_eval_result`, slash-command output (`/sig`, `/type`, `/info`),
/// and error formatting that includes type display.
pub fn format_type_qualified(ty: &Type) -> String;

/// Formats a `Scheme` (forall-quantified type) with constraints and FQTypeName-qualified
/// argument types — the canonical scheme display per `repl/spec.md` §3. Used by `/sig name`,
/// `EvalResult::Def` display, and `describe_symbol`.
pub fn format_scheme_display(scheme: &Scheme) -> String;
```

Backend imports nothing from display; int's `format_eval_result`, `format_command_result`, `format_error`, and the slash-command flows all call these helpers directly.

### Cache writer — `src/cache_writer.rs` (per Phase 2 reach-around R4)

Per the Phase 2 review §3 reach-around catalogue (R4), `CacheWritePacket` and `process_cache_packet` are caller-specific orchestration types — their single consumer is int's cache writer. They land in int's source per the single-consumer relocation pattern of FIXME 0100, NOT in backend's facade.

```rust
/// Per-module work item written by codegen workers when an `.o` artefact is ready
/// for cache persistence. Internal to int's cache-writer subsystem.
#[non_exhaustive]
pub struct CacheWritePacket {
    pub module: ModuleFullPath,
    pub artefact: cranelisp_backend::ObjectArtefact,        // (.o bytes + sidecar SymbolTable<(), ()>)
}

/// Internal cache-writer pump — consumes a `CacheWritePacket`, hands the artefact to
/// `ObjectCache::write`, and accumulates errors into the session's warnings list.
/// Not re-exported across crates; lives in int's source so the file IO discipline
/// (atomic write + temp + rename, schema-version stamping) stays co-located with the
/// orchestration that drives it.
pub(crate) fn process_cache_packet(packet: CacheWritePacket, cache: &ObjectCache) -> Result<(), CacheError>;
```

### Link orchestration helpers — `src/exe.rs` / `cranelisp-exe-bundle` (per Phase 2 reach-around R5)

Per the Phase 2 review §3 reach-around catalogue (R5), `generate_startup_object` is part of `--link` orchestration and lives on int's side, NOT in backend's facade. The function builds the `_main` alias `.o` per Decision 36 ("Link orchestration" §3 above) and lives in `crates/cranelisp-exe-bundle/`.

```rust
/// Builds the tiny alias `.o` whose only content is an exported `_main` symbol that
/// jumps through `__cranelisp_got_{entry_module}[main_slot]`. Backend stays uniform
/// (bare-Local for every function including `main`); this alias is int's targeted
/// addition for the system linker's expected entry point. Invoked from `link_by_name`.
pub fn generate_startup_object(entry_module: &ModuleFullPath, main_slot: usize) -> Result<Vec<u8>, CranelispError>;
```

### Tracing helpers — `src/trace/` (per Phase 2 reach-around R6)

Per the Phase 2 review §3 reach-around catalogue (R6), `TracedFnInfo` is an int-only consumer concern — it carries metadata about traced function instances (the GOT-swap wrapper machinery for `(trace ...)`) and lives in int's `src/trace/` per Decision 40's relocation. It is NOT part of backend's facade. If a duplicate type previously existed on backend's side, it deletes; `TracedFnInfo` lives in int, sourced from int's tracing subsystem.

```rust
#[non_exhaustive]
pub struct TracedFnInfo {
    pub fq: FQSymbol,
    pub original_code_ptr: *const u8,                  // pre-trace GOT slot value
    pub wrapper_code_ptr: *const u8,                   // post-trace wrapper that emits trace events around the call
    /* … */
}
```

### Public consts

```rust
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
```

---

## `process_form` — the gap-orchestration retry loop

`int::process_form` is the sole orchestrator of the form-processing chain. It composes `frontend::expand`, `frontend::build_form` (returning `Vec<ParsedEntry>` per S66 FIXME 0156), and `cranelisp_typecheck::check_form` (a pure function returning `Vec<(Symbol, ModuleEntry)>` per S66 FIXME 0160); catches their `ResolutionGap` returns; dispatches to the scheduler; and retries until the form fully processes or a non-gap error fires.

Frontend and typecheck stay pure (no `Sess`, no `CompileScheduler` dependency — Principle 3). Workers park inside `wait_for_*` calls — that IS the worker's allowed parking site, never inside library code. `process_form` is THE crossing point where the gap value becomes a scheduler call.

```rust
// process_form runs on workers — takes &SharedState (the worker's Arc clone).
// Per Decisions 25, 33 + the per-symbol mutability model: scope_table is acquired
// via shared .get() (a shared shard read lock on the outer DashMap), NOT via
// .entry().or_default() (which would acquire a per-form whole-module write lock).
// Per-symbol mutation inside check_form goes through the inner DashMap's per-key
// write lock via SymbolTable::insert_or_update(&self, ...).
//
// Phase 0 (write_structural_decls + defn_order seed) ran in register_module
// before this work item was dispatched — see "register_module Phase 0" below.
pub fn process_form(shared: &SharedState, form: Sexp, scope: &ModuleFullPath) -> Result<ProcessedForm, CranelispError> {
    let mut sexp = form;
    loop {
        let expanded = match cranelisp_frontend::expand(sexp.clone(), &shared.symbol_tables) {
            Ok(s) => s,
            Err(ExpansionError::Gap(gap)) => {
                handle_gap(shared, gap)?;
                continue;                                           // retry — gap resolved
            }
            Err(other) => return Err(other.into()),                 // genuine expansion failure
        };

        let parsed_entries = cranelisp_frontend::build_form(&expanded)?;  // build_form returns Vec<ParsedEntry>; no gaps — pure transform (S66 FIXME 0156)

        // Shared shard read lock on m1's SymbolTable. Per Decision 25/33 + per-symbol
        // mutability — check_form takes [&SymbolTable] (not [&mut]) and writes via
        // SymbolTable::insert_or_update(&self, ...) which acquires the inner DashMap's
        // per-entry write lock briefly. No whole-module lock contention with cross-module
        // readers. Phase 0 (in register_module) guarantees the SymbolTable already exists.
        let scope_table = shared.symbol_tables.get(scope)
            .expect("Phase 0 must run in register_module before process_form");

        // S66 FIXME 0160 — check_form is pure: drive once per ParsedEntry returned by build_form
        // (multi-clause defmacro and deftype-with-constructors yield multiple ParsedEntry items).
        // On Ok, accumulate the returned (Symbol, ModuleEntry) pairs for caller-side commit
        // (insert_symbol). On Err(Gap), retry with the same ParsedEntry — nothing was written.
        let mut all_entries: Vec<(Symbol, ModuleEntry<Code>)> = Vec::new();
        for parsed in &parsed_entries {
            let entries = match cranelisp_typecheck::check_form(parsed.clone(), &scope_table, &shared.symbol_tables) {
                Ok(v) => v,
                Err(CheckError::Gap(gap)) => {
                    handle_gap(shared, gap)?;
                    continue;                                       // retry — gap resolved
                }
                Err(other) => return Err(other.into()),             // genuine type error
            };
            all_entries.extend(entries);
        }

        return Ok(ProcessedForm::from(all_entries));
    }
}

fn handle_gap(shared: &SharedState, gap: ResolutionGap) -> Result<(), CranelispError> {
    match gap {
        ResolutionGap::SymbolTypechecked(fq) => {
            ensure_registered(shared, &fq.module)?;
            shared.scheduler.wait_for_typecheck_symbol(&fq)?;
        }
        ResolutionGap::MacroInMem(fq) => {
            ensure_registered(shared, &fq.module)?;
            shared.scheduler.wait_for_typecheck_symbol(&fq)?;
            // Orchestrator-side macro discrimination — peek at the entry now that typecheck is complete.
            // Only force code into memory if it's actually a macro that needs to be invoked.
            let needs_code = shared.symbol_tables
                .get(&fq.module)
                .and_then(|st| st.get(&fq.symbol).map(|entry| {
                    matches!(entry.kind(), DefKind::Macro { .. }) && entry.code().is_none()
                }))
                .unwrap_or(false);
            if needs_code {
                shared.scheduler.priority_boost_jit(&fq);
                shared.scheduler.wait_for_inmem(&fq)?;
            }
        }
        ResolutionGap::Type(fqt) => {
            ensure_registered(shared, &fqt.module)?;
            shared.scheduler.wait_for_typecheck_type(&fqt)?;
        }
    }
    Ok(())
}

fn ensure_registered(shared: &SharedState, module: &ModuleFullPath) -> Result<(), CranelispError> {
    if !shared.symbol_tables.contains_key(module) {
        // Phase 0 — runs synchronously here for the on-demand registration case.
        // Acquires entry(module).or_default() briefly, calls write_structural_decls,
        // drops the RefMut. Then dispatches PriorityWork::Typecheck via scheduler.
        register_module_internal(shared, module)?;
    }
    Ok(())
}
```

(`process_form` is shown as a free function for clarity — the actual Rust may keep it as a `CompilerSession` method that immediately delegates to a free function `worker::process_form(&self.shared, …)`. Workers invoke the free-function form directly with their `&SharedState` reference.)

**Termination.** Each `handle_gap` call advances the dependency state monotonically (registers a module, satisfies a typecheck wait, satisfies an inmem wait). Subsequent retries see strictly more state than the previous attempt; the loop terminates when expand + check_form both succeed, when a non-gap error fires, or when the scheduler returns `SchedulerError::Cycle` (mutual import per Decision 30).

**Gap design rationale** (one round-trip per FQ ref encountered):
- A single FQ ref produces one gap → one `handle_gap` → one retry. The loop doesn't fire N+1 round-trips per FQ.
- `expand` returns `MacroInMem(fq)` uniformly for any FQ ref it can't yet resolve — regardless of whether the module is unregistered, typecheck is incomplete, or code is missing. Expand stays uniform; the gap-name reflects expansion's MAXIMUM possible need.
- The orchestrator owns the **macro-vs-fn discrimination**. After `wait_for_typecheck_symbol` completes, it peeks at the entry: only forces a JIT (`priority_boost_jit` + `wait_for_inmem`) if the entry actually IS a macro with missing code. Functions are NOT speculatively JIT-pushed — the function will be JIT'd when its caller is processed. This avoids yanking a function ahead of pending priority work for code that expand never actually needs.
- `check_form` asks for `SymbolTypechecked` only — by the time check_form runs, any macros are already expanded out, so only types/schemes are needed.
- Multiple FQ refs in the same form still cost one round-trip each (expand or check_form returns at the first unresolved ref). Batching across multiple gaps in one return would require expand/check_form to continue past the first unresolved ref and accumulate; deferred until profiling shows it matters.

## Composed introspection flows (slash commands)

Slash commands are **composed flows over the existing primitives**, not new facade surface. They orchestrate `CompilerSession` accessors and other facade calls. Each flow below shows: what reads, what calls, what produces.

### `/list` — current REPL module's defined symbols

- Read: `Sess::list_user_definitions() -> Vec<SymbolInfo>` (filters `ST_current.defined_symbols()` to user-authored entries, categorises by `DefKind`).
- Format: per `repl/spec.md §3.3` — categories (Modules, Macros, Traits, Types, Fns), one line per entry with `:Type name ; classification - docstring`.

### `/imports`, `/exports <module>` — module visibility

- `/imports`: `Sess::module_imports(current_repl_module) -> &[ImportSpec]` plus the special-forms always-available list.
- `/exports m`: `Sess::module_exports(m) -> Vec<(Symbol, &ModuleEntry<Code>)>` filtered to `Visibility::Public`.

### `/sig name`, `/doc name`, `/type name`, `/info name`, `/source name`

- `Sess::describe_symbol(name) -> Option<SymbolDescription>` — looks up `name` in `current_repl_module` (or as FQ if dotted), returns scheme + docstring + source per `repl/spec.md §3.6`. The `source` field on `SymbolDescription` mirrors `Sess::symbol_source(fq)` for one-shot describe convenience.
- `/source name`: `Sess::symbol_source(fq) -> Option<String>` — reads `shared.introspection[fq].source` per Decision 39 (per-defn source on Introspection — no module-global source store; spans on Defn are per-defn-local).

### `/sexp name`, `/ast name`, `/clif name`, `/disasm name` — codegen artefact inspection

- `/sexp`: `Sess::symbol_sexp(fq)` — reads `shared.introspection[fq].sexp`. Populated by the parser at parse-time when introspection is enabled (REPL or trace mode).
- `/ast`: reads `entry.ast` directly from `ModuleEntry::Def` — `ast` is always present (it's the codegen-compilable predicate per Decision 22), no introspection dependency.
- `/clif`: `Sess::symbol_clif(fq)` — reads `shared.introspection[fq].clif_ir`. Populated by JIT codegen when trace mode is active (`CRANELISP_CODEGEN_TRACE` or REPL-trace).
- `/disasm`: `Sess::symbol_disasm(fq)` — reads `shared.introspection[fq].disasm`. Same population condition.
- `/clif` and `/disasm` formatting headers also use `Sess::symbol_code_size(fq)`.
- All four accessors return `None` in production batch mode (introspection is `None`); slash commands surface "not available — REPL/trace mode required" in that case.

### `/time name`, `/mem` — performance / allocation stats

- `/time`: `Sess::symbol_compile_duration(fq) -> Option<Duration>` — reads `shared.introspection[fq].compile_duration`. Populated by the codegen wrapper when introspection is enabled.
- `/mem`: composes `cranelisp_intrinsics::{alloc_count, dealloc_count, bytes_allocated, bytes_current, bytes_peak}` directly (post-Decision-43; the allocator and stats accessors live in `cranelisp-intrinsics`). No new int facade method needed — `process_command` in the `/mem` branch calls these and formats the result.

### `/run-tests` — the most composed flow

Per `spec/09-macros.md` and `repl/spec.md`:
- Iterate `ST_current.defined_symbols()` filtered to symbols whose name starts with `test-` (or matches a configured pattern).
- For each match: `Sess::trampoline(code_ptr_of_symbol, expected_type)` — per-test eval. Capture pass/fail from the result type (test fns return `(Option String)` per `lib/testing.cl`).
- Accumulate pass/fail; print summary.

This flow uses no new facade surface. `Sess::trampoline` (already exposed for Run mode) is the per-test invocation; iteration is via existing `defined_symbols`.

### `/mod [name]`, `/reload [name]` — module switching + reload

- `/mod name`: `Sess::set_current_repl_module(name)`. The next `eval` appends to the new module.
- `/reload [name]`: `Sess::re_register_module(name)`. Triggers the watcher branch of `exec-flow-compilation`.

### `/expand src` — show macro expansion

- Composes `cranelisp_frontend::parse(src)` + `cranelisp_frontend::expand(sexp, &symbol_tables)` for each top-level form. Display the post-expansion Sexp.

---

## Link orchestration (`--link` mode)

`Sess::link_by_name(module_name)` is the sole `--link` entry. Internals (per `exec-flow-link` LINK phase):

1. **Validate `main`.** Look up `SymbolTable[entry_module].symbols["main"]`. Confirm it exists and the scheme matches `repl/spec.md §0.2.1` (`(fn [] (IO Int))`, `(fn [] (IO Bool))`, `(fn [] Int)`, etc.). Surface mismatch as `CranelispError::LinkError`.

2. **Read `main`'s GOT slot.** `let main_slot = SymbolTable[entry_module].symbols["main"].got_slot;` — this is the `__cranelisp_got_{entry_module}` slot index for `main`. Captured for the alias `.o`.

3. **Emit `_main` alias `.o`.** Backend's `compile_to_object` does NOT emit `_main` (per Decision 36 — backend stays uniform: bare-Local for every function including `main`). `int` constructs a tiny additional `.o` whose only content is:
   - An `Linkage::Export` symbol named `_main` (or `main` on Linux) declared as a code symbol whose body is a single relocation: `jmp [__cranelisp_got_{entry_module} + main_slot * 8]` (or the equivalent indirect call). Lives in `crates/cranelisp-exe-bundle/`.

4. **Collect `.o` paths.** For the entry module + every transitively-loaded module, read the `.o` path from `ObjectCache`. (The `wait_for_object_codegen()` call earlier in `exec-flow-link` ensures all `.o` files are written.)

5. **Spawn system linker.** `std::process::Command::new("ld")` (macOS / Linux) or `"link.exe"` (Windows) with arguments:
   - `-o {project_root}/target/{entry_module}` (executable output path; `.exe` on Windows)
   - The collected `.o` paths
   - The alias `.o` from step 3
   - The `cranelisp-intrinsics` and `cranelisp-primitives` static archives (linked at build time via `build.rs`; paths captured in consts) — post-Decision-43 the previously-single `cranelisp-runtime` archive is replaced by these two siblings
   - Any platform `.dylib`/`.so` files for transitively-loaded platforms
   - Standard system libraries (`-lc`, etc. — platform-specific)

6. **Surface failures.** Non-zero exit code from the linker becomes `CranelispError::LinkError { message: stderr }`.

The system linker invocation is opaque to the facade — `std::process::Command` is not wrapped in a Cranelisp facade type. The contract is: backend's `.o` files conform to the Object file contract (see `facades/backend.md`), and `int` invokes ld with them plus the alias. The two-GOT model in Decision 23 means the `.o` data section GOT (`Linkage::Export __cranelisp_got_{module}`) is what ld resolves; the in-memory GOT is irrelevant in `--link` mode.

---

## Re-exports from `cranelisp-types`

```rust
pub use cranelisp_types::{
    CodegenBehaviour, ModuleStrategy,
    Symbol, ModuleFullPath, FQSymbol, FQTypeName,
    Sexp, Type, Scheme, SymbolTable, ModuleEntry, DefKind,
    ImportSpec, ExportSpec, NamedImport, NamedExport, ImportNames, PlatformSpec, ModDecl,
    CranelispError, Warning, Span,
    PrimitiveDef, PrimitiveKind, SchedulingClass,
    GotTable, GOT_TABLE_SIZE,
    CheckResult, CheckError, ResolutionGap, ReplSnapshot,
};
```

Re-exports cover every type that crosses `int`'s public surface.

---

## Consumed surface

The integration crate imports from:

- **`cranelisp-types`** — the full set above.
- **`cranelisp-frontend`** — `parse`, `expand`, `build_form` (returns `Vec<ParsedEntry>` per S66 FIXME 0156; replaces the prior `build_ast` shape at the per-form boundary), `build_expr`, `extract_module_declarations`, `synthesize_macro_clause_defn`, `next_synthetic_span`, `is_defmacro`, `is_begin`, `flatten_begin`, `expand_quasiquotes`, `parse_preserving_comments`, `ParseProduct`, `Ast`, `ExpansionError`. (Per FIXME 0156 resolution: `parse_defmacro` becomes `pub(crate)` inside `build_form`'s dispatcher; `DefmacroInfo` and `ParsedEntry` move to `cranelisp-types` — int imports both from there.)
- **`cranelisp-typecheck`** — `check_form`, `register_builtins`, `CheckResult`, `CheckError`, `CheckState`, `TypeCheckEnv`, the trace install hook.
- **`cranelisp-backend`** — `compile_to_module` (returns `Result<(), CompilationError>` per Decision 41; writes `Code::Jit` and `Introspection` directly into the passed-in shared stores via `&self`-interior-mutable methods), `load_object`, `compile_to_object`, `Code` (re-exported per Decision 41), `LinkerArtefact`, `ObjectArtefact`, `Jit`, `Linker`, `CompilationError` (with `SymbolNotCompilable` variant per §2.7), `GotObserver` + `GotEvent` + `GotEventTag` + `GotProvenance` + `register_got_observer` (per FIXME 0099 — backend-originated observer types, int registers consumer state). Cranelift `Module`, `JITModule`, `ObjectModule`, `JITBuilder` (via cranelift crates re-exported from backend).
- **`cranelisp-intrinsics`** — backend-emitted intrinsic extern functions registered with the JIT (via `JITBuilder::symbol`) per Decision 43: `cranelisp_alloc`, `heap_alloc_payload`, `heap_dealloc`, `rc_inc`, `rc_dec`, `consume_shallow`, `dec_shallow_io`, `vec_*`, `heap_alloc_string`, `string_read`, `sconcat`, `quote_sexp`, `cranelisp_run_io`, `io_run`, `run_io_trampoline`, `ivar_*`, `runtime_panic`. Stats accessors (`alloc_count`, `dealloc_count`, `bytes_allocated`, `bytes_current`, `bytes_peak`, `reset_counts`) for `/mem`. The IO observer extension point (`IoEvent`, `IoEventTag`, `IoObserver`, `register_io_observer`, `trace_anchor`) per Decision 40 — int registers an `IoObserver` at session init when REPL/trace mode is on or `CRANELISP_IO_TRACE=1`.
- **`cranelisp-primitives`** — user-callable primitive extern functions registered with the JIT and seeded into the synthetic `primitives` module's symbol table by `int` at session init per Decision 43: integer ops (`add_i64`, `sub_i64`, `mul_i64`, `div_i64`, `mod_i64`, `eq_i64`, `lt_i64`, `gt_i64`, `le_i64`, `ge_i64`), float ops, `not`, conversions (`int_to_string`, `parse_int`, `float_to_string`, `bool_to_string`). Each primitive gets a GOT slot (so `(let [f +] (f 1 2))` resolves through the slot).
- **`cranelisp-platform`** — `HostContext`, `HostCallbacks`, `OwnedPlatformFnDescriptor`, `PlatformFn`, `load_manifest`, `parse_type_sig`, `derive_jit_name`. `int` constructs `HostCallbacks` at session init pointing at runtime fns.
- **`cranelisp-exe-bundle`** — for `--link` mode. The crate provides the alias `.o` template + system linker invocation helpers. Per `bounded-contexts.md` §6 — exe-bundle is part of the binary surface; one D/D/R cycle covers both.

External:
- **`rustyline`** (or equivalent) — for the line editor.
- **`notify`** — for the file watcher.
- **`libloading`** (transitively via platform) — for DLL loading.
- **`dashmap`** — for the SymbolTables map.
- **`rayon`** — for IO trampoline `Par` fork-join (used by runtime, but `int` configures the rayon pool size from `SessionSettings`).

---

## Sealed traits

None implemented. `int` does not implement traits from `cranelisp-types`.

---

## `#[non_exhaustive]` DTOs

All public DTOs published from `int` are `#[non_exhaustive]`:
- `SessionSettings`, `ProjectTarget`
- `EvalResult`, `EvalValue`, `HeapRetention`
- `CommandResult`, `SlashCommand`
- `SymbolInfo`, `SymbolDescription`, `SymbolCategory`
- `PriorityWork`, `NiceWork`, `SchedulerError`
- `CacheLookupResult`, `CacheError`
- `InputState`, `ContinuationState`, `ReplError`
- `FileChangeEvent`
- `Action`, `CliError`
- `IoTraceFlushGuard`, `SchedulerTraceFlushGuard` (per Decision 40 + FIXME 0103)
- `CacheWritePacket`, `TracedFnInfo` (per Phase 2 reach-around R4 + R6 — single-consumer relocations)

`Code` is a `pub` enum without `#[non_exhaustive]` — both variants are load-bearing per Decision 35 and the integration layer pattern-matches exhaustively at known sites. New variants would be a deliberate extension requiring `/arch` decision.

---

## Bounded-context invariants

These hold across sprints — the contract `int` makes with the rest of the workspace:

1. **Single CompilerSession.** Per pipeline-v4 §1 — one `CompilerSession` per process. Run / Link / REPL all use it; the only difference is which methods are invoked after `register_module`. Workers are spawned at session construction and live for the session.

2. **Workers are persistent.** Per Decision 27 — priority workers are spawned once per session and parked on condvars; not respawned per work item. (The G9 persistent-worker refactor is Sprint 57's work; this facade reflects the post-G9 target.)

3. **`Code` lives in `cranelisp-backend` (Decision 41 amends Decision 35; S66 amendment slims variants).** The concrete `C` parameter for `SymbolTable<C, L>` is `Code` — the enum lives in `cranelisp-backend/src/code.rs` (moved per Decision 41 from the previous `src/code.rs` location). `cranelisp-types` stays Cranelift-ignorant — Principle 3 protection intact. Backend constructs `Code::Jit(Arc<Jit>)` directly and writes via Decision 38's `write_code(&self, sym, code)` (interior-mutable; no `&mut` flow needed), and writes the resulting fn pointer to the same entry's `fn_ptr` field (S66 fn_ptr unification — `Code` carries lifecycle owner only; the call address lives on `ModuleEntry::Def.fn_ptr`). Decision 35 Layer 2 Option B retracts. `int` re-exports `Code` for session-boundary `SymbolTable<Code, ()>` instantiation; the previous worker-side post-loop (iterate-over-names + GOT-store + `Code::Jit`-construct + three error cascades) collapses into the per-symbol call-site loop documented in `facades/backend.md` §"`Code` — the per-symbol lifecycle owner". Backend signatures use `&DashMap<ModuleFullPath, SymbolTable<Code, ()>>` (non-blind for `C`); non-codegen crates (frontend, typecheck) stay generic on `SymbolTable<(), ()>` per Decision 32's empty-marker traits.

4. **Scheduler is sole coordination authority.** Per the runtime/platform diagrams' explicit merge — `CompileScheduler` owns BOTH work dispatch AND per-symbol/per-module wait/release. There is no separate `DependencyService`.

5. **`process_form` + `insert_symbol` is the shared form-processing entry.** Per `exec-flow-compilation` and `exec-flow-repl` — workers and eval both call `process_form` for typechecking; defining-form callers follow up with `insert_symbol`. Eval expressions skip `insert_symbol` (temp closure — no commit target).

5a. **`process_form` is the gap-orchestration crossing point.** Frontend and typecheck stay pure — they surface dependencies as `Err(ExpansionError::Gap(ResolutionGap))` / `Err(CheckError::Gap(ResolutionGap))`. `int::process_form` is the sole crate-crossing where gap values become scheduler calls (`handle_gap` → register + wait + priority_boost). Workers park inside the scheduler's `wait_for_*` calls — never inside frontend or typecheck library code. See "`process_form` — the gap-orchestration retry loop" above.

6. **Per-eval JIT lifetime (Decision 31).** Per pipeline-v4 §6.2 — each eval expression compiles its temp closure on a fresh `JITModule` wrapped in `Arc<Jit>`. The wrapper's custom `Drop` reclaims pages when the trampoline returns and the value is consumed.

7. **REPL never calls `wait_for_*` at startup.** Per the `exec-flow-repl` rewrite — startup is `register_module` only. The first iteration's STEP 4 wait catches up the entry module's in-mem code. This keeps the prompt responsive immediately.

8. **Watcher events processed concurrently with prompt-wait.** Per `exec-flow-repl` STEP 1–STEP 3 — `set_repl_input_active(true)` opens the watcher window during `read_line`; `set_repl_input_active(false)` closes it on input submission. STEP 4's `wait_for_inmem_codegen()` catches up everything triggered during the prompt.

9. **Definitions append to `current_repl_module`, not `user`.** Per `exec-flow-repl` — `current_repl_module` is the session-scoped target for `eval`'s defining forms. Defaults to the entry module from `parse_args`. `/mod` changes it. `"user"` is a default name, not architecturally special.

10. **Additive append, not re-register.** Per `exec-flow-repl` — `Sess::eval` for a defining form calls `Sched::append_form(current_repl_module, sexp)` and waits for that single symbol's typecheck + jit. The whole module is NOT re-typechecked.

11. **Cache-hit decision lives at `notify_typecheck_done_from_cache` (Decision 37).** Cache-hit-typecheck path enqueues `LoadObject(m1)` only; cache-miss path uses per-symbol `Jit(fq)`. The decision is implicit in which `notify_typecheck_done_*` variant fires — no mid-flight cache rechecking.

12. **`--link` emits the `_main` alias (Decision 36).** Backend stays uniform (bare-Local for every function); `int::link_by_name` emits the entry-point alias `.o` that exports `_main` as a relocation against the entry module's `__cranelisp_got_{module}[main_slot]`. This is one targeted alias, not a whole-module asymmetry.

13. **`Code::Jit` and `Code::Linker` retention dissolves on session shutdown.** Per Decisions 31 + 35 — `drop(Sess)` drops every `ModuleEntry::Code`; the `Arc<Jit>` and `Arc<Linker>` chains reach refcount 0; custom `Drop` reclaims pages.

14. **Mutual-import deadlock is a known constraint (Decision 30).** Two modules `A` and `B` that each import from the other will deadlock the form-by-form scheduler. Documented; not fixed by this facade. Workaround: `discover-tests` + `run-test` builtins for test scaffolding (per Decision 30's "Safe patterns").

15. **`SharedState` vs `CompilerSession` split is mode-aligned (Decision 38).** `SharedState` carries everything reachable by workers — `symbol_tables`, `scheduler`, `cache`, `kept_dlls`, `introspection`, read-only configuration. `CompilerSession` carries everything reachable only by the initiator thread — watcher channel, REPL eval cursor, worker pool handles, accumulated warnings. Workers receive `Arc<SharedState>` at spawn, never see `CompilerSession`. No worker-side merge step: all mutation happens through interior mutability of the contained types under per-cell locks.

16. **Per-symbol mutability after Phase 0 (Decision 38, FIXMEs 0008/0009).** `register_module` runs Phase 0 synchronously: `parse → entry(m).or_default() → write_structural_decls → drop RefMut`. After Phase 0, all SymbolTable access is `&SymbolTable` + per-entry inner-DashMap locks. `process_form` uses shared `.get(&scope)`, not `.entry().or_default()`. `check_form` takes `&SymbolTable`, not `&mut`. The only `&mut SymbolTable` operations are Phase 0 (structural decls + defn_order seed) and per-form REPL appends to `defn_order`.

17. **Introspection is mode-conditional (Decisions 38, 39).** `shared.introspection` is `Some(DashMap)` iff REPL mode OR `CRANELISP_CODEGEN_TRACE` is set. Production batch leaves it `None` and pays zero per-symbol metadata overhead. Source text is per-defn on `Introspection.source` — there is no module-global source store. Parse errors capture context inline (in `ErrorLocation.context`); typecheck/codegen errors capture coordinates (`line_col` + `fq`) and let the formatter resolve source via introspection at display time.
