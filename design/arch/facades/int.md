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
    // Sprint 67 Cluster B sub-fire 2 (per `src/session_v4.rs:923-980`) collapsed
    // the prior 3 worker-handle fields (`priority_worker_handles`,
    // `nice_worker_handles`, `nice_workers`) into the single `WorkerPool` facade
    // entry (sub-fire 2a/2b), relocated `current_repl_module` off SharedState
    // (sub-fire 2d), and added `repl_input_active` + `warnings` to give the
    // facade-prescribed accessors a real backing store (sub-fire 2c).
    error_modules: HashSet<ModuleFullPath>,                                        // REPL-eval failure accumulator; consulted by /list + diagnostic surfacing
    watcher: Option<WatcherChannel>,                                               // notify::Event receiver (impl: `src/watch.rs:22 FileWatcher`)
    worker_pool: WorkerPool,                                                       // priority + nice handles + nice-count; joined on shutdown / Drop
    current_repl_module: ModuleFullPath,                                           // /mod state; PIF-relocated from `SharedState.current_module` in sub-fire 2d (REPL is single-threaded — no Mutex)
    repl_input_active: Arc<AtomicBool>,                                            // shared with watcher event handler via Arc clone; watcher-windowing read pending (FIXME residual; S68)
    warnings: Vec<Warning>,                                                        // initiator-collected accumulator; worker → session merge wiring pending (FIXME residual; S68)
}

impl CompilerSession {
    // Construction
    pub fn new(settings: SessionSettings, project_root: PathBuf) -> CompilerSession;

    // Module registration (entry point — fire-and-forget per exec-flow-compilation)
    // Phase 0 (parse + write_structural_decls) runs synchronously here, before dispatching PriorityWork::Typecheck.
    pub fn register_module(&mut self, module: &ModuleFullPath) -> Result<(), CranelispError>;
    pub fn re_register_module(&mut self, module: &ModuleFullPath) -> Result<bool, CranelispError>;       // file watcher path; Sprint 67 W1 PIF target — thin forward to `self.shared.scheduler.re_register_module(module)` (currently only `CompileScheduler::re_register_module` exists at `scheduler.rs:412`; the `CompilerSession`-level forward lands in W3)

    // Shared cluster-processing entry — used by both compilation worker and eval (per exec-flow-compilation + exec-flow-repl).
    // Per Decision 44 (amended FIXME 0167 for Approach B + SymbolTableAccess; 2026-05-13 third amendment collapsing the
    // two-pass split into a single typecheck call) — a cluster is one form (non-`begin` REPL input), the contents of
    // (begin form₁ ... formN) (explicit REPL cluster), or a file's non-structural forms (batch one-big-cluster). The
    // orchestrator constructs SymbolTableAccess::Cluster { modules, staging, current_module }, threads &mut ctx through one
    // `cranelisp_typecheck::check_forms` call (typecheck mutates staging via ctx.current_symbol_table_mut() — the same
    // accessor used in committed-mode; the two-pass discipline is internal to check_forms), and commits atomically on
    // success by draining staging into the live SymbolTable.
    //
    // Sprint 67 W1 PFR — `process_cluster` and `insert_cluster` are NOT
    // `CompilerSession` methods; they are free functions in `src/cluster.rs`
    // (lines 177 / 248) that take `&SharedState`. Workers call the free-fn
    // form directly with their `Arc<SharedState>` clone; the initiator thread
    // calls it via `&self.shared`. This is the durable shape and matches the
    // "process_cluster — the cluster-atomic orchestration loop" section
    // further down in this file (free-fn definition). The pre-S67 facade
    // text showed `CompilerSession` methods; that shape never landed in
    // source. The free-fn form is canonical.
    //
    // ```rust
    // pub fn process_cluster(shared: &SharedState, forms: Vec<Sexp>, scope: &ModuleFullPath) -> Result<ProcessedCluster, CranelispError>;
    // pub fn insert_cluster(shared: &SharedState, processed: ProcessedCluster, target: &ModuleFullPath);
    // ```

    // REPL eval — composes process_cluster + insert_cluster (defns) or process_cluster + temp-closure JIT (expressions).
    // Eval unwraps a top-level `(begin ...)` into its inner forms before constructing the cluster; non-`begin` inputs
    // become single-form clusters.
    pub fn eval(&mut self, src: &str) -> Result<Option<EvalResult>, CranelispError>;

    // REPL slash-command dispatch
    pub fn process_commands(&mut self, input: &str, stdout: &mut impl Write) -> CommandResult;

    // Trampoline — the runtime cadence entry (per exec-flow-runtime)
    pub fn trampoline(&mut self, module_name: &str) -> Result<(i64, Type), CranelispError>;              // Run mode + REPL eval expression form

    // Cli pre-exit affordances (per exec-flow-run, exec-flow-link, exec-flow-repl)
    // Sprint 67 W1 PFR — names canonicalised against `scheduler.rs:930/1021`
    // (`CompileScheduler::wait_inmem_complete` / `wait_object_complete`); the
    // `CompilerSession` forwarders adopt the same shorter name. Pre-S67 facade
    // text said `wait_for_inmem_codegen` / `wait_for_object_codegen` — those
    // names never landed in source.
    pub fn wait_inmem_complete(&self) -> Result<(), CranelispError>;
    pub fn wait_object_complete(&self) -> Result<(), CranelispError>;

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
    //
    // Sprint 67 W1 PIF target — the whole introspection-accessor family is
    // absent from `src/` pre-S67. /dev Wave 3 authors the bodies. Per the
    // REV-3 discipline (read-side-only accessors), every accessor reads from
    // `shared.symbol_tables` and `shared.introspection` ONLY — no
    // `SharedState` restructure is required to land them, and no `&mut self`
    // is required on the reads (the two mutating methods —
    // `set_current_repl_module`, `set_repl_input_active` — write to
    // `CompilerSession`-side state per the SharedState alignment plan's PIF
    // direction for `current_module` and `repl_check_state`). The accessors
    // are pure projections; FQSymbol resolution from a bare `&str` is shared
    // through a `resolve_symbol_name(&self, name: &str) -> Option<FQSymbol>`
    // helper that consults `current_repl_module()` for unqualified lookups.
    pub fn list_user_definitions(&self) -> Vec<SymbolInfo>;
    pub fn describe_symbol(&self, name: &str) -> Option<SymbolDescription>;
    pub fn module_imports(&self, module: &ModuleFullPath) -> Vec<ImportSpec>;
    pub fn module_exports(&self, module: &ModuleFullPath) -> Vec<(Symbol, ModuleEntry<Code>)>;
    pub fn current_repl_module(&self) -> &ModuleFullPath;
    pub fn set_current_repl_module(&mut self, module: ModuleFullPath);                                   // /mod implementation; writes CompilerSession.current_repl_module per SharedState plan PIF direction

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
    /// Impl uses the `SessionSymbolTable` alias (= `SymbolTable<Code, ()>`).
    /// Materialised as the canonical `SymbolTables<Code, ()>` typedef in
    /// `cranelisp-types` (see `crates/cranelisp-types/src/module.rs`
    /// `SymbolTable` rustdoc + `bounded-contexts.md` §7).
    pub symbol_tables: SymbolTables<Code, ()>,

    /// Session-level module-alias storage — parallel to `symbol_tables`,
    /// keyed by the alias's full path (e.g., `m.n.str` for an alias `str`
    /// declared inside module `m.n`). Written by the parse-time alias
    /// installer (int-side / frontend StructuralDecl processing — NOT a
    /// typecheck concern: typecheck reads `module_aliases` read-only during
    /// §8.6.6 resolution and does not populate it); read by §8.6.6
    /// qualified-name resolution everywhere a qualified name might traverse
    /// an alias.
    /// Cross-table mount-vs-submodule conflict check applies at insert time
    /// (see `bounded-contexts.md` §7 "Per-namespace insertion-time conflict
    /// enforcement"). Per Decision pending S69 W3
    /// — full path keying chosen over per-module-segment storage so the
    /// resolver does single-table longest-prefix-match rather than
    /// segmenting per-module.
    pub module_aliases: ModuleAliases,

    /// Monotonic counter for fresh type variable IDs. Per Decision 44 +
    /// `facades/typecheck.md` `TypeCheckEnv::new(modules, next_id)`, all
    /// TypeCheckEnv instances borrow this `&AtomicU32` to allocate fresh
    /// vars across concurrent workers. **Int-internal — no clean alternative
    /// carrier**; typecheck APIs take the reference directly. S68: PFR
    /// remains stable.
    pub next_type_id: AtomicU32,

    // ──────────── Coordination ────────────
    /// Work dispatch + per-module/per-symbol readiness coordination.
    /// Workers call notify_* on completion and wait_for_* on dependencies.
    pub scheduler: CompileScheduler,                                               // facade ideally prescribes `Arc<CompileScheduler>`; impl holds it inline — S68 PFR may wrap. Drift noted (cosmetic).

    /// Object cache — workers read sidecars + .o on cache-hit, write on
    /// cache-miss codegen. **Sprint 67 Cluster B sub-fire 3 landing**: the
    /// pre-S67 four scattered fields (`cache_dir: Option<PathBuf>`,
    /// `cache_state: Mutex<Option<CacheState>>`, `compiled_o_paths:
    /// Mutex<Vec<PathBuf>>`, `cached_modules: Mutex<HashSet>`) collapse
    /// here. `cached_modules` deletes entirely (scheduler-only via
    /// `CompileScheduler::cached_module_*`). See §"ObjectCache" below.
    pub cache: Arc<ObjectCache>,

    // ──────────── Long-lived runtime state ────────────
    /// Loaded platform DLLs — session-global, kept alive for the session's
    /// lifetime (per /platform addendum §A3). **Target shape (post-Submission-21):
    /// the DLL handle relocates to the platform module's own
    /// `SymbolTable.dll: Option<D>` field** per spec §8.9.3 (see
    /// `crates/cranelisp-types/src/module.rs` `SymbolTable` rustdoc
    /// + `D: DllStore` generic; `ModuleEntry::PlatformDecl`
    /// retires alongside). The interim `kept_dlls` field is retained
    /// only as the transitional carrier; once the source migration in
    /// the /dev wave-3 concurrency-cluster brief lands the `D` generic
    /// + `dll: Option<D>` field on the platform module's SymbolTable,
    /// the platform-load path writes the handle there and `kept_dlls`
    /// retires entirely. **There is NO separate session-level
    /// `platform_dlls` field** — earlier sketches that proposed one
    /// are superseded by the SymbolTable-co-location architecture.
    /// Platform-module introduction flows through the existing
    /// `ensure_module_exists` path against the `platform.<name>` key;
    /// idempotency by `ModuleFullPath` uniqueness in `symbol_tables`.
    pub kept_dlls: Mutex<Vec<LoadedPlatform>>,

    /// File path → module path mapping for the file-watcher cascade.
    /// Populated during `handle_import` when modules are first discovered;
    /// read by `try_pop_changes` to identify which module a changed file
    /// belongs to. Worker-shared by nature. **Int-internal — S68 PFR**
    /// (S67 W1 plan row: facade widens).
    pub file_to_module: Mutex<HashMap<PathBuf, ModuleFullPath>>,

    /// Flag for nice worker priority promotion during hot flush (Step 10).
    /// Set by `wait_object_complete` (initiator); read per-iteration by
    /// `spawn_nice_workers`. Worker-shared atomic. **Int-internal — S68 PFR**
    /// (S67 W1 plan row: facade widens).
    pub promote_nice_workers: AtomicBool,

    /// Test runner state used by the `run-test` / `discover-tests` JIT
    /// intrinsics (Sprint 66 Wave 3a-γ; src/CLAUDE.md §"Int-owned JIT
    /// intrinsics"). **Boxed for session-lifetime pointer stability** — the
    /// `TEST_RUNNER` thread-local stores `*const TestRunnerState` derived
    /// from this Box, so the alloc must not move. Lifted from per-compile
    /// init to session-wide init so the test intrinsics may be registered
    /// unconditionally at every JIT setup (architectural answer to
    /// FIXME 0177). **Int-internal — S68 PFR** (S67 W1 plan row: facade
    /// widens). `current_module: Mutex<ModuleFullPath>` sub-field carries
    /// the REPL `/mod` indirection.
    pub test_runner_state: Box<TestRunnerState>,

    // ──────────── REPL / trace introspection (Decision 38) ────────────
    /// Per-symbol introspection metadata — sexp, source, clif_ir, disasm,
    /// code_size, compile_duration. **Facade prescribes
    /// `Option<DashMap<FQSymbol, Introspection>>`** (None outside REPL/trace
    /// mode — zero overhead per Decision 38). **Impl is `DashMap` direct
    /// (always allocated)** — S68 PFR-rename to wrap in `Option`. Drift noted.
    /// Per-defn source lives here per Decision 39 — there is no separate
    /// module_sources field.
    pub introspection: DashMap<FQSymbol, Introspection>,

    // ──────────── REPL-only carry-forward (S68 PIF — relocate to CompilerSession) ────────────
    /// REPL carry-forward: CheckState that persists across REPL evals
    /// (substitution, scope stack, overloads, module aliases). None in
    /// batch mode (CheckState is stack-local per worker). **Live in S67**:
    /// read by both REPL eval paths (`session_v4.rs:2395, 3377`) + the
    /// `tc_snapshot`/`tc_restore` REPL error-recovery primitives; mutated
    /// by `/mod` (`session_v4.rs:1152`). Facade-plan `PIF — relocate to
    /// CompilerSession`; deferred to S68 (gated on cluster-atomic
    /// completion).
    pub repl_check_state: Mutex<Option<CheckState>>,

    // ──────────── Cluster-atomic transition residuals (S68 PIF — delete via redesign) ────────────
    /// Sexps awaiting typecheck, keyed by module. Populated by
    /// `register_module_with_source` / `reload_module` on the main thread;
    /// read (and removed when complete) by persistent priority workers.
    /// **Cross-thread dep-publishing handshake**; the cluster-atomic flip
    /// (Decision 44, FIXME 0179) eliminates the need (in-call-stack value
    /// only). Currently load-bearing; S68 redesign deletes.
    pub module_sexps: Mutex<HashMap<ModuleFullPath, Vec<Sexp>>>,

    /// Per-module suspension state for resuming a partially-typechecked
    /// module when a dependency becomes available. **Load-bearing in S67**
    /// for the pre-cluster-atomic resume-on-dep-arrival path (see
    /// `src/CLAUDE.md` "Known regressions from Wave 3a-β collapse"). The
    /// facade-plan direction `PIF — relocate or eliminate` is correct;
    /// cluster atomicity (gated on FIXME 0179 read-union) eliminates this
    /// state by construction.
    pub suspend_states: Mutex<HashMap<ModuleFullPath, ModuleSuspendState>>,

    /// Per-module typecheck products. **Vestigial — Sprint 56 gutted most
    /// fields; 2 thin fields survive** (the parallel-store role is replaced
    /// by reads off `symbol_tables[m].defined_symbols()`). S68 migrates the
    /// last residuals onto `SymbolTable` and deletes the field.
    pub typecheck_products: DashMap<ModuleFullPath, TypecheckProduct>,

    // ──────────── Configuration ────────────
    // Sprint 67 Wave 4 follow-up: `codegen_behaviour: CodegenBehaviour` was
    // here. Retired. The frontend `build_form` / `build_expr` boundary is
    // mode-agnostic; `(trace ...)` in `--link` standalone-binary mode fails at
    // link time via the architecture's natural missing-symbol detection. The
    // session-construction value still lives on `SessionSettings` for
    // potential future consumers; no projection onto `SharedState` is needed.

    /// Project root directory (read-only after construction).
    pub project_root: PathBuf,

    /// Lib directories for module resolution (§8.11.2 tier 3). **Wrapped
    /// in `Mutex` to support runtime reconfiguration (tests + future
    /// reload)** — workers hold the lock only for a single read per
    /// compile. Facade prescribed plain `Vec`; the `Mutex` shape is the
    /// reality and the right shape. S67 W1 PFR: facade widens.
    pub lib_dirs: Mutex<Vec<PathBuf>>,

    /// Extra platform DLL search directories (§8.11.3 tier 3). Same Mutex
    /// rationale as `lib_dirs`.
    pub platform_dirs: Mutex<Vec<PathBuf>>,

    // `settings: SessionSettings` — not currently held as one cohesive
    // struct on SharedState; with `codegen_behaviour` retired in the
    // Sprint 67 Wave 4 follow-up subtraction, no SessionSettings field is
    // currently projected onto SharedState. The S67 W1 PIF-relocate row for
    // `settings` lands in S68 along with the remaining alignment work.
}

#[non_exhaustive]
pub struct WatcherChannel {
    /* opaque — receiver side of notify::Event mpsc.
       Impl is `src/watch.rs:22 pub struct FileWatcher`. The facade name
       `WatcherChannel` is documentary; source uses `FileWatcher`. W3 may
       PFR-rename source to `WatcherChannel` for facade alignment, or
       widen this facade entry to admit the source name; both work — choice
       cosmetic. */
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
| `module_aliases` | SharedState | Session-level parallel table per `bounded-contexts.md` §7 ("Module aliases live at session level"). Workers read during §8.6.6 qualified-name resolution; the int-side / frontend-StructuralDecl parse-time alias installer writes (NOT typecheck — the struck `register_imports` / `register_exports` typecheck free functions are gone; typecheck reads aliases read-only and does not populate them, see `facades/typecheck.md` §"Import/export registration is not a typecheck concern") |
| `next_type_id` | SharedState | Workers borrow `&AtomicU32` to allocate fresh type-var IDs per Decision 44 |
| `scheduler` | SharedState | Workers call `notify_*` and `wait_for_*` |
| `cache` | SharedState | Worker reads sidecars + writes `.o`; the underlying file IO is internally synchronised |
| `kept_dlls` | SharedState | Platform calls happen on workers (during JIT registration + IO trampoline) |
| `file_to_module` | SharedState | File-watcher cascade needs the inverse map from any worker that resolves imports |
| `promote_nice_workers` | SharedState | Initiator sets during hot flush; nice workers read per-iteration to self-promote OS priority |
| `test_runner_state` | SharedState | JIT-emitted-call intrinsics (`run-test` / `discover-tests`) dereference the session-stable Box from worker threads via thread-local pointer |
| `introspection` | SharedState | Codegen workers populate `clif_ir`/`disasm`/`compile_duration` |
| `repl_check_state` | SharedState (S68 PIF to CompilerSession) | REPL-only carry-forward; deferred relocation pending cluster-atomic completion |
| `module_sexps` | SharedState (S68 PIF — delete via redesign) | Pre-cluster-atomic cross-thread dep-publishing; in-call-stack value after FIXME 0179 |
| `suspend_states` | SharedState (S68 PIF — delete via redesign) | Pre-cluster-atomic resume-on-dep-arrival; eliminated by cluster atomicity |
| `typecheck_products` | SharedState (S68 PIF — vestigial; ~2 fields left) | Sprint 56 gutted; remaining fields migrate onto `SymbolTable` |
| `project_root` / `lib_dirs` / `platform_dirs` | SharedState | Read by workers (e.g., for cache path resolution); `lib_dirs` / `platform_dirs` `Mutex`-wrapped for runtime reconfiguration |
| `error_modules` | CompilerSession | REPL-eval failure accumulator; read by `/list` + `eval` (blocks against a known-bad module). Workers report failures via the scheduler. Initiator-only. |
| `watcher` | CompilerSession | mpsc receiver — only the initiator thread reads from it |
| `worker_pool` | CompilerSession | Joining on shutdown is initiator's job. Sub-fire 2a/2b collapsed 3 worker fields into one facade |
| `current_repl_module` | CompilerSession (sub-fire 2d — PIF-relocated from SharedState) | Mutated by `/mod` (initiator-only — REPL is single-threaded; no Mutex). Workers receive module per `PriorityWork` / `NiceWork` |
| `repl_input_active` | CompilerSession (with `Arc<AtomicBool>` clone for watcher event handler) | Initiator-side coordination of watcher windowing; watcher-read wiring is S68 residual |
| `warnings` | CompilerSession | Initiator-collected; worker → session merge wiring is S68 residual |

**Worker access pattern**: workers receive `Arc<SharedState>` at spawn time (one Arc clone per worker). All reads through `&shared.*` — never `&mut`. All mutations through interior mutability of the contained types. No worker-side merge step; mutations are immediately visible to other workers as soon as the per-cell lock releases.

## SharedState facade alignment plan (Sprint 67)

The facade (§"SharedState" above) prescribes an 8-field worker-shared subset; `src/session_v4.rs:573` defines ~17 fields. Per Phase 2 audit the gap is edge drift (not interior), pulled into S67 scope by the user's second challenge ("how do those deferrals not break the premise?"). Per-field disposition below; `/dev (int)` executes the listed direction in Wave 3.

Direction discipline:
- **PFR (pull facade to reality)**: current field is structurally correct + worker-shared in nature; facade widens to admit it.
- **PIF (push implementation to facade)**: current field is per-form transient or carries initiator-only state; relocate off `SharedState` (typically to `CompilerSession` or to a local frame).
- **PFR-rename**: same role, different name; canonicalise to facade.
- **Cross-field**: two impl fields merge / split.

| Field (impl side) | Current location | Direction | Rationale | Owning /dev task |
|---|---|---|---|---|
| `scheduler: CompileScheduler` | `SharedState` | PFR-rename — facade has `scheduler: Arc<CompileScheduler>` | Worker coordination is genuine worker-shared. Facade's `Arc<>` wrapper is the canonical shape (allows `Arc::clone` per worker without holding `Arc<SharedState>` ref). Adapt impl to `Arc<CompileScheduler>`. | /dev (int) Wave 3 |
| `project_root: PathBuf` | `SharedState` | PFR | Read-only config; worker-shared per facade §"Read-only configuration". Already aligned. | none — no-op |
| `lib_dirs: Mutex<Vec<PathBuf>>` | `SharedState` | PFR — facade widens to admit `Mutex` | Facade prescribes plain `Vec<PathBuf>`; impl wraps in `Mutex` for runtime reconfiguration (tests + future). The `Mutex` IS the right shape — facade narrows from "read-only after construction" to "interior-mutable plain config". Document the test-driven reconfiguration use case. | /dev (int) Wave 3 (facade text + impl unchanged) |
| `platform_dirs: Mutex<Vec<PathBuf>>` | `SharedState` | PFR — same as `lib_dirs` | Same rationale. | /dev (int) Wave 3 |
| `module_sexps: Mutex<HashMap<ModuleFullPath, Vec<Sexp>>>` | `SharedState` | **PIF** — relocate | Per-form parse-time transient. Module sexps are produced by `register_module_with_source` and consumed by the priority worker that picks up the module; they do NOT need to survive past `check_forms` completion. The cluster-atomic typecheck refactor (Decision 44 third amendment) makes this an in-call-stack value: `process_cluster` parses → builds `Vec<ParsedEntry>` → passes to `check_forms` → drops. The `SharedState` field is a `Mutex<HashMap>` only because pre-cluster-atomic workers might race on the same module; cluster-atomic eliminates the race. **Move to `process_cluster`-local Vec; delete the field.** | /dev (int) Wave 3 |
| `suspend_states: Mutex<HashMap<ModuleFullPath, ModuleSuspendState>>` | `SharedState` | **PIF** — relocate or eliminate | Worker-resume scaffolding from the pre-cluster-atomic shape. Per the same Decision-44 amendment, cluster atomicity eliminates partial-typecheck resumption: a cluster either succeeds (commits to live) or fails (whole-cluster retry on `Gap`). There is no "module half-typechecked, resume on dep arrival" state to retain. **Field deletes once cluster mode activates** (gated by FIXME 0179 read-union landing — same release as `module_sexps`). | /dev (int) Wave 3 (post-0179) |
| `cache_dir: Option<PathBuf>` | `SharedState` | PFR — facade widens | Worker-shared (nice worker writes `.o` to it). Facade should list under §"Read-only configuration" alongside `project_root`. | /dev (int) Wave 3 (facade text only) |
| `compiled_o_paths: Mutex<Vec<PathBuf>>` | `SharedState` | PFR — facade widens | Nice-worker output collection (path-list for `--link` mode). Worker-shared by nature. Facade adds field. | /dev (int) Wave 3 (facade text only) |
| `promote_nice_workers: AtomicBool` | `SharedState` | PFR — facade widens | Hot-flush priority signal; workers atomically read. Worker-shared. Facade adds field. | /dev (int) Wave 3 (facade text only) |
| `cached_modules: Mutex<HashSet<ModuleFullPath>>` | `SharedState` | PFR — facade widens | Read by workers during codegen to decide Linker fast path. Worker-shared by nature. Facade adds field. | /dev (int) Wave 3 (facade text only) |
| `file_to_module: Mutex<HashMap<PathBuf, ModuleFullPath>>` | `SharedState` | PFR — facade widens | File watcher cascade needs this from any worker that resolves imports. Worker-shared. Facade adds field. | /dev (int) Wave 3 (facade text only) |
| `cache_state: Mutex<Option<CacheState>>` | `SharedState` | PFR — facade widens | Manifest + hash-records snapshot. Workers update via `record_cache_hit`. Worker-shared. Facade adds field. | /dev (int) Wave 3 (facade text only) |
| `symbol_tables: DashMap<ModuleFullPath, SessionSymbolTable>` | `SharedState` | PFR-rename | Facade now names `SymbolTables<Code, ()>` (the materialised typedef in `cranelisp-types` per S69 audit F-1 + the session-level alias-table cascade). Impl uses `SessionSymbolTable` alias (= `SymbolTable<Code, ()>`). Adopt `SymbolTables<Code, ()>` in the impl. | /dev (int) Wave 3 (facade text only) |
| `module_aliases: ModuleAliases` | `SharedState` | New — session-level table | Parallel to `symbol_tables` per `bounded-contexts.md` §7. Keyed by `ModuleFullPath` (alias's full path). Constructed empty at session init; written by the int-side / frontend-StructuralDecl parse-time alias installer (NOT typecheck — `register_imports` / `register_exports` are struck from the typecheck surface; typecheck reads `module_aliases` read-only). /dev (int) Wave 3 — add the field; cascade the read-only param to `expand` / `check_forms` / `compile_to_module` / `load_object` / `compile_to_object` call sites. | /dev (int) Wave 3 |
| `next_type_id: AtomicU32` | `SharedState` | PFR — facade widens | Per Decision 44 + facade `typecheck.md` `TypeCheckEnv::new(modules, next_id)` — workers need shared access to allocate fresh type-var IDs. Worker-shared. Facade adds field. | /dev (int) Wave 3 (facade text only) |
| `current_module: Mutex<ModuleFullPath>` | `SharedState` | **PIF** — relocate to `CompilerSession` | REPL-only state (`/mod` switches it). Workers don't need it — they receive `module` per `PriorityWork`/`NiceWork` work item. Facade's `CompilerSession.current_repl_module: ModuleFullPath` is the right home (no `Mutex` needed — REPL is single-threaded against this field; initiator-only). **Move to `CompilerSession`.** | /dev (int) Wave 3 |
| `repl_check_state: Mutex<Option<CheckState>>` | `SharedState` | **PIF** — relocate to `CompilerSession` | REPL-only carry-forward across evals. Workers do not use this. **Move to `CompilerSession`.** | /dev (int) Wave 3 |
| `typecheck_products: DashMap<ModuleFullPath, TypecheckProduct>` | `SharedState` | PFR — facade widens OR cross-field merge | Post-S66 the staging product is folded into `SymbolTable` entries directly; `typecheck_products` is a parallel store. Need cross-check: if all current consumers can read from `symbol_tables[m].defined_symbols()` instead, **eliminate the field**; otherwise document under §"The single store". Wave 3 task: audit consumers, then decide. | /dev (int) Wave 3 |
| `kept_dlls: Mutex<Vec<LoadedPlatform>>` | `SharedState` | PFR-rename + cross-field | Facade prescribes `kept_dlls: DashMap<PathBuf, Arc<DllHandle>>`. Impl uses `Mutex<Vec<LoadedPlatform>>` — different shape. The DashMap-by-path shape supports per-manifest deduplication (load-once); the Vec shape requires linear scan for dedup. **Convert impl to facade shape.** | /dev (int) Wave 3 |
| `introspection: DashMap<FQSymbol, Introspection>` | `SharedState` | PFR-rename | Facade prescribes `Option<DashMap<FQSymbol, Introspection>>` — None in production batch (zero overhead per Decision 38). Impl uses plain `DashMap` (always allocated). **Convert to `Option`.** Per Decision 38, the mode discriminator IS `Option::is_some()`. | /dev (int) Wave 3 |
| `test_runner_state: Box<TestRunnerState>` | `SharedState` | **PFR — facade widens** | Test-intrinsic backing per Wave 3a-γ. Session-stable pointer for thread-local indirection. Worker-shared by nature (the intrinsic fires from JIT-emitted code). Facade adds field; document the session-stable-Box discipline + the `current_module: Mutex<ModuleFullPath>` sub-field for `/mod`. | /dev (int) Wave 3 (facade text only) |
| `cache: Arc<ObjectCache>` | absent in impl (sketched at facade) | **PIF — author** (alternative: PFR-keep the four scattered fields) | Facade prescribes `cache: Arc<ObjectCache>`; impl has `cache_dir`+`cache_state`+`compiled_o_paths`+`cached_modules` as four scattered fields. The facade's `ObjectCache` is a cohesion target — merge the four impl fields into a single `ObjectCache` type owned by `int::cache`. **Reconciliation note (S67 W1):** the four-field rows above list PFR direction (admit each field individually); this row lists PIF-author (merge into one). The two are alternatives; /dev Wave 3 picks one and the other rows update accordingly. The preferred direction is PIF-author IFF the four fields are genuinely accessed together at every call site — Wave 3 audit decides. If the call-site audit finds the fields are accessed independently, PFR-keep the four-field shape and delete this row. | /dev (int) Wave 3 |
| `settings: SessionSettings` | impl HAS `pub struct SessionSettings` at `session_v4.rs:98` (5 fields: `no_color`, `no_cache`, `codegen_behaviour`, `priority_workers`, `nice_workers`) — matches facade §"Settings and config" exactly; what's absent is a `SharedState.settings: SessionSettings` field threading it through | **PIF — relocate to `SharedState`** | Currently `SessionSettings` is constructed in `main.rs` and passed to `CompilerSession::new`, which destructures it into the individual fields on `SharedState`. The facade target is to hold it as one cohesive struct on `SharedState` for read access. /dev Wave 3 adds the field; the destructure-then-store pattern collapses to one assignment. (This row was previously titled "PIF-author" — corrected to PIF-relocate per W1 source inspection. The struct already exists; only the per-field destructure on `SharedState` needs collapsing.) | /dev (int) Wave 3 |

Net direction (S67 W1 reconciliation): ~12 PFR (facade text catches up to impl reality), 4 PIF (impl narrows to facade — `module_sexps`, `suspend_states`, `current_module`, `repl_check_state`), 1 PIF-author-or-keep (`ObjectCache` cohesion — Wave 3 audit decides; alternative: PFR-keep the four scattered fields), 1 PIF-relocate (`SessionSettings` onto `SharedState` — the struct already exists, only the destructure-then-store collapses), 2 PFR-rename (`kept_dlls` shape, `introspection` `Option` wrap).

**S67 Cluster B landing (sub-fires 1–3, 2026-05-17).** What actually landed in S67 vs what carries to S68:

- **PIF-author taken** for `ObjectCache` (sub-fire 3) — the four scattered cache fields (`cache_dir`, `cache_state`, `compiled_o_paths`, `cached_modules`) collapse. `cached_modules` deletes outright (scheduler-only via `CompileScheduler::cached_module_*` accessors — sub-fire 2e). The remaining three fold into `Arc<ObjectCache>` (the thin wrapper at `src/cache.rs`); call sites dispatch through the method surface (`is_enabled`, `cache_dir`, `record_source_hash`, `record_cache_hit`, `record_compiled`, `source_hash`, `is_cache_valid`, `flush_manifest`, `append_o_path`, `all_paths`). Internals are interim (pass-through to `CacheState`); the facade-prescribed `open` / `lookup_sidecar` / `load_object` / `write` constructor + cache-protocol methods are S68 cohesion work.
- **PIF taken** for `current_repl_module` (sub-fire 2d) — relocated from `SharedState.current_module: Mutex<ModuleFullPath>` to `CompilerSession.current_repl_module: ModuleFullPath`. The `Mutex` was vestigial (REPL is single-threaded against this field).
- **PIF deferred to S68** for `repl_check_state`, `module_sexps`, `suspend_states` — all three are confirmed load-bearing in S67 source inspection; relocation/deletion is gated on cluster-atomic completion (FIXME 0179 read-union).
- **PFR taken** for `cache: Arc<ObjectCache>` field row (facade reflects the landed shape).
- **PFR deferred** for the listed widening rows (`next_type_id`, `test_runner_state`, `promote_nice_workers`, `file_to_module`, `lib_dirs`/`platform_dirs` Mutex shapes) — addressed by this fire's §"SharedState" facade-text refresh; impl shapes unchanged. (`codegen_behaviour` had been added per FIXME 0205; retired in the Sprint 67 Wave 4 follow-up subtraction.)
- **PFR-rename deferred to S68** for `kept_dlls` (still `Mutex<Vec<LoadedPlatform>>`; facade prescribes `DashMap<PathBuf, Arc<DllHandle>>`) and `introspection` (still bare `DashMap`; facade prescribes `Option<DashMap>` per Decision 38). Drift documented in §"SharedState" rather than masked.
- **PIF-relocate deferred to S68** for `SessionSettings` — still destructured into individual fields on construction.

After S67 close the impl `SharedState` field count stands at 16 (`cached_modules`/`cache_dir`/`cache_state`/`compiled_o_paths`/`current_module` removed = 5 deletions; `cache` added = 1 addition; `codegen_behaviour` was added per FIXME 0205 then retired in the Sprint 67 Wave 4 follow-up subtraction = net 0). The field count is not the metric — **facade-alignment is**, and the §"SharedState" block above now enumerates all 16 with disposition notes per residual.

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

### Cluster orchestration result (returned by `process_cluster`, consumed by `insert_cluster`)

Per Decision 44 (2026-05-13 third amendment) — the typed product of one cluster's `check_forms` run, ready for atomic commit. The wrapper carries the drained staging entries plus the cluster-level cross-symbol bookkeeping that `int` collects during cluster processing. It is an opaque carrier between `process_cluster` and `insert_cluster`; callers do not mutate it but may read its metadata accessors (for warning surfacing, scheduler notifications, REPL display).

```rust
#[non_exhaustive]
pub struct ProcessedCluster {
    /* opaque — fields are crate-private; constructed inside `process_cluster`,
       drained inside `insert_cluster`:
         staged_entries: Vec<(Symbol, ModuleEntry<Code>)>,
         warnings: Vec<Warning>,
         resolved_imports: Vec<(ModuleFullPath, ImportNames)>,
         introspection_records: Vec<(FQSymbol, Introspection)>,
    */
}

impl ProcessedCluster {
    pub fn is_empty(&self) -> bool;                                                // no staged entries — orchestrator may skip commit
    pub fn into_iter(self) -> impl Iterator<Item = (Symbol, ModuleEntry<Code>)>;   // consumed by insert_cluster
    pub fn warnings(&self) -> &[Warning];                                          // surfaced by Sess::warnings / EvalResult
    pub fn resolved_imports(&self) -> &[(ModuleFullPath, ImportNames)];            // applied via SymbolTable::install_import_bindings post-drain
    pub fn introspection_records(&self) -> &[(FQSymbol, Introspection)];           // drained into shared.introspection in insert_cluster
}
```

**No separate `ModuleCheckAccumulator` exists** — either on the typecheck side or the int side. Per Decision 44's 2026-05-13 third amendment:

- **Per-symbol Pass-2 side products** (method resolutions, expr types, mono defns, callees) live on staging `ModuleEntry::Def` entries directly per `facades/typecheck.md` invariant 3a; they ride into live with each entry on `insert_cluster`'s drain.
- **Pass-1-to-Pass-2 working state** (`defn_type_vars`, default-method-defn deferrals, generalisation inputs, multi-sig variant accumulation, the deferred-resolution working set) is **internal to `cranelisp_typecheck::check_forms`'s stack frame** — it is constructed when `check_forms` enters, consumed across the internal Pass 1 → Pass 2 boundary, and dropped when `check_forms` returns. It never crosses the typecheck facade. The state-threading hole that the two-function shape exposed (Pass-1-to-Pass-2 working state could not be carried across two separate calls without a public accumulator) is closed by construction.
- **Cluster-level cross-symbol bookkeeping that `int` collects during cluster processing** (warnings, resolved-import bindings, introspection records) lives on `ProcessedCluster` directly — see the struct definition above. The pre-S66 `cranelisp_typecheck::ModuleCheckAccumulator` (public-api.txt L133–L153) is removed; what was on it migrates either onto staging `Def` fields (per-symbol) or onto `ProcessedCluster` (cross-symbol).

The retired alternative — relocating `ModuleCheckAccumulator` to `int` as a separately-typed cluster aggregate — was a misapplication of Principle 15 (it treated `int` as the consumer of structure rather than as a holder of an opaque carrier). The collapsed `check_forms` shape obviates the need for any cross-call accumulator: there is only one call, and the cluster-level bookkeeping it surfaces fits cleanly on the existing `ProcessedCluster` carrier.

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
    pub category: SymbolCategory,                                                  // Module | Macro | Trait | Type | Fn | SpecialForm | Constructor
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
- `process_cluster` after `parse`: write `source` + `sexp` for each defn form in the cluster.
- `compile_to_module` per-symbol call (Decision 41; S70 Phase B amendment): backend returns `CompilationArtifacts { clif_ir, code_size, compile_duration }` by value from each `compile_to_module` call. The int-side caller (the priority worker that issues the call) composes the `Introspection` for that FQSymbol by combining the backend artefact's `clif_ir` / `code_size` / `compile_duration` fields with the parse/expansion-populated `source` / `sexp` fields collected earlier in the cluster (then `disasm: None` — the disassembly is produced lazily by `cranelisp_backend::produce_disasm(fq, symbol_tables)` when a REPL `/disasm` request fires). Backend does NOT name `Introspection` at its boundary; the type stays in the int crate; no DAG inversion. Per-symbol JIT cardinality means one `Introspection` write per `compile_to_module` call.

**Consistency with Decision 31 carry-forward.** REPL redefinition replaces the `ModuleEntry::Def` for the same FQSymbol; the corresponding `Introspection` entry is overwritten in the same `process_cluster` pass (`introspection.insert(fq, fresh_intro)`). The two stores share keying by FQSymbol and are mutated at the same orchestration points; no drift.

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

**Sprint 67 Cluster B sub-fire 3 landing (`src/cache.rs`).** The four pre-S67 scattered cache fields on `SharedState` (`cache_dir`, `cache_state`, `compiled_o_paths`, `cached_modules`) collapse into a single `Arc<ObjectCache>` owner. `cached_modules` deletes outright (scheduler-only via `CompileScheduler::cached_module_*`). The remaining three are hoisted as `Mutex`-wrapped private state inside `ObjectCache`; callers depend on the method surface.

**Two-tier surface:**

1. **Pass-through method surface (landed S67 W4 — call sites depend on this)** — wraps the existing `crate::session::CacheState` semantics behind one owner. S68 may reshape internals freely without changing call sites.

```rust
pub struct ObjectCache {
    /* opaque — interior:
         dir: Option<PathBuf>,                           // None when caching disabled
         state: Mutex<Option<CacheState>>,               // manifest + source hashes
         compiled_o_paths: Mutex<Vec<PathBuf>>,          // nice-worker .o output collection
    */
}

impl ObjectCache {
    /// Construct from already-resolved cache state. `CompilerSession::new` is the
    /// sole caller; passes the directory plus initial `CacheState`. The
    /// facade-prescribed `open(project_root)` constructor (below) is S68 work.
    pub fn new(dir: Option<PathBuf>, state: Option<CacheState>) -> Self;

    pub fn is_enabled(&self) -> bool;                                              // dir.is_some() && state loaded
    pub fn cache_dir(&self) -> Option<PathBuf>;
    pub fn record_source_hash(&self, module: &ModuleFullPath, hash: String);       // dep hash tracking
    pub fn is_cache_valid(&self, module: &ModuleFullPath, current_source_hash: &str, dep_hashes: &HashMap<ModuleFullPath, String>) -> bool;
    pub fn record_cache_hit(&self, module: &ModuleFullPath, source_hash: String);
    pub fn record_compiled(&self, module: &ModuleFullPath, source_hash: String, dep_hashes: HashMap<String, String>);
    pub fn source_hash(&self, module: &ModuleFullPath) -> Option<String>;
    pub fn flush_manifest(&self);
    pub fn append_o_path(&self, path: PathBuf);                                    // nice-worker output collection
    pub fn all_paths(&self) -> Vec<PathBuf>;                                       // for `--link` collection
}
```

2. **Cohesion target (S68 — facade-prescribed cache-protocol surface)** — the canonical `open` / `lookup_sidecar` / `load_object` / `write` surface that hides `CacheState` internals entirely and consolidates per Decision 43 + the BC §"Object cache" alignment. Sub-fire 3 deliberately landed the thin-wrapper shape first per the user's "no premature performance workarounds" + "target state first" disciplines: the method surface is the load-bearing structural change; the cohesion refactor is interim S68 work.

```rust
impl ObjectCache {
    // S68 — facade-prescribed surface (NOT YET LANDED):
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

Backend is no longer C-blind — it constructs `Code::Jit(Arc<Jit>)` directly inside `compile_to_module` and writes via Decision 38's `write_code(&self, sym, code)`, and writes the resulting fn pointer to the entry's GOT slot via `symbol_table.got().store_slot(entry.got_slot.unwrap(), ptr)` (S66 amendment + rollback `1dc57ae` — `Code` carries lifecycle owner only; the GOT is the single source of truth for callable addresses). Int still names `Code` at the session-boundary instantiation `SymbolTable<Code, ()>`, but no longer wraps a backend return tuple — the previous post-loop in `worker.rs:2860-3018` (iterate-over-names + GOT-store + `Code::Jit`-construct + three error cascades) collapses into the per-symbol call-site loop. Per the S70 Phase B amendment to D41, `compile_to_module` returns `Result<CompilationArtifacts, CompilationError>`; int composes the per-symbol `Introspection` from the artefact + the cluster-collected parse-time fields:

```rust
for sym in defined_symbols(&shared.symbol_tables[scope]) {
    let jit = Jit::new_with_symbols(&extra)?;
    let artifacts = compile_to_module(scope, &[sym], &shared.symbol_tables, &shared.module_aliases, jit.jit_module())?;
    if let Some(intro_map) = shared.introspection.as_ref() {
        let fq = FQSymbol::new(scope.clone(), sym.clone());
        // Merge backend's always-created artefacts with parse-time fields collected
        // for this fq during process_cluster (source, sexp); disasm stays None until
        // /disasm fires and calls backend::produce_disasm(&fq, &shared.symbol_tables).
        intro_map.insert(fq, Introspection {
            source: parse_time.source.take(),
            sexp:   parse_time.sexp.take(),
            clif_ir:          Some(artifacts.clif_ir),
            code_size:        Some(artifacts.code_size),
            compile_duration: Some(artifacts.compile_duration),
            disasm: None,
        });
    }
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

### Observability — `src/io_trace.rs`, `src/observability.rs` (scheduler trace), `src/got_trace.rs` (per Decision 40 + FIXME 0099 + FIXME 0103)

Per Decision 40, the consumer-side ring buffers and formatters that pre-S65 lived in `cranelisp-runtime` (`trace.rs`, `io_trace.rs`) relocate to int. Per Decision 43, the `IoObserver` registration API lives in `cranelisp-intrinsics`; int registers an observer at session init. Per FIXME 0099, the `GotObserver` registration API lives in `cranelisp-backend`; int registers similarly. All three follow the same shape — env-var-gated activation, per-thread `VecDeque` ring buffer with FIFO overflow, end-of-session flush formatter, RAII guards over the buffers.

**Source-tree hosting (post-Sprint 67 Wave 4 — landed).** Decision 40 Path B1 (user-arbitrated 2026-05-16 amendment) is now complete int-side. The trace edifice lives in int in full:

| Facade name | Source file | Note |
|---|---|---|
| `io_trace::*` | `src/io_trace.rs` (landed) | Post-Decision-40 consumer-side ring buffer + observer-record + flush + panic hook hosted here in full. Public surface: `record_event`, `record` (the observer callback registered with `cranelisp_intrinsics::register_io_observer`), `install_if_enabled` (env-var gate on `CRANELISP_IO_TRACE=1`), `flush_to_stderr`, `IoTraceFlushGuard`, `install_panic_hook`, plus internal per-thread buffer publishing (`publish_thread_buffer`, `dump_thread_buffer`, `dump_all_buffers`). |
| `scheduler_trace::*` | `src/observability.rs` (exists) | The pre-existing `observability` module IS the scheduler trace consumer (`SchedulerTraceTag`, `SchedulerTracePayload`, `record_event`, `flush_to_stderr`, `SchedulerTraceFlushGuard`, `TraceFilter`). The facade name `scheduler_trace` is a rename target for clarity; the source can either rename the module or re-export `pub use observability as scheduler_trace`. |
| `got_trace::*` | `src/got_trace.rs` (exists) | Hosts the post-FIXME-0099 GOT observer ring buffer. The `record`/`install_if_enabled`/`flush_to_stderr`/`install_panic_hook`/`GotTraceFlushGuard` shape already lands. Registration call to `cranelisp_backend::register_got_observer` at session init. |
| `trace::cranelisp_trace_*` (the `(trace ...)` special-form runtime helpers) | `src/trace.rs` (landed — Decision 40 Path B1) | **Sprint 67 Wave 4 landing**: all 12 `cranelisp_trace_*` JIT-emitted-call bodies relocated from `cranelisp-intrinsics::trace` to int (per FIXMEs 0197 + 0202 + 0204; backend's 12 `IntrinsicSymbol` entries deleted in the same change-set). The file hosts: `cranelisp_trace_enter`, `cranelisp_trace_exit`, `cranelisp_trace_swap_got`, `cranelisp_trace_restore_got`, `cranelisp_collect_trace`, `cranelisp_trace_first_child_nanos`, `cranelisp_trace_name`, `cranelisp_trace_params`, `cranelisp_trace_result`, `cranelisp_trace_children`, `cranelisp_trace_nanos`, plus the int-side fallback `cranelisp_trace_format` (the production symbol is the `repl_trace_format` shim at `session_v4.rs` — the REPL session has access to the TypeChecker for proper display dispatch; `trace.rs`'s body is the unit-test fallback). The `TraceDisplayState` thread-local + `clear_trace_display_state` companion machinery remains at `session_v4.rs` for session-state proximity; trace.rs is host for the 12 JIT-emitted bodies. Registration is via `int_intrinsics()` — see §"Int-owned JIT intrinsics" below. |

**Naming reconciliation.** The pre-S65 facade text said `src/io_trace/` (directory-style); current source has flat `src/io_trace.rs` (file-style). Both shapes satisfy the facade — directory-style is only required when the module grows multiple sub-files. No PFR/PIF needed; the facade text is updated to name the actual file paths.

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

### Int-owned JIT intrinsics — `int_intrinsics()` (post-Decision-40 Path B1)

Per `src/CLAUDE.md` §"Int-owned JIT intrinsics", `src/session_v4.rs::int_intrinsics()` returns the array of `(JIT-symbol, fn-ptr)` pairs that **every** JIT-build site in int must register with `JITBuilder::symbol(...)` before constructing the `Jit`. Backend-emitted CLIF declares these as `Linkage::Import`; without uniform registration the JIT fails to resolve them.

**Post-Sprint 67 Wave 4 (Decision 40 Path B1 amendment, 2026-05-16) — the trace edifice is complete int-side.** The inventory grew from 3 entries (pre-S67) to 14 entries:

| JIT symbol | Rust fn (host) | Reader / use |
|---|---|---|
| `discover-tests` | `discover_tests_extern` (`session_v4.rs`) | `(run-tests ...)` special form (Wave 3a-γ) |
| `run-test` | `run_test_extern` (`session_v4.rs`) | `(run-tests ...)` special form (Wave 3a-γ) |
| `cranelisp_trace_format` | `repl_trace_format` (`session_v4.rs`) | `(trace ...)` — display-state-aware wrapper (production); `src/trace.rs`'s `cranelisp_trace_format` is the unit-test fallback |
| `cranelisp_trace_enter` | `crate::trace::cranelisp_trace_enter` | `(trace ...)` — frame entry |
| `cranelisp_trace_exit` | `crate::trace::cranelisp_trace_exit` | `(trace ...)` — frame exit |
| `cranelisp_trace_swap_got` | `crate::trace::cranelisp_trace_swap_got` | `(trace ...)` — GOT-swap wrapper install |
| `cranelisp_trace_restore_got` | `crate::trace::cranelisp_trace_restore_got` | `(trace ...)` — GOT-swap wrapper teardown |
| `cranelisp_collect_trace` | `crate::trace::cranelisp_collect_trace` | `(trace ...)` — collect frame tree as ADT |
| `cranelisp_trace_first_child_nanos` | `crate::trace::cranelisp_trace_first_child_nanos` | `(trace ...)` — first-child timing accessor |
| `cranelisp_trace_name` | `crate::trace::cranelisp_trace_name` | `(trace ...)` — name field accessor |
| `cranelisp_trace_params` | `crate::trace::cranelisp_trace_params` | `(trace ...)` — params field accessor |
| `cranelisp_trace_result` | `crate::trace::cranelisp_trace_result` | `(trace ...)` — result field accessor |
| `cranelisp_trace_children` | `crate::trace::cranelisp_trace_children` | `(trace ...)` — children list accessor |
| `cranelisp_trace_nanos` | `crate::trace::cranelisp_trace_nanos` | `(trace ...)` — total-nanos field accessor |

The 11 new entries land via FIXMEs 0197 (backend deletion) + 0202 (int registration) + 0204 (host migration). Backend's `IntrinsicSymbol` registry shrinks by 12 entries in the same change-set; the JIT-resolution path for these symbols flips from `cranelisp_intrinsics::trace::*` (pre-S67) to `crate::trace::*` (post-S67).

**Trace-in-`--link` rejection (S67 W4 follow-up — subtraction).** Per `spec/04-expressions.md §4.12.9`, `(trace ...)` is REPL/`--run`-only; `--link` rejects programs that use the form. The rejection is **the architecture's natural missing-symbol failure** — there is no frontend pre-pass check, no inline `build_trace` rejection, no `CodegenBehaviour` parameter threaded through `build_form` / `build_expr`. Backend emits `cranelisp_collect_trace` as `Linkage::Import` regardless of mode (one codegen source path; Module as generic param). The JIT path (REPL, `--run`) resolves the import at finalize via `JITBuilder::symbol()` (int_intrinsics() provides the trace runtime symbols). The object path (`--link`) writes the import to `.o`; exe-bundle force-link for trace was deleted in commit 0202, so the trace runtime is not present in the staticlib produced for standalone binaries; the system linker errors with "undefined symbol cranelisp_collect_trace". That link-time error IS the rejection. The earlier `link_mode::validate_*` validator (introduced via FIXME 0199, retired in `4191374`) and its successor inline `build_trace` rejection (commit `4191374`, retired in the Sprint 67 Wave 4 follow-up subtraction) were both engineering around a failure mode the architecture already produces. FIXME 0209 reframes the spec wording from "compile-time error" to "link-time rejection" to align with this mechanism.

**Unconditional registration is mandatory.** Every JIT-build site in this crate folds `int_intrinsics()` into the `JITBuilder::symbol` set before calling `Jit::new_with_symbols`. The two current sites are `worker::inline_jit_codegen_for_names` and `pipeline::compile_and_execute_expr` (plus its trace variant). No syntactic gating — the pre-S66 `program_uses_test_forms` / `program_needs_trace` / `any_compiled_defn_uses_test_forms` helpers were deleted in Wave 3a-γ (see `src/CLAUDE.md`'s forbidden-patterns note + FIXME 0178).

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
pub const QUIT_SENTINEL: &str = "\x00QUIT";    // session_v4.rs:215 — sentinel returned by `process_commands` on /quit; consumed by main.rs REPL loop. Internal-but-exposed: the binary entry point reads it. /dev Wave 3 may relocate to `pub(crate)` if no out-of-crate caller exists.
```

### Session init — referencing the static `PRIMITIVES_TABLE` (Decision 48)

Per Decision 48 (Sprint 68; **shape amended S73 Phase 2 — backend sever**), `cranelisp-primitives` owns a single pub static `PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<(), ()>>>` — a **`()`-flavoured** table (primitives never names `Code`; `primitives ⟂ backend`, FIXME 0244 + the S73 severance). The static's `Arc<GotTable>` (reachable via `.got()`) is populated at `LazyLock` init time with raw `*const u8` fn ptrs at prescribed slot indices for every non-inlined primitive. Because `int`'s session holds a `SymbolTables<Code, ()>` map, the session-init seeding routine must **concretize** the static to `<Code, ()>` before inserting it — it does so via `SymbolTable::into_concrete::<Code, ()>()` (the proven cache-restore bridge in `cranelisp-types`), which maps each entry's `code: Option<()>` to `None::<Code>` and carries the shared `Arc<GotTable>` (`got: self.got`) through verbatim. This is where `int` (not primitives) names `Code`.

This seeding routine is `int`-owned (a function on `src/session_v4.rs`, sketched below). It is **not** `cranelisp_typecheck::register_builtins` — synthetic-module assembly is deleted from typecheck (FIXME 0241). Beyond the primitives concretize-and-mount shown below, this routine also mounts the synthetic `primitives`/`macros` modules and the `Option`/`IO`/`Trace`/`TestResult` ADTs that the deleted typecheck assembly used to seed; `int` reconstructs that mount sequence from git history per FIXME 0242. The sketch below shows only the primitives slice for brevity. (The int-side mount + cascade is **S74** per the S73 re-scope — out of scope this sprint; the handoff is the `<(), ()>` static + `into_concrete`.)

```rust
// src/session_v4.rs — sketch of the post-S73 shape (replaces the pre-S68
// `populate_ring0_got_slots` cross-table copy loop, which retires).
fn register_builtins(symbol_tables: &SymbolTables<Code, ()>, next_id: &AtomicU32) {
    // PRIMITIVES_TABLE is <(), ()>; concretize to <Code, ()> for the session map.
    let primitives = (*cranelisp_primitives::PRIMITIVES_TABLE)
        .as_ref().clone()                  // SymbolTable<(), ()>  (got: Arc<GotTable> shared)
        .into_concrete::<Code, ()>();      // SymbolTable<Code, ()> — code: None per entry; got carried through
    symbol_tables.insert(ModuleFullPath::primitives(), primitives);
    // … other builtins (special forms on "user", trait registration, etc.)
}
```

From the instant `register_builtins` returns, primitives are dispatched through the standard cross-module GOT path (Decision 23 + Decision 31): backend's CLIF emits `global_value` on `Linkage::Import __cranelisp_got_primitives`; the JIT-mode `Module::symbol_lookup_fn` resolves the name to `symbol_tables[primitives()].got().base_ptr()` — which is the static `GotTable`'s base. **No primitives special-case in backend's `symbol_lookup_fn`.** The per-process static `Arc<GotTable>` IS the SymbolTable-GOT row of Decision 23's two-GOT model — no third "static GOT" category introduced (Decision 48 Alt B2 rejected).

The pre-S68 cross-table copy loop (`populate_ring0_got_slots`, which reads pointers out of the static GOT and writes them back into a separate session-allocated GOT) retires — it was the manifestation of Decision B1's per-batch redundancy (Principle 7 — single source of truth). The clone + `into_concrete` is the post-S73 replacement: the structural `SymbolTable` fields are per-session-cloned (cheap), but the address-bearing `Arc<GotTable>` is shared — one GOT for primitives in the process, regardless of how many sessions exist concurrently.

The session's primitives `ModuleEntry`s hold `code = None` — per Decision 0048 (A2 reversed, FIXME 0244, 2026-05-31). Primitive-ness is read from `kind: DefKind::Primitive`, not from a `code` marker variant; the raw `*const u8` lives in the GOT slot per Decision 35 (GOT is the single source of truth for callable addresses). Decision 30's cache-hit reload path does not run for the primitives module — primitives are never cached.

---

## Internal-but-exposed `src/` items

The following items are `pub` in `src/` (via `pub mod` re-export from `lib.rs`) but are not part of the application-layer facade above. They are exposed by `src/lib.rs` for test access and per-module cohesion; they are NOT promised to consumers outside `src/`. Sprint 67 W1 coverage check — every such item is enumerated here so the facade↔src delta is auditable.

| Source location | Items | Disposition |
|---|---|---|
| `src/code.rs` | `Code` enum (variants + `jit`/`linker`/`ptr` ctors), `SessionSymbolTable` alias, `SessionModuleEntry` alias | Re-exported from `cranelisp-backend` per Decision 41; the int-side alias `SessionSymbolTable = SymbolTable<Code, ()>` is the session-boundary instantiation per facade §"`Code` — the per-entry retention root". Internal-but-exposed: `pub` so worker.rs and cluster.rs can refer to it. |
| `src/cluster.rs` | `ProcessedCluster::{is_empty, into_iter, warnings, resolved_imports, introspection_records, from_parts (pub(crate)), empty (pub(crate))}` | Already in facade §"Cluster orchestration result". `from_parts` + `empty` are construction helpers; `pub(crate)`. |
| `src/expander.rs` | `MacroClauseEntry`, `MacroEntry`, `MacroResolver`, `clause_matches`, `find_matching_clause`, `invoke_clause`, `rewrite_spans`, `expand_sexp_recursive`, `expand_macro_call_with_entry`, `EXPANSION_DEPTH_LIMIT` | All `pub(crate)`. Internal cooperation between the cluster orchestrator and the expander host. NOT facade. **Status (Submission 13):** `MacroEnv` sidecar retires with the macro-unification cascade — `MacroEntry`/`MacroClauseEntry` (the in-source expander's sidecar lookup shapes) are restructured so that clause-body dispatch reads through the unified `Def { kind: DefKind::Macro { clauses_meta }, … }` parent and GOT-dispatches to each `{macro-name}$clause-{N}` mangled-variant Def. The `clause_matches` / `find_matching_clause` / `invoke_clause` clause-walk-and-match logic is unchanged in substance; only the storage it reads from moves. Tracked in the concurrency-cluster /dev brief alongside the `ModuleEntry::Macro` source retirement. |
| `src/marshal.rs` | `sexp_to_runtime`, `runtime_to_sexp`, `build_runtime_slist`, `rc_inc`, `debug_dump_sexp` | Sexp ADT marshalling for macro intrinsics. Internal cooperation between codegen and macro expansion. Not a stable boundary; relocates to `cranelisp-intrinsics` if/when the macro-Sexp ABI is formalised across the boundary (no near-term plan). |
| `src/pipeline.rs` | `resolve_module_file`, `compile_and_execute_expr` | Internal — `compile_and_execute_expr` is the temp-closure JIT for eval-expression `EvalResult::Value`. Wave 3 may PIF to `pub(crate)` if no out-of-crate caller exists. |
| `src/save.rs` | `generate_module_source`, `atomic_write` | `regenerate_backing_file`'s helpers. `generate_module_source` writes per-defn Introspection source by iterating `SymbolTable::defn_order`; `atomic_write` is the temp+rename file IO primitive. Internal; not facade. |
| `src/platform.rs` | `LoadedPlatform` (struct + fields), `resolve_platform_path`, `load_platform_dll`, `register_platform_in_tc`, `is_platform_form`, `extract_platform_name`, `load_and_register_platform` | Platform-loading lifecycle from int's side. `LoadedPlatform` is the type stored in `SharedState.kept_dlls` per the alignment plan; the load helpers compose with `cranelisp_platform::{load_manifest, parse_type_sig, derive_jit_name}`. Internal cooperation, not facade. |
| `src/style.rs` | `Style` enum, `init_color`, `is_color_enabled`, `styled` | ANSI styling for the REPL prompt and pretty-printed display. Internal display helpers (`display.rs` + `process_commands` reach in); not exposed across the crate boundary. |
| `src/watch.rs` | `FileWatcher::{new, watch_file, poll_changes, update_content_hash, clear_all}` | The `notify::Event` mpsc wrapper; `WatcherChannel` of the facade is the opaque view. Internal-but-exposed for `CompilerSession::init_watcher` + `sync_watcher` + `poll_and_reload`. |
| `src/session.rs` | `CacheState::{new, cache_dir, record_recompiled, source_hashes, source_hashes_mut, record_module, flush, flush_manifest, is_cache_valid, record_cache_hit}`, `load_project_config_lib_dirs`, `assemble_lib_dirs`, `assemble_platform_dirs`, `resolve_prelude`, `determine_exit_code`, `inject_prelude_import (pub(crate))`, `apply_bind_chain_analysis (pub(crate))` | `CacheState` is the per-session manifest + hash records held under `SharedState.cache_state`. The free functions are session-init helpers consumed by `CompilerSession::new`. Internal; absorbed into the SharedState plan's `ObjectCache` cohesion target (PIF-author). |
| `src/observability.rs` | `SchedulerTraceTag`, `SchedulerTracePayload`, `SchedulerTraceEvent`, `TraceFilter`, `parse_filter_from_env_value`, `record_event`, `record_module_event(_with_state)`, `record_bulk_event`, `record_symbol_table_ensure_forward`, `install_symbol_table_ensure_hook_to_scheduler_trace`, `dump_thread_buffer`, `publish_thread_buffer`, `dump_all_buffers`, `format_event_line`, `flush_to_stderr`, `SchedulerTraceFlushGuard`, `install_panic_hook`, `SCHEDULER_TRACE_BUFFER_CAPACITY` | The scheduler-trace consumer named `scheduler_trace::*` in the facade. Internal cooperation between the scheduler (producer) and the `--scheduler-trace` end-of-session flush (consumer). Wave 4 may add `pub use observability as scheduler_trace` for facade-name alignment. |
| `src/io_trace.rs` | `record`, `install_if_enabled`, `flush_to_stderr`, `install_panic_hook`, `IoTraceFlushGuard` | Already covered by facade §"Observability". |
| `src/got_trace.rs` | `StoredGotEvent` (struct + fields), `record`, `install_if_enabled`, `publish_thread_buffer`, `flush_to_stderr`, `GotTraceFlushGuard`, `install_panic_hook`, `emit_redefinition` | Already covered by facade §"Observability"; `StoredGotEvent`/`publish_thread_buffer`/`emit_redefinition` are the on-record per-thread buffer surface, internal cooperation, not facade. |
| `src/exe.rs` | `MainReturnKind`, `validate_main`, `generate_main_alias_object`, `entry_main_got_slot`, `link_executable`, `find_platform_rlibs`, `find_bundle_lib`, `collect_platform_manifest_names`, `pub use cranelisp_backend::exe::generate_startup_object` | The `--link` orchestration helpers. The facade names `generate_startup_object` already. The other helpers are internal to `Sess::link_by_name`. Internal; not facade. |
| `src/cache_writer.rs` | `CacheWriterHandle::{new, queue_write, flush}`, `CacheWritePacket` (already in facade), `process_cache_packet (pub(crate))` | `CacheWriterHandle` is the background thread that drains the queue; internal pump helper, not facade. `CacheWritePacket` already in facade. |
| `src/thread_util.rs` | `set_nice_priority`, `set_normal_priority` | OS thread-priority helpers for nice-worker promotion. Internal. |
| `src/display.rs` | `format_value`, `format_result_value`, `format_result`, `format_type_qualified` (in facade), `format_scheme_display` (in facade), `format_ctor_display`, `format_adt_type_qualified` | The facade covers `format_type_qualified` and `format_scheme_display`. The other helpers are display utilities composed inside `format_eval_result`; internal. |
| `src/pretty.rs` | `pretty_print`, `pretty_print_str` | Sexp pretty-printer used by `Sess::pretty_print`. Internal helper. |
| `src/bind_chain_analysis.rs` | `SymbolTables` alias, `auto_schedule_defn`, `auto_schedule_expr`, `auto_schedule_expr_owned`, `scheduling_of` | Per-defn `SchedulingClass` annotation pass executed at register-form time. Internal cooperation between cluster orchestrator and scheduler. Not facade. |
| `src/worker.rs` | `ModuleCheckAccumulator` (still present pre-W3a-β collapse follow-up), `ModuleCompiler<'a>`, `priority_worker_loop_shared`, `process_module_forms`, `compile_macro_for_repl`, `collect_jit_setup_public`, `derive_codegen_batch`, `inline_jit_codegen_for_module`, `inline_jit_codegen_for_names`, `ModuleSuspendState`, plus ~15 `pub(crate)` helpers | The worker module is genuinely interior per FIXME 0109 (no `pub` surface change planned); the listed `pub` items are exposed only across the int crate boundary. `ModuleCheckAccumulator` is a pre-S66 type that survives in source pending the W3a-β follow-up resolution; per Decision 44's third amendment + `src/CLAUDE.md` "Cluster-Atomic Orchestration", the type is fully retired in the cluster-mode flip. Wave 3 deletes it. The worker file decomposition is FIXME 0109 (long-running, NOT in S67 scope). |
| `src/session_v4.rs` | `SessionSettings` (in facade), `CommandResult` (in facade), `EvalResult` (in facade) + `EvalResult::warnings`/`warnings_mut`/`value`/`ty`/`is_def`, `QUIT_SENTINEL` (above), `parens_balanced_pub`, `TypecheckProduct`, `Introspection` (in facade), `SharedState` (in facade + SharedState alignment plan), `CompilerSession` (in facade) + ~40 methods (most in facade; the additional pub methods: `set_lib_dirs`, `set_platform_dirs`, `push_platform_dir`, `poll_and_reload`, `current_module_name`, `register_module_with_source`, `register_entry_module`, `error_modules: HashSet<ModuleFullPath>`), `spawn_nice_workers`, `TestRunnerState::stub`, `clear_trace_display_state` | The main bulk is the facade; the additional pub methods listed are extension/test-driven helpers. Wave 3 may PIF-narrow `error_modules` (currently `pub`) to `pub(crate)` if no out-of-crate caller exists; `register_module_with_source` is the source-text variant of `register_module` and stays facade (file watcher invokes it). |

This table is the W1 reconciliation snapshot. As `src/` evolves, the table updates in step with the facade above per the W0 baseline-diff discipline (`design/arch/CLAUDE.md §"Baseline-diff discipline"`).

---

## `process_cluster` — the cluster-atomic orchestration loop

`int::process_cluster` is the sole orchestrator of the cluster-processing chain. It composes `frontend::expand`, `frontend::build_form` (returning `Vec<ParsedEntry>` per S66 FIXME 0156), and the single-call typecheck surface (`cranelisp_typecheck::check_forms` per Decision 44's 2026-05-13 third amendment); catches `ResolutionGap` returns from any of them; dispatches to the scheduler; and retries until the cluster fully processes or a non-gap error fires.

A **cluster** is the unit of typecheck atomicity (Decision 44):
- A non-`(begin)` REPL input is a one-form cluster (per the spec twin FIXME 0165 — non-`begin`-grouped REPL inputs are processed as single-form clusters; cross-input forward references are NOT supported).
- A `(begin form₁ … formN)` REPL input is the explicit multi-form cluster boundary — `eval` unwraps the top-level `begin` and passes the inner forms to `process_cluster`.
- Batch (file) compilation passes a file's non-structural forms as one big cluster (per spec §5.13.1's MAY-reference-freely rule at file scope).

Frontend and typecheck stay pure with respect to live state (no `Sess`, no `CompileScheduler` dependency — Principle 3). Per Decision 44 (amended FIXME 0167 for Approach B + SymbolTableAccess; 2026-05-13 third amendment collapsing the two-pass split), typecheck may mutate the orchestrator-handed staging `SymbolTable` via the `ctx.current_symbol_table_mut()` accessor — staging mutation is invisible to typecheck and to other workers. Workers park inside `wait_for_*` calls — that IS the worker's allowed parking site, never inside library code. `process_cluster` is THE crossing point where the gap value becomes a scheduler call AND where the `SymbolTableAccess::Cluster` construction mediates the cluster-internal Pass 1 / Pass 2 visibility (the two-pass discipline is internal to `check_forms`).

```rust
// process_cluster runs on workers — takes &SharedState (the worker's Arc clone).
// Per Decisions 25, 33 + the per-symbol mutability model: live_table is acquired
// via shared .get() (a shared shard read lock on the outer DashMap), NOT via
// .entry().or_default() (which would acquire a per-form whole-module write lock).
//
// Phase 0 (write_structural_decls + defn_order seed) ran in register_module
// before this work item was dispatched — see "register_module Phase 0" below.
//
// Per Decision 44 (amended FIXME 0167 for Approach B + SymbolTableAccess;
// 2026-05-13 third amendment collapsing the two-pass split) — staging is a
// transient, orchestrator-local SymbolTable that holds Pass 1 signature shells
// and Pass 2 body-checked entries until cluster commit. The orchestrator
// constructs SymbolTableAccess::Cluster { modules, staging, current_module } and
// threads &mut ctx to one cranelisp_typecheck::check_forms call. Typecheck
// reads via ctx.current_symbol_table() (returns View::union(staging, live)) and
// writes via ctx.current_symbol_table_mut() (returns &mut staging). The 91
// register-call sites in typecheck/program.rs do NOT change individually — the
// staging-vs-live distinction is absorbed by the accessors. The internal
// two-pass ordering is a check_forms implementation phase, not a facade
// surface; Pass-1-to-Pass-2 working state is internal to that frame.
pub fn process_cluster(shared: &SharedState, forms: Vec<Sexp>, scope: &ModuleFullPath) -> Result<ProcessedCluster, CranelispError> {
    // Cluster-scoped bookkeeping the orchestrator collects across forms.
    let mut warnings: Vec<Warning> = Vec::new();
    let mut resolved_imports: Vec<(ModuleFullPath, ImportNames)> = Vec::new();
    let mut introspection_records: Vec<(FQSymbol, Introspection)> = Vec::new();

    // Whole-cluster retry envelope — on any Gap from frontend or typecheck the
    // orchestrator dispatches via handle_gap, drops the staging frame, and
    // restarts the cluster. Cluster atomicity has no sub-cluster granularity.
    loop {
        // 1. Expand + build_form for every form in the cluster.
        let mut parsed_list: Vec<ParsedEntry> = Vec::new();
        let mut needs_retry_after_expand = false;
        for form in &forms {
            let expanded = match cranelisp_frontend::expand(form.clone(), &shared.symbol_tables, &shared.module_aliases) {
                Ok(s) => s,
                Err(ExpansionError::Gap(gap)) => {
                    handle_gap(shared, gap)?;
                    needs_retry_after_expand = true;
                    break;
                }
                Err(other) => return Err(other.into()),
            };
            let entries = cranelisp_frontend::build_form(&expanded)?;   // pure — no gaps
            parsed_list.extend(entries);
        }
        if needs_retry_after_expand { continue; }

        // 2. Construct staging + SymbolTableAccess.
        let mut staging: SymbolTable<Code, ()> = SymbolTable::new(scope.clone());
        let mut ctx = SymbolTableAccess::Cluster {
            modules: &shared.symbol_tables,
            staging: &mut staging,
            current_module: scope.clone(),
        };

        // 3. Single check_forms call. Internally: Pass 1 sweeps `parsed_list`
        //    (signatures into staging), Pass 2 sweeps `parsed_list` (bodies
        //    against ctx.current_symbol_table() = View::union(staging, live)).
        //    Per-symbol Pass-2 side products land on staging Def fields.
        //    Pass-1-to-Pass-2 working state is internal to the call.
        match cranelisp_typecheck::check_forms(parsed_list, &mut ctx, &shared.symbol_tables, &shared.module_aliases) {
            Ok(()) => {}
            Err(CheckError::Gap(gap)) => {
                drop(ctx);            // release &mut staging — staging dissolves
                handle_gap(shared, gap)?;
                continue;             // whole-cluster retry against fresh staging
            }
            Err(other) => return Err(other.into()),
        }

        // 4. Drop ctx to release the &mut staging borrow, then package.
        drop(ctx);
        return Ok(ProcessedCluster::from_parts(
            staging, warnings, resolved_imports, introspection_records,
        ));
    }
}

// insert_cluster commits the ProcessedCluster's drained staging entries into
// the live SymbolTable for `target`. Called by callers that want commit-side
// control (REPL defns; compilation worker). Eval expressions skip insert_cluster
// — the temp closure has no module commit.
pub fn insert_cluster(shared: &SharedState, processed: ProcessedCluster, target: &ModuleFullPath) {
    let live = shared.symbol_tables.get(target).expect("module registered");
    for (k, e) in processed.into_iter() {
        live.insert_or_update(k, e);                    // per-entry inner-DashMap write
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

(Sprint 67 W1 PFR — `process_cluster` and `insert_cluster` are free functions hosted in `src/cluster.rs:177/248`, NOT `CompilerSession` methods. They take `&SharedState`. Workers invoke them with their `Arc<SharedState>` clone; the initiator thread invokes them through `&self.shared`. The previous facade text presented them as `CompilerSession` methods with a parenthetical note allowing a delegation shape; the actual implementation skipped the delegating method and exposes the free fns directly. This is the durable shape.)

**Atomicity guarantees**:
- A failure at any point — `expand` Gap that the scheduler resolves to a cycle, `check_forms` Gap, `check_forms` TypeError — drops the staging `SymbolTable` on the floor when the function frame returns. The live `SymbolTable` is byte-identical to its pre-cluster state. The live invariant ("if it's in the live table, it's checked AND committed") holds across cluster boundaries; only completed clusters are visible to other workers.
- Inside `check_forms`, Pass 1's signature shells become visible to Pass 2 through `ctx.current_symbol_table()` — which returns a `View::union(staging, live)` in `SymbolTableAccess::Cluster` mode. That is how mutual recursion / forward references resolve. Other workers seeing the live table mid-cluster cannot observe staging contents; staging is orchestrator-local and is held under the orchestrator's stack-frame `&mut` borrow inside the `SymbolTableAccess`.

**Termination**. Each `handle_gap` call advances the dependency state monotonically (registers a module, satisfies a typecheck wait, satisfies an inmem wait). Subsequent retries see strictly more state than the previous attempt; the loop terminates when expand + both passes succeed, when a non-gap error fires, or when the scheduler returns `SchedulerError::Cycle` (mutual import per Decision 30).

**Gap design rationale** (one round-trip per FQ ref encountered):
- A single FQ ref produces one gap → one `handle_gap` → one retry. The loop doesn't fire N+1 round-trips per FQ.
- `expand` returns `MacroInMem(fq)` uniformly for any FQ ref it can't yet resolve — regardless of whether the module is unregistered, typecheck is incomplete, or code is missing. Expand stays uniform; the gap-name reflects expansion's MAXIMUM possible need.
- The orchestrator owns the **macro-vs-fn discrimination**. After `wait_for_typecheck_symbol` completes, it peeks at the entry: only forces a JIT (`priority_boost_jit` + `wait_for_inmem`) if the entry actually IS a macro with missing code. Functions are NOT speculatively JIT-pushed — the function will be JIT'd when its caller is processed. This avoids yanking a function ahead of pending priority work for code that expand never actually needs.
- `check_forms` asks for `SymbolTypechecked` only — by the time it runs, any macros are already expanded out, so only types/schemes are needed.
- Multiple FQ refs in the same form still cost one round-trip each (expand or `check_forms` returns at the first unresolved ref). Batching across multiple gaps in one return would require continuing past the first unresolved ref and accumulating; deferred until profiling shows it matters.

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

4. **Collect `.o` paths.** For the entry module + every transitively-loaded module, read the `.o` path from `ObjectCache`. (The `wait_object_complete()` call earlier in `exec-flow-link` ensures all `.o` files are written.)

5. **Spawn system linker.** `std::process::Command::new("ld")` (macOS / Linux) or `"link.exe"` (Windows) with arguments:
   - `-o {project_root}/target/{entry_module}` (executable output path; `.exe` on Windows)
   - The collected `.o` paths
   - The alias `.o` from step 3
   - The `cranelisp-intrinsics` and `cranelisp-primitives` static archives (linked at build time via `build.rs`; paths captured in consts) — post-Decision-43 the previously-single `cranelisp-runtime` archive is replaced by these two siblings
   - Any platform `.dylib`/`.so` files for transitively-loaded platforms
   - Standard system libraries (`-lc`, etc. — platform-specific)

6. **Surface failures.** Non-zero exit code from the linker becomes `CranelispError::LinkError { message: stderr }`.

The system linker invocation is opaque to the facade — `std::process::Command` is not wrapped in a Cranelisp facade type. The contract is: backend's `.o` files conform to the Object file contract (see the `crates/cranelisp-backend/src/lib.rs` + `cache/object.rs` rustdoc + `bounded-contexts.md` §3; `facades/backend.md` retired S75 W5b → BC §3 + source rustdoc), and `int` invokes ld with them plus the alias. The two-GOT model in Decision 23 means the `.o` data section GOT (`Linkage::Export __cranelisp_got_{module}`) is what ld resolves; the in-memory GOT is irrelevant in `--link` mode.

### Exe-bundle startup contract — `cranelisp_init_primitives()` (Decision 48)

Per Decision 48 (S68 — `/arch` Phase 2 recommendation), `cranelisp-exe-bundle` exposes an explicit startup hook `cranelisp_init_primitives()` — a `pub extern "C" fn` with a no-op body that forces `LazyLock::force(&cranelisp_primitives::PRIMITIVES_TABLE)`. The standalone binary's startup stub calls it (alongside `cranelisp_init_platform(...)`) before any user code runs, so the static's `LazyLock` init runs and the `.o` data-section GOT — `Linkage::Export __cranelisp_got_primitives` — is populated with the raw fn ptrs at the prescribed slot indices before any backend-emitted import resolves through it.

```rust
// crates/cranelisp-exe-bundle/src/lib.rs — sketch of the post-S68 shape.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_init_primitives() {
    // Force the LazyLock to initialise so PRIMITIVES_TABLE's static
    // GotTable is populated before any compiled call site resolves
    // through `__cranelisp_got_primitives`.
    LazyLock::force(&cranelisp_primitives::PRIMITIVES_TABLE);
}
```

This **replaces** the pre-S68 force-link `pub use cranelisp_primitives::{bool, float, int, marshal, ring0, string as primitives_string, vec as primitives_vec};` re-exports that lived in `cranelisp-exe-bundle/src/lib.rs` to coax the linker into retaining `#[no_mangle]` runtime functions. Those re-exports relied on **implicit** discipline (`#[used]` annotations + `pub use` referencing) and made the dependency invisible at the call site that needed it. The explicit `cranelisp_init_primitives()` call makes the dependency **legible at the site** — the startup stub names what it needs, and the link-time symbol resolution is the natural enforcement (a missing primitives symbol fails the link cleanly). Per /arch's Phase 2 recommendation, the explicit init-hook shape is preferred over implicit `#[used]` discipline.

The `cranelisp-primitives` per-fn `pub extern "C"` items demote to `pub(crate)` post-S68 (with `#[used]` on each function as a belt-and-suspenders DCE guard); the only pub item the crate publishes is `PRIMITIVES_TABLE`. The static archive `libcranelisp_exe_bundle.a` retains the runtime functions because the static `PRIMITIVES_TABLE`'s `LazyLock` init code references them at compile time — the linker preserves them as transitive dependencies of the static-init body. `cranelisp_init_primitives()`'s sole runtime effect is forcing that LazyLock — once forced, the symbols are referenced from the GotTable slots, which `__cranelisp_got_primitives` indexes into.

Intrinsics force-link re-exports (`cranelisp_intrinsics::{alloc, drop, io, ivar, panic, rc, heap_string, vec_runtime}`) remain — intrinsics are not a module (Decision 43) and have no SymbolTable/GotTable to seed; their runtime symbols are JITBuilder-registered by-name in JIT mode and linker-resolved by-name in `--link` mode (same shape as `--link` mode user fns reaching extern intrinsics).

---

## Re-exports from `cranelisp-types`

```rust
pub use cranelisp_types::{
    CodegenBehaviour, ModuleStrategy,
    Symbol, ModuleFullPath, FQSymbol, FQTypeName,
    Sexp, Type, Scheme, SymbolTable, ModuleEntry, DefKind,
    ImportSpec, ExportSpec, NamedImport, NamedExport, ImportNames, PlatformSpec, ModDecl,
    CranelispError, Warning, Span,
    PrimitiveDef, SchedulingClass,
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
- **`cranelisp-typecheck`** — `check_forms` (per Decision 44's 2026-05-13 third amendment — single-call cluster surface; the internal two-pass discipline does not cross the facade), `CheckResult`, `CheckError`, `CheckState`, `SymbolTableAccess`, `TypeCheckEnv`, the trace install hook. (`register_builtins` is no longer consumed from typecheck — synthetic-module assembly is deleted from typecheck per FIXME 0241; `int`'s own session-init seeding routine reconstructs the mount, see §"Session init" + FIXME 0242.)
- **`cranelisp-backend`** — `compile_to_module` (returns `Result<CompilationArtifacts, CompilationError>` per Decision 41 + S70 Phase B amendment; writes `Code::Jit` and the GOT slot ptr directly into the passed-in shared stores via `&self`-interior-mutable methods; returns the always-created introspection contributions as `CompilationArtifacts` by value — int composes its `Introspection` struct from the artefact plus parse-time fields), `produce_disasm` (the on-demand disassembly free function — int invokes when a REPL `/disasm` request fires), `CompilationArtifacts` (the value-returned per-call introspection contributions), `load_object`, `compile_to_object`, `Code` (re-exported per Decision 41), `LinkerArtefact`, `ObjectArtefact`, `Jit`, `Linker`, `CompilationError` (with `SymbolNotCompilable` variant per §2.7), `GotObserver` + `GotEvent` + `GotEventTag` + `GotProvenance` + `register_got_observer` (per FIXME 0099 — backend-originated observer types, int registers consumer state). Cranelift `Module`, `JITModule`, `ObjectModule`, `JITBuilder` (via cranelift crates re-exported from backend).
- **`cranelisp-intrinsics`** — backend-emitted intrinsic extern functions registered with the JIT (via `JITBuilder::symbol`) per Decision 43: `cranelisp_alloc`, `heap_alloc_payload`, `heap_dealloc`, `rc_inc`, `rc_dec`, `consume_shallow`, `dec_shallow_io`, `vec_*`, `heap_alloc_string`, `string_read`, `sconcat`, `quote_sexp`, `cranelisp_run_io`, `io_run`, `run_io_trampoline`, `ivar_*`, `runtime_panic`. Stats accessors (`alloc_count`, `dealloc_count`, `bytes_allocated`, `bytes_current`, `bytes_peak`, `reset_counts`) for `/mem`. The IO observer extension point (`IoEvent`, `IoEventTag`, `IoObserver`, `register_io_observer`, `trace_anchor`) per Decision 40 — int registers an `IoObserver` at session init when REPL/trace mode is on or `CRANELISP_IO_TRACE=1`.
- **`cranelisp-primitives`** — one pub item consumed: the static `PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<(), ()>>>` (per Decision 48 — S68; `<(), ()>` flavour per the S73 backend sever). Session init clones it and calls `.into_concrete::<Code, ()>()` to mount it into `shared.symbol_tables` at `ModuleFullPath::primitives()` (`int` names `Code` here; primitives does not). The concretized table shares the static's `Arc<GotTable>` (populated at static-init with raw `*const u8` fn ptrs for every non-inlined primitive: string ops, marshal, per-type to-string, int/float/bool conversions, `not`). From the instant session-init completes, primitives dispatch is functionally equivalent to any other module — the standard cross-module GOT-indirect path (Decision 23, Decision 31) resolves `(let [f +] (f 1 2))` via `__cranelisp_got_primitives[slot]`. **No special case in backend's `symbol_lookup_fn`** — the per-process static `Arc<GotTable>` IS the SymbolTable-GOT row of Decision 23's two-GOT model. The pre-S68 per-fn `pub extern "C"` items demote to `pub(crate)` (with explicit init-hook discipline; see "Link orchestration" below for exe-bundle's force-link replacement). Inline substitution in backend (`primitives_inline.rs`) remains a separate code-size + dispatch-cost optimisation — identical semantics, faster code.
- **`cranelisp-platform`** — `HostContext`, `HostCallbacks`, `OwnedPlatformFnDescriptor`, `PlatformFn`, `load_manifest`, `parse_type_sig`, `derive_jit_name`. `int` constructs `HostCallbacks` at session init pointing at runtime fns.
- **`cranelisp-exe-bundle`** — for `--link` mode. The crate provides the alias `.o` template + system linker invocation helpers, plus the `cranelisp_init_platform` and `cranelisp_init_primitives` (Decision 48) startup hooks the produced standalone binary's stub calls before running user code. Per `bounded-contexts.md` §6 — exe-bundle is part of the binary surface; one D/D/R cycle covers both.

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
- `ProcessedCluster` (per Decision 44)
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

3. **`Code` lives in `cranelisp-backend` (Decision 41 amends Decision 35; S66 amendment slims variants — preserved through same-day rollback `1dc57ae`).** The concrete `C` parameter for `SymbolTable<C, L>` is `Code` — the enum lives in `cranelisp-backend/src/code.rs` (moved per Decision 41 from the previous `src/code.rs` location). `cranelisp-types` stays Cranelift-ignorant — Principle 3 protection intact. Backend constructs `Code::Jit(Arc<Jit>)` directly and writes via Decision 38's `write_code(&self, sym, code)` (interior-mutable; no `&mut` flow needed), and writes the resulting fn pointer to the entry's GOT slot via `symbol_table.got().store_slot(entry.got_slot.unwrap(), ptr)` — the GOT is the post-rollback single source of truth for callable addresses (the briefly-considered sibling `fn_ptr` field landed in `b09ec76` and was rolled back the same day in `1dc57ae`). `Code` carries lifecycle owner only. Decision 35 Layer 2 Option B retracts. `int` re-exports `Code` for session-boundary `SymbolTable<Code, ()>` instantiation; the previous worker-side post-loop (iterate-over-names + GOT-store + `Code::Jit`-construct + three error cascades) collapses into the per-symbol call-site loop documented in `bounded-contexts.md` §3 (backend — invariant 3) + the `crates/cranelisp-backend/src/code.rs` rustdoc (`facades/backend.md` retired S75 W5b → BC §3 + source rustdoc). Backend signatures use `&SymbolTables<Code, ()>` + `&ModuleAliases` (non-blind for `C`; alias-table threaded for §8.6.6 qualified-name resolution); non-codegen crates (frontend, typecheck) stay generic on `SymbolTables<(), ()>` per Decision 32's empty-marker traits.

4. **Scheduler is sole coordination authority.** Per the runtime/platform diagrams' explicit merge — `CompileScheduler` owns BOTH work dispatch AND per-symbol/per-module wait/release. There is no separate `DependencyService`.

5. **`process_cluster` + `insert_cluster` is the shared cluster-processing entry.** Per `exec-flow-compilation` and `exec-flow-repl` — workers and eval both call `process_cluster` for the single-call `check_forms` typecheck (per Decision 44's 2026-05-13 third amendment; the two-pass discipline is internal to `check_forms`) against orchestrator-owned staging; defining-form callers follow up with `insert_cluster` to commit staging into the live `SymbolTable` atomically. Eval expressions skip `insert_cluster` (temp closure — no commit target). Per Decision 44, a cluster is one form (non-`begin` REPL input), the contents of `(begin ...)` (explicit REPL cluster), or a file's non-structural forms (batch).

5a. **`process_cluster` is the gap-orchestration crossing point.** Frontend and typecheck stay pure — they surface dependencies as `Err(ExpansionError::Gap(ResolutionGap))` / `Err(CheckError::Gap(ResolutionGap))`. `int::process_cluster` is the sole crate-crossing where gap values become scheduler calls (`handle_gap` → register + wait + priority_boost). Workers park inside the scheduler's `wait_for_*` calls — never inside frontend or typecheck library code. See "`process_cluster` — the cluster-atomic orchestration loop" above.

5b. **Cluster-atomic commit, staging is orchestrator-local (Decision 44 amended FIXME 0167; 2026-05-13 third amendment).** Within `process_cluster` the orchestrator owns a transient `SymbolTable` ("staging") that holds the cluster's signature shells and body-checked entries; typecheck reads via `ctx.current_symbol_table()` (returns `View::union(staging, live)` in `Cluster` mode) and writes via `ctx.current_symbol_table_mut()` (returns `&mut staging`). The 91 register-call sites in typecheck do not change individually — staging-vs-live distinction is absorbed inside the accessors. On any `Err` from `check_forms` (Gap or TypeError), the orchestrator drops staging on the floor when the function frame returns; the live `SymbolTable` is byte-identical to its pre-cluster state. On Gap, the orchestrator dispatches and retries the whole `check_forms` call against a fresh staging frame. On full success, `insert_cluster` drains staging into the live table per-entry (under inner-DashMap locks). The live invariant ("if it's in the live table, it's checked AND committed") holds across cluster boundaries — staging contents are never observable to other workers.

6. **Per-eval JIT lifetime (Decision 31).** Per pipeline-v4 §6.2 — each eval expression compiles its temp closure on a fresh `JITModule` wrapped in `Arc<Jit>`. The wrapper's custom `Drop` reclaims pages when the trampoline returns and the value is consumed.

7. **REPL never calls `wait_for_*` at startup.** Per the `exec-flow-repl` rewrite — startup is `register_module` only. The first iteration's STEP 4 wait catches up the entry module's in-mem code. This keeps the prompt responsive immediately.

8. **Watcher events processed concurrently with prompt-wait.** Per `exec-flow-repl` STEP 1–STEP 3 — `set_repl_input_active(true)` opens the watcher window during `read_line`; `set_repl_input_active(false)` closes it on input submission. STEP 4's `wait_inmem_complete()` catches up everything triggered during the prompt.

9. **Definitions append to `current_repl_module`, not `user`.** Per `exec-flow-repl` — `current_repl_module` is the session-scoped target for `eval`'s defining forms. Defaults to the entry module from `parse_args`. `/mod` changes it. `"user"` is a default name, not architecturally special.

10. **Additive append, not re-register.** Per `exec-flow-repl` — `Sess::eval` for a defining-form input constructs a one-form cluster (or unwraps a `(begin ...)` into a multi-form cluster per Decision 44), runs `process_cluster` against `current_repl_module`'s live table + transient staging, commits via `insert_cluster` on success, and waits for that cluster's symbols' jit. The whole module is NOT re-typechecked.

11. **Cache-hit decision lives at `notify_typecheck_done_from_cache` (Decision 37).** Cache-hit-typecheck path enqueues `LoadObject(m1)` only; cache-miss path uses per-symbol `Jit(fq)`. The decision is implicit in which `notify_typecheck_done_*` variant fires — no mid-flight cache rechecking.

12. **`--link` emits the `_main` alias (Decision 36).** Backend stays uniform (bare-Local for every function); `int::link_by_name` emits the entry-point alias `.o` that exports `_main` as a relocation against the entry module's `__cranelisp_got_{module}[main_slot]`. This is one targeted alias, not a whole-module asymmetry.

13. **`Code::Jit` and `Code::Linker` retention dissolves on session shutdown.** Per Decisions 31 + 35 — `drop(Sess)` drops every `ModuleEntry::Code`; the `Arc<Jit>` and `Arc<Linker>` chains reach refcount 0; custom `Drop` reclaims pages.

14. **Mutual-import deadlock is a known constraint (Decision 30).** Two modules `A` and `B` that each import from the other will deadlock the form-by-form scheduler. Documented; not fixed by this facade. Workaround: `discover-tests` + `run-test` builtins for test scaffolding (per Decision 30's "Safe patterns").

15. **`SharedState` vs `CompilerSession` split is mode-aligned (Decision 38).** `SharedState` carries everything reachable by workers — `symbol_tables`, `scheduler`, `cache`, `kept_dlls`, `introspection`, read-only configuration. `CompilerSession` carries everything reachable only by the initiator thread — watcher channel, REPL eval cursor, worker pool handles, accumulated warnings. Workers receive `Arc<SharedState>` at spawn, never see `CompilerSession`. No worker-side merge step: all mutation happens through interior mutability of the contained types under per-cell locks.

16. **Per-symbol mutability after Phase 0 (Decision 38, FIXMEs 0008/0009; Decision 44 amended FIXME 0167; 2026-05-13 third amendment).** `register_module` runs Phase 0 synchronously: `parse → entry(m).or_default() → write_structural_decls → drop RefMut`. After Phase 0, all live `SymbolTable` access is `&SymbolTable` + per-entry inner-DashMap locks. `process_cluster` uses the `&shared.symbol_tables` DashMap reference (housed under `SymbolTableAccess::Cluster.modules`) for cross-module reads, not `.entry().or_default()`. The single-call typecheck surface `cranelisp_typecheck::check_forms` takes `&mut SymbolTableAccess<'_, C, L>`; in `Cluster` mode the orchestrator owns a separate transient `SymbolTable` ("staging") that is `&mut`-borrowed inside `SymbolTableAccess` for the lifetime of the cluster — typecheck mutates staging via the `current_symbol_table_mut()` accessor, oblivious to the staging-vs-live distinction. The two-pass discipline lives inside `check_forms`'s frame, not on the facade. Staging is never published — it dissolves on cluster failure or drains into live atomically on success. The only `&mut SymbolTable` operations on the **live** table are Phase 0 (structural decls + defn_order seed) and per-cluster REPL appends to `defn_order` during `insert_cluster`.

17. **Introspection is mode-conditional (Decisions 38, 39).** `shared.introspection` is `Some(DashMap)` iff REPL mode OR `CRANELISP_CODEGEN_TRACE` is set. Production batch leaves it `None` and pays zero per-symbol metadata overhead. Source text is per-defn on `Introspection.source` — there is no module-global source store. Parse errors capture context inline (in `ErrorLocation.context`); typecheck/codegen errors capture coordinates (`line_col` + `fq`) and let the formatter resolve source via introspection at display time.
