> **HISTORICAL — superseded slice / working doc (triaged S110, FIXME 0607).** A
> point-in-time implementation-slice narrative, retained for the audit trail only; NOT
> current design intent. The durable design is `int.md` (master) plus the subsystem docs
> indexed in `design/int/CLAUDE.md` §"Document index". Where this doc disagrees with the
> current source or the master, the source and master win.

# Sprint 66 Wave 3a — int `process_form` shape-pivot + Waves A/B/C + D43 source migration

> **Superseded 2026-05-13:** This document's references to the two-pass typecheck surface (`check_form_signatures` + `check_form_body`) are **superseded by Decision 44's 2026-05-13 third amendment** — `int::process_cluster` now makes one `cranelisp_typecheck::check_forms` call per cluster (not two). On `Err(Gap)` the orchestrator drops staging and retries the whole `check_forms` call (whole-cluster retry; no per-form retry granularity). `ProcessedCluster` carries `warnings`/`resolved_imports`/`introspection_records` in addition to staged entries; the int-side `ModuleCheckAccumulator` stub authored in this design's first implementation pass is removed in favour of those fields on `ProcessedCluster`. Cluster-atomic protocol (staging owner, drain-on-Ok, drop-on-Err) is unchanged. The canonical orchestration shape is `design/arch/facades/int.md` §"`process_cluster` — the cluster-atomic orchestration loop". `/dev (int)` will refresh §1 of this document in detail when implementing the collapsed shape.

**Status.** Phase 5 Stage 2 design refinement against Wave 3a parallel /design agents (frontend `build_form`, typecheck single-call cluster surface).
**Author.** /design (int), 2026-05-12.
**Reads.** `design/arch/facades/int.md` §"`process_cluster` — the cluster-atomic orchestration loop", `design/int/int.md` master, `design/int/implementation-slice-s66.md` Waves A/B/C/D, `design/arch/decisions/0044-cluster-atomic-typecheck-orchestrator-staging.md` (post-FIXME-0167 + 0168 amendments), `design/arch/decisions/0043-runtime-split-into-primitives-intrinsics.md`, `design/arch/fixmes/0098-*.md` Phase 4 (int row), `design/arch/fixmes/0107-*.md` (verify-only on int side).

This doc elaborates a single intra-crate refinement that ties together five Wave 3a deliverables on int: the `process_form → process_cluster` shape pivot per Decision 44; the Waves A + B + C structural foundation that must land before β fires; the D43 source migration; the FIXME 0107 verify task; and the resulting facade-compliance delta. It is subordinate to `int.md` (the master), not a replacement; rows referenced here trace back to `implementation-slice-s66.md`.

Wave 3a-α (locality-correctness refactor per Decision 0046) is parallel /design-typecheck's deliverable; this doc covers β — the post-α triad re-fire as it lands int-side.

---

## 1. `process_form → process_cluster` shape-pivot

### 1.1 Target signature

Per facade §"`process_cluster`" and Decision 44 (post-FIXME-0167 amendment):

```rust
// On CompilerSession — the public façade
pub fn process_cluster(&mut self, forms: Vec<Sexp>, scope: &ModuleFullPath)
    -> Result<ProcessedCluster, CranelispError>;
pub fn insert_cluster(&mut self, processed: &ProcessedCluster, target: &ModuleFullPath);

// Free function the method delegates to — worker-callable, takes &SharedState
pub fn process_cluster(shared: &SharedState, forms: Vec<Sexp>, scope: &ModuleFullPath)
    -> Result<ProcessedCluster, CranelispError>;
pub fn insert_cluster(shared: &SharedState, processed: ProcessedCluster, target: &ModuleFullPath);
```

The shape pivot is **three combined moves** vs the as-built `process_form`:

1. Per-form retry loop → **per-cluster two-pass loop** (Decision 44).
2. Ad-hoc string-parse gap detection → **typed pattern-match** on `ExpansionError::Gap(ResolutionGap)` and `CheckError::Gap(ResolutionGap)` (FIXME 0098 Phase 4 + Phase 2 + Phase 3 upstream).
3. Frontend `build_form` returning a **single Defn-or-Defmacro** → **`Vec<ParsedEntry>`** (FIXME 0156, parallel /design frontend's deliverable).

These three moves are **bundled** because the inner data type at every step changes — splitting them would mean an intermediate shape that doesn't compose.

### 1.2 Cluster construction (orchestrator-owned)

The orchestrator allocates a transient empty `SymbolTable<Code, ()>` for `staging` at cluster start, constructs `ClusterContext::Cluster { modules: &shared.symbol_tables, staging: &mut staging, current_module: scope.clone() }`, and threads `&mut ctx` through both passes. Staging is a stack-local borrow for the duration of the cluster; commit drains entries via `insert_cluster` on Pass-2 success; failure drops staging when the function frame returns and live is byte-identical to pre-cluster.

The 91 typecheck register-call sites do **not** change individually (per the FIXME 0167 amendment) — typecheck's `current_symbol_table_mut()` accessor absorbs the staging-vs-live distinction. Int is the only caller that constructs `ClusterContext::Cluster`; the rest of typecheck's call surface is mode-agnostic.

### 1.3 Pass interleaving — sequence

```text
process_cluster(shared, forms, scope):
  // Step 1: parse-side gap loop (per-form expand + build_form)
  parsed_list = []
  for form in forms:
    loop:
      try expand(form, &shared.symbol_tables)
        on Ok(expanded) -> entries = build_form(&expanded); parsed_list.extend(entries); break
        on Err(ExpansionError::Gap(g))  -> handle_gap(shared, g); continue
        on Err(other)                   -> return Err(other.into())

  // Step 2: stage + context
  staging = SymbolTable::<Code, ()>::new(scope.clone())
  ctx = ClusterContext::Cluster { modules: &shared.symbol_tables, staging: &mut staging, current_module: scope.clone() }

  // Step 3: Pass 1 — signatures across every ParsedEntry
  for parsed in &parsed_list:
    loop:
      try check_form_signatures(parsed.clone(), &mut ctx, &shared.symbol_tables)
        on Ok(())                  -> break
        on Err(CheckError::Gap(g)) -> handle_gap(shared, g); continue
        on Err(other)              -> return Err(other.into())     // staging drops on frame exit

  // Step 4: Pass 2 — bodies; entries supersede Pass-1 shells via staging mutation
  for parsed in &parsed_list:
    loop:
      try check_form_body(parsed.clone(), &mut ctx, &shared.symbol_tables)
        on Ok(())                  -> break
        on Err(CheckError::Gap(g)) -> handle_gap(shared, g); continue
        on Err(other)              -> return Err(other.into())     // staging drops on frame exit

  // Step 5: release the staging &mut, hand it to ProcessedCluster
  drop(ctx)
  return Ok(ProcessedCluster::from_staging(staging))

// commit is a separate call so REPL eval-expression form can skip it
insert_cluster(shared, processed, target):
  let live = shared.symbol_tables.get(target).expect("module registered");
  for (sym, entry) in processed.into_iter():
    live.insert_or_update(sym, entry)
    // populate introspection if shared.introspection.is_some() — Decision 38/39
```

**Why per-form gap loop inside Steps 3/4** (not whole-cluster gap loop): a gap surfaced on form N tells us "register module M; wait for symbol s" — the rest of the cluster's forms are untouched and stay valid. Retrying form N is the minimal unit of progress; restarting the whole cluster pass is unnecessary work. The single-form retry preserves monotonic progress (each `handle_gap` strictly advances scheduler state).

**Macro-vs-fn discrimination stays orchestrator-owned** per master design §6.3; `handle_gap` peeks at the entry post-typecheck and only forces JIT for `DefKind::Macro` entries whose `code` is `None`. Functions are never speculatively JIT-pushed — that distinction lives in `handle_gap`, not in `expand` (which returns a uniform `MacroInMem(fq)` for any unresolved FQ ref).

### 1.4 REPL eval composition

```text
eval(src):
  parse(src) → top_sexp
  if let Sexp::List([SexpSym("begin"), forms..]) = top_sexp:
    cluster_forms = forms                       // unwrap (begin ...)
  else:
    cluster_forms = vec![top_sexp]              // one-form cluster

  match classify_form(&cluster_forms[0]):       // peek at first form's kind
    EvalExpr =>
      // Eval-expression form — compile a temp __expr closure on a fresh Jit; trampoline; return EvalResult::Value
      processed = process_cluster(shared, cluster_forms, &shared.session_eval_scope())?;
      // NO insert_cluster — temp closure has no module commit
      trampoline → EvalResult::Value
    Defining =>
      processed = process_cluster(shared, cluster_forms, &self.current_repl_module)?;
      insert_cluster(shared, processed, &self.current_repl_module);
      EvalResult::Def { ... }
    Import =>
      processed = process_cluster(shared, cluster_forms, &self.current_repl_module)?;
      insert_cluster(shared, processed, &self.current_repl_module);
      EvalResult::Import { ... }
```

`classify_form` simplifies because `FormKind::Defmacro` merges into `FormKind::Regular` per FIXME 0156 — the dispatch on macro-vs-defn-vs-other now lives inside `build_form`'s `Vec<ParsedEntry>` shape, not at int's classification point.

### 1.5 Worker dispatch composition

```text
worker_loop(shared: Arc<SharedState>):
  loop:
    match shared.scheduler.take_priority_work_blocking():
      Some(Typecheck(module)) =>
        // Read all forms for the module from its parsed cache (Phase 0 captured forms during register_module)
        forms = shared.symbol_tables.get(&module).expect("Phase 0 ran").pending_forms()
        processed = process_cluster(&shared, forms, &module)?
        insert_cluster(&shared, processed, &module)
        shared.scheduler.notify_typecheck_done(&module)
      Some(Jit(fq))              => compile_jit(&shared, fq),
      Some(LoadObject(module))   => load_cache_o(&shared, module),
      None                       => break
```

The worker treats a whole module's non-structural forms as **one big cluster** (per spec §5.13.1; per Decision 44 §"Cluster boundaries" — batch is one-big-cluster). This is the file-scope MAY-reference-freely rule made structural.

## 2. Cluster-atomic protocol — invariants

Invariants the orchestration must uphold (cited from Decision 44 §"Rationale" + master design §4):

1. **Live-table single source of truth** (Principle 7). `shared.symbol_tables[scope]` contains only fully-checked, fully-committed entries. The live invariant is unconditional — *"if it's in the live table, it's checked AND committed."*
2. **Cluster atomicity** (Decision 44). On Pass-1 or Pass-2 failure, the staging table dissolves with the function frame; live is byte-identical to its pre-cluster state. On success, `insert_cluster` drains staging entries into live under per-entry inner-DashMap locks.
3. **Staging non-publication.** The staging `SymbolTable` is stack-local, `&mut`-borrowed for the cluster's duration, never `Arc`-shared. No worker can observe it from another thread. (Other workers reading the same module see the live table only.)
4. **Worker exclusivity per cluster.** Per Decision 30 (reframed by Decision 38): at most one `PriorityWork::Typecheck(module)` is dispatched at a time. The scheduler's ordering primitive enforces this; the lock layer no longer requires it. Wave 3a does NOT change this — int's `scheduler.notify_typecheck_done` already serialises module-level dispatch.
5. **Gap-retry termination.** Each `handle_gap` call advances dependency state monotonically; retries see strictly more state. Loop terminates on success, non-gap error, or `SchedulerError::Cycle` (Decision 30 mutual-import deadlock — known; documented; workaround via `discover-tests`).
6. **Introspection consistency** (Decision 38 + 39). `shared.introspection` populates synchronously with `insert_cluster` (or at the per-symbol `compile_to_module` call for codegen-side fields). `shared.introspection.insert(fq, fresh)` overwrites on REPL redefinition; carry-forward of the `Arc<Jit>` reference happens via the `ModuleEntry::Def.code` field per Decision 31 §"carry-forward invariant".

The orchestrator (`process_cluster` + `insert_cluster`) is the only crate-crossing point where ResolutionGap values become scheduler calls. Frontend `expand` and typecheck `check_form_*` are pure with respect to live state per Principle 3 — they return Gaps, they don't call the scheduler.

## 3. SharedState extraction (FIXME 0153 Interpretation A)

Per the user-arbitrated resolution of FIXME 0153: SharedState extraction lands in S66 Wave 3a as the structural prerequisite for the receive-side commitments downstream. The full god-file decomposition (FIXME 0109 — splitting `session_v4.rs` and `worker.rs` into modular files) is deferred to S67+ because it can land cleanly on top of the post-Wave-3a shape but not before.

### 3.1 Target data-model split

Per master design §4 + `facades/int.md` §"`SharedState`":

```rust
// Lives at session_v4.rs (or, post-S67 decomposition, at src/session/shared.rs)
pub struct SharedState {
    // The single store — Decisions 25, 26, 33
    pub symbol_tables: DashMap<ModuleFullPath, SymbolTable<Code, ()>>,

    // Coordination
    pub scheduler: Arc<CompileScheduler>,
    pub cache:     Arc<ObjectCache>,

    // Long-lived runtime
    pub kept_dlls: DashMap<PathBuf, Arc<DllHandle>>,

    // REPL / trace introspection (Decision 38) — mode-conditional
    pub introspection: Option<DashMap<FQSymbol, Introspection>>,

    // Read-only configuration
    pub settings:      SessionSettings,
    pub project_root:  PathBuf,
    pub lib_dirs:      Vec<PathBuf>,
    pub platform_dirs: Vec<PathBuf>,
}

// CompilerSession — initiator-thread-only
pub struct CompilerSession {
    pub shared: Arc<SharedState>,

    watcher:             Option<WatcherChannel>,
    current_repl_module: ModuleFullPath,
    repl_input_active:   Arc<AtomicBool>,             // shared with watcher event handler
    worker_pool:         WorkerPool,
    warnings:            Vec<Warning>,
}
```

### 3.2 What moves where

| As-built today (`CompilerSession` god-struct field) | Wave 3a target |
|---|---|
| `symbol_tables: DashMap<...>` | `SharedState.symbol_tables` (interior-mutable; per-entry locks) |
| `scheduler: Arc<CompileScheduler>` | `SharedState.scheduler` (was already Arc; just reparents) |
| `cache: Arc<ObjectCache>` | `SharedState.cache` |
| `kept_dlls: DashMap<...>` | `SharedState.kept_dlls` |
| `module_sources` (legacy per D39) | **DELETE** (per master §8.3 + FIXME 0153 Interpretation A — but this row is Wave F of the slice, sequenced after Wave 3a-β's process_cluster ladders bind) |
| `kept_linkers` (legacy per D31) | **DELETE** (per master §7.4 — verify zero matches first) |
| `settings, project_root, lib_dirs, platform_dirs` | `SharedState.*` (read-only after construction) |
| `watcher: Option<WatcherChannel>` | `CompilerSession.watcher` (stays initiator-side; mpsc receiver) |
| `current_repl_module: ModuleFullPath` | `CompilerSession.current_repl_module` |
| `repl_input_active: Arc<AtomicBool>` | `CompilerSession.repl_input_active` (Arc-cloned to watcher event handler) |
| `warnings: Vec<Warning>` | `CompilerSession.warnings` (initiator-collected; never cross-thread) |
| `worker_pool` handles | `CompilerSession.worker_pool` (joins on Drop) |

### 3.3 Wave-3a-α dependency

Pre-α, typecheck's 40+ direct `self.modules.X` accesses bypass per-module accessors (cross-module short-name searches, impl-resolution sites, direct cross-module gets, direct mutating writes). Wave 3a-β cannot start before α completes because cluster-atomic correctness depends on every typecheck read/write flowing through `ctx.current_symbol_table[_mut]()`. SharedState extraction in this slice's Wave C lands *concurrently* with α — α touches typecheck's internals; Wave C touches int's session struct; both must be in place before β's `process_cluster` typed pattern-match wiring lands.

Sequencing: α + Wave C run in parallel (α in typecheck, Wave C in int); β's gap-orchestration wiring is downstream of both.

## 4. Wave A + Wave B + Wave C plan

The structural foundation. All three must land before Wave D (process_cluster typed pattern-match) wires up.

### 4.1 Wave A — physical relocations (~1.5–2 days)

**Pure file-shuffles**; downstream import sweeps depend on this being done first.

| Move | Source | Target | LOC |
|---|---|---|---|
| `trace.rs` | `crates/cranelisp-runtime/src/trace.rs` | `src/trace/` (or `src/scheduler_trace/` per row 24) | ~740 |
| `io_trace.rs` | `crates/cranelisp-runtime/src/io_trace.rs` | `src/io_trace/` | ~952 |
| `display.rs` | `crates/cranelisp-backend/src/display.rs` | `src/display.rs` | ~831 |
| `observability.rs` (rename only) | `src/observability.rs` | `src/scheduler_trace/` | 1,362 (unchanged) |
| `code.rs` | `src/code.rs` | `crates/cranelisp-backend/src/code.rs` | ~397 |
| `generate_startup_object` (extract from `exe.rs`) | `src/exe.rs` | `crates/cranelisp-exe-bundle/` | ~150 |

After Wave A: int re-exports `pub use cranelisp_backend::Code`; trace/io_trace/got_trace are the three-instance `*_trace/` pattern; the post-D43 destination paths for runtime-side files are set.

### 4.2 Wave B — Cargo + import-rewrite sweep (~1 day)

**Mechanical sweep**; build must pass after this wave or a defect is live.

Cargo.toml swap:
- Remove `cranelisp-runtime` dependency from `src/Cargo.toml` (workspace member).
- Add `cranelisp-primitives` + `cranelisp-intrinsics` dependencies (per Decision 43; the new crates exist post-runtime-retiring slice).

Import rewrites across `src/`:
- `cranelisp_runtime::{add_i64, sub_i64, ...}` → `cranelisp_primitives::{add_i64, sub_i64, ...}` at JIT-name registration sites (per D43 §"Migration scope").
- `cranelisp_runtime::{cranelisp_alloc, rc_inc, rc_dec, ...}` → `cranelisp_intrinsics::{cranelisp_alloc, rc_inc, rc_dec, ...}`.
- `cranelisp_runtime::register_io_observer` → `cranelisp_intrinsics::register_io_observer` (per D40 §"IO observation"; the registration-site host moved to intrinsics post-D43).
- Linker invocation in `src/exe.rs`: replace `cranelisp-runtime.a` archive with `cranelisp-primitives.a` + `cranelisp-intrinsics.a`.

The full migration table is enumerated in `design/arch/decisions/0043-runtime-split-into-primitives-intrinsics.md` §"Migration scope". Int touches ~30+ import-path edits; mechanical; no behaviour change.

### 4.3 Wave C — SharedState extraction + worker mutability pivot (~3–4 days)

The structural centrepiece. The field-by-field migration §3.2 above is the surgical plan. Touches `session_v4.rs` (5,417 LOC) and `worker.rs` (5,041 LOC); does NOT decompose them (FIXME 0109 deferred).

Acceptance:
- `pub struct SharedState` authored; `CompilerSession` holds `Arc<SharedState>`.
- Worker spawn site clones `Arc<SharedState>` per worker; loop body reaches every field via `&shared.*`.
- Grep `&mut CompilerSession` outside the initiator-thread paths returns zero matches reachable from worker code.
- Grep `.entry().or_default()` outside the Phase 0 block in `register_module` (and its mirror in `re_register_module`) returns zero matches.
- Per-symbol mutation via `SymbolTable::insert_or_update(&self, ...)` and `SymbolTable::write_code(&self, sym, code)`; no whole-module `&mut SymbolTable` outside Phase 0 + REPL `append_defn_order`.

The 91 register-call sites in typecheck don't change individually (per Decision 44 amended) — that's α's territory. Wave C reshapes int's session struct only.

## 5. D43 source migration plan — int touch points

The D43 split divides runtime symbols into two destinations:

### 5.1 Primitives (user-callable; symbol-table-entry + GOT slot)

Registration sites in int that name primitives:
- `src/jit_names.rs` (if it exists) — JIT-builder symbol registration for `add-i64`, `sub-i64`, etc.
- `src/session_v4.rs` `CompilerSession::new` — primitives synthetic-module seeding (per FIXME 0159 Resolution: `cranelisp_primitives::PRIMITIVES_TABLE` `LazyLock<SymbolTable>` is the source-of-truth; int's session init does `shared.symbol_tables.insert(ModuleFullPath::primitives(), PRIMITIVES_TABLE.clone())`).

Import-path migrations: all `cranelisp_runtime::{integer_ops, float_ops, bool_ops}` → `cranelisp_primitives::{integer_ops, float_ops, bool_ops}`; per-primitive symbol-name resolution stays unchanged (the JIT name format `name` or `module/name` is the same; only the Rust-side fn lookup target changes).

### 5.2 Intrinsics (backend-emitted-call targets; NOT in symbol table)

JIT registration sites in int that name intrinsics:
- `src/session_v4.rs` `CompilerSession::new` — `JITBuilder::symbol("cranelisp_alloc", cranelisp_intrinsics::cranelisp_alloc as *const u8)` and similar registrations for `rc_inc`, `rc_dec`, `consume_shallow`, `dec_shallow_io`, `vec_*`, `heap_alloc_*`, `string_read`, `sconcat`, `quote_sexp`, `cranelisp_run_io`, `io_run`, `run_io_trampoline`, `ivar_*`, `runtime_panic`.
- IO trampoline registration: `cranelisp_intrinsics::register_io_observer(Some(io_trace::record))` when `shared.introspection.is_some()` OR `CRANELISP_IO_TRACE=1` (per master design §11 + Decision 40).
- `src/exe.rs` static-archive linking for `--link` mode (per Wave B §4.2 above; this is just the `.a` archive name list).

Import-path migrations: all `cranelisp_runtime::*` for intrinsic helpers → `cranelisp_intrinsics::*`.

### 5.3 IoObserver host post-D43

Per Decision 40 §"as amended": the `IoObserver` registration API moved with the D43 split to live in `cranelisp-intrinsics` (not `cranelisp-runtime`). Int's session-init registration site uses `cranelisp_intrinsics::register_io_observer` — confirmed in the facade and the master design §11. No int-side authoring; pure import-path rewrite.

### 5.4 Boundary check

D43 does NOT introduce any new int-side type or function. The split is entirely about *where in the workspace* the runtime symbols live. Int's facade is unchanged by D43 in terms of public surface; only the implementation crate name on the import path changes. Per Decision 43 §"Bounded-context shift": int's BC ("integration layer") still subsumes the responsibility of registering JIT symbols at session init; the *names* of the source crates change from one to two.

## 6. FIXME 0107 — `OwnedPlatformFnDescriptor` `#[non_exhaustive]`

**This FIXME targets `/dev (platform)`, not `/dev (int)`** (re-read of `design/arch/fixmes/0107-*.md`). The platform crate adds the attribute; int's contribution is verifying its pattern-match sites on `OwnedPlatformFnDescriptor` honour the `#[non_exhaustive]` discipline (catch-all arm in match expressions).

**Acceptance**: grep for `match.*OwnedPlatformFnDescriptor` in `src/`; each match must have a `_` arm or destructure with `..` rest. The R9 truth-telling has already landed per substance-scoping; this is a verify-only step.

If a pattern-match site is found without a wildcard arm, file a one-line mechanical edit. Expected: none.

## 7. int facade-compliance delta

Drift between today's `src/` exports and `design/arch/facades/int.md`'s target surface, after Waves A + B + C + D land:

| Facade item | Today | Post-Wave-3a-β | Delta vector |
|---|---|---|---|
| `CompilerSession::process_form` | per-form retry loop, ad-hoc gap detection | renamed/reshaped as `process_cluster` per §1.1 | shape-pivot |
| `CompilerSession::insert_cluster` | bundled into `process_form` post-typecheck | extracted as separate method per §1.1 | new |
| `ProcessedCluster` (opaque carrier) | does not exist | new struct per facade §"Cluster orchestration result" | new |
| `CompilerSession.shared: Arc<SharedState>` | god-struct fields directly on session | extracted per §3 | shape-pivot |
| `pub struct SharedState` | does not exist | new public type per facade §"`SharedState`" | new |
| `Code` (struct) | lives at `src/code.rs` | re-exported `pub use cranelisp_backend::Code` per Decision 41 | migrate-out |
| `cranelisp-primitives` + `cranelisp-intrinsics` Cargo deps | absent; `cranelisp-runtime` present | added; `cranelisp-runtime` removed per D43 | dependency swap |
| `Introspection` (struct) | scattered fields on session/module-sources | unified type at `shared.introspection: Option<DashMap<FQSymbol, Introspection>>` per Decision 38/39 | new (formal type) |
| `cranelisp-frontend::expand` consumed | int hosts `src/expander.rs::expand_sexp_recursive` (MacroResolver glue) | int imports `cranelisp_frontend::expand`; `MacroResolver` deletes per Decision 8 retract | import-rewrite + delete |
| `cranelisp-typecheck::check_form_*` consumed | `TypeCheckEnv::check_form` method form | int calls free-function pair `check_form_signatures` + `check_form_body` per Decision 44 | import-rewrite + signature-change |
| `cranelisp-backend::compile_to_module` consumed | tuple-returning + int-side unpack at `worker.rs:~2860–3018` | `Result<(), CompilationError>`; backend writes Code via `&self`-interior-mutable methods directly | signature-change + delete-int-side-unpack |
| `Sess::format_error::Platform(PlatformError)` arm | stringly-typed `ModuleError(String)` | structured `Platform(PlatformError)` per Decision 42 | new (downstream wave) |
| `module_sources: DashMap<...>` field | exists on session | deleted; per-defn source on `Introspection.source` per Decision 39 | delete (downstream wave) |
| `kept_linkers` field | exists on session (Sprint-58 pre-Wave-3 carryover) | deleted; per-symbol retention via `Code::Linker.linker: Arc<Linker>` | delete (verify-first) |

The wave breakdown maps these as:
- **Wave 3a β (this doc)**: rows 1, 2, 3, 4, 5, 9, 10 — the cluster-atomic + SharedState foundation + D43 + Code re-export.
- **Wave 3b (downstream)**: rows 11, 12, 13 — D41 per-symbol JIT + D42 PlatformError + D39 source-store collapse + observability wiring. These ride on top of β.

## 8. Open questions / coordination

1. **Cluster-internal Pass-1-mutation visibility to Pass-2 consumers in same form.** When form N introduces type `T` in Pass 1 and form N's own Pass 2 body references `T`, Pass 2 reads `ctx.current_symbol_table()` (`View::union(staging, live)`) and sees `T` from staging. This is correct per Decision 44 §"Pass 1 / Pass 2" but worth verifying once typecheck-α's `current_symbol_table` accessor lands — the View's staging-first lookup must return `T`'s staging shell when live doesn't have it. **No FIXME needed**; verify-during-implementation.

2. **`pending_forms()` accessor on SymbolTable.** Worker §1.5 above reads `shared.symbol_tables.get(&module).expect("Phase 0 ran").pending_forms()` to fetch the cluster forms. The current SymbolTable surface has `defn_order` (per-symbol) but the worker needs the raw `Vec<Sexp>` captured by Phase 0. **Verify** whether `SymbolTable::pending_forms()` exists or whether Phase 0 needs to add a field. If a new field is needed, file FIXME `target: /arch` requesting the addition to `cranelisp-types::SymbolTable` (it's a per-cluster-input cache).

3. **Coordination with parallel /design-frontend.** `build_form -> Result<Vec<ParsedEntry>, CranelispError>` is the upstream signature. This doc's §1.3 step-1 calls `frontend::build_form(&expanded)` expecting `Vec<ParsedEntry>`. If frontend's /design agent lands a different return type (e.g., `Result<Vec<ParsedEntry>, FrontendError>`), the wrapping in this doc adjusts. No substantive change to the orchestration.

4. **Coordination with parallel /design-typecheck.** `check_form_signatures` and `check_form_body` signatures per Decision 44 amendment — `(parsed: ParsedEntry, ctx: &mut ClusterContext<'_, C, L>, symbol_tables: &SymbolTables<C, L>) -> Result<(), CheckError>`. The `symbol_tables` parameter is named separately from `ctx.modules` because typecheck may need read access outside of the staging view for some operations (e.g., resolving FQ references across modules during inference). If parallel /design-typecheck collapses the two parameters into one (folding `symbol_tables` into `ClusterContext::Live { modules }` for the non-cluster mode), this doc's pseudocode adjusts to pass only `&mut ctx`. No substantive change.

5. **No /arch FIXME filed in this doc.** Per the workflow, this design pass surfaces no cross-crate gaps beyond those parallel /design agents are already handling. Open questions 2–4 above are coordination notes, not architectural blockers.

## 9. Test acceptance (failing-gate tests this design must close)

Per the task brief:
- `tests/process_form_dispatch.rs::*` ×3 — cluster-atomic acceptance. Int is the orchestrator; these tests assert that a failing form mid-cluster leaves live byte-identical to pre-cluster, that `(begin ...)` REPL input produces atomic commit, and that cross-input forward refs in non-`begin` REPL inputs produce a clear error.
- `tests/got_trace_*` ×3 — receive-side. Int's dispatch must not emit duplicate JIT events for the same symbol (per Decision 41 §"per-symbol JIT cardinality"). The per-cluster `compile_to_module` per-symbol call-site loop (slice row 8 + Wave E in the slice) is what closes this — but Wave 3a's structural foundation (Wave C SharedState + Wave D process_cluster) is the prerequisite that makes that wiring tractable.

Unit-test acceptance (the slice §5 enumerates):
- `process_cluster` returns Gap-typed errors and dispatches via `handle_gap` (rows 3, 4).
- `handle_gap` macro-vs-fn discrimination (row 4).
- `ensure_registered` runs Phase 0 synchronously (row 5).
- SharedState extraction — workers don't see `&mut` (rows 1, 2).
- Per-symbol mutability discipline outside Phase 0 (rows 6, 7).
- Cluster-atomic commit — failure mid-cluster leaves live unchanged (new test for this doc; not in slice §5).

The final test in this list — "failure mid-cluster leaves live unchanged" — is the canonical acceptance for Decision 44 from int's side and should be authored as a `src/` unit test against a stub `SharedState` with a forced Pass-2 error. The corresponding e2e test lives in `tests/process_form_dispatch.rs` per /qa's domain.

## 10. Cross-references

- `design/arch/facades/int.md` §"`process_cluster` — the cluster-atomic orchestration loop" — the contract (lines 667–800)
- `design/arch/facades/int.md` §"`SharedState`" — the data model split (lines 110–190)
- `design/int/int.md` §4 (SharedState architecture), §6 (pipeline orchestration), §8 (REPL flow) — master design context
- `design/int/implementation-slice-s66.md` Waves A, B, C — the row-level enumeration that this doc elaborates
- `design/arch/decisions/0044-cluster-atomic-typecheck-orchestrator-staging.md` (post-FIXME-0167 + 0168 amendments) — cluster-atomic protocol
- `design/arch/decisions/0046-wave3a-locality-refactor-precedes-triad.md` — α/β sequencing rationale
- `design/arch/decisions/0043-runtime-split-into-primitives-intrinsics.md` §"Migration scope" — D43 import-path migration table
- `design/arch/decisions/0040-runtime-trace-io-trace-relocate-to-int.md` — IoObserver registration host post-D43
- `design/arch/fixmes/0098-*.md` Phase 4 — int callsite typed-pattern-match wiring
- `design/arch/fixmes/0107-*.md` — verify-only on int side (targets `/dev (platform)` for the platform crate's attribute add)
- Parallel /design agents (in-flight): frontend `build_form` shape; typecheck `check_form_signatures` + `check_form_body` shape — this doc consumes both contracts.

## 11. Principle citations

- **P1 Decoupling, P7 Single source of truth** — staging is a transient orchestrator-local frame; the live `SymbolTable` is the single durable source of truth; cluster atomicity preserves this.
- **P2 Narrow interfaces** — `process_cluster` and `insert_cluster` are two narrow surfaces, not one wide one with a mode flag.
- **P3 Dependency flows toward stability** — frontend and typecheck stay pure with respect to live state; int is the sole orchestrator that crosses from value to scheduler call.
- **P11 Single pipeline mode parameters** — the same `process_cluster` serves REPL eval (one-form cluster), REPL `(begin)` (multi-form cluster), and batch (one-big-cluster); cluster shape is the mode parameter, not a `--repl-vs-batch` dispatch.
- **P17 (S66 Wave 3a-α addition) Locality** — short-name resolution is current-module-only; this doc's §3 SharedState extraction doesn't reintroduce cross-module lookups; the cluster's `current_module` field is the locality anchor.
