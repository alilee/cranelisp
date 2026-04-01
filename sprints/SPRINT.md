# Sprint 47: Pipeline v4 Steps 11+12 — Multi-Threaded Priority Workers + Concurrent TypeChecker

**Status**: ACTIVE
**Ring**: — (structural / pipeline v4 migration)
**Goal**: Multiple priority worker threads typecheck and codegen modules in parallel, with DashMap-backed TypeChecker enabling concurrent module table access.

## Context

Sprint 46 delivered Step 10: nice worker threads for background `.o` compilation. The scheduler has `Mutex<SchedulerState>` + condvars, and nice workers run in scoped threads via `Arc<SharedState>`. The priority worker loop still runs inline on the calling thread.

Steps 11 and 12 are combined into one sprint because they are tightly coupled:
- **Step 11** spawns multiple priority worker threads running `priority_worker_loop`.
- **Step 12** replaces `Mutex<TypeChecker>` with DashMap-backed concurrent module tables.

Without Step 12, multiple priority workers would serialize on `Mutex<TypeChecker>` — no parallelism gain. Without Step 11, DashMap adds complexity with no benefit. They must ship together.

**The key challenge**: `WorkerContext` currently holds `&mut TypeChecker` and `&mut InMemWorkerState`. Multiple workers need either:
1. `TypeChecker` behind DashMap with `&self` API (Step 12), and
2. Per-worker JIT instances instead of shared `InMemWorkerState` (per `pipeline-v4.md` §5.2).

**All skills MUST read:**
- `design/arch/pipeline-v4-roadmap.md` — Steps 11 and 12 specifications
- `design/arch/concurrent-pipeline.md` §5.1 (Priority Workers), §5.2 (Typecheck Form Processing), §7 (Lock Granularity)
- `design/arch/pipeline-v4.md` §5 (CompilerSession — no worker state on session)
- `src/worker.rs` — WorkerContext struct (the `&mut` problem)
- `src/scheduler.rs` — `take_priority_work` needs condvar parking
- `src/session_v4.rs` — `spawn_priority_workers` is currently a no-op
- `crates/cranelisp-typecheck/` — TypeChecker internal structure (HashMap-based module tables)

## Scope

### Step 11: Multi-Threaded Priority Workers

1. `spawn_priority_workers(n)` spawns N threads running `priority_worker_loop`.
2. `take_priority_work` parks on `priority_work_available` condvar when no work. Woken by module registration, unblocking, typecheck completion.
3. Workers own thread-local JIT instances — no shared `InMemWorkerState`.
4. GOT writes use atomic stores to pre-assigned slots.
5. The calling thread no longer runs the worker loop inline — it just waits.

### Step 12: Concurrent TypeChecker Maps (DashMap)

1. Replace TypeChecker's internal `HashMap<ModuleFullPath, CompiledModule>` with `DashMap`.
2. Per-shard locking: one worker writing its module doesn't block another reading a different module.
3. `tc.check_form()` takes `&self`. Internal mutation via DashMap per-shard locks.
4. Add `dashmap` dependency to `cranelisp-typecheck`.
5. WorkerContext changes from `&mut TypeChecker` to `&TypeChecker`.

### Combined changes

- `WorkerContext` becomes `Send`-safe: `&TypeChecker` (not `&mut`), per-worker JIT, `&CompileScheduler`.
- `InMemWorkerState` (GOT, JIT) becomes per-worker thread-local state.
- GOT must be thread-safe: pre-assigned slots with atomic stores, or a concurrent map.
- `CompilerSession` moves TypeChecker to `SharedState` (behind `Arc`), enabling worker access.

### Not in scope

- Step 13 (cache-hit loading via register_module_cached)
- Step 14 (file watcher integration)
- Step 15 (legacy code deletion)
- New language features

## FIXME Debt

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `spec/09-macros.md:147` | /spec | §9.2.5 macro bodies may call imported functions | 2nd carry from S45. Spec-only, filed for /spec. Must resolve this sprint or escalate. |

## Architecture Review

**Verdict: PASS WITH RECOMMENDATIONS**

The sprint combines two tightly coupled steps (11+12) into a coherent increment. Combining them is the right call — Step 11 without Step 12 serialises on `Mutex<TypeChecker>`, and Step 12 without Step 11 adds complexity with no benefit. The scope is well-defined, testable, and the code will survive into Steps 13-15.

### Answers to Key Questions

**1. DashMap scope: Which TypeChecker maps need DashMap?**

Only `modules: HashMap<ModuleFullPath, SymbolTable>` needs DashMap. Rationale:

- **`modules`**: Multiple workers concurrently read (import resolution, macro lookup) and write (one writer per module). This is the core contention point. DashMap's per-shard locking gives fine-grained concurrent access. Replace with `DashMap<ModuleFullPath, SymbolTable>`.
- **`next_id`**: Already `AtomicU32` — no change needed. Lock-free allocation is correct.
- **`type_defs`, `trait_registry`, `impl_registry`**: Already behind `RwLock` (Sprint 40 Phase 3). These registries are written during Pass 1 (register) and read during Pass 2 (check body). Since the scheduler guarantees no two workers typecheck the same module, and cross-module reads use `RwLock::read()`, the existing `RwLock` wrapping is sufficient. DashMap is overkill here — the access pattern is "rare writes, many reads" which `RwLock` handles well.
- **`module_locks`**: Already `HashMap<ModuleFullPath, Arc<AtomicBool>>`. This map is mutated only during module registration (which happens on one thread at a time via the scheduler mutex). The `AtomicBool` values are accessed concurrently but are already atomic. No change needed. If `/typecheck` encounters contention during registration, it could be wrapped in a small `Mutex`, but this is unlikely given the scheduler serialises module registration.
- **`state: CheckState`**: This is the per-check transient state. For multi-threaded workers, each worker MUST have its own `CheckState` on the stack (not shared). The `check_form()` call must take `CheckState` as a parameter or create it internally, NOT use `self.state`. This is the key API change: `check_form()` changes from `&mut self` to `&self` by taking an explicit `&mut CheckState` parameter (or the `ModuleCheckAccumulator` already serves this purpose — the accumulator carries per-module transient state and is already per-worker in `ModuleSuspendState`).
- **`overloads`, `resolved_overloads`**: These are on `CheckState`, not `TypeChecker`. They are per-check transient state. No concurrency concern — each worker has its own accumulator.

**Recommendation for /typecheck**: The migration path is:
1. Change `self.modules` from `HashMap` to `DashMap`.
2. All methods that access `self.modules` must change from `.get()/.get_mut()` to DashMap's `.get()/.get_mut()` (returns `Ref`/`RefMut` guard types — beware of holding multiple guards simultaneously, which can deadlock on same-shard keys).
3. `check_form()` signature becomes `fn check_form(&self, module: &ModuleFullPath, form: &TopLevel, pass: CheckPass, acc: &mut ModuleCheckAccumulator) -> Result<FormCheckResult, CranelispError>`. The accumulator already exists and is per-worker.
4. Methods that currently access `self.state` for transient inference state must instead receive it via the accumulator or a new `&mut CheckState` parameter.

**Critical DashMap hazard**: `current_symbol_table()` and `current_symbol_table_mut()` return `&SymbolTable` / `&mut SymbolTable` by borrowing directly from the `HashMap`. With `DashMap`, these return guard types (`Ref<K,V>` / `RefMut<K,V>`) that hold a shard lock. Any method that calls `current_symbol_table()` and then tries to access a different module's table will deadlock if both keys hash to the same shard. `/typecheck` must audit all call sites for this pattern and restructure to drop guards before acquiring new ones.

**2. GOT concurrency model: Pre-assigned slots with atomic stores.**

The current `GotTable` already uses `AtomicPtr<u8>` slots with `Release`/`Acquire` ordering — it is already correct for concurrent writes to disjoint slots. The concurrency model is:

- **Slot assignment** (the `next_got_slot` counter and `def_codegen` map on `ModuleCodegenState`): This must be centralised and thread-safe. Currently `ModuleCodegenState.allocate_slot()` uses a plain counter and `HashMap` — neither is thread-safe.
- **Slot writes** (`GotTable.store_slot`): Already atomic. Correct.

**Recommendation**: Split `ModuleCodegenState` into:
- **Shared GOT coordinator** (`Arc<GotCoordinator>`): owns the `GotTable`, the `AtomicUsize` slot counter, and a `DashMap<Symbol, DefCodegen>` for the `def_codegen` map. `ensure_slot_for()` uses `def_codegen.entry().or_insert_with(|| allocate_slot())` with atomic slot allocation.
- **Per-worker JIT state**: owns `jit_modules`, `cache_linkers`, trace state. Not shared.

The `GotCoordinator` replaces the current `ModuleCodegenState` as the shared session field. Workers get `&GotCoordinator` (read-write via atomics and DashMap) plus their own per-worker JIT state.

Alternatively, slot assignment could be pre-assigned during typecheck: when a symbol is typechecked, assign its GOT slot. This keeps slot assignment single-writer (the typechecking worker for that module) and avoids contention on the slot counter. Workers doing codegen look up the pre-assigned slot by symbol name. This is cleaner but requires a typecheck-to-codegen handoff of slot assignments. Given the current code already calls `ensure_slot_for` during `pre_register_got_slots` (which runs per-module before codegen), pre-assigning during that phase is natural — just make the counter atomic.

**Chosen model**: `Arc<GotTable>` (already exists) + `AtomicUsize` for `next_got_slot` + `DashMap<Symbol, DefCodegen>` for `def_codegen`. This is the minimum change that makes the GOT concurrent-safe.

**3. Per-worker JIT: How do function pointers remain valid after JIT drop?**

Cranelift's `JITModule::finish()` leaks the code memory intentionally — the memory is never freed. After `finish()`, the JIT module can be dropped without invalidating code pointers. This is Cranelift's documented behaviour (see `cranelift_jit::JITModule::finish` docs).

However, the current code stores JIT instances in `InMemWorkerState.jit_modules: Vec<Jit>` to keep them alive. This suggests the codebase may NOT be calling `finish()` — it may be relying on the JIT instance staying alive to keep code memory valid.

**Recommendation for /int and /backend**: Audit `cranelisp_backend::jit::Jit` to determine whether `finish()` is called. If it is, JIT instances can be dropped after codegen — no need to keep them alive, and per-worker JIT instances are safe to create and drop. If `finish()` is NOT called, either:
- (a) Start calling `finish()` on the JIT after extracting code pointers. This is the clean solution. Code memory is leaked (by design), pointers remain valid, JIT is dropped.
- (b) Keep per-worker JIT instances alive by collecting them into a session-level `Mutex<Vec<Jit>>` at the end of each codegen operation. Workers push their finished JITs to the shared vec before moving on.

Option (a) is strongly preferred — it makes the lifetime model explicit and removes the need to keep JIT instances alive.

For **Linker instances** (`cache_linkers`), the same analysis applies: they own executable memory mapped by the loader. These MUST be kept alive (Linker code regions are mmapped, not leaked). Collect them into a session-level `Mutex<Vec<Linker>>`.

**4. MacroEnv thread safety**

The `MacroEnv` struct in `src/expander.rs` already wraps its `HashMap<Symbol, MacroEntry>` in an `RwLock`. Multiple concurrent readers (macro expansion) are safe. Write access (registering new macros via `compile_macro`) acquires a write lock.

However, macro expansion calls function pointers (`invoke_clause`). The function pointers themselves are raw `*const u8` — they point to JIT-compiled code in memory. Calling a function pointer from multiple threads concurrently is safe as long as:
- The code is read-only (it is — JIT code pages are marked executable, not writable).
- The function itself has no shared mutable state (macro functions are pure — they take an SList and return an Sexp, no side effects).

**Assessment**: `MacroEnv` is safe for concurrent reads. The existing `RwLock` is sufficient. No changes needed.

**Note**: In the current v4 pipeline, macros are stored as `ModuleEntry::Macro` in the TypeChecker's module tables, NOT in the standalone `MacroEnv`. The `MacroEnv` is part of the old `CompilationSession`. The v4 path looks up macros via `tc.symbol_table(module).get(name)` and calls function pointers stored on the `MacroClauseEntry`. Once `modules` is behind DashMap, macro lookup acquires a DashMap read guard, extracts the function pointer, drops the guard, then calls the pointer. This is safe — the function pointer is a plain value copied out of the guard, not a reference into the map.

**5. `InMemWorkerState` decomposition**

Current `InMemWorkerState` fields and their disposition:

| Field | Disposition | Rationale |
|-------|-------------|-----------|
| `got_state: ModuleCodegenState` | **Shared** — becomes `Arc<GotCoordinator>` | All workers write to the same GOT and need slot assignment. See Q2. |
| `jit_modules: Vec<Jit>` | **Per-worker**, then drained to shared | Each worker creates JIT instances. If `finish()` is called, these can be dropped. Otherwise drain to shared `Mutex<Vec<Jit>>`. |
| `traced_fns: Vec<TracedFnInfo>` | **Per-worker** (REPL-only) | Trace is a REPL feature. Only the eval path uses it. Not relevant for parallel batch workers. |
| `trace_extra_symbols: Vec<(String, *const u8)>` | **Per-worker** (REPL-only) | Same as `traced_fns`. |
| `cache_linkers: Vec<Linker>` | **Per-worker**, then drained to shared | Workers that load cached `.o` via Linker must keep the Linker alive. Drain to session-level `Mutex<Vec<Linker>>`. |

**Concrete decomposition**:
```rust
// Shared (on CompilerSession, behind Arc):
struct SharedCodegenState {
    got_table: Arc<GotTable>,
    next_got_slot: AtomicUsize,
    def_codegen: DashMap<Symbol, DefCodegen>,
    kept_jits: Mutex<Vec<Jit>>,         // if finish() not used
    kept_linkers: Mutex<Vec<Linker>>,
}

// Per-worker (stack-local in worker thread):
struct WorkerJitState {
    jit_modules: Vec<Jit>,              // drained to shared on completion
    cache_linkers: Vec<Linker>,         // drained to shared on completion
    traced_fns: Vec<TracedFnInfo>,      // REPL-only, empty for batch workers
    trace_extra_symbols: Vec<(String, *const u8)>,
}
```

Workers build a `WorkerJitState` at thread start, use it for codegen, and drain `jit_modules` + `cache_linkers` to the shared state before exiting (or at module completion).

### Technical Coherence Assessment

The sprint forms a complete, testable increment:
- **Step 11** is testable by verifying that `spawn_priority_workers(n)` spawns real threads and multi-module programs compile with parallelism.
- **Step 12** is testable by verifying `cargo test` passes and thread sanitizer is clean (`RUSTFLAGS="-Z sanitizer=thread"`).
- The combined change is testable by compiling multi-module programs and confirming parallel typecheck + codegen. Correctness is verified by existing test suite (same results, no data races).

The scope is well-bounded: no new language features, no new pipeline stages, just concurrency enablement on the existing single-threaded path. This is the right granularity.

**One gap**: The sprint proposal says "the calling thread no longer runs the worker loop inline — it just waits." This means `register_module` must change its flow: instead of calling `priority_worker_loop` inline, it registers the module with the scheduler and blocks on `wait_inmem_complete`. The worker threads (spawned by `spawn_priority_workers`) do the actual work. This is a significant change to `session_v4.rs::register_module()` that should be called out explicitly in the /int plan.

### Principle 8 Assessment (No Interim Architecture)

**PASS.** All code introduced in this sprint survives into Steps 13-15:
- `DashMap`-backed `TypeChecker.modules` is the permanent concurrent data structure.
- `Arc<GotTable>` with atomic slot assignment is the permanent GOT model.
- Per-worker JIT instances are the permanent worker state model.
- `spawn_priority_workers(n)` is the permanent thread spawning mechanism.
- The scheduler condvar parking for `take_priority_work` is the permanent work selection mechanism.

No throwaway infrastructure is introduced. The current single-threaded inline worker loop (`priority_worker_loop` called by `register_module`) is being replaced, not extended — this is replacement, not interim scaffolding.

### Thread Safety Analysis

**Safe patterns**:
- `CompileScheduler` uses `Mutex<SchedulerState>` + condvars. Workers hold the mutex briefly for O(1) operations. All compilation happens outside the lock. Correct.
- `GotTable` uses `AtomicPtr` with `Release`/`Acquire` ordering. Disjoint slot writes are safe. Correct.
- `TypeChecker.next_id` is `AtomicU32`. Lock-free allocation. Correct.
- `TypeChecker.type_defs/trait_registry/impl_registry` are behind `RwLock`. Correct for the "rare writes, many reads" pattern.

**Hazards requiring attention**:
1. **DashMap guard lifetime**: Methods that hold a DashMap `Ref` guard while trying to access another entry risk deadlock if both keys hash to the same shard. `/typecheck` must audit all cross-module lookup paths.
2. **`CheckState` on `TypeChecker`**: The `self.state` field is NOT safe for concurrent access. Workers must use stack-local `CheckState` (via `ModuleCheckAccumulator`). The `state` field should be gated behind a `cfg(test)` or REPL-only accessor, not used by worker code paths.
3. **GOT slot allocation**: `ModuleCodegenState.next_got_slot` is currently a plain `usize`. Must become `AtomicUsize` or equivalent. The `def_codegen` `HashMap` must become concurrent (`DashMap`).
4. **`WorkerContext` borrows**: Currently `WorkerContext` holds `&mut TypeChecker` and `&mut InMemWorkerState`. Multi-threaded workers cannot hold `&mut` to shared state. `WorkerContext` must change to `&TypeChecker` + `&SharedCodegenState` + per-worker `WorkerJitState`. This is a significant refactor of `WorkerContext` and all its callers.

### Interface Gaps

1. **`WorkerContext` struct** (`src/worker.rs`): Needs redesign. Current:
   ```rust
   pub struct WorkerContext<'a> {
       pub tc: &'a mut TypeChecker,
       pub inmem_worker: &'a mut InMemWorkerState,
       ...
   }
   ```
   Target:
   ```rust
   pub struct WorkerContext<'a> {
       pub tc: &'a TypeChecker,            // shared, &self
       pub shared_codegen: &'a SharedCodegenState,  // shared, concurrent
       pub worker_jit: WorkerJitState,      // owned, per-worker
       ...
   }
   ```

2. **`compile_and_register_defn`** (`src/pipeline.rs`): Currently takes `&mut InMemWorkerState`. Must be refactored to take `&SharedCodegenState` + `&mut WorkerJitState`. This function is the primary codegen entry point and touches GOT slot assignment, JIT compilation, and code pointer registration.

3. **`codegen_module_symbols`** (`src/worker.rs`): Same refactor as above — takes `&mut InMemWorkerState` today, needs split references.

4. **`TypeChecker::check_form`**: Currently takes `&mut self`. Must become `&self` with explicit `CheckState`/accumulator threading. The `ModuleCheckAccumulator` already carries most per-check state but may need to absorb remaining `CheckState` fields (subst, env, scope stack).

### Design References

- **For /int**: `design/arch/pipeline-v4.md` §5 (CompilerSession — no worker state on session), `design/arch/concurrent-pipeline.md` §5.1 (priority workers), §7 (lock granularity). Key: the decomposition of `InMemWorkerState` and the `WorkerContext` refactor are the primary /int deliverables.
- **For /typecheck**: `design/arch/concurrent-pipeline.md` §7.3 (session concurrent maps). Key: DashMap migration of `modules`, `check_form` signature change to `&self`, audit of guard lifetimes across cross-module lookups.
- **For /backend**: `crates/cranelisp-backend/src/got.rs` — the `ModuleCodegenState` decomposition. Verify `Jit::finish()` behaviour. Ensure `compile_function` and friends can work with `&SharedCodegenState`.

### FIXME Debt

The `spec/09-macros.md:147` FIXME is on its 2nd carry. Per the sprint proposal, it must ship this sprint or be escalated. This is a spec-only item with no implementation coupling to Steps 11+12, so there is no technical reason to defer it further.

### Recommendations Summary

1. **Audit `Jit::finish()` before implementing** — determines whether JIT instances need to be kept alive.
2. **DashMap guard audit** — `/typecheck` must map all code paths that hold a DashMap guard and access another entry.
3. **`WorkerContext` refactor** — the `&mut` to `&` transition is the largest mechanical change. Plan it as the first wave.
4. **Pre-assign GOT slots during typecheck** — avoids contention on the slot counter during parallel codegen. The `pre_register_got_slots` function already runs per-module; making the counter atomic is sufficient.
5. **Thread sanitizer CI** — add `RUSTFLAGS="-Z sanitizer=thread" cargo test` to the acceptance criteria. This is the primary safety net for concurrency bugs.

### Phase 3 Design Doc Review

Review of `design/typecheck/dashmap-migration.md` and `design/int/concurrent-workers.md`.

**Overall: PASS for both docs.** Both are thorough, well-reasoned, and aligned with the architecture review. No blockers. Several points requiring attention before implementation.

#### `design/typecheck/dashmap-migration.md` — PASS

The doc is comprehensive. The guard lifetime audit (section 4) addresses the primary DashMap hazard identified in the arch review. The clone-and-drop discipline is the right invariant. The migration steps (A-F) are well-ordered and each produces a compilable, passing state.

Findings:

1. **`check_form` signature: aligned with arch review.** The doc proposes `check_form(&self, module, form, pass, state, accumulator)` with explicit `&mut CheckState`. The arch review suggested either explicit `CheckState` or absorbing it into `ModuleCheckAccumulator`. The doc chose explicit `CheckState` as a separate parameter, which is cleaner — `CheckState` carries inference transient state (subst, env, scope stack) while `ModuleCheckAccumulator` carries cross-form results. Good separation of concerns.

2. **`module_locks` wrapping.** The doc chooses `Mutex<HashMap>` (option 1). The arch review noted this map is "mutated only during module registration (serialised by the scheduler)" and suggested no change unless contention is found. The `Mutex` is a safe conservative choice and acceptable.

3. **`self.state` retention for REPL.** The doc retains `self.state` for REPL `snapshot()`/`restore()` and proposes a `check_with_state()` overload. This is acceptable for the current sprint but accumulates surface area. Note for future cleanup: the REPL should own its persistent `CheckState` in `ReplSession`, not on `TypeChecker`.

4. **Missing: interaction with `RwLock` fields under concurrent load.** Section 7.3 says "the audit found no methods that hold both an RwLock write guard and a DashMap guard simultaneously" but this claim needs verification during implementation. `register_trait_impl()` writes to `impl_registry` (RwLock) and may read `modules` (DashMap) for visibility checks. If this pattern exists, apply the same clone-and-drop.

5. **No `FIXME(/typecheck)` needed** — the doc is owned by `/typecheck` and self-consistent.

#### `design/int/concurrent-workers.md` — PASS

The doc is thorough and the `SharedCodegenState` / `WorkerJitState` split matches the arch review's recommended decomposition exactly. The migration waves are well-structured.

Findings:

1. **JIT lifecycle: drain-to-shared is sound.** The doc correctly identifies that `finish()` is NOT called, audits the consequence (JIT instances must be kept alive), and chooses the conservative drain-to-shared approach. The `FIXME(/backend)` is the right action — `/backend` can add `finish()` later to simplify lifetimes. No architectural concern with the current approach.

2. **Single scope for both worker pools (Option B).** Good decision. Avoids nested lifetime complexity. The `run_with_workers` API is clean.

3. **`Mutex<TypeChecker>` interim in Wave 3 step 4.** The doc notes that if Step 12 is not ready, `Mutex<TypeChecker>` is used as a fallback. Since the sprint combines Steps 11+12, this interim should be brief. However, there is a risk: if `/typecheck` Step B (threading `CheckState` through ~40 methods) takes longer than expected, `/int` could be blocked. The migration ordering recommendation below addresses this.

4. **`WorkerContext` is not `Send`.** The doc correctly notes this and uses `std::thread::scope` so each worker constructs its own `WorkerContext`. This is the right pattern.

5. **Trace state omitted from `WorkerJitState`.** Correct — batch workers do not need trace state. The REPL eval path runs inline and handles its own trace context.

6. **DashMap iteration snapshot concern (section 6, "GOT Reads During Codegen").** The doc acknowledges that iterating `def_codegen` during concurrent insertions may see a partial view, and correctly argues this is acceptable because `ensure_slot_for` handles missing entries on demand. Sound reasoning.

#### Cross-Skill Consistency

The two docs agree on:
- `check_form` changes from `&mut self` to `&self` -- aligned.
- `WorkerContext.tc` changes from `&mut TypeChecker` to `&TypeChecker` -- aligned.
- `CheckState` is stack-local per worker, threaded explicitly -- aligned.
- `ModuleCheckAccumulator` remains per-worker, per-module -- aligned.

One minor inconsistency:
- **/typecheck doc** §5.2 says workers call `tc.check_form(&self, module, form, pass, &mut state, &mut acc)` -- the `&self` in the argument list is clearly a typo (should be just `tc.check_form(module, form, pass, &mut state, &mut acc)` since `tc` is `&TypeChecker`). Cosmetic, not a design conflict.
- **/int doc** §10 Wave 3 step 4 mentions `&Mutex<TypeChecker>` as an interim. The `/typecheck` doc does not mention this interim because its migration (Steps A-F) assumes the two land together. No conflict — the interim is `/int`'s fallback plan, not `/typecheck`'s responsibility.

#### Hazards

1. **Guard + RwLock interaction (repeated from above).** The `/typecheck` doc's section 7.3 assertion that no method holds both an `RwLock` write guard and a DashMap guard needs active verification during implementation. The risk is real but manageable with the clone-and-drop discipline.

2. **`set_current_module` under DashMap.** Section 4.7 shows `set_current_module` reading from `primitives` and `user` modules to seed a new module. After DashMap, this becomes `&self` (interior mutation). But it is also listed in section 3.4 as remaining `&mut self`. The doc resolves this in Step E (change to `&self`), but the path through Steps C-D where it remains `&mut self` while other methods are `&self` needs care — callers of `set_current_module` must still hold `&mut TypeChecker` during those intermediate steps.

3. **No deadlock from condvar + DashMap interaction.** The `/int` doc's condvar parking (section 8) uses the scheduler's `Mutex<SchedulerState>`, which is completely separate from the TypeChecker's DashMap shards. Workers release the scheduler mutex before calling any TypeChecker method. No cross-lock deadlock possible. Sound.

4. **Memory ordering on GOT slot assignment.** The `/int` doc uses `AcqRel` on `fetch_add` for `next_got_slot` and `Release/Acquire` on `AtomicPtr` stores/loads for GOT slots. This is correct — `AcqRel` on the counter ensures the slot number is visible before the DashMap entry is written, and `Release` on the GOT slot store ensures the code pointer is visible before the condvar notification unblocks waiters.

#### Recommended Migration Ordering

The two docs propose compatible but independent migration sequences. The recommended combined ordering:

1. **/typecheck Step B first**: Thread `CheckState` through all internal methods. This is the largest mechanical change (~40 method signatures) but is purely internal — no API change visible to `/int`. All methods remain `&mut self`. Tests pass.

2. **/int Wave 1 second**: Extract `SharedCodegenState` and `WorkerJitState`. Refactor `compile_and_register_defn` and callers. Still single-threaded. Tests pass.

3. **/typecheck Steps C+D**: Change worker-called methods to `&self`, switch `modules` to `DashMap`. Tests pass.

4. **/typecheck Step E + /int Wave 2**: Change `check()` to `&self`. Add condvar parking to `take_priority_work`. Tests pass.

5. **/int Wave 3**: Spawn worker threads, wire `&TypeChecker`, move sexps and suspend states to shared maps. Thread sanitizer validation.

6. **/int Wave 4 + /typecheck Step F**: Cleanup (`InMemWorkerState` deletion, `WorkerContext` finalized).

This ordering ensures `/typecheck` finishes the internal `CheckState` threading before `/int` needs the `&self` API, and `/int`'s data structure extraction can proceed in parallel with `/typecheck`'s internal refactor (steps 1 and 2 are independent).

## Skill Plans

### /arch
**Task**: Review sprint proposal, confirm DashMap scope, GOT concurrency model, per-worker JIT lifecycle.
**Design doc**: `design/arch/concurrent-pipeline.md` (existing)
**Acceptance**: Architecture review filled, concurrency model confirmed.

### /int
**Task**: Implement multi-threaded priority workers, wire DashMap TypeChecker, per-worker JIT, concurrent GOT.
**Design doc**: `design/int/concurrent-workers.md` — PASS (Phase 3 review)
**Acceptance**: `spawn_priority_workers(n)` spawns real threads. Multi-module programs compile with parallelism. All tests pass.

### /typecheck
**Task**: Migrate TypeChecker internal maps to DashMap. Change `check_form` from `&mut self` to `&self`.
**Design doc**: `design/typecheck/dashmap-migration.md` — PASS (Phase 3 review)
**Acceptance**: `cargo test` passes. TypeChecker API takes `&self` for all worker-called methods.

### /qa
**Task**: Write concurrency tests — parallel compilation correctness, data race detection.
**Acceptance**: Tests verify multi-module parallel compilation produces correct results.

### /review
**Task**: Review implementation for thread safety, data races, correct DashMap usage.
**Acceptance**: 0 blockers, all important findings resolved.

### /frontend
**Task**: No implementation work this sprint.
**Acceptance**: N/A

### /backend
**Task**: Verify codegen functions are safe with per-worker JIT instances. Assess GOT atomic write safety.
**Acceptance**: Codegen callable from multiple worker threads.

### /platform
**Task**: No implementation work this sprint.
**Acceptance**: N/A

### /spec
**Task**: Resolve FIXME on §9.2.5 (2nd carry — must ship this sprint).
**Acceptance**: FIXME removed, spec updated.

### /stdlib
**Task**: No implementation work this sprint.
**Acceptance**: N/A

### /examples
**Task**: No implementation work this sprint.
**Acceptance**: N/A

### /docs
**Task**: No implementation work this sprint.
**Acceptance**: N/A

### /repl
**Task**: No implementation work this sprint. Verify REPL works with multi-threaded compilation.
**Acceptance**: Demo files play cleanly.

### /port
**Task**: No implementation work this sprint.
**Acceptance**: N/A

## Waves

Per the Phase 3 design doc review recommended ordering:

### Wave 1: Internal refactors (parallel, no API changes)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /typecheck | Step B: Thread `CheckState` through ~40 internal methods | done | |
| /int | Wave 1: Extract `SharedCodegenState` + `WorkerJitState` from `InMemWorkerState`. Refactor `compile_and_register_defn`. | done | Still single-threaded. |
| /qa | Write concurrency test plan (spec-first, before implementation) | pending | |

### Wave 2: API changes (sequential: /typecheck then /int)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /typecheck | Steps C+D: Change worker-called methods to `&self`, switch `modules` to DashMap | done | |
| /typecheck | Step E: Change `check()` to `&self` | done | |
| /int | Wave 2: Add condvar parking to `take_priority_work`. Wire `&TypeChecker` in WorkerContext. | done | |

### Wave 3: Thread spawning
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Wave 3: Spawn priority worker threads, shared sexp map, run_with_workers | done | |
| /qa | Concurrency tests, thread sanitizer validation | pending | |
| /review | Review all new code for thread safety | pending | |

### Wave 4: Cleanup
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Wave 4: Clippy fixes, assess remaining debt | done | `InMemWorkerState` and `self.state` retained — still needed by REPL/old pipeline. See notes. |
| /typecheck | Step F: Remove `self.state` field, cleanup | deferred | 51+ references in checker.rs, used by REPL snapshot/restore and backward-compat wrappers. Requires REPL migration to v4 first. |

## Notes

### Wave 4 Cleanup Assessment

**`InMemWorkerState` — RETAINED.** Cannot delete. The REPL path (`src/repl/mod.rs`) uses `extract_from`/`sync_back_to` in 3 places. The old `CompilationSession` (used by REPL, old pipeline) stores it as a field (`src/session.rs:781`). The old pipeline (`src/pipeline.rs`) uses it in ~30 functions for GOT, JIT, and trace state. Deletion requires migrating the REPL to use `SharedCodegenState` natively instead of bridging through `InMemWorkerState`, which is a future step (post-REPL-v4-migration).

**`self.state` on TypeChecker — RETAINED.** 51+ references in `checker.rs`, plus heavy use in `program.rs`, `infer.rs`, `builtins.rs`, `traits.rs`. Used for REPL `snapshot()`/`restore()`, backward-compat test wrappers (`check_program_self`, `register_trait_decl_self`, etc.), and `current_module` tracking. Requires REPL to own its persistent `CheckState` in `ReplSession` instead of on `TypeChecker`. This is a /typecheck + /int joint migration gated on REPL v4.

**Bridge pattern (`extract_from`/`sync_back_to`) — RETAINED.** Used in `session_v4.rs` (2 call sites: `register_module` and `register_module_with_workers`) and `repl/mod.rs` (3 call sites: REPL module compilation paths). The bridge converts between `InMemWorkerState` (HashMap-based) and `SharedCodegenState` (DashMap-based) at worker loop boundaries. Removal requires REPL migration.

**`.bak` files — NONE FOUND.**

**Clippy — 15 warnings fixed in `src/`.** Remaining warnings (5) are structural: large enum variants (`ProcessResult`, `WriterMessage`), complex return type, loop indexing, too-many-args. These require non-trivial refactoring beyond cleanup scope.

**Pre-existing test failures — 2 in v4_pipeline** (`v4_platform_io_trampoline`, `v4_platform_empty_registry`), confirmed pre-existing on main before any changes. **sketch_port hangs** — also pre-existing.

## Outcome

### Delivered

### Deferred

### Findings
