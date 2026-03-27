# Pipeline v3 Migration Roadmap

How to get from the current state to the architecture described in `pipeline-v3.md`. Each step produces a working compiler — no step leaves things broken.

## Current State

- `compile_unit` (in `pipeline_v2.rs`) does stages 1-7: parse through execute, synchronous.
- `run_batch_v2` and `compile_for_link_v2` orchestrate session setup, platform prescan, prelude pre-loading, then call `compile_unit`.
- `CompilationSession` (in `pipeline.rs`) is a 20-field struct mixing pipeline state, codegen state, cache state, and link-time state.
- `CompileContext` has four fields: `module`, `strategy`, `compile_mode`, `codegen_target`.
- REPL `eval` owns its own parse-intercept-expand-typecheck-execute pipeline in `repl/mod.rs`, calling `tc.check()` and `compile_and_execute` directly.
- `compile_unit_from_sexps` and `compile_unit_from_program` are transitional entry points.
- 449 test call sites use `compile_and_run` (v1 batch helper in `pipeline.rs`).
- File watcher and hot-reload exist in `repl/watch.rs` but are wired to v1 REPL internals.

## Step 1: Decouple codegen from `compile_unit`

**Goal**: `compile_unit` returns after stage 5. Codegen moves to callers.

**Changes**:
- `compile_unit_inner` stops at line 212 (after `tc.check`). Remove lines 217-255 (codegen dispatch, module aliases, cache write, func_sigs).
- `CompileUnitResult` gains `program: Vec<TopLevel>` and `module_structure: ModuleStructure`. Loses `value` and `result_type`.
- New function `codegen_and_execute(session, &CompileUnitResult, ctx)` contains the extracted codegen+execute logic from `compile_and_execute_batch` and `compile_and_execute_interactive`. Called by `run_batch_v2`, `compile_for_link_v2`, and the test helper.
- All current callers of `compile_unit` add a `codegen_and_execute` call after it.
- Tests: all 449 `compile_and_run` sites continue working (they call the combined path).

**Verification**: `cargo test` passes. No behaviour change. Codegen just moved out of `compile_unit` into the caller.

## Step 2: Introduce `CodegenItem` and synchronous queues

**Goal**: Codegen goes through a queue abstraction, still drained synchronously.

**Changes**:
- Define `CodegenItem { module, program, check_result, module_structure, source }`.
- Add `inmem_queue: Vec<CodegenItem>` and `object_queue: Vec<CodegenItem>` to `CompilationSession`.
- `compile_unit` pushes a `CodegenItem` to one or both queues after stage 5, based on `codegen_target`.
- New methods: `flush_in_mem_queue(&mut self)` and `flush_object_queue(&mut self)`. These drain the queue and call the existing codegen functions (`compile_and_execute_batch`, `compile_and_execute_interactive`, `queue_background_cache_write`). Synchronous, single-threaded.
- `run_batch_v2`: replace `codegen_and_execute` with `flush_in_mem_queue`.
- `compile_for_link_v2`: replace direct cache writing with `flush_object_queue`.

**Verification**: `cargo test` passes. Same behaviour, but codegen goes through queues.

## Step 3: Simplify `CompileContext`

**Goal**: Remove `CompileMode`, rename `CodegenTarget` to `CodegenBehaviour`.

**Changes**:
- `CompileContext` becomes `{ module, codegen: CodegenBehaviour }`. `ModuleStrategy` becomes a parameter on `compile_unit`.
- `CodegenBehaviour::InMemoryAndObject` replaces `JitAndCache`. `CodegenBehaviour::ObjectOnly` replaces `ObjectOnly`.
- `CompileMode` deleted. The in-mem queue consumer decides GOT-indirect vs direct calls based on whether `got_state` exists (interactive) or not (batch). This is a queue-consumer concern, not a pipeline concern.
- Update all `CompileContext` construction sites.

**Verification**: `cargo test` passes. `CompileMode` no longer exists.

## Step 4: Move platform handling into `compile_unit`

**Goal**: `compile_unit` handles `(platform ...)` forms during stage 2a. No prescan.

**Changes**:
- When `extract_module_declarations` finds a `(platform ...)` form, it returns it in `ModuleStructure.platform_specs` (or similar).
- `compile_unit` stage 2a iterates `platform_specs`: loads DLLs, registers symbols in `platform_symbols` and `scheduling_registry`, registers types in tc.
- `CompilerSession` gains `project_root: PathBuf` field (needed for DLL path resolution).
- Delete the prescan loops in `run_batch_v2` (lines 781-798) and `compile_for_link_v2` (lines 976-993). These are now redundant.

**Verification**: `cargo test` passes. `--run` and `--link` with platform programs still work.

## Step 5: Move prelude loading into `compile_unit`

**Goal**: Prelude loads via the normal dependency resolution path. No pre-loading.

**Changes**:
- `compile_unit` stage 2e already injects `(import [prelude [*]])` if prelude is loaded. Change this: if prelude is *not* loaded and this isn't the prelude module, resolve and compile it via recursive `compile_unit` (same as any other dependency at stage 2c).
- Delete `load_prelude_for_link` in `pipeline_v2.rs`.
- Delete prelude pre-loading in `run_batch_v2` (lines 800-852).
- The prelude's own dependencies (the core modules it re-exports) load via recursive `compile_unit` from the prelude's imports — same mechanism.

**Verification**: `cargo test` passes. Prelude loads automatically on first import.

## Step 6: Collapse orchestration into `main`

**Goal**: Delete `run_batch_v2` and `compile_for_link_v2`. Main calls `compile_unit` directly.

**Changes**:
- `main.rs` Run mode: create session, read source, `compile_unit`, `flush_in_mem_queue`, trampoline, `flush_object_queue`.
- `main.rs` Link mode: create session, read source, `compile_unit` with `ObjectOnly`, `flush_object_queue`, link.
- Delete `run_batch_v2` and `compile_for_link_v2` from `pipeline_v2.rs`.
- Move `trampoline` (main verification, IO trampoline) and `link` (startup object, system linker invocation) to methods on `CompilerSession` or to `main.rs`.
- `compile_and_run` test helper: calls `compile_unit` + `flush_in_mem_queue` inline. This is a two-line function now.

**Verification**: `cargo test`, `--run`, `--link` all work. `pipeline_v2.rs` shrinks dramatically — it's now just `compile_unit` and its stage helpers.

## Step 7: Decompose `CompilationSession`

**Goal**: Separate pipeline core from worker state.

**Changes**:
- Extract `InMemWorkerState { got_state, jit_modules, traced_fns, trace_extra_symbols }` from `CompilationSession`. Owned by `flush_in_mem_queue`, not by `compile_unit`.
- Extract `ObjectWorkerState { cache_dir, compiled_o_paths, compiled_module_structures, cross_module_func_sigs }`. Owned by `flush_object_queue`.
- `CompilationSession` retains: `tc`, `expander`, `compile_stack`, `lib_dirs`, `scheduling_registry`, `platform_symbols`, `module_deps`, queues, worker states, `settings`, `project_root`.
- `compile_unit` can only access pipeline core fields and queues. Enforce by making worker state fields private with accessors only on the flush methods.

**Verification**: `cargo test` passes. Compile errors if `compile_unit` accidentally touches worker state.

## Step 8: Add `ModuleDependencyGraph`

**Goal**: Dependency graph populated at stage 2, used for file watcher cascade.

**Changes**:
- Define `ModuleDependencyGraph { imports, dependents, file_to_module }` on `CompilerSession`.
- `compile_unit` stage 2b registers import edges in `module_deps` before loading dependencies. This happens even if later stages fail.
- Move `file_to_module` and `module_dependencies` from `ReplSession` to `CompilerSession.module_deps`.

**Verification**: `cargo test` passes. Dependency graph populated but not yet consumed by anything new.

## Step 9: Refactor REPL to use `compile_unit`

**Goal**: REPL `eval` calls `compile_unit` instead of its own pipeline. `process_commands` is thin.

**Changes**:
- New `process_commands(&mut self, input: &str) -> CommandResult` method. Returns `Nothing`, `Final(Form)`, or `Compile(String)`.
- Slash command dispatch moves from REPL eval to `process_commands`. Returns `Nothing` or `Final`.
- Blank/comment detection moves to `process_commands`. Returns `Nothing`.
- Everything else returns `Compile(input.to_string())`.
- REPL interceptions (defmacro, import, platform, bare symbol introspection) are already handled inside `compile_unit` stages 2-3. The REPL no longer needs its own interception layer.
- REPL eval loop becomes: `process_commands` → if `Compile`, call `compile_unit` + `flush_in_mem_queue` → `pretty_print_form`.
- TC snapshot/restore wraps the `Compile` path in the loop.
- Delete `eval_sexp`, `eval_flattened_forms`, `eval_annotation_expr`, `eval_defmacro`, `eval_import`, `eval_platform`, `check_bare_symbol_introspection` from `repl/mod.rs`.

**This is the high-risk step.** The REPL has 15+ interception points. Each must be verified to work correctly when handled inside `compile_unit` instead. Incremental approach: move one interception at a time (defmacro first, then import, then platform, then introspection), testing after each.

**Verification**: All REPL demo files play cleanly. All REPL tests pass. Slash commands work. Error recovery works. Session persistence works.

## Step 10: Wire file watcher to `recompile_module_and_dependents`

**Goal**: File watcher uses `compile_unit` + cascade via `module_deps`.

**Changes**:
- New method `recompile_module_and_dependents(module, src)` on `CompilerSession`: calls `compile_unit(Replace)`, looks up transitive dependents in `module_deps`, topo-sorts, recompiles each.
- File watcher callback calls `recompile_module_and_dependents` instead of the current v1 reload path.
- Delete `reload_single_module` and related v1 reload infrastructure.

**Verification**: Edit a file while REPL is running → dependents recompile → REPL sees updated definitions.

## Step 11: Concurrent codegen queues

**Goal**: `spawn_hot_inmem_codegen` and `spawn_nice_object_codegen` drain queues on thread pools.

**Changes**:
- `inmem_queue` and `object_queue` become `Arc<Mutex<Vec<CodegenItem>>>` (or crossbeam channel).
- `spawn_hot_inmem_codegen`: spawns N worker threads (one per core) at normal priority. Each loops: pop item from queue, JIT-compile, write code pointer to GOT slot (atomic store).
- `spawn_nice_object_codegen`: spawns N worker threads at nice priority. Each loops: pop item from queue, compile to `.o`, write to disk.
- `hot_flush_in_mem_queue`: signals workers to drain, blocks until queue is empty and all in-flight items complete.
- `hot_flush_object_queue`: promotes worker thread priority to normal, then blocks until queue is empty.
- `InMemWorkerState` and `ObjectWorkerState` move into the worker threads (each worker has thread-local JIT state). Only the GOT is shared (atomic writes).

**Verification**: `cargo test` passes. Performance improvement on multi-module programs.

## Step 12: Per-module locks

**Goal**: `compile_unit` takes an exclusive lock on its target module. `try_lock` semantics.

**Changes**:
- `TypeChecker.modules` entries gain a `Mutex` or equivalent lock.
- `compile_unit` calls `tc.try_lock_module(&ctx.module)` at entry. Returns error if already locked.
- Lock is RAII — released when `compile_unit` returns (success or error).
- File watcher retries on lock failure.

**Verification**: Concurrent `compile_unit` calls for the same module fail fast. Different modules compile concurrently.

## Step 13: Parallel dependency typechecking

**Goal**: Independent dependencies at stage 2c compile in parallel.

**Changes**:
- Stage 2c partitions unresolved imports into: already loaded, cache hits, cache misses.
- Cache misses are checked for independence (no edges between them in `module_deps`).
- Independent cache misses fork into parallel `compile_unit` calls (rayon or std::thread::scope).
- Each parallel call takes its module lock, typechecks, enqueues codegen, releases lock.
- Parent resumes after join.

**Verification**: Multi-module programs with independent dependencies compile faster. No correctness regressions.

## Step 14: Delete v1 dead code

**Goal**: Remove all v1 pipeline code that is no longer reachable.

**Changes**:
- Delete `pipeline.rs` functions no longer called: `compile_program`, `check_program`, `check_repl_input`, `compile_expr_with_got`, `load_prelude_into_session`, `load_module_into_session`, `compile_module_graph`, `discover_module_graph`, `toposort`, `compile_and_run`, `build_check_for_backend`, and all their helpers.
- Delete `compile_unit_from_sexps` and `compile_unit_from_program` from `pipeline_v2.rs`.
- Delete `ReplSession.eval`, `eval_sexp`, `eval_flattened_forms`, and all REPL v1 eval infrastructure.
- Delete v1 types if any remain: `ReplInput`, `ReplCheckResult`.
- `pipeline.rs` retains only: `CompilationSession` struct/impl, `assemble_lib_dirs`, `resolve_prelude`, `CraneliftExpander`, `CacheState`, and any small utilities still referenced.
- Consider merging remaining `pipeline.rs` content into `pipeline_v2.rs` (now the sole pipeline module) or into `session.rs`.

**Verification**: `cargo test` passes. `cargo clippy` clean. Significant line count reduction.

## Step 15: New `main.rs`

**Goal**: `main.rs` matches the v3 sketch exactly.

**Changes**:
- Replace `main.rs` with the structure from `pipeline-v3.md` §2.2.
- CLI parsing handles: positional entry module, `--run`, `--link`, `--release`, `--lib_search`, `--no-color`.
- Entry module defaults to `cwd/user.cl` when omitted.
- Settings from `cranelisp.toml` (if present).
- Delete `main_new.rs` scratch file.

**Verification**: All modes work. All tests pass. Clean entry point.

## Ordering and Dependencies

```
Step 1: Decouple codegen from compile_unit
  │
  ▼
Step 2: Introduce CodegenItem and synchronous queues
  │
  ├─► Step 3: Simplify CompileContext (independent)
  │
  ▼
Step 4: Move platform handling into compile_unit
  │
  ▼
Step 5: Move prelude loading into compile_unit
  │
  ▼
Step 6: Collapse orchestration into main
  │
  ▼
Step 7: Decompose CompilationSession
  │
  ├─► Step 8: Add ModuleDependencyGraph (independent of 7)
  │
  ▼
Step 9: Refactor REPL to use compile_unit  ◄── highest risk
  │
  ├─► Step 10: Wire file watcher (needs 8 + 9)
  │
  ▼
Step 11: Concurrent codegen queues
  │
  ▼
Step 12: Per-module locks
  │
  ▼
Step 13: Parallel dependency typechecking
  │
  ▼
Step 14: Delete v1 dead code
  │
  ▼
Step 15: New main.rs
```

Steps 1-6 are mechanical refactoring with compiler-enforced correctness.
Step 7-8 are structural reorganisation.
Step 9 is the highest-risk step (REPL migration).
Steps 10-13 add concurrency.
Steps 14-15 are cleanup.

## Post-Migration Assessment (Sprint 38 Complete)

Steps 1-10 and 14 are complete (Sprints 29-38). Steps 11-13 (concurrency) planned for Sprint 39. The single-pipeline invariant is established: all compilation flows through `compile_unit`.

### Step 15 Assessment: Mostly Delivered

Step 15 as written ("New main.rs") is substantially delivered by Step 6 (Sprint 33). The current `main.rs` (306 lines) is clean, well-structured, and uses `compile_unit` exclusively. What remains from the Step 15 spec:

- **Positional entry module**: Not implemented. `--run <file>` is required; bare `cranelisp file.cl` does not work. Low priority — the `--run` flag is clear and unambiguous.
- **Entry module defaults to `cwd/user.cl`**: Not implemented. The REPL starts when no file is given. Could be useful but is not blocking.
- **`--release` flag**: Not relevant until Phase H (Tier 2 backend).
- **`--lib_search` flag**: Not implemented. `CRANELISP_LIB` env var and `assemble_lib_dirs` serve this role already.
- **`cranelisp.toml` settings**: Not implemented. No user demand yet. Premature to add a config file format before the language is stable.
- **Delete `main_new.rs`**: Already done (Sprint 33).

**Decision**: Step 15 is retired. The remaining items are minor CLI polish that can land as part of feature sprints when motivated by user need. No dedicated sprint.

### Remaining Structural Debt

Four categories of deferred work remain from the v3 migration:

#### 1. Cache-Hit Loading (4 ignored tests)

The v2 pipeline writes `.o` and `.meta.json` files via `queue_background_cache_write` but never loads from cache. The v1 `try_restore_from_cache` was deleted in Sprint 38. Four tests in `tests/cache.rs` are `#[ignore]` awaiting reimplementation.

**Impact**: Every REPL startup and `--link` rebuild recompiles all modules from source. For the stdlib prelude (27 modules), this is the dominant cost. Cache-hit loading is the single highest-impact performance improvement available.

**Scope**: Read `.meta.json` manifest, compare source hash, load `.o` if valid, register types/symbols in tc, register JIT symbols in GOT. The v2 `compile_unit` needs a cache-check early return path (after stage 2a module resolution, before stage 3 expansion).

#### 2. REPL restore_user_cl Bypass

The REPL's session restoration path (`repl/mod.rs` lines ~362-396) still calls `process_forms_with_originals`, `tc.check`, and `compile_checked_program` directly instead of routing through `compile_unit`. This is a pipeline invariant violation — the last one.

**Impact**: Low risk in practice (restore only runs on REPL startup with a saved user.cl). But it means the restore path does not get platform prescan, bind-chain analysis, or any future compile_unit stages for free. It is also the last call site for `compile_checked_program`.

**Scope**: Small — rewrite the restore path to build source text from saved sexps, then call `compile_unit` + `codegen_and_execute`. The tricky part is preserving the original-sexp tracking for round-trip fidelity.

#### 3. REPL Direct tc.check Calls

Two additional sites call `tc.check` directly:
- `eval_annotation_expr` (`repl/mod.rs` ~988) — constructs a `CompileUnitResult` manually
- `handle_type` (`repl/commands.rs` ~124) — uses `tc.check` for `/type` command

These are not full pipeline bypasses (they handle single expressions, not module-level compilation), but they manually construct `CompileUnitResult` and `CompileContext` instead of flowing through `compile_unit`. The annotation path is defensible (it synthesizes an `Expr::Annotate` that has no source text). The `/type` command is read-only (no codegen).

**Decision**: Accept as-is. These are leaf-node uses for REPL-specific expression evaluation, not alternative compilation pipelines. They do not violate the single-pipeline invariant because they are not compiling modules.

#### 4. Code Quality (Deferred Review Findings)

From accumulated `/review` findings across Sprints 29-38:
- `compile_unit_inner` is ~153 lines (guideline: 100). Not egregious; the stages are linear and well-commented. Decompose into stage helpers if it grows further.
- `run_file_inner` / `link_file_inner` are ~108 / ~116 lines with duplicated session setup. Extract a `create_session_for_file` helper.
- `compile_checked_program` signature should take `&mut InMemWorkerState` (not full session). Blocked until restore_user_cl is migrated (it is the last caller that needs full session access).
- `file_for_module` uses linear scan on `file_to_module` HashMap values. Acceptable for current module counts (<100). Add reverse index if profiling shows a hotspot.
- Stale design docs: `interfaces.md` and `pipeline-v2.md` reference `CompileMode` which no longer exists. Need a doc cleanup pass.

### Forward Priority Order

1. **Cache-hit loading** — highest user-visible impact (REPL startup time, --link speed). One sprint.
2. **REPL restore bypass + code quality** — clean up the last pipeline invariant violation and address accumulated review findings. One sprint, combinable with cache work if cache sprint is undersized.
3. **Stale doc cleanup** — update `interfaces.md`, `pipeline-v2.md` to reflect post-v3 state. Can be folded into any sprint as a wave-0 task.
4. **Steps 11-13 (concurrency)** — Sprint 39. Pragmatic approach: codegen overlap + parallel file I/O. TypeChecker remains single-threaded.

### Steps 11-13: Concurrency (Sprint 39)

Reactivated for Sprint 39. The approach avoids making TypeChecker thread-safe by using a pragmatic design:
- **Step 11**: Codegen worker thread overlaps codegen(N) with typecheck(N+1). TypeChecker stays single-threaded.
- **Step 12**: Coarse `RwLock` on `tc.modules` (preparatory — no actual concurrency yet).
- **Step 13**: Dependency-level partitioning with parallel file I/O via rayon. TypeChecker still single-threaded; parallelism is in file reads + codegen overlap.

See `sprints/SPRINT.md` (Sprint 39) for the full implementation plan.
