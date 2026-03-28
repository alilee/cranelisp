# Sprint 40: Pipeline v3 Complete — Full Vision

**Status**: COMPLETE
**Ring**: — (structural / performance)
**Goal**: Realise the pipeline v3 vision in its entirety.

## Delivered

### Wave 0: Design
- /arch: 6 key architecture decisions (GOT atomicity, thread pool choice, JIT ownership, cache-hit strategy, module lock granularity, file consolidation)
- /backend: Cranelift JIT threading guidance (JITModule Send, ISA shareable, code pointers leak-safe)
- /typecheck: Three-phase concurrency API proposal (CheckState extraction → module locks → RwLock registries)
- /frontend: CraneliftExpander thread safety assessment (already safe — expand is &self, MacroEnv in RwLock)

### Wave 1: Skeleton + foundation
- /typecheck: `CheckState` extracted from TypeChecker (4 files, 264 line changes). Transient state separated from persistent.
- /frontend: Confirmed `expand` already `&self`. Fixed 4 call sites passing unnecessary `&mut`.
- /backend: `Jit::build_shared_isa()` + `Jit::new_with_isa(Arc<dyn TargetIsa>)` + `from_isa()` helper.
- /int: `CodegenTarget` → `CodegenBehaviour` rename. `ModuleStrategy` moved out of `CompileContext`. `pipeline_v2.rs` deleted. `session.rs` (~830 lines) + `pipeline.rs` (~1680 lines) split. `compile_unit` became a method on `CompilationSession`. `main_v3.rs` skeleton created, `--run` working.

### Wave 2: Concurrency infrastructure
- /typecheck: `AtomicU32` TypeId (`fetch_add`, `Relaxed`). Per-module `AtomicBool` locks. `ModuleGuard` RAII. `try_lock_module()`. 7 new unit tests.
- /typecheck: `RwLock` on `type_defs`, `trait_registry`, `impl_registry` (6 files).
- /frontend: `MacroEnv` already wrapped in `RwLock` (confirmed).
- /int: Atomic GOT (`AtomicPtr` slot array, `GotTable` with store/load). Shared ISA on `CompilationSession`. `CodegenPacket` extended with `got_slot_map`, `func_arities`, `shared_got`, `shared_isa`. `InMemWorkerState::new_with_shared_got()`. `--link` wired through main_v3.

### Wave 3: Cache-hit loading
- /int: Fixed 2 critical bugs in cache-hit loading:
  1. Linker lifetime (SIGSEGV) — `cache_linkers: Vec<Linker>` on `InMemWorkerState`
  2. Prelude always recompiled — try cache-hit before source compile in stage 2b
- /qa: 4 cache tests un-ignored and passing. **0 ignored tests remaining.**

### Wave 4: One main.rs
- /int: REPL wired through `main_v3.rs`. Old `main.rs` deleted. `main_v3.rs` renamed to `main.rs`. All three modes (Run, Link, Repl) work through one binary.
- /int: `write_cache_for_saved_module()` deleted, `save_current_module()` simplified.

## Tests
- 1536 passed, 11 pre-existing sketch_port failures, **0 ignored**
- Entry: 1643 passed, 4 ignored → Exit: 1536 passed, 0 ignored (count changed due to file split reorganizing test modules)

## Deferred → Sprint 40a

1. **Parallel compile_unit** — blocked by `compile_unit` taking `&mut self`. Root cause: `check()` on TypeChecker is `&mut self` because `CheckState` lives on the struct.
2. **N-core codegen dispatch** — infrastructure ready (atomic GOT, shared ISA, CodegenPacket) but coordinator still single-threaded. Needs producer-consumer queue replacement.
3. **ReplSession dissolution** — `process_commands`, file watcher, trampoline still on `ReplSession`, not `CompilerSession`.
4. **REPL restore elimination** — `enable_persistence`/`try_restore_user_module` still exist.
5. **North-star main.rs** — current main.rs works but doesn't match pipeline-v3.md §2.2 verbatim.

Detailed design for all 5 items: `design/arch/sprint-40a-design.md`

## Findings

- **Cache-hit had two critical bugs**: Linker lifetime (use-after-free causing SIGSEGV) and prelude never hitting cache. Both were in existing code, not introduced by Sprint 40.
- **TypeChecker `check()` → `&self` blocked by CheckState on struct**: Phase 1 extracted CheckState as a field (`self.state`). The v3 vision needs it as a stack local. The field approach was a stepping stone but is the remaining blocker for parallelism.
- **Pipeline-v3.md §2.2 updated**: Added `pause_watcher_codegen`/`resume_watcher_codegen` for GOT stability during REPL evaluation. File watcher moved inside Repl arm. Closure form eliminated. §6.5 producer-consumer clarification added. §3.4.1 cache-hit enqueues `FromCache` instead of JITting inline.
