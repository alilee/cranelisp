# Sprint 39: Pipeline v3 Step 11 — Codegen Decoupled from Session (Foundation)

**Status**: COMPLETE
**Ring**: — (structural / performance)
**Goal**: Decouple codegen functions from `CompilationSession` so they can run on worker threads. Add `send_codegen`/`flush_codegen` API and single async worker as proof of concept.

## Delivered

### Codegen decoupled from CompilationSession
- `codegen_and_execute` is now a free function taking `(&mut InMemWorkerState, &mut ObjectWorkerState, &CodegenPacket)` — no longer takes `&mut CompilationSession`
- `compile_checked_program`, `compile_and_register_defn`, `compile_and_execute_interactive`, `compile_and_execute_expr`, `compile_and_execute_expr_with_trace` all refactored to take worker state params
- `queue_background_cache_write` takes `(&mut ObjectWorkerState, &SymbolTable, ...)`
- `register_module_aliases_filtered` and `register_got_alias` extracted as free functions

### Send verification
- `CodegenPacket` struct with `unsafe impl Send` — carries all data needed for codegen across thread boundary
- Compile-time `Send` assertions for `CodegenPacket`, `CompileUnitResult`, `CompileContext`, `CheckResult`, `CodegenResult`, `InMemWorkerState`, `ObjectWorkerState`

### send_codegen / flush_codegen API
- `CodegenMode` enum: `Sync` (tests) and `Async` (production)
- `send_codegen()`: Sync buffers, Async sends to worker
- `flush_codegen()`: Sync drains buffer, Async sends flush and blocks
- `shutdown_codegen()`: retrieves worker state back to session

### Async worker (single thread — needs upgrade in Sprint 40)
- Single dedicated worker thread owns InMemWorkerState + ObjectWorkerState
- Processes CodegenPackets sequentially
- Shutdown returns state to session for introspection

## Not delivered — Sprint 40 scope

The roadmap (`design/arch/pipeline-v3-roadmap.md` Step 11) specifies:
- **N worker threads (one per core)** for in-mem codegen at normal priority
- **N worker threads at nice priority** for object codegen
- **Atomic GOT writes** so multiple workers can write concurrently
- **Thread-local JIT state** per worker
- **`hot_flush_object_queue`** promotes nice→normal priority on flush

Sprint 39 delivered a single worker thread. Sprint 40 must upgrade to the full N-core model.

## Tests
1643 passed, 23 pre-existing failures, 4 ignored (cache-hit)

## Outcome
Foundation for concurrent codegen is solid — all codegen functions are decoupled from the session, Send bounds verified, channel-based API works. Sprint 40 builds the actual thread pools on this foundation.
