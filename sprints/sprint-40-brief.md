# Sprint 40 Brief: Pipeline v3 Step 11 Complete — N-Core Codegen Pools

## Goal

Deliver the full Step 11 from `design/arch/pipeline-v3-roadmap.md`: N-core thread pools for both in-mem and object codegen, atomic GOT writes, thread-local JIT state, nice priority for object workers.

## What the roadmap requires (verbatim from pipeline-v3-roadmap.md Step 11)

- `spawn_hot_inmem_codegen`: spawns N worker threads (one per core) at normal priority. Each loops: pop item from queue, JIT-compile, write code pointer to GOT slot (atomic store).
- `spawn_nice_object_codegen`: spawns N worker threads at nice priority. Each loops: pop item from queue, compile to `.o`, write to disk.
- `hot_flush_in_mem_queue`: signals workers to drain, blocks until queue is empty and all in-flight items complete.
- `hot_flush_object_queue`: promotes worker thread priority to normal, then blocks until queue is empty.
- `InMemWorkerState` and `ObjectWorkerState` move into the worker threads (each worker has thread-local JIT state). Only the GOT is shared (atomic writes).

## What Sprint 39 delivered (foundation)

- Codegen functions decoupled from CompilationSession (free functions taking worker state params)
- `CodegenPacket` is Send — carries all data for codegen across thread boundary
- `send_codegen`/`flush_codegen` API on CompilationSession
- Single async worker thread as proof of concept
- All compile-time Send assertions pass

## What Sprint 40 must deliver

### 1. Replace single worker with N-core in-mem codegen pool

- `spawn_hot_inmem_codegen()`: thread pool with N threads (N = num_cpus or rayon global pool)
- Each worker has its own `Jit` instance (thread-local JIT state) — Cranelift `JITModule` is Send but not Sync
- Workers pop `CodegenPacket` from a shared queue (crossbeam channel or `Arc<Mutex<VecDeque>>`)
- Each worker JIT-compiles the module and writes code pointers to the GOT via **atomic stores**
- The GOT (`ModuleCodegenState`) must support concurrent writes to different slots — use `AtomicPtr` or similar for the slot array

### 2. Atomic GOT writes

- GOT slot table: change from `HashMap<Symbol, *const u8>` to a structure that supports atomic pointer writes
- Each worker writes its module's function pointers to assigned GOT slots
- The main thread reads GOT slots only after `hot_flush` (no concurrent read/write)
- Workers write to disjoint slots (each module's functions get unique slots) — no contention

### 3. N-core object codegen pool at nice priority

- `spawn_nice_object_codegen()`: separate thread pool at reduced OS priority
- Workers pop from the object queue, compile to `.o` via `cranelift-object`, write to disk
- `hot_flush_object_queue()`: promotes thread priority to normal, blocks until queue is empty
- This replaces the existing `CacheWriter` single-thread model for `.o` compilation (the CacheWriter may remain for the actual file I/O, or be absorbed)

### 4. Flush semantics

- `hot_flush_in_mem_queue()`: blocks until all in-flight in-mem codegen completes. After return, all GOT slots from processed items are populated.
- `hot_flush_object_queue()`: promotes nice→normal priority, blocks until all .o files are written.
- Both flushes return `Vec<CodegenResult>` for warning/error aggregation.

### 5. Scale consideration

Design for 200+ modules (100 stdlib + 100 application). The thread pools must handle large batch submissions efficiently. Work-stealing (rayon) is preferred over fixed-partition.

## Key technical challenges

1. **GOT atomicity**: The GOT is currently a `HashMap<Symbol, DefCodegen>` where `DefCodegen` contains `code_ptr: *const u8`. For concurrent writes, either use `DashMap` or pre-allocate a slot array with `AtomicPtr`.

2. **JIT lifetime management**: Each worker creates `Jit` instances that must stay alive (their code memory is referenced by GOT pointers). Workers must transfer completed `Jit` instances back to a central collection (channel or mutex-protected Vec).

3. **Priority control**: `libc::setpriority` or `nice(2)` for the object codegen threads. Not all platforms support this — fall back gracefully.

4. **Interaction with load_dependencies**: Currently `load_dependencies` calls `send_codegen` + `flush_codegen` per dependency. With N-core pools, the pattern becomes: send all deps in a batch, then flush once. This needs the Step 13 level-partitioning to be effective — without it, deps are still sent one at a time.

## Relationship to Steps 12-13

Step 11 (this sprint) makes codegen concurrent. Steps 12-13 make typechecking concurrent. They compose:
- Step 11: multiple codegen workers process the codegen queue
- Step 12: per-module locks so multiple compile_unit calls are safe
- Step 13: parallel compile_unit calls for independent deps, each enqueueing codegen to the Step 11 pool

Sprint 40 delivers Step 11 fully. Steps 12-13 follow in subsequent sprints.

## Entry state

- `send_codegen`/`flush_codegen` API exists
- `CodegenPacket` is Send
- All codegen functions take worker state params (not &mut CompilationSession)
- Single async worker thread proves the channel pattern works
- Tests: 1643 passed, 23 pre-existing failures, 4 ignored
