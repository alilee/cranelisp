# Concurrency Architecture — current structures, intent, interfaces, and risk

**Status**: analysis draft
**Purpose**: enumerate the **currently designed** concurrency structures in the
system, explain **why each one exists**, **where concurrency is architecturally
justified**, **how each part is encapsulated**, **what the interfaces are**, and
**what the risk level is**.

**Diagram companion**: see `design/int/concurrency/README.md` and the Mermaid
artifacts in `design/int/concurrency/` for current-state, target-state,
scheduler-lifecycle, protocol, and structure-matrix views of the same analysis.

This document is intentionally broader than the Sprint 62 audit and the recent
observability docs. It draws on:

- `design/arch/pipeline-v4.md`
- `design/arch/concurrent-pipeline.md`
- `design/int/persistent-workers.md`
- `design/int/concurrent-workers.md`
- `design/int/cache-hit-loading.md`
- `design/int/step5-lazy-discovery.md`
- `design/int/step7-repl-eval.md`
- `design/int/session-persistence.md`
- `design/int/io-integration.md`
- `design/int/observability.md`
- current code in `src/`, `crates/cranelisp-runtime/`, `crates/cranelisp-backend/`, and `crates/cranelisp-types/`

---

## 1. Architectural stance

The project does **not** use concurrency everywhere. Concurrency is justified in
specific places where the design says it buys something real:

1. **Inter-module compiler throughput**
   - independent modules can typecheck/codegen in parallel
2. **Latency hiding for macro expansion**
   - macro dependencies need callable code while other work continues
3. **Background object generation / cache production**
   - `.o` output is lower urgency than in-memory code used for execution
4. **Runtime parallel evaluation**
   - independent bindings may be sparked and forced concurrently
5. **Observability across threads**
   - the system needs thread-aware diagnostic logs to understand failures
6. **OS-driven file notifications**
   - source-change events arrive asynchronously from outside the process

By contrast, concurrency is **not architecturally justified** where it only
exists because the current implementation spreads one protocol across multiple
modules. Those cases are design debt, not design intent.

---

## 2. High-level map

There are three broad concurrency zones in the current system:

### A. Compiler concurrency (`src/`)
- scheduler
- priority workers
- nice workers
- shared session state
- dependency publication / blocking / resume
- cache-hit loading and code publication

### B. Runtime concurrency (`crates/cranelisp-runtime/`)
- atomic RC
- IVars for lenient evaluation
- runtime trace / IO trace buffers

### C. Diagnostic / host-edge concurrency
- observability ring buffers and panic hooks
- file watcher callback channel

The bulk of the current risk is in **A**, not because concurrency there is
unjustified, but because the intended architecture is still not sufficiently
compartmentalised.

---

## 3. Inventory of current concurrency structures

## 3.1 `CompileScheduler` — the concurrency kernel

**Where**:
- `src/scheduler.rs`
- design intent in `design/arch/concurrent-pipeline.md`

**Why concurrency is justified here**:
- parallelism is primarily **inter-module**
- macro expansion can block on callable code
- workers need a central place to coordinate readiness, blocking, and completion

**Intent**:
- own module lifecycle and work coordination only
- **not** own ASTs, symbol tables, or compiled code
- act as a pure coordination kernel

**Encapsulation**:
- strong in principle: all scheduler state is behind one `Mutex<SchedulerState>`
- weaker in practice: correctness still depends on publication discipline in
  surrounding modules (`worker.rs`, `session_v4.rs`)

**Primary interfaces**:
- registration:
  - `register_module`
  - `register_module_cached`
  - `re_register_module`
- worker claim:
  - `take_priority_work_blocking`
  - `take_object_codegen`
- waiting / blocking:
  - `block_for_typecheck`
  - macro/codegen blocking APIs
  - `wait_inmem_complete`
  - `wait_module_inmem_complete_blocking`
- completion:
  - `notify_typecheck_done`
  - `notify_inmem_codegen_complete`
  - `notify_object_codegen_complete`
  - failure/reset/shutdown APIs

**Risk level**: **High**

**Why high**:
- this is the global concurrency authority
- mistakes are systemic, not local
- it manages queue state, pool transitions, waiters, condvars, and completion
- several correctness properties depend on code outside the scheduler
  publishing data before scheduler flags move

**Assessment**:
Architecturally justified and necessary. The main risk is not that it exists;
it is that it is not yet the sole owner of the full concurrency protocol.

---

## 3.2 Priority worker subsystem

**Where**:
- `src/worker.rs`
- session spawn path in `src/session_v4.rs`
- design intent in `design/int/persistent-workers.md`

**Why concurrency is justified here**:
- this is the mechanism that turns scheduler readiness into real parallel work
- inter-module typecheck and JIT codegen are the main throughput gain in v4

**Intent**:
- claim typecheck / blocking-codegen / JIT work from the scheduler
- process one claimed module or symbol at a time
- publish results back through the scheduler and shared state

**Encapsulation**:
- moderate
- there is a coherent worker loop and `ModuleCompiler` context
- but worker logic is still too entangled with session and scheduler details

**Primary interfaces**:
- worker loop:
  - `priority_worker_loop_shared`
- form processing:
  - `process_module_forms`
  - `ProcessResult`
  - `ModuleCompiler`
- dependency work:
  - `handle_import`
  - `register_dep`
  - `try_cache_hit_load`
- codegen work:
  - `inline_jit_codegen_for_module`
  - `inline_jit_codegen_for_names`
  - `load_cached_module_via_linker`

**Risk level**: **High**

**Why high**:
- owns the most concurrency-sensitive protocol surface after the scheduler
- mixes typecheck progression, dependency discovery, cache-hit paths, and code publication
- contains mirrored or near-mirrored flows called out in comments
- directly participates in the known H6 residue surface

**Assessment**:
Architecturally justified. Not yet sufficiently isolated. This should be one of
the main targets for design-level compartmentalisation.

---

## 3.3 Nice worker subsystem

**Where**:
- `src/session_v4.rs` currently owns `nice_worker_loop` and `compile_module_object`
- design intent in `pipeline-v4.md` and `persistent-workers.md`

**Why concurrency is justified here**:
- object generation is useful but lower urgency than execution
- background workers keep `.o` production and cache writes off the critical path

**Intent**:
- consume `TypecheckDone` modules
- compile object output
- write cache artifacts
- notify scheduler on object completion

**Encapsulation**:
- weak to moderate
- conceptually one worker subsystem
- structurally split away from priority-worker code

**Primary interfaces**:
- `nice_worker_loop`
- `compile_module_object`
- scheduler object-claim / object-complete APIs

**Risk level**: **Medium**

**Why medium**:
- its state transitions are simpler than the priority path
- but ownership is split, and it shares some of the same global state
- cache write and object completion correctness still matter to session behavior

**Assessment**:
Architecturally justified. Should be unified with the worker subsystem to reduce
reasoning cost.

---

## 3.4 `SharedState` — the concurrent session data plane

**Where**:
- `src/session_v4.rs::SharedState`

**Why concurrency is justified here**:
- persistent workers and the REPL/session thread need a shared data plane
- some data is authoritative and legitimately cross-thread:
  - symbol tables
  - typecheck products
  - dependency source payloads
  - cache state
  - platform retention handles

**Intent**:
- central repository of mutable state shared by main thread, priority workers,
  and nice workers

**Encapsulation**:
- mixed
- strong at the field level (`Mutex`, `DashMap`, atomics)
- weak at the module level: too many consumers reach too many fields directly

**Primary field groups**:

### A. Publication / resumption state
- `module_sexps`
- `suspend_states`

### B. Authoritative compiler state
- `symbol_tables`
- `typecheck_products`
- `next_type_id`
- `introspection`

### C. Session/config/cache support
- `lib_dirs`
- `platform_dirs`
- `cache_state`
- `cached_modules`
- `compiled_o_paths`
- `file_to_module`

### D. REPL-only/session-only state mixed into SharedState
- `current_module`
- `repl_check_state`

### E. Lifetime / retention state
- `kept_dlls`
- scheduler reference itself

**Risk level**: **High**

**Why high**:
- this is the broadest concurrent surface in the system
- even when individual fields are safe, broad direct access weakens local reasoning
- REPL-only and worker-facing concerns coexist in one structure
- at least one dual-store smell (`cached_modules`) already exists here

**Assessment**:
Architecturally justified as a concept, but too broad as a concrete structure.
The right direction is stronger ownership boundaries within it, not removal.

---

## 3.5 Dependency publication / readiness protocol

**Where**:
- worker path: `handle_import`, `register_dep`, `publish_dep_sexps`
- REPL/session path: `register_dep_for_eval`
- scheduler readiness APIs in `scheduler.rs`

**Why concurrency is justified here**:
- lazy dependency discovery is a core v4 design choice
- modules must be registered dynamically during form processing
- waiting callers must block and resume without global serialization

**Intent**:
- when a dependency is discovered:
  1. parse/publish the source payload,
  2. register with the scheduler,
  3. block or continue depending on readiness,
  4. resume safely once data is available

**Encapsulation**:
- poor
- this is currently a **protocol**, not a single subsystem
- multiple files collectively implement one temporal invariant

**Primary interfaces**:
- worker-side dependency discovery APIs
- session-side retry/recovery API
- scheduler register/block/wait APIs

**Risk level**: **Very High**

**Why very high**:
- this is the most important concurrency design smell in the current system
- one logical protocol exists in more than one place
- known observed failure already sits on this surface
- difficult to reason about and difficult to test because authority is split

**Assessment**:
Architecturally justified. Current encapsulation is not acceptable long-term.
This should become a single internal concurrency service.

---

## 3.6 Symbol publication and typecheck visibility

**Where**:
- `SharedState.symbol_tables`
- typecheck `ensure_module_exists` and form finalization
- scheduler `notify_typecheck_done`
- worker fast paths that observe readiness then read tables

**Why concurrency is justified here**:
- typechecked module state must become visible to other workers and the REPL
  without stopping the world
- lazy discovery and concurrent module progress require publish-and-observe semantics

**Intent**:
- symbol tables are the authoritative module state
- pool transitions publish readiness
- readers that observe terminal readiness should see complete module data

**Encapsulation**:
- moderate at best
- the store is singular, which is good
- but the publication contract spans typecheck, scheduler, and reader fast paths

**Primary interfaces**:
- `TypeCheckEnv::ensure_module_exists`
- symbol-table writes during typecheck/finalization
- scheduler readiness observation
- worker/session read fast paths

**Risk level**: **High**

**Why high**:
- one of the core correctness contracts of the concurrent compiler
- directly involved in the observed import race
- difficult to prove without stronger compartmentalisation

**Assessment**:
Architecturally justified. Needs a cleaner one-authority publication story.

---

## 3.7 Code publication: `Code`, `GotTable`, `Arc<Jit>` / `Arc<Linker>`

**Where**:
- `src/code.rs`
- `crates/cranelisp-types/src/got.rs`
- backend JIT/linker code
- symbol-table `ModuleEntry::Def.code`

**Why concurrency is justified here**:
- compiled code must be published cross-thread
- redefinition must update callable addresses atomically
- multiple workers may produce code for different modules concurrently

**Intent**:
- compiled code lives on symbol-table entries
- GOT slot swap is the dynamic publication mechanism
- `Arc<Jit>` / `Arc<Linker>` carry lifetime roots for raw code pointers

**Encapsulation**:
- conceptually good
- the model is fairly explicit
- but the invariant still crosses types and modules (`Code`, `GotTable`, symbol tables, scheduler timing)

**Primary interfaces**:
- `Code` enum
- `GotTable::store_slot/load_slot`
- backend compile results
- worker codegen publication paths

**Risk level**: **High**

**Why high**:
- raw pointers + unsafe impls + temporal lifetime invariants
- wrong reasoning here becomes use-after-free or stale-call bugs
- source SAFETY comments have already drifted once (`GotTable`)

**Assessment**:
Architecturally justified and unavoidable. This is a place to keep concurrency
narrow and invariants extremely explicit.

---

## 3.8 Cache-hit loading and cached-module state

**Where**:
- `try_cache_hit_load`
- `load_cached_module_via_linker`
- scheduler `register_module_cached`
- `cached_modules` tracking in session and scheduler

**Why concurrency is justified here**:
- the whole point is to avoid rebuilding work and let workers continue
- cached modules need to join the same scheduler-driven pipeline as fresh modules

**Intent**:
- restore metadata cheaply
- defer in-memory code loading until needed
- let workers treat cached and fresh modules uniformly after registration

**Encapsulation**:
- mixed
- the flow is reasonably coherent
- but dual-store `cached_modules` suggests unresolved ownership

**Primary interfaces**:
- cache validity/load path
- scheduler cached registration
- linker-based in-memory publication

**Risk level**: **Medium-High**

**Why medium-high**:
- the shape is justified, but not fully simplified
- wrongness produces stale code, missing code, or unnecessary rebuilds
- duplicated cached-module state increases risk beyond the basic mechanism

**Assessment**:
Architecturally justified. Needs ownership cleanup.

---

## 3.9 Platform DLL retention and cross-thread function-pointer use

**Where**:
- `src/platform.rs::LoadedPlatform`
- `SharedState.kept_dlls`
- `ModuleEntry::Def.platform_fn_ptr`

**Why concurrency is justified here**:
- platform functions are callable from runtime-executed code regardless of which
  worker/session path originally loaded them
- DLL handles must outlive all such calls

**Intent**:
- load once
- retain DLL handle for session lifetime
- publish function pointers through symbol-table entries

**Encapsulation**:
- reasonably good
- retention root is explicit
- callsites don’t manage DLL lifetime themselves

**Primary interfaces**:
- platform loader
- kept-dll retention pool
- symbol-table platform entries

**Risk level**: **Medium**

**Why medium**:
- raw function pointers and unsafe impls exist
- but the lifetime model is clearer and narrower than the scheduler/worker protocol

**Assessment**:
Architecturally justified and reasonably encapsulated.

---

## 3.10 File watcher callback + channel handoff

**Where**:
- `src/watch.rs`

**Why concurrency is justified here**:
- OS notifications arrive asynchronously
- the REPL loop must not block on watcher callbacks

**Intent**:
- capture external file-change events asynchronously
- poll them from the main thread at prompt boundaries
- use content hashing to suppress self-writes and metadata noise

**Encapsulation**:
- strong
- the watcher owns its callback/channel/hash state internally
- compiler logic receives a clean polling interface

**Primary interfaces**:
- `FileWatcher::new`
- `watch_file`
- `poll_changes`
- `update_content_hash`
- `clear_all`

**Risk level**: **Low-Medium**

**Why low-medium**:
- there is asynchronous host interaction, but the interface is simple
- most logic collapses onto one polling thread
- failures are more likely to cause missed or delayed reloads than memory/model corruption

**Assessment**:
Architecturally justified and relatively well encapsulated.

---

## 3.11 Observability subsystem

**Where**:
- `src/observability.rs`
- `crates/cranelisp-runtime/src/io_trace.rs`
- related trace modules

**Why concurrency is justified here**:
- diagnostics must observe multiple threads without distorting hot paths too much
- thread-local buffering is appropriate for event capture

**Intent**:
- per-thread ring buffers
- publish buffers on thread shutdown
- merge-sort on flush
- parse-once env var gating

**Encapsulation**:
- good
- the subsystem is internally coherent
- interfaces are narrow and diagnostic-only

**Primary interfaces**:
- `record_*` event calls
- `publish_thread_buffer`
- `flush_to_stderr`
- panic-hook installers / flush guards

**Risk level**: **Low-Medium**

**Why low-medium**:
- mostly diagnostic, not semantic
- but bad hooks or stale thread-local invariants could interfere with debugging or panic behavior

**Assessment**:
Architecturally justified and mostly well encapsulated.

---

## 3.12 Runtime atomic RC

**Where**:
- `crates/cranelisp-runtime/src/rc.rs`
- `drop.rs`, runtime heap users
- backend RC emission assumptions

**Why concurrency is justified here**:
- the runtime deliberately uses atomic RC from Ring 1 onward to avoid an ABI/model change when runtime parallelism arrives
- heap values may cross concurrent runtime paths (e.g. parallel evaluation)

**Intent**:
- one RC discipline everywhere
- thread-safe retain/release semantics at the runtime boundary

**Encapsulation**:
- fairly strong
- runtime helpers and backend emission are distinct, but the RC model itself is centralised

**Primary interfaces**:
- runtime RC helpers
- backend inline RC emission
- consuming helpers

**Risk level**: **Medium**

**Why medium**:
- low-level and safety-relevant
- but more localized than scheduler/session concurrency

**Assessment**:
Architecturally justified by the runtime model.

---

## 3.13 IVars and parallel evaluation

**Where**:
- `crates/cranelisp-runtime/src/ivar.rs`

**Why concurrency is justified here**:
- this is the runtime mechanism for lenient / sparkable parallel evaluation
- concurrency is a language/runtime feature here, not just implementation detail

**Intent**:
- write-once evaluation cells
- one thread claims evaluation, others force/wait
- represent parallelism explicitly and locally

**Encapsulation**:
- strong
- self-contained state machine
- much better isolated than the compiler concurrency kernel

**Primary interfaces**:
- `ivar_create`
- `ivar_spark`
- `ivar_force`

**Risk level**: **Medium-High**

**Why medium-high**:
- it is true semantic concurrency with atomics and background execution
- but the design is localized and easier to model than the compiler scheduler

**Assessment**:
Architecturally justified and comparatively well compartmentalised.

---

## 4. Risk summary by structure

| Structure | Justification quality | Encapsulation quality | Risk |
|---|---|---|---|
| `CompileScheduler` | Strong | Moderate | High |
| Priority worker subsystem | Strong | Moderate-low | High |
| Nice worker subsystem | Strong | Low-moderate | Medium |
| `SharedState` | Strong concept, over-broad concrete shape | Low-moderate | High |
| Dependency publication/readiness protocol | Strong need, weak current structure | Low | **Very High** |
| Symbol publication visibility | Strong | Moderate | High |
| Code publication / GOT / JIT lifetime | Strong | Moderate | High |
| Cache-hit loading | Strong | Moderate | Medium-High |
| Platform DLL retention | Strong | Moderate-good | Medium |
| File watcher channel handoff | Strong | Good | Low-Medium |
| Observability buffers/hooks | Strong | Good | Low-Medium |
| Atomic RC | Strong | Good | Medium |
| IVars / parallel eval | Strong | Good | Medium-High |

---

## 5. Where the architecture is healthy vs unhealthy

### Healthy concurrency shapes
These are concurrent by design and reasonably isolated:
- scheduler as a coordination kernel
- observability thread-local buffers
- file watcher callback-to-channel handoff
- platform DLL retention
- runtime IVars
- atomic RC

### Unhealthy concurrency shapes
These are concurrent for understandable reasons, but their **current
encapsulation is too weak**:
- dependency publication / readiness protocol
- broad direct access to `SharedState`
- split worker ownership across `worker.rs` and `session_v4.rs`
- duplicate-store state like `cached_modules`
- REPL-only state mixed into broadly shared state

These are the places where design-level containment should precede or accompany
proof work.

---

## 6. Architectural recommendations

### 6.1 Create one explicit concurrency boundary inside `src/`
A dedicated internal subsystem should own:
- dependency publication,
- readiness observation,
- scheduler registration,
- unblock/wait protocol.

This is the highest-leverage architecture change.

### 6.2 Reduce the surface area of `SharedState`
Not by deleting it, but by:
- giving each field an owner module,
- moving REPL-only state out where possible,
- and preventing broad direct mutation from unrelated modules.

### 6.3 Unify worker ownership
The priority and nice worker loops should be one subsystem, even if they keep
separate queues.

### 6.4 Treat duplicate state as suspect by default
Any dual-store design should be assumed risky until explicitly justified.

### 6.5 Prefer narrow publish/observe interfaces over ambient shared-map access
If a protocol can be expressed as:
- prepare packet,
- publish packet,
- register work,
- wait,
- consume packet,

that is usually easier to reason about than “several components share several
maps and infer readiness from each other.”

---

## 7. Bottom line

Concurrency is **architecturally justified** in this system in several places:
- compiler throughput,
- lazy dependency handling,
- background object generation,
- runtime parallel evaluation,
- and thread-aware diagnostics.

The main current architectural problem is **not that the system is concurrent**.
It is that the most important compiler-side concurrency protocol — dependency
publication and readiness — is **not yet sufficiently encapsulated**.

So the right next move is not only to test more. It is to make the current
concurrent structures:
- more **local**,
- more **owner-driven**,
- and more **separable**,

so each one can be reasoned about and verified on its own.
