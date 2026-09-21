# Persistent priority workers — the delivered worker-lifecycle contract

**Owner**: `design` (int). **Status**: delivered (S57 G9/G11); this is the
contract live source and tests cite, not a migration plan.

Priority workers are session-persistent: spawned in `CompilerSession::new`,
parked on a scheduler condvar, joined at shutdown. Work reaches them by
enqueue, never by spawn. The worker *pool* that owns spawn/park/join for both
worker classes is `src/worker_pool.rs`; the inventory of the whole
compiler-internal scheduling axis is
`design/int/concurrency-architecture.md`.

**Section numbers are pinned.** Live source and tests cite `§4.1`, `§4.2`,
`§4.3`, `§4.5`, `§4.6`, `§5.1`, `§5.2`, `§9.1` and `§11` (including `§11`
criterion 2 by position). The gaps in the numbering are deliberate: the
pre-migration current-state survey, the sketch comparison, the deletion list,
the refactor-risk register and the descope contingency were removed in the S122
consolidation, and are recoverable from Git.

## 4. The delivered shape

### 4.1 Spawn at session init

`CompilerSession::new` spawns `priority_workers` named threads, each running
`priority_worker_loop_shared(&SharedState)`. Workers reach session state through
`Arc<SharedState>` — there is no borrowed-reference refs bundle and no
`thread::scope` in worker lifecycle code outside tests. Count resolution (and
the interpretation of `0`) is documented at
`src/session_v4/lifecycle.rs::CompilerSession::new`.

A bound from above matters because nice workers exist alongside: if both pools
sized to CPU count, total threads would be twice the core count and
oversubscribe the OS scheduler. Niceness is best-effort on macOS and does not
prevent it.

### 4.2 Park on condvar, wake on work

A worker loops on `scheduler.take_priority_work_blocking()`, dispatching
`PriorityWork::Typecheck` and the codegen variants, and returns only when the
call yields `None`.

**Behavioural invariant**: `take_priority_work_blocking` returns `None` *only*
on shutdown. Workers park indefinitely when the queue is empty; they do not
exit because "no work is pending". That invariant is what makes enqueue-only
submission (§4.3) safe.

### 4.3 Submission enqueues; it does not spawn

`register_module_with_source`, `reload_module` and REPL `eval` all submit
through the scheduler and then wait on a completion condvar. None of them spawns
a worker cohort, swaps a registry mutex, or builds per-call worker state.

The sexps a worker needs ride the work packet. The cross-thread
`module_sexps` / `suspend_states` parking maps that an earlier revision of this
document specified on `SharedState` were deleted by the S78 in-call-stack
restructure: a caller's cluster state now lives on its own stack frame and no
worker reads it (`design/int/int.md` §6.2). Do not reintroduce a shared map to
hand a worker its input.

### 4.6 Reload runs through the scheduler

`reload_module` is G9's fallout, not a second path: it drops the module's stale
typecheck product, re-parses, and re-registers with the scheduler carrying the
fresh sexps (and the captured instantiation demands) on the work packet. The
parked persistent workers wake and do the typecheck and in-memory codegen; the
caller waits on the completion condvar. No scoped-thread cohort is spawned, and
the file watcher's call path is unchanged — it too enqueues and waits.

Compiled owners are **not** cleared ahead of recompilation. They stay attached
until staged publication replaces them, and the publication record hands each
displaced owner to the commit gate for retention
(`design/int/session-transaction.md` §6.3, §7.3). Clearing code up front would
reopen a NULL window for a stale closure mid-reload.

### 4.5 Per-batch JIT, not per-worker (Decision 31)

One `JITModule` per compile batch. A worker claims a codegen work item, creates
a **fresh** JIT for that batch, compiles, finalises, writes each function's code
pointer into the GOT, and stores an `Arc<Jit>` on each produced
`ModuleEntry::Def.code`. A worker carries no long-lived JIT between work items.
The `__expr` synthetic defn for REPL eval is compiled inline on the eval path
against its own fresh JIT, not submitted to a worker.

`Arc<Jit>` is the sharing primitive: the functions produced by one
`compile_to_module` call share one underlying `Jit`, whose custom `Drop` calls
`JITModule::free_memory()` when the last sibling `Code` entry releases it.

Why per-batch rather than per-worker:

1. A long-lived worker JIT coalesces every batch that worker ever ran, so its
   refcount cannot reach zero until session end and executable pages are never
   reclaimed mid-session. Per-batch gives batch-level granularity.
2. Cranelift's `JITModule::define_function` is single-use per `FuncId`; a reused
   worker JIT would need `hotswap_enabled` + `prepare_for_function_redefine`,
   and that path explicitly does not reclaim. Per-batch avoids the hotswap dance
   entirely.

`JITModule` is not `Sync`, and per-batch keeps each worker's JIT stack-local
during `compile_to_module`. The shared `Arc<Jit>` is read-only except for
`Drop`, which fires on whichever thread releases the last reference.

Retention of a JIT *displaced* by redefinition is not this document's
mechanism: displaced owners move into the session retention pool
(`design/int/session-transaction.md` §6–§7).

## 5. Lifecycle details

### 5.1 Worker count

The effective priority-worker count is resolved from
`SessionSettings::priority_workers`: `0` means auto-detect
(`available_parallelism() - 1`), and every value — auto or explicit — is
clamped to `[1, 8]`. Tests pass `1` for determinism.

- `available_parallelism() - 1` leaves a core for the main thread and OS work.
- The upper clamp exists because **nice workers run alongside**. Sizing both
  pools to core count would put twice the core count of threads on the OS
  scheduler, and niceness is best-effort on macOS, so it does not compensate.
  Past 8 priority workers, contention on the scheduler mutex and the
  symbol-table shards is expected to grow faster than the parallelism gain; 8
  is a deliberately conservative bound, not a measured optimum.

### 5.2 Shutdown sequence

`CompilerSession::shutdown` signals `scheduler.shutdown()` — which sets the flag
and wakes every condvar — then joins the priority-worker handles, then the
nice-worker handles. `Drop` shuts down defensively so a session dropped without
an explicit shutdown still wakes and joins its workers.

**A worker mid-codegen is not interrupted.** It is past its park point, so it
finishes the current work item, publishes its result, notifies the scheduler,
re-enters `take_priority_work_blocking`, observes shutdown and exits. The join
therefore waits for the current item's runtime, not indefinitely. Workers race
`shutdown()` only on the scheduler's atomic flag; everything else they touch is
reached through `Arc` or condvar-protected state.

**A panicking worker does not bring down the session.** `join()` returns `Err`
and shutdown ignores it; the other workers continue.

**Deadlock avoidance is a standing invariant**: workers block on scheduler
condvars and nothing else, and no main-thread function is called *by* a worker.
All compilation work happens outside the scheduler mutex. The file watcher runs
on its own thread; cache writes run on nice workers. Preserve both halves.

## 6. Coordination with nice workers

The two pools share `SharedState` and the `CompileScheduler`, and nothing else —
separate queues, separate condvars (`priority_work_available`,
`object_work_available`), separate thread-local codegen state. All coordination
is mediated by the scheduler: a module reaching `TypecheckDone` becomes
claimable by both (priority for background JIT, nice for the `.o`);
`promote_nice_workers` lets nice workers self-promote to normal OS priority;
`shutdown()` wakes both condvars and both pools drain.

## 9. Evidence

### 9.1 Unit scenarios

The four scenarios that pin this contract, in
`src/session_v4/persistent_worker_tests.rs`:

1. **park and wake** — with no work enqueued the workers park; an enqueued item
   wakes a worker, which processes it and parks again.
2. **shutdown under load** — the session is dropped with work still enqueued:
   no panic, no leak, every worker joins.
3. **concurrent register** — two modules registered at once both reach
   `Complete`, with no lost update.
4. **reload during compile** — a reload issued while a registration is mid-flight
   completes without wedging either side.

They are end-to-end session tests over trivial source, so they depend on no
prelude or stdlib and observe the worker lifecycle alone. A separate guard
(`harvest_thread_scope_absent_outside_cfg_test`) is the executing check for §11
criterion 2.

## 11. Acceptance criteria

1. Priority workers spawned in `CompilerSession::new`; joined in `shutdown()`
   and `Drop`.
2. `thread::scope` appears zero times in worker lifecycle code outside
   `#[cfg(test)]`.
3. `register_module_with_source`, `reload_module` and REPL `eval` submit through
   the scheduler; no per-call worker cohort.
4. Worker functions take `&SharedState` / `Arc<SharedState>`; no borrowed-refs
   bundle.
5. The four lifecycle scenarios in §9.1 pass, including shutdown under load and
   reload during a mid-flight compile.
