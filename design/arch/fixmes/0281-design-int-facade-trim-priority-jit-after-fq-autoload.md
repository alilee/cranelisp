---
number: 0281
target: /design
filed_by: /dev (int)
filed_at: 2026-06-07
sprint_filed: 76
refers_to: design/arch/facades/int.md §"process_cluster" gap-orchestration (priority_boost_jit/wait_for_inmem pseudocode lines ~648-649, ~1160-1173, ~1206; the "cross-module FQ half" retention note line ~1054), src/scheduler.rs, src/worker.rs::load_fq_dep_module
status: open
---

# Facade trim — `priority_boost_jit` / `wait_for_inmem` priority-codegen half is now dead (FQ auto-load landed without it)

## Issue

FIXME 0268 (FQ auto-loading, spec §8.5.4 / §9.3.6) landed in S76 W3. The facade
(`facades/int.md` §"process_cluster") retained the `priority_boost_jit` +
`wait_for_inmem` gap machinery **specifically for the cross-module-FQ half**:

> "The `priority_boost_jit` + `wait_for_inmem` gap remains for the
> **cross-module FQ** half (lazy-load + wait on a dependency module's macro)."

The B5 disposition (sequenced after 0268, user-decided) was: *if* the 0268
implementation used the priority machinery, keep it; *if not*, delete the dead
subsystem and report the matching facade trim.

**The implementation did NOT need it.** FQ auto-loading (`src/worker.rs::load_fq_dep_module`
+ `handle_fq_autoload_gap` + the Pass-2 `BlockedOnFqModule` path) loads the
dependency module via the **same synchronous `block_for_typecheck` +
worker-loop resume** mechanism that `import` uses. Macro-vs-fn discrimination
stays orchestrator-owned and is implicit in the resume: the dependency's own
Pass-2 codegen JITs its macro clause code, so when the referencing form resumes
the recogniser finds the clause in memory — no speculative per-symbol JIT boost
is ever needed. Functions are not speculatively JIT-pushed.

Consequently the priority-codegen-queue subsystem (already noted dead post-
W-Macro in `src/CLAUDE.md`) was **deleted** in the same change-set:
`PriorityEntry`, `PriorityStatus`, `PriorityWork::BlockingJitCodegen`, the
`SchedulerState.priority_queue` field, `claim_priority_codegen_locked`,
`notify_priority_codegen_complete`, `find_priority_entry_locked`,
`resolve_priority_entry_locked`, `priority_queue_len`, and the
`BlockingJitCodegen` worker-loop arm are all gone. A new
`CompileScheduler::unblock_module` was added (re-queues a module blocked on an
already-loaded/cache-hit dep — the only new scheduler surface).

## Proposed resolution

Trim the facade's gap-orchestration text to match the as-built shape:

1. Drop the `priority_boost_jit(&fq)` + `wait_for_inmem(&fq)` lines from the
   `process_cluster` pseudocode (the `MacroInMem` arm, ~lines 1160-1173) and the
   scheduler-method list (~lines 648-649). They name a subsystem that no longer
   exists.
2. Revise the "cross-module FQ half" retention note (~line 1054) and the
   macro-vs-fn discrimination note (~line 1206): the discrimination is now
   served by the **synchronous dependency typecheck-and-compile** (the dep's own
   codegen JITs its macro clauses), not by a `priority_boost_jit`/`wait_for_inmem`
   force. The "only a macro with missing clause code gets the JIT force"
   statement should become "the dependency module is loaded and compiled
   synchronously (same mechanism as `import`); its own Pass-2 codegen makes the
   macro clause code resident before the referencing form resumes."
3. Add `unblock_module` to the scheduler-method surface in the facade (re-queues
   a waiter blocked on an already-satisfied dep — used by the FQ cache-hit /
   already-loaded path).

The as-built mechanism is documented in `src/CLAUDE.md` §"FQ auto-loading +
just-in-time dependency compile (S76 W3, FIXME 0268 resolved)".

## Operational implication / Context

S76 W3 B5 disposition (user-decided, sequenced after 0268). This is a
facade↔source coherence trim — the source moved (dead subsystem deleted), the
facade text still describes the retained-but-now-unused machinery. Per the
baseline-diff discipline, `/design (int)` owns the facade update; the `int`
`public-api.txt` baseline regen for the scheduler surface change rides the same
change-set as the source deletion (the `unblock_module` add + the
`notify_priority_codegen_complete`/`priority_queue_len` removals + the
`PriorityWork::BlockingJitCodegen` variant removal are public-surface deltas).
