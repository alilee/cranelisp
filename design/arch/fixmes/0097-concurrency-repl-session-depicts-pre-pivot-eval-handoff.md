---
number: 0097
target: /arch
filed_by: /arch
filed_at: 2026-05-01
sprint_filed: 63
refers_to: design/arch/sequences/concurrency-repl-session.mmd, design/arch/facades/int.md §"CompilerSession", design/arch/facades/int.md §"process_form"
status: open
---

# concurrency-repl-session diagram depicts a pre-pivot eval-handoff model

## Issue

`design/arch/sequences/concurrency-repl-session.mmd` shows the REPL handing eval submissions to a worker via `Sched ->> PW: enqueue` and receiving back via a `ResultCh` channel:

```
REPL ->> Sched: EvalSubmission(handoff value)
Sched ->> PW: enqueue
PW ->> PW: typecheck + JIT-compile
PW ->> ResultCh: EvalResult (handoff value)
REPL ->> ResultCh: blocking recv
```

This contradicts the current facade in `design/arch/facades/int.md`:

- `CompilerSession::eval(&mut self, src: &str) -> Result<Option<EvalResult>, CranelispError>` runs **synchronously on the initiator thread**.
- Per `int.md` §"`process_form` — the gap-orchestration retry loop", `eval` directly invokes `process_form` (which composes `frontend::expand` → `frontend::build_ast` → `cranelisp_typecheck::check_form`) and then either calls `insert_symbol` (defns) or compiles a one-shot temp closure on a fresh `JITModule` (trailing expression).
- The scheduler (`CompileScheduler`) is consulted via `wait_for_inmem` / `block_for_macro_codegen` for per-symbol JIT readiness — not as the eval transport.
- There is no `EvalSubmission` work item, no `ResultCh`, and no `repl_check_state` field anywhere in the facade. Snapshot/restore is `ReplSnapshot` per `cranelisp-types` (typecheck rollback).

The diagram's intent — that REPL-thread state is initiator-exclusive and workers reach in only via well-defined handoffs — IS a genuine and currently-true invariant. But the specific transport it shows (eval → submit work item → recv result) is not the architecture's intent; eval runs in-thread and only blocks on scheduler waits when a per-symbol dependency requires it.

## Proposed resolution

Two options for `/arch` to choose between:

1. **Rewrite to depict the current architecture.** The invariant being depicted becomes:

   - `CompilerSession` initiator-only fields (`current_repl_module`, `warnings`, `worker_pool`, `watcher`, `repl_input_active`) are written only by the REPL thread.
   - Workers hold `Arc<SharedState>` (no `&CompilerSession`) per Decision 38; they cannot reach the initiator-only fields.
   - `eval` invokes `process_form` synchronously and parks in the scheduler's `wait_for_inmem` / `block_for_macro_codegen` when a dependency needs the worker pool.
   - `ReplSnapshot` (per `cranelisp-types`) is the snapshot/restore primitive for typecheck-state rollback on eval error.

   Most of the current diagram's structure is preserved (the REPL → Session → Sched → PW chain), but the messages change from `EvalSubmission` / `ResultCh` to `process_form` (synchronous) + scheduler `wait_for_*` (parking).

2. **Retire the diagram** if it duplicates what `concurrency-symbol-table-entry.mmd` already covers (initiator vs worker access discipline). The SymbolTable diagram already exercises the per-symbol mutability + per-thread access pattern at finer grain.

Filing FIXME rather than rewriting unilaterally because the rewrite is structural — different transport, different participants — not the currency sweep this filing was scoped to. `/arch` chooses between (1) and (2) at the next review.

## Operational implication / Context

- Filed during the post-Sprint-64 sequence-diagram currency sweep. The other 10 diagrams aligned cleanly with the current facades after signature updates; this one carries a flow that no facade describes.
- The diagram is referenced from `design/arch/sequences/README.md` (likely) and from skill-level pointers.
- Decision 38 (`SharedState` formal worker-shareable subset) is the canonical statement of the access discipline this diagram tries to illustrate; an updated diagram would cite Decision 38 inline.
