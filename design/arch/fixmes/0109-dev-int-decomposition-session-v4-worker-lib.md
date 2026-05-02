---
number: 0109
target: /dev
filed_by: /design (int)
filed_at: 2026-05-02
sprint_filed: 64
refers_to: design/int/int.md §3 (current-state per-file table) + §16 (open /dev work), audits/src-20260423.md (F1, F2, F5, F6 + recommendations 1, 2, 4), src/session_v4.rs, src/worker.rs, src/session.rs, src/lib.rs
status: open
---

# int decomposition: split `session_v4.rs` + `worker.rs`; delete `session.rs`; narrow `lib.rs`

## Issue

`audits/src-20260423.md` (Sprint 62, predates Decisions 38/39/40/41/42) reported four structural-debt findings against `src/`:

- **F1 (HIGH)** — `session_v4.rs` is a god-file (5,417 LOC; 149 fns; 23 ≥60-line). Mixed authority: REPL UX, eval, dep registration, watcher, introspection, trace setup, worker lifecycle, link control, large in-file tests.
- **F2 (HIGH)** — `worker.rs` is a second god-file (5,041 LOC; 33 ≥60-line). Mirrors logic across paths (`compile_macro_clause_with_state` / `_inline`, `collect_jit_setup_public` / `inline_jit_codegen_for_module`); functionally converged but not structurally so.
- **F5 (MEDIUM-HIGH)** — `src/lib.rs` exports almost the whole kitchen sink (18 public modules); not a thin facade.
- **F6 (MEDIUM)** — Legacy/transitional structure visible: `session.rs` (543 LOC of v3) lingers next to `session_v4.rs`.

The audit's recommendations 1, 2, and 4 cover this work. None has been filed as a numbered FIXME because the work is mechanical and well-scoped. This FIXME consolidates the four items into one tracker so the work doesn't drift.

The S64 FIXMEs (0098, 0099, 0100, 0103, 0104, 0107, 0108) all land code into int but do not themselves close F1/F2/F5/F6. Decomposition is best sequenced AFTER the S64 FIXMEs land — the post-FIXME shape is what gets decomposed (otherwise the decomposition has to be redone as the FIXMEs reshape the affected files).

## Proposed resolution

Sequenced as four independent waves; each is mechanical and crate-narrow.

**Wave A — Delete `src/session.rs` (F6)**:

The v3 session type has no callers in the v4 pipeline. Verify with `grep -r "use crate::session::" src/ tests/` (expect empty after migration), then delete. Update `src/lib.rs` to remove the `pub mod session;` line.

If any callers turn out to remain, migrate them to `session_v4::CompilerSession` first (no API design — straight rewrite per pipeline-v4) then delete.

**Wave B — Narrow `src/lib.rs` (F5 + audit recommendation 4)**:

Current 18 public modules → facade-shape exports. Per `design/arch/facades/int.md`, the public surface is:
- `CompilerSession` (re-exported from `session_v4`)
- Worker loops (`priority_worker_loop`, `nice_worker_loop`)
- `Code` (re-exported from `cranelisp-backend` per Decision 41)
- Scheduler types (`CompileScheduler`, `PriorityWork`, `NiceWork`, `SchedulerError`)
- `ObjectCache` + `CacheLookupResult` + `CacheError`
- `LineEditor`, `InputState`, `ContinuationState`, `ReplError`
- `FileChangeEvent`
- CLI types (`Action`, `ProjectTarget`, `SessionSettings`, `CliError`)
- `EvalResult`, `EvalValue`, `HeapRetention`, `CommandResult`, `SlashCommand`
- `SymbolInfo`, `SymbolDescription`, `SymbolCategory`
- `Introspection`
- The cranelisp-types re-export wall per facade §"Re-exports"

Sweep test imports against this set; demote unused-publicly modules to `pub(crate)`.

**Wave C — Extract `process_form` to its own module (audit recommendation 1, plus the design's own observation)**:

`process_form` is the gap-orchestration crossing point — distinct authority from the priority worker loop. Extract from `worker.rs` to `src/process_form.rs` (or `worker::process_form` as a free function with the worker loop calling it) per `facades/int.md` §"`process_form` — the gap-orchestration retry loop". This is the simplest decomposition increment; it isolates one well-bounded responsibility before tackling the larger god-file split.

**Wave D — Decompose `session_v4.rs` + `worker.rs` (F1 + F2 + audit recommendation 1)**:

Per `design/int/int.md` §3.3 module map (target shape):

| Module | Responsibility |
|---|---|
| `src/session_v4.rs` (or `session_v4/core.rs`) | `CompilerSession` struct + lifecycle; `SharedState` construction; `Drop`; worker pool spawn + join |
| `src/scheduler.rs` | `CompileScheduler` (already extracted) |
| `src/worker.rs` | `priority_worker_loop` + `nice_worker_loop`; per-form processing on `&SharedState` |
| `src/process_form.rs` | The shared form chain (Wave C) |
| `src/eval.rs` | REPL eval — wraps `process_form` + appends to `defn_order` for defining forms; trampolines for expression forms |
| `src/repl.rs` (or `session_v4/repl.rs`) | Slash-command dispatch, prompt formatting, banner, line editor wrapper |
| `src/save.rs` | `regenerate_backing_file` (already extracted) |
| `src/cache.rs` | `ObjectCache` facade |

The extraction sequence within Wave D should be: `eval.rs` first (clean module-level boundary), then `repl.rs` (slash commands + prompt + line editor — also clean boundary), leaving the residual `session_v4.rs` as `CompilerSession` lifecycle + worker-pool plumbing only.

For `worker.rs`: collapse the mirrored paths (`_with_state` / `_inline`, `collect_jit_setup_public` / `inline_jit_codegen_for_module`) into single implementations. The post-Decision-41 collapse (the `worker.rs:2860–3018` post-loop machinery folds into the per-symbol call-site loop) is bundled with FIXME 0098 Phase 4 — that closure removes ~150 LOC and clarifies the surrounding code.

## Sequencing notes

- Sequence after FIXMEs 0098 + 0103 + 0108 land. Those reshape the files being decomposed; doing decomposition first means redoing it.
- Wave A and Wave B can land first (independent of the S64 FIXMEs).
- Wave C is independent of waves D's larger split and can land at any point.
- Wave D is the largest chunk; consider splitting across multiple sprints.
- All four waves are int-narrow `/dev` work; no cross-skill coordination needed.

## Operational implication / Context

This is the structural-debt cleanup the audit identified eight months ago. The S64 Decision sweep made it possible to do without redoing — once the S64 FIXMEs land, the post-FIXME shape is stable enough to decompose against.

The two god-files together account for 10,458 LOC (49.6% of `src/`). Decomposition into the §3.3 module map produces ~8 smaller files in the 200–800 LOC range, each with single-responsibility ownership. This makes future change-of-shape work (adding a slash command, reshaping the gap protocol, adding an observer sink) bounded — the change touches one or two files instead of cascading through 5,000-LOC monoliths.

The decomposition is not load-bearing for any feature; it is purely maintainability/readability work. But it is the largest remaining structural-debt item in the workspace per the audit set, and leaving it indefinitely deferred risks the audit becoming stale (further accretion making the recommendations less applicable).
