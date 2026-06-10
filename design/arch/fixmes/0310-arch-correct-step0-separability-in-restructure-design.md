---
number: 0310
target: /arch
filed_by: /sprint
filed_at: 2026-06-10
sprint_filed: 77
refers_to: design/int/s77-int-restructure.md §5 (Step 0) + §2.3 (publisher-side split), src/worker.rs:4279/4289 (handle_typecheck_work_shared single read site), src/session_v4.rs:2233 (republish_module_sexps_from_symbol_table — H5 fix), src/scheduler.rs:1351 (try_unblock_locked requeue)
status: open
---

# Correct the design doc: Step 0 (sexps-onto-packet) is NOT cleanly separable

## Issue

`design/int/s77-int-restructure.md §5` classifies Step 0 (move `module_sexps`
onto the work packet) as LOW-risk / build-green / separable ("the maps still
exist for the dep half until step 2"). A source-grounded /dev separability check
(S77, zero edits) DISPROVED this:

- The publisher-side split (entry-module sexps vs dep sexps, §2.3) does NOT hold
  on the **reader/resume** side. All modules — entry, dep, resumed — flow through
  ONE `handle_typecheck_work_shared` read site (`worker.rs:4289`); the work item
  is a bare `ModuleFullPath` with no sexps; resume requeue (`try_unblock_locked`)
  carries no sexps.
- The entry/REPL module's sexps (payload #1) are read on the **resume** path, not
  just at first processing, kept alive deliberately by the H5 fix's unconditional
  `republish_module_sexps_from_symbol_table(&caller)` (`session_v4.rs:2233`).
- Removing payload #1 from the map therefore breaks the H5 fix and forces editing
  the block→resume kernel (`eval_in_flight`/republish/`try_unblock_locked`) — the
  VERY-HIGH-risk S78 Steps 1+2. Step 0 is not a standalone de-risker.

## Proposed resolution

In the S78 restructure design pass, correct §5 (Step 0 risk classification) +
§2.3 (publisher-side vs reader-side split): fold "Step 0" into the indivisible
Steps 1+2 span (the in-call-stack drop-and-retry-from-top resume model that
deletes `suspend_states` + the cross-thread requeue is the ONLY coherent way to
relocate the entry-module sexps off the shared map). The restructure is one
indivisible change, per §7's risk note (which §5 contradicted).

## Operational implication / Context

S78 int-restructure planning input. The design doc returns for user review
before S78 /dev; this correction lands in that review.
