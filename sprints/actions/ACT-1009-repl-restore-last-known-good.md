---
id: ACT-1009
title: Add explicit REPL restoration of a module's last known good state
status: open
priority: advisory
from: sprint
to: spec
sprint: 122
filed_at: 2026-09-29
refers_to:
  - repl/spec/14-file-watching.md
  - repl/spec/15-session-persistence.md
  - src/repl/commands.rs
  - src/session_v4/lifecycle.rs
---

## Approved direction

The user deferred a REPL function to reset a module to its last known good
state: “later we'll add a reset to last known good repl function.” Schedule
in a future sprint; no particular sprint or command spelling is approved.

The current policy preserves a changed file when checking fails, reports its
errors, and locks the module until a successful check. This action adds an
explicit recovery choice later; it must not turn a failed reload into an
automatic overwrite or silently make the existing `/reset` restore files.

## Future scope

`spec` captures the user-visible restoration contract before implementation:
what constitutes the last known good state, what happens to the failed saved
edit, and how restoration affects dependent modules. The command spelling,
snapshot representation and treatment of unsaved editor buffers are unsettled.
`design` then selects a proportionate realization and QA allocates recovery
and edit-preservation evidence.

## Completion

An explicit restoration operation has an approved contract, documented
behavior and tests showing its recovery outcome and treatment of the failed
edit. No implementation of this capability is part of the S122 failed-reload
protection correction.

## S125 disposition — 2026-11-27

**Open, awaiting user ruling:**
[S125-Q11](../../spec/appendix-d-open-questions.md#s125-q11-what-does-explicit-restoration-of-a-modules-last-known-good-state-restore).

Verified first against the current `refers_to` specifications: REPL
§14.2 and §14.4–§14.6, §15.2–§15.6, together with §18 and language §8.10.
They define current-source reload, failed-edit preservation and the session
lock, not an explicit restoration operation. The S125 authored-entry and
containment changes do not supply that missing contract. Opened
`src/repl/commands.rs` (module-load failure handling) and
`src/session_v4/lifecycle.rs` (`install_fresh_generation`, `displace_table`
and `reset_module_session_state`): retained code and rebuild references are
implementation mechanisms, not authority for a user recovery operation.

The question separates the recovery boundary (one module or a compatible
program checkpoint), treatment of the failed saved edit and unsaved buffers,
dependents, unavailable snapshots and failed recovery. Runtime-only recovery
is presented as requiring an explicit change to current policy. No command
spelling, snapshot representation or normative change is selected. `sprint`
obtains the ruling and routes `design` on `src/` and QA evidence work. This
action stays open through its stated completion; no new deferral is recorded.
