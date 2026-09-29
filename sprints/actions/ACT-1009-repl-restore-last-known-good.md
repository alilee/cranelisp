---
id: ACT-1009
title: Add explicit REPL restoration of a module's last known good state
status: deferred
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
