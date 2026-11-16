---
id: ACT-1051
title: The idle unreadable-save lock test races the file-change event
status: open
priority: required
from: qa
to: test
sprint: 123
filed_at: 2026-11-16
refers_to:
  - tests/repl_persist.rs::watch_idle_unreadable_save_locks_before_the_next_definition_overwrites_it
  - design/int/repl-lifecycle.md
  - repl/spec/14-file-watching.md
  - tests/plan/s123-evidence-delta.md
---

## Observation

`watch_idle_unreadable_save_locks_before_the_next_definition_overwrites_it`
failed once in the S123 W3 full suite (`.local/s123-w3/qa-full-suite.log`) and
passed 5 of 5 isolated reruns.

- In the failing run, the file-change event for the test's save arrived after
  the REPL had processed the next input line. The definition was accepted
  with the "changed on disk" warning, the user's bytes were kept, and the lock
  was reported one turn late. That lateness is the limit
  [`design/int/repl-lifecycle.md` §1.2](../../design/int/repl-lifecycle.md#12-poll-and-reload)
  accepts.
- The harness's write step sends the next line without waiting for the event,
  so the "idle save" the test assumes is not guaranteed to happen.
- Not a W3 regression: W3 changed neither the REPL poll nor that harness step.

## Attribution

Provisional, by `qa`: `test`, so the harness waits for the event before
sending the next line. If instead
[REPL spec §14.2](../../repl/spec/14-file-watching.md#142-eager-recompilation)
must reload however late the event arrives, the owner is `design`(int), and
`spec` frames that for the user.

**Falsifier:** the test fails on its own, or a harness that waits for the
event still accepts the definition.
