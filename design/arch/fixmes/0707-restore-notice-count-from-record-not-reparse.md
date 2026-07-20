---
number: 0707
target: /dev
filed_by: /repl
filed_at: 2026-07-20
sprint_filed: 114
refers_to: src/session_v4/lifecycle.rs::startup_restore_notice + repl/spec.md §15.2.2
status: open
---

# Startup restore notice counts by re-parsing the backing file, not the restore record

## Severity
Minor

## Issue

Carried forward from the 0700 review (now ruled/deleted — §15.2.2 TTY qualifier
scribed this sprint). The `; resumed N definition(s) from user.cl` notice derives
`N` by **re-reading and re-parsing the backing `user.cl`** rather than by counting
the definitions the session **actually restored**. Under a **degraded startup**
(§18.8 `FailedForms` — a persisted definition that no longer type-checks against a
changed dependency), the re-parse counts forms that **failed to restore**, so
`resumed N definitions` **over-counts**: it reports forms present in the file, not
forms live in the session. This contradicts §15.2.2's "the number of restored
**definitions**."

Counting from the restore record is both truer to the spec wording and
single-sourced (one authority for "what restored", consumed by both the notice and
the session state).

## Proposed resolution

`/dev` (src/): change `startup_restore_notice` to take its count from the session's
own restore-result record (the successfully-restored definition set), not a fresh
re-parse of the backing file. Unit-pin at the `lifecycle.rs` seam: a restore record
carrying K succeeded + M failed forms yields `resumed K definition(s)`, never K+M.
The notice stays TTY-gated (§15.2.2, S114 ruling) — this is a count-source fix, not
an emission-mode change.

## Context

`/repl` S114 Phase-6a assessment. The §15.2.2 spec text now names this as the
count-source obligation (FIXME 0707 cited inline).
