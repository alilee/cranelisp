---
number: 0700
target: /repl
filed_by: /review
filed_at: 2026-07-20
sprint_filed: 114
refers_to: repl/spec.md §15.2.2 + src/main.rs::repl_prologue (restore-notice
  emission) + src/session_v4/lifecycle.rs::startup_restore_notice
status: open
---

# §15.2.2 startup restore notice landed TTY-gated — spec ruling needed

## Severity
Important

## Issue

The W5 change-set (commit `58ac8e46`, FIXME 0674 — deleted) implemented the
§15.2.2 startup restore notice gated on `stdin().is_terminal()`: the notice is
emitted for interactive sessions only, so non-TTY (piped/harness) transcripts
stay byte-identical with their fresh-mode siblings (§10.8 contract; same gate as
`poll_search_index_notice` — a consistent in-repo precedent).

Two consequences the spec does not currently cover:

1. §15.2.2 has **no TTY qualifier** — it says the REPL SHOULD emit the notice
   when startup restores a non-empty backing file, and its implementation
   handoff explicitly asks for the positive guard ("a directory with a
   persisted `user.cl` shows the line"). Under the TTY gate that positive face
   is **unauthorable in the non-TTY e2e harness** — the
   `tests/plan/s114-test-plan.md` §4.1 rider cell ("appears on restore and NOT
   on a fresh dir — pos+neg one cell") cannot be landed as planned.
2. The alternative (emit in non-TTY too) would diverge restore-mode REPL
   transcripts from fresh-mode ones and disturb the output-equivalence
   mode-parity harness.

The /dev flagged this ("/repl+/qa confirm §15.2.2 intent") but 0674 was deleted
with the question recorded only in the commit message — no durable trigger
survived for the wave gate. This FIXME is that trigger.

## Proposed resolution

/repl rules: either (a) scribe the TTY qualifier into §15.2.2 (notice is
interactive chrome, like the R13 prompt-styling deferral §10.8) and re-frame the
guard as a unit-tier obligation (`startup_restore_notice` returning
Some/None is already unit-tested in lifecycle.rs — the residual e2e gap is only
the prologue wiring), or (b) rule the notice mode-uniform and coordinate with
/qa on the output-equivalence carve-out. Then /qa re-bases the §4.1 rider cell.

Implementation note for whichever way it goes (/dev, Minor):
`startup_restore_notice` re-reads and re-parses the backing file rather than
reading the session's own restore record, so under degraded startup (§18.8
FailedForms) the count includes definitions that failed to restore — "resumed N
definitions" can over-count. Counting from the restore record would be both
truer to §15.2.2 ("restored definitions") and single-sourced.

## Context

W5 /review of `58ac8e46`, review priority 5.
