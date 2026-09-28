---
id: ACT-0998
title: Decide whether a failed watcher reload may lose the external edit
status: open
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-27
refers_to:
  - repl/spec/14-file-watching.md
  - repl/spec/15-session-persistence.md
  - design/int/session-persistence.md
  - tests/repl_persist.rs
---

Face 1, structural type edits on reload, is realized under REPL §14.8. Its
record is the plan's
[restart-boundary final adequacy](../../tests/plan/s122-evidence-delta.md#restart-boundary--final-adequacy-2026-09-29).
Face 2 remains.

## Face 2 — a failed reload loses the external edit (intake)

**User impact.** A user saves a file edit that fails to reload, then enters an
accepted definition at the REPL before fixing the file. That turn rewrites the
file from the last published session state, and the unaccepted edit is gone
from disk. The only notice is the earlier `[errors: …]`.

**Current behaviour: the edit is always lost.** The same inputs were run
before and after the S122 P3/P5 correction:

| Failed reload, no earlier turn | Before | After |
|---|---|---|
| Face 1 refusal (p2a) | kept | lost |
| Type error (p2b) | kept | lost |
| Parse error (p2c) | lost | lost |

- Before: `.local/s122-persistence-residual-test-scratch/probe-run1.log`.
  `probe-run2.log` adds that, after an earlier definition turn, a face 1
  refusal already lost the edit and a type error kept it.
- After: `.local/s122-persistence-records-dev-scratch/p2-observed.log`,
  binary `d9a1ebd4…2ec1`, with the archived P2 section run unchanged. Its
  inputs are identical to the pre-fix cells.
- The hypothesis held: the earlier "kept" outcomes came from records written
  before any commit decision, and from a declaration with no record.
- The loss now follows
  [design §2.4.4](../../design/int/session-persistence.md#244-known-limits).
  It is uniform and predictable, and it destroys the edit.
- This is a diagnostic observation. It selects no policy and makes neither
  outcome a requirement.

**Requirement.** §14.8 settles retention for a structural failure only:
p2a's shape is now RB-3. For type-error and parse-error reloads (p2b, p2c)
the requirement is silent. §15.1 says the file reflects "the last
successfully compiled state". §14.5 says a failed reload leaves the module's
state cleared. §15.2.3's retention applies only to startup. No RED can be
written until `spec` records the user's answer. If the ruling requires
retention, the design extends it to these failures and `test` writes a RED
from p2b and p2c. If the ruling accepts the loss, `spec` states it and the
loss is no longer a defect.

## Completion

Resolved by the user's disposition: either a RED is allocated, or `spec`
records the loss as accepted.
