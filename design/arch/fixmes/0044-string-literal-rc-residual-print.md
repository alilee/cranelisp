---
number: 0044
target: /backend
filed_by: /review
filed_at: 2026-05-01
sprint_filed: 64
refers_to: design/backend/ring2-rc.md §10, design/review/sprint57-wave3-review.md S-3, crates/cranelisp-runtime/src/io.rs:28, design/review/sprint58-wave6-review.md (one-deferral-permitted note at io.rs:28)
status: open
migrated_from_inline: true
---

# 0044 — String-literal RC residual through `print` (Sprint 58 Wave 3 carry)

## Issue

The string-literal lifetime through `print` does not fully reclaim. REPL-observed: `(print "a")` through the trampoline leaks the string allocation. Root cause hypothesis: codegen emits string-literal heap alloc for argument to Effect thunk construction but the thunk's consume-on-call discipline isn't propagated to the captured string.

`design/backend/ring2-rc.md §10` is PRESCRIPTIVE for the fix. Per `/arch` Sprint 58 review condition 6, this MUST land in Wave 3 alongside other RC work, OR be deferred with explicit rationale and a named regression-test symptom for `/qa`. Disposition selected at S58: fix in Wave 3 (one-deferral-permitted held in reserve). Sprint 58 Wave 6 review noted the FIXME is still in `io.rs:28` under the one-deferral-permitted policy.

## Source location

`design/backend/ring2-rc.md §10` (the PRESCRIPTIVE addendum); referenced by `crates/cranelisp-runtime/src/io.rs:28`, `design/review/sprint57-wave3-review.md` S-3, and `design/review/sprint58-wave6-review.md` Focus 7 audit (one-deferral-permitted accounting).

## Context

Sprint 57 Wave 3 closed the trampoline-internal IO-node leak via §3.5.4 (`current_is_fresh` discipline + `dec_shallow_io`); this string-literal leak is in a different code path. The `print` extern at `platforms/stdio/src/lib.rs:18-25` follows the capture-RC pattern and incs the string's RC, but the matching dec at thunk-drop is missing.

## Proposed resolution

`/backend` lands the §10 fix per `ring2-rc.md`. If implementation surfaces unexpected scope, may invoke one-deferral-permitted again with explicit rationale + regression-test symptom — but per S58 condition 6 the deferral count is now exhausted.
