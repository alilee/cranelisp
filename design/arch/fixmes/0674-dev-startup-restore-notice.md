---
number: 0674
target: /dev
filed_by: /repl
filed_at: 2026-07-19
sprint_filed: 113
refers_to: repl/spec.md §15.2.2 (Startup Restore Notice, spec landed S113);
  src/ session-restore seam (session_v4 lifecycle / repl boot); routed from
  FIXME 0657 action 2
status: open
---

# Implement the startup restore notice (spec'd in repl/spec.md §15.2.2)

`repl/spec.md §15.2.2` (landed S113) specifies a boot-time R6-metadata line the
REPL SHOULD emit when startup restores a **non-empty** backing file:

```
; resumed 7 definitions from user.cl
user>
```

- Count = number of restored **definitions** (§15.7 persisted forms), not
  transient expressions.
- MUST be **suppressed when the backing file is absent or empty** — a first
  session in an empty directory reaches the prompt with no extra output
  (preserves §6.2 first-session experience; keeps fresh-dir transcripts
  byte-identical).
- Startup-only chrome; never persisted, never part of a value/definition
  response.

This is REPL boot-time runtime output (src/ session-restore path), not a `repl/`
config change — hence the /dev handoff. `/repl` owns the wording + count
semantics + empty-suppression rule (above); `/dev` implements at the restore
seam. Land the guard both ways: a directory with a persisted `user.cl` shows the
line; an empty directory shows nothing. Closure: implementation + guard land →
delete this file (or /qa pins it and it becomes the record).
