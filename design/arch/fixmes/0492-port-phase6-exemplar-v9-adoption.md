---
number: 0492
target: /port
filed_by: /sprint
filed_at: 2026-07-01
sprint_filed: 97
refers_to: exemplar/main.cl, exemplar/web.cl, exemplar/serve.cl, tests/fixtures/web_fanout/ (the v9-adopted reference), tests/launch_grid_corrupt.rs (bug #2 — see FIXME 0486)
status: open
---

# Phase-6 (carried): exemplar adopts the v9 ctx-vtable handle model + marquee replay

## Issue

S97 delivered the v9 ctx-vtable handle model (opaque `Connection [fd]`, ctx-vtable poll-fn skeleton); the lighter `tests/fixtures/web_fanout/` reference was v9-adopted during the cutover, but the **exemplar** (`exemplar/web.cl`/`serve.cl`/`main.cl`) Phase-6 adoption + the marquee "server with no spawn" replay were not executed (S97 closed before Phase 6).

## Proposed resolution

/port (next-sprint Phase 6): reshape the exemplar to the v9 handle model (opaque `Connection`, slim leaf calls, `web.cl`/`serve.cl` split), replay the marquee fan-out green. **BLOCKED on FIXME 0486 / bug #2** — the exemplar's heavy Sudoku handler double-frees under concurrent launch (the launched-send-terminal arg-lifetime UAF; deterministic guard `tests/launch_grid_corrupt.rs` RED, `exemplar_web` quarantined). The exemplar's full concurrent replay can only go green once 0486's arg-lifetime fix lands. Until then, adopt the v9 *shape* and keep the heavy-handler concurrent path guarded/quarantined per 0486.
