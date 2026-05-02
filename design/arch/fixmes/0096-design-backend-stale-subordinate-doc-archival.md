---
number: 0096
target: /sprint
filed_by: /design
filed_at: 2026-05-01
sprint_filed: 64
refers_to: design/backend/backend.md §8, design/backend/cache-repl-loads-triage.md, design/backend/defect-8-repro-notes.md, design/backend/defects-456-reduction.md, design/backend/slice-4-21-hello-io-investigation.md, design/backend/io-trampoline-trace.md
status: open
---

# Schedule a backend stale-doc archival pass

## Issue

Six subordinate docs under `design/backend/` are incident-debug or pivot residue that no longer reflects live design intent. They are documented as **stale-as-live-design** in `design/backend/backend.md` §8 (the master) but remain at the top level of `design/backend/`, where a contributor scanning the directory cannot tell which docs are live.

Stale-as-live-design list:

1. `cache-repl-loads-triage.md` — post-Decision-37 superseded; live design lands in `module-caching.md`. Reference for history only.
2. `defect-8-repro-notes.md` — incident-debug residue; keep as cross-skill repro example.
3. `defects-456-reduction.md` — Sprint 59 W1 incident-debug residue.
4. `slice-4-21-hello-io-investigation.md` — Sprint 61 era closure double-free reduction; keep for repro.
5. `io-trampoline-trace.md` — Wave 1 IO-scheduling debug residue.
6. (Partially) `sprint51-fqtypename-cache.md`, `ast-sourced-codegen.md` — Sprint 51 / Sprint 55 era; partially superseded by Decisions 34 / 25 respectively.

The §8 master table flags each, but the directory listing does not. New contributors must read the master to know what's live — workable, but adds friction.

## Proposed resolution

`/sprint` schedules a 30-minute housekeeping pass:

1. Create `design/backend/archive/` (parallel to the `design/arch/archive/` precedent).
2. `git mv` the six stale docs into `archive/`.
3. Author `design/backend/archive/README.md` indexing what each captured (one line per doc: original sprint, what it documented, why archived).
4. Update `design/backend/backend.md` §8 cross-references to point to `archive/{name}.md` for the moved docs.

This mirrors the `design/arch/archive/` pattern already established in S63 substance-scoping.

The work is mechanical — no design judgement involved beyond the staleness flagging already done in §8. A `/dev`-narrow `/design` invocation can execute it; `/sprint` decides which sprint to land it in.

## Operational implication / Context

This is housekeeping, not blocking. The master `backend.md` §8 already carries the staleness flags; readers who consult the master have the right information. Archival makes the directory listing self-explanatory.

Suggested sprint: when the broader S64 substance-scoping continues with backend-specific cleanup, OR as a small filler item in a sprint where backend-narrow `/design` time is otherwise underutilised. No urgency.

Cost: 30 min, mostly `git mv` + a one-page README.
