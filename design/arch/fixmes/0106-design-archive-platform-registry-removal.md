---
number: 0106
target: /design
filed_by: /design (platform)
filed_at: 2026-05-02
sprint_filed: 64
refers_to: design/platform/platform-registry-removal.md, design/platform/platform.md §8 + §11, design/arch/decisions/0027-g8-lands-before-g9.md, design/arch/decisions/0026-platform-fn-pointer-on-moduleentry-def.md (legacy decisions index)
status: open
---

# Archive `platform-registry-removal.md` post-deletion

## Issue

`design/platform/platform-registry-removal.md` (~384 lines) documents the Sprint 57 G8 deletion of `PlatformRegistry` and the Sprint 58 cache-restore addendum. Both pieces of work have landed:

- `PlatformRegistry` is deleted from `int` (`src/platform_registry.rs` no longer exists).
- Cache restore via `Sprint 58 Phase 5` is operational.
- Lessons folded into Decisions 26, 27, 38; into the post-S64 facade (`facades/platform.md`); and into this directory's master `platform.md` §8.

The doc remains at the top level of `design/platform/`, where a contributor scanning the directory cannot tell which docs are live and which are historical. This mirrors the situation FIXME 0096 addressed for `design/backend/`.

## Proposed resolution

`/design` (platform) executes a 30-minute housekeeping pass:

1. Create `design/platform/archive/` (parallel to the `design/arch/archive/` and `design/backend/archive/` precedents).
2. `git mv design/platform/platform-registry-removal.md design/platform/archive/platform-registry-removal.md`.
3. Author `design/platform/archive/README.md` indexing what each captured file documented (one-liner per doc: original sprint, what it documented, why archived).
4. Update `design/platform/platform.md` §11 cross-reference to point to the new path.
5. Update `design/platform/platform-dlls.md` cross-reference (currently cites `platform-registry-removal.md §A2/§A4` for cache restore).

Mechanical work — no design judgement involved beyond the staleness flagging done in `platform.md` §11.

## Operational implication / Context

This is housekeeping, not blocking. The master `platform.md` §11 already flags the doc as archive-bound; readers who consult the master have the right information. Archival makes the directory listing self-explanatory.

Suggested sprint: bundle with the FIXME 0104 (PlatformError) sprint that will need to refresh `platform-dlls.md` anyway, OR as a small filler in any sprint with low platform load. No urgency.

Cost: 30 min, mostly `git mv` + a one-page README.
