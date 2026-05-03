---
number: 0114
target: /arch
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: CLAUDE.md (root, §"Annotation Convention" table), sprints/reimplementation.md (ring-planning model)
status: open
---

# Retire ring axis from root `CLAUDE.md` annotation convention

## Issue

User decision (Sprint 64): rings are retired as a project-wide planning axis. Sprint is the sole scheduling axis going forward.

Root `CLAUDE.md` §"Annotation Convention" table currently reads:

```
| `[R{N} S{M}]` | Not yet tested; targeted for Ring N, Sprint M |
| `[R{N} S{M} — tests/file::test_name IGNORED]` | Test exists but is `#[ignore]`'d (known gap) |
```

Should be updated to:

```
| `[S{M}]` | Not yet tested; scheduled for sprint M |
| `[S{M} — tests/file::test_name IGNORED]` | Test exists but is `#[ignore]`'d (known gap) |
```

## Proposed resolution

`/arch` updates the annotation-convention table in root `CLAUDE.md`. Add a one-line note explaining the ring axis was retired in Sprint 64 (so future readers encountering pre-S64 `[R4 S10]` annotations in archived docs know what they meant).

Coordinate with FIXME 0113 (`/spec` removes ring annotations from spec headings) — the two should land together so the convention and the corpus are consistent.

Adjacent: `sprints/reimplementation.md` documents the ring-based phasing model (Phase C–G are Ring 0–4). That doc is `/sprint`'s territory; if the ring planning model is fully retired, `/sprint` should evaluate whether to archive `reimplementation.md` or annotate it as historical. Not blocking; flag for `/sprint`'s next review.

## Operational implication / Context

`/qa` has already updated:
- `tests/plan/PLAN.md` (Position B notation: `[S{M}]`-only)
- `tests/CLAUDE.md` (helper table: dropped "Available from Ring" column)
- `.claude/commands/qa.md` (skill def: §"Test plan obligation" annotation list)

Root `CLAUDE.md` is the canonical convention source; the rest of the project should derive from it. Once root updates, the whole annotation vocabulary is internally consistent.
