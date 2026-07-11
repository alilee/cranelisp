---
number: 0052
target: /repl
filed_by: /docs
filed_at: 2026-05-01
sprint_filed: 64
refers_to: user/plan-docs.md:480
status: deferred
deferred_at: 2026-07-10
deferred_by: user (S107 close directive)
deferred_reason: >
  Long carry since S64 (past the METHOD §2.4 2×-escalation line). The `/learn`
  watch-mechanism is a user-onboarding REPL FEATURE, not a near-term rendering/
  correctness item, and has re-surfaced in every per-sprint scope scan. User
  gave explicit sign-off at S107 close to SCHEDULE it to the Phase-H release/
  tutorial track and stop re-litigating it each sprint. Not actionable until
  that track opens.
target_sprint: Phase H (release-prep — user onboarding / tutorial track)
migrated_from_inline: true
re_targeted_by: /qa (S81 W-H)
re_targeted_reason: REPL /learn feature, not a /qa test — owned by /repl (feature) + /docs (tutorial)
---

# 0052 — `/learn` system requires REPL feature planning (U0.2)

## Issue

The `/learn` system requires a REPL feature (watch mechanism, trigger evaluation, progress tracking). This is not just documentation content — it's REPL implementation work. `/qa` needs to plan this as a Ring 0 deliverable so the tutorial is available from the first release.

Companion finding: `/arch` updates `design/arch/roadmap.md` to include U0.1 (the parallel architecture finding). This FIXME tracks the U0.2 (qa-side) request.

## Source location

`user/plan-docs.md:480` (HTML-comment FIXME at end of `/docs` Sprint 0 findings).

## Context

`/docs` Sprint 0 surfaced two findings while authoring tutorial content: (1) architecture work (U0.1) and (2) REPL feature work for `/learn` (U0.2). This entry tracks U0.2.

## Proposed resolution

`/qa` adds U0.2 to `tests/plan/ring0.md` as a Ring 0 deliverable: planning + tests for the `/learn` REPL feature (watch mechanism, trigger evaluation, progress tracking).
