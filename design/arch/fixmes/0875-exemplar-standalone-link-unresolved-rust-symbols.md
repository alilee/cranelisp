---
number: 0875
target: /qa
filed_by: /sprint
filed_at: 2026-07-25
sprint_filed: 118
refers_to: sprints/archive/sprint-117.md §Outcome "Deferred";
  exemplar/
status: open
---

# Exemplar standalone Link parity unverifiable — platform archive has unresolved Rust symbols

S117 Phase 6b could not verify the exemplar's standalone `--link` parity:
producing the executable fails **before** link-parity comparison because the
platform archive carries unresolved Rust symbols. The S117 close record parked
this in a deferral bullet with no FIXME; this file makes it durable.

No attribution exists yet — the visible error (unresolved symbols at archive
link time) may belong to exe-bundle, platform, or the build of the platform
staticlib itself. Per root `CLAUDE.md` §Cross-skill defect handoff, a minimal
repro is required before any cross-skill fix dispatch: `/qa` attributes (or
routes to `/testing` for reduction) and the repro — not the symptom — names
the owner.

Scheduling: S118 if adjacent to Track B's linked-startup work (0745 touches
the same link path); otherwise S119 with rationale.
