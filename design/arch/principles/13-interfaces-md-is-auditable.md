---
number: 13
title: `interfaces.md` is auditable
---

# Principle 13 — `interfaces.md` is auditable

**Statement.** The design book must be validated against architectural principles, not merely documented. Structural identicals (duplicate types, adapter functions, parallel pipeline entry points) in `interfaces.md` are architectural violations — not features to document.

**Rationale.** A design doc that records "what is" without checking "what should be" enshrines defects as legitimate architecture. `interfaces.md` enshrined the `TopLevel` / `ReplInput` duplication as legitimate architecture for 25 sprints before Sprint 26 surfaced the cost.

**Consequence.** Every gate review (Phase 2 architecture review per the methodology) includes a coherence check: read the active boundary types against principles 1–12. Violations surfaced are sprint-scope items, not deferred documentation chores. *(Sprint origin: Sprint 26.)*
