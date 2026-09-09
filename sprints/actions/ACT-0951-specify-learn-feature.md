---
id: ACT-0951
title: Specify the complete `/learn` feature before designing or implementing its tutorial engine
status: open
priority: required
from: sprint
to: spec
sprint: 121
filed_at: 2026-09-01
refers_to:
  - repl/spec.md
  - design/arch/fixmes/0052-docs-learn-system-repl-feature.md
  - user/CLAUDE.md
---

## Request

The user ruled during Sprint 121 Phase 3 that the project must not guess the
behaviour of `/learn`. The feature remains desirable, but its live authority
does not define enough behavior to design or implement a tutorial engine.
Sprint 121 therefore removes `/learn` from its C6 implementation package and
does not retain a provisional command contract in `repl/spec.md`.

A retired Sprint-0 documentation plan described a Socratic tutorial, a
`(section, prompt, trigger, answer)` content shape, value/type/name/structural
triggers, local progress and answer/skip commands. That material is useful
provenance only. It was removed from the live document set and MUST NOT be
treated as authority or restored without fresh user arbitration.

Before `/learn` returns to an implementation sprint, `spec` must frame the
remaining product choices for the user and then establish one complete,
coherent feature contract in `repl/spec.md`. At minimum it must define:

1. command grammar, entry, resume and topic/section routing;
2. the curriculum and step schema, stable identifiers, ordering and versioning;
3. the tutorial state machine and the effect of ordinary evaluation and every
   tutorial command in each state;
4. exact trigger semantics for each supported evidence kind, including value
   equality, type equivalence, definition/name scope and structural matching;
5. retry, answer, skip, completion, reset and navigation behavior;
6. progress identity, persistence boundary, atomicity, corruption handling and
   curriculum-version migration;
7. unknown-topic, compile-error, runtime-error and unavailable-content behavior;
8. output/display requirements and interaction with other REPL commands;
9. the engine/content ownership boundary and packaging needed for deterministic,
   offline availability; and
10. normative acceptance statements that `qa` can classify and allocate before
    tests or implementation are authored.

This action is not permission to implement the feature, author its curriculum
or infer decisions from the retired plan. It returns at the scope gate of the
future sprint that proposes `/learn`.

## Completion evidence

- The user has ruled every material product choice framed by `spec`.
- `repl/spec.md` contains a complete, internally consistent `/learn` contract
  covering items 1–10, with no open behavior hidden in implementation notes.
- `qa` has reviewed the contract for buildability, observability and acceptance
  allocation; architecture and C6 design can consume it without inventing
  user-visible behavior.
- The owning sprint explicitly approves `/learn` implementation scope after the
  specification gate.
