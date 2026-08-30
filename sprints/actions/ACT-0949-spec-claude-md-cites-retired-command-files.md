---
id: ACT-0949
title: Repoint spec/CLAUDE.md from the retired command files to the role contracts
status: open
priority: advisory
from: sprint
to: spec
sprint: 120
filed_at: 2026-08-30
refers_to:
  - spec/CLAUDE.md
---

## Request

The 2026-08-30 wiring change retired `.claude/commands/`. Two references in
`spec/CLAUDE.md` point at it:

- `:12` — the scribe rule, "This mirrors `.claude/commands/spec.md`." The mirror
  is now `.agents/skills/spec/SKILL.md`, whose "Decide and proceed" section makes
  the same distinction: the form of the record is `spec`'s, the content of an
  obligation never is. Worth checking the two still say the same thing before
  repointing, because the package contract is generic and `spec` here is a
  scribe against a user arbiter — root `CLAUDE.md` §Roles carries that.
- `:75` — the traceability-band ownership rule cites `.claude/commands/qa.md`
  §Boundary. That boundary now sits in root `CLAUDE.md` §Requirements/Test
  Traceability, which states the band is `qa`'s to maintain in place with no
  filing cycle back to `spec`.

Neither is load-bearing for behaviour; both are stale citations in a live
document, which is the class root `CLAUDE.md` §Assurance calls a claim that has
decayed.

Note also that `spec` now owns `repl/spec.md` as a surface specification, per the
role declaration — `spec/CLAUDE.md` may want to say so, since the REPL experience
spec previously had its own role.

## Completion evidence

- Neither reference cites `.claude/commands/`.
- The scribe rule's mirror is checked against the package contract rather than
  assumed, and any divergence is reported rather than silently adopted.
