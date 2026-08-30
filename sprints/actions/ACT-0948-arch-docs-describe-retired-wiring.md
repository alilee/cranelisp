---
id: ACT-0948
title: Repair design/arch documents that describe the retired command-file wiring
status: open
priority: required
from: sprint
to: arch
sprint: 120
filed_at: 2026-08-30
refers_to:
  - design/arch/principles/CLAUDE.md
  - design/arch/CLAUDE.md
  - design/arch/bounded-contexts.md
  - design/arch/tracing.md
  - design/arch/principles.md
---

## Request

The 2026-08-30 wiring change retired `.claude/commands/` in favour of the shared
role contracts at `.agents/skills/`. Several `arch`-owned documents describe the
retired mechanism as live. These are `arch`'s files to repair; `sprint` broke the
references and is filing rather than editing them.

**`design/arch/principles/CLAUDE.md` is the substantive one.** Its procedure for
adding a principle instructs the author to add an `@design/arch/principles/NN-…`
line to the import block at the top of `.claude/commands/arch.md` and to *each
triad skill def*, and its removal procedure reverses that. **No import block
exists any more.** The procedure cannot be followed as written, and its steps 2,
3 and the removal mirror need replacing with whatever `arch` decides now carries
principle reachability.

`sprint` has restored reachability provisionally — `sprints/METHOD.md` §1.1
states the principles are the standard the surfaces are built and reviewed
against, and the `design`/`dev`/`review` wrappers name `design/arch/principles.md`
as a first-read. That is a stopgap chosen to avoid shipping a behavioural loss;
whether it is the right mechanism is `arch`'s call, and it may want something
stronger than prose given §Assurance's preference for structure over reminder.

Also citing the retired wiring, as ordinary drift:

- `design/arch/CLAUDE.md` — "auto-imported by `.claude/commands/arch.md`" in
  three places, plus a `.claude/commands/arch.md` row in its document table and a
  reference to that file's §"The manifestation-site question" for the Decisions
  drain. The Decisions-drain rule itself survives in that file; only its citation
  is dead.
- `design/arch/bounded-contexts.md` — "The skill def (`.claude/commands/arch.md`
  §The crate-shaped surfaces) carries the one-line…"; that statement now lives at
  `sprints/METHOD.md` §1.1.
- `design/arch/tracing.md` — cites `.claude/commands/arch.md` §"Target
  documentation set" for its own ownership.

The former arch command file also held content with no current home: the facade
convention (`lib.rs` mechanics), public-API discipline and the `api.txt`
baseline, sequence-diagram conventions, the configuration-consistency checklist,
and the target documentation set. Recover what is still wanted from
`git show 47f7425a~1:.claude/commands/arch.md` and place it in `design/arch/`,
or rule that it is superseded.

## Completion evidence

- `design/arch/principles/CLAUDE.md` states a procedure that can actually be
  followed, and the reachability mechanism is either the METHOD stopgap ratified
  or something `arch` prefers.
- No `arch`-owned document cites `.claude/commands/` as live.
- A ruling on each orphaned section of the former arch command file: rehomed in
  `design/arch/`, or recorded as superseded.
