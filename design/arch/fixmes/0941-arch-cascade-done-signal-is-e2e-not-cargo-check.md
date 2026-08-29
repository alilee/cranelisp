---
number: 0941
target: /arch
filed_by: /sprint
filed_at: 2026-08-29
sprint_filed: 119
refers_to: .claude/commands/dev.md §Release gate — the gate is crate-narrow
  (`cargo check -p`, `cargo nextest run -p`); nothing distinguishes a
  cross-crate cascade's done-signal from an ordinary slice's
status: open
---

# A cross-crate cascade's done-signal is a full e2e green-up, not `cargo check`

## Issue

For a cross-crate data-model or boundary-type reshape, a green `cargo check` does not
mean the work is done, and the current `/dev` release gate cannot tell the difference.

The S79 product-ctor dual-facet cascade (`cranelisp-types` → typecheck → backend → int)
is the exhibit. Every consumer-cascade `/dev` agent correctly reported `cargo check -p
<crate>` green. The full e2e green-up came in at **1090 passing / 105 failing** —
roughly 104 regressions the compile check could never surface, because they were
resolution, inference, and display *behaviour* changes that still type-check. The
largest single cause: a `type_def_view_of`-style accessor applied at the enumerated
sites but missed at sibling sites (`resolve_named`, pattern-ctor gates, `classify_adt`),
so qualified constructors in patterns — and therefore all macros and stdlib — broke at
runtime while compiling cleanly.

The mechanism generalises: a boundary-type reshape changes behaviour at every consumer
that pattern-matches the old shape, and `cargo check` proves only that the new shape
type-checks, not that each consumer handles it correctly. The missed sites are reliably
"one more than the spec enumerated" — every consumer in S79 found sites beyond `/arch`'s
list.

This bears directly on the root `CLAUDE.md` §Assurance grading. A cascade signed off on
`cargo check` is graded by inspection wearing a compiler's clothes: the check executes,
but it is not measuring the property being claimed.

## Proposed resolution

`/arch` to rule on the home and wording. The claim to record: **for a data-model or
boundary-type cascade, the done-signal is a full `cargo nextest run --no-fail-fast`,
never `cargo check`** — with three consequences: (1) the cascade is expected to land
red, and a triage-and-fix wave back to the deliberate REDs is budgeted as part of the
work, not treated as a regression; (2) the enumeration of consumer sites is a starting
point, so grep every match site of the old shape; (3) a wave that reports `cargo check`
green as its completion criterion has not met the gate.

Candidate homes: a Consequence on the migration-directionality item filed as FIXME 0940
(same cascade, opposite end — 0940 is how it starts, this is how it ends), or
`design/arch/bounded-contexts.md` alongside the boundary-change narrative. If `/arch`
concludes the durable home is the `/dev` release gate in `.claude/commands/dev.md`, that
edit is the user's — flag it rather than filing a second FIXME.
