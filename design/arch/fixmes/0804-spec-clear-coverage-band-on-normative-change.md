---
number: 0804
target: /spec
filed_by: /sprint
filed_at: 2026-07-21
sprint_filed: 115
refers_to: sprints/METHOD.md §2.2 "A spec change clears its coverage
  annotations" + spec/07-traits.md §7.1.1 (the S115 worked failure — the
  occurrence-rule ruling changed the requirement while its band stayed green)
  + spec/05-definitions.md §5 (the dotted-binder ruling, 14 table rows changed
  this sprint) + spec/07-traits.md §7.1.4 (example corrected)
status: open
---

# /spec clears the coverage band on any normative change (and the S115 backfill)

## Issue

User-directed mechanism (2026-07-21), binding in METHOD §2.2: **the skill that
changes a normative statement clears that row's coverage annotation in the same
edit.** Clearing is an *invalidation*, not a coverage judgment — which is
precisely why it does not breach `/qa`'s ownership of the band: any skill may
clear (only the author of a change knows a requirement moved); **only `/qa` may
restore**.

The rule exists because S115 demonstrated the failure end to end: the user's
occurrence-rule ruling changed §7.1.1 from a nullary corner to a general
requirement, `/spec` scribed it faithfully, the band stayed `[Tested …]`, the
cited test still existed and still passed — and the implementation was never
widened. Nothing in the toolchain could see it, because every check that runs
validates *citation liveness*, not *requirement currency*.

## Proposed resolution

Going forward: when a `/spec` edit changes what a requirement *means* — new
MUST, narrowed or widened scope, a settled ruling, a corrected example that was
itself normative — clear that row/section's `[Tested …]` / `[Tested+Neg …]`
annotation in the same edit. Prose that does not change a requirement
(typography, cross-references, rationale, legibility promotions) does **not**
clear. When in doubt, clear: the cost of a false clear is one backlink re-read
by `/testing`; the cost of a missed clear is a green band over an unenforced
requirement, which is what happened this sprint.

**Wait for FIXME 0803 (`/qa`) to settle the cleared-row marker** before
clearing anything, so the first cleared rows are written in the final
vocabulary. `[S{M}]` may be reused, or a distinct marker may be adopted that
preserves the prior covering set as the starting point for the backlink walk.

**S115 backfill, once the marker exists** — normative changes landed this
sprint whose bands were not cleared:

- `spec/07-traits.md` §7.1.1 — the occurrence rule `[S115]` (scope widened by
  user ruling; the known-uncovered case is the non-nullary column, already
  filed as FIXME 0805 to `/testing`) **and** the marker-trait parked-boundary
  note.
- `spec/07-traits.md` §7.1.4 — the `Convertible` example was itself the
  normative defect (it contradicted §7.1.1's MUST); corrected this sprint.
- `spec/07-traits.md` §7.3.6 — sub-question 1 closed by user ruling.
- `spec/05-definitions.md` §5 — the dotted-binder ruling: prose plus **14 of 18
  binder-table rows**, plus ten per-subsection restatements and four
  out-of-file restatements in §4/§6/§7.
- `spec/05-definitions.md` §5.4.5 — impl-redefinition hot-reload `[S115]`.
- `spec/05-definitions.md` §5.2.7 — the constructor-case sentence corrected.
- `spec/01-lexical.md` §1.4.5/§1.8, `spec/02-grammar.md` §2.3.8/§2.4,
  `spec/03-types.md` §3.9, `spec/09-macros.md` §9.1.2/§9.2.2/§9.4.2 — the
  read-time annotation fold (**note: these describe S116 behaviour that is not
  yet implemented**, so their rows are legitimately uncovered until the S116
  flip wave; clearing makes that visible rather than implied).

Coordinate the backfill with `/qa` (0803) so the first `--check` run after the
marker lands reports a known, intended set rather than a surprise.
