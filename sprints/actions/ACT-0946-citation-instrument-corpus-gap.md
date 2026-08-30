---
id: ACT-0946
title: Decide the citation checker's corpus, which today cannot see sprints/ or .claude/
status: open
priority: required
from: sprint
to: qa
sprint: 120
filed_at: 2026-08-30
refers_to:
  - scripts/verify-citations.py
  - scripts/citation-drift-baseline.txt
---

## Request

`scripts/verify-citations.py` is the mechanism root `CLAUDE.md` §Assurance names
for keeping records honest — "a discipline that depends on remembering is not a
mechanism". It has two coverage holes, and both sit on scheduling surfaces.

**Documents it never scans.** `DOC_GLOBS` is `design/**/*.md`, `audits/*.md`,
`tests/plan/*.md`, `spec/*.md`, `repl/*.md`, `CLAUDE.md`, `**/CLAUDE.md`. So
`sprints/METHOD.md`, `sprints/ROADMAP.md`, `sprints/SPRINT.md` and the new
`sprints/actions/` are unscanned, as is every role definition under `.claude/`.

**Paths it never validates.** `SOURCE_ROOTS` is `src/ crates/ tests/ platforms/
stdlib/ examples/ exemplar/ repl/ scripts/ benches/`. A citation to
`sprints/anything.md` is therefore not checked *even from a document that is
scanned* — including from root `CLAUDE.md`.

Measured 2026-08-30 by planting two faults in root `CLAUDE.md`: `src/nope.rs`
was reported; `sprints/this-file-does-not-exist.md` was not. The corpus run
returned the identical `433 documents, 7499 citations, 0 findings` across three
different repo states — before the S120 method alignment, after deleting
`sprints/METHOD_OLD.md` and `sprints/METHOD_PROPOSED.md`, and after deleting
`sprints/artefacts.md`. Those three deletions broke roughly twenty citations,
every one repaired by hand because the instrument could not see any of them.

The script's own comment calls FIXMEs "the highest-value corpus: they drive
scheduling." METHOD, ROADMAP, SPRINT and the actions directory drive scheduling
too.

## Why this needs a decision, not a fix

Adding `sprints/` to `DOC_GLOBS` and `SOURCE_ROOTS` will surface an unknown
quantity of pre-existing stale citations at once. Root `CLAUDE.md` §Assurance
rules that baseline entries "are never added by hand, because a new finding is a
new stale record and stopping those is the point." A bulk enrolment is exactly
that hand-addition, at scale, so the ratchet's own rule has to be ruled on
before the corpus widens.

`.claude/` is a separate call and probably moot: those definitions retire when
the wiring connects to `.agents`, and the package's contracts live in a
submodule with its own verification.

## Completion evidence

- A ruling on whether `sprints/` joins `DOC_GLOBS`, `SOURCE_ROOTS`, or both, and
  on how the resulting findings are absorbed — enrolled in the baseline with the
  rationale recorded, or repaired before the corpus widens.
- If widened: the run, its finding count, and a detection proof for the newly
  covered kind — a planted `sprints/` fault reported, and silence once removed.
- `.claude/` explicitly ruled in or out, with the reason.
