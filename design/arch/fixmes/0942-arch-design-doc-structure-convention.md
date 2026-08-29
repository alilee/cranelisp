---
number: 0942
target: /arch
filed_by: /sprint
filed_at: 2026-08-29
sprint_filed: 119
refers_to: design/CLAUDE.md §Design-doc expectations — says what design docs are
  ABOUT, not how they are structured; sprints/METHOD.md §1.4 governs only which
  home content goes to
status: open
---

# Design-doc structure convention: solution first, change history last

## Issue

There is no recorded convention for how a `design/` document is *shaped*. METHOD §1.4
governs which home content goes to; `design/CLAUDE.md` says what design docs are about.
Neither says what a reader should find in what order — so each doc's structure is
re-invented, and the failure mode is consistent: opening with archaeology, organised as
a list of questions and decisions, dense with reference lists.

The user's ruling (2026-06-06, given on the first `test-discovery.md` drafts, which were
"very dense with long paragraphs and lists of references"): design documents lead with
the solution, not the journey, and read as explanation rather than as a decision log.
The reader needs the solution and a map first; how we arrived is appendix material.

Required shape:

1. Overview of the solution, plus a map of the document's topics.
2. A short list of open questions, immediately after the overview.
3. The requirement — what the feature is for, the intent.
4. The user experience — what a user writes and sees, with concrete examples.
5. The language constructs — surface forms, signatures, semantics.
6. The implementation — mechanism, mapped onto crates and components.
7. Data structures, functions, and sequence (diagrams and walks).
8. **Change history at the END** — superseded explorations compressed into appendices,
   never the opening.

Register: explanatory paragraphs over reference-dense lists; keep `file:line` and §
grounding, but inside the relevant section rather than as inline walls.

This has survived three years of sprints only as a cross-workstation memory, which is
why documents keep drifting back to the decision-log shape.

## Proposed resolution

Record the shape where every design-authoring skill will see it. `/arch` owns
`design/arch/`; `/design` owns `design/{crate}/` — so the convention needs a home both
read. Candidates: `design/CLAUDE.md` (nearest existing home, and a `CLAUDE.md` at that
level is auto-read by any agent working under `design/`), or a short section in
`design/arch/CLAUDE.md` cross-referenced from `design/CLAUDE.md`. One home, not both.

If `/arch` judges `design/CLAUDE.md` to be outside its ownership, re-target this FIXME
to `/design` rather than resolving it — but note the convention applies to `design/arch/`
documents too, so a `/design`-only home would under-reach.
