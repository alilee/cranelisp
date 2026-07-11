# design/review/

Owned by `/review` (per-crate triad reviewer). This directory is a **historical
archive**, not a live standard: it holds ring-era and sprint-wave review records
produced when review was gate-shaped rather than change-set-shaped.

## What this directory holds now

The files here (`ring0-*`, `ring1-*`, `ring2-*`, `checklist.md`,
`crate-quality.md`, `naming-convention-review.md`, and the dated `sprintNN-*`
review write-ups) are **frozen artifacts** from earlier sprints. The ring axis
was retired as a scheduling axis in Sprint 64, and review moved to per-crate
narrow-deployment; the ring checklists and completion reports are read as a
record of what was reviewed and when, not as instructions for a current pass.
Nothing new is written here — findings are per-FIXME now (see below).

## Where the live review standard actually lives

`/review` carries no persistent owned artefact. The standard a change set is
reviewed against is assembled per invocation from:

- **`.claude/commands/review.md`** — the `/review` role: workflow, findings
  classification, quality checks, unsafe-code audit.
- **`design/arch/principles.md`** + **`design/arch/principles/NN-*.md`** — the
  architectural principles, cited by name in findings.
- **`design/{crate}/{crate}.md`** — the per-crate design intent the change is
  reviewed against.
- **`crates/{crate}/CLAUDE.md`** (or `src/CLAUDE.md`) — local conventions and
  API gotchas; drift from them is a finding.
- The crate's committed **`public-api.txt`** baseline + `design/arch/bounded-contexts.md`
  — the as-designed public surface (facade specs retired S69–S81).
- The most recent **`audits/{crate}-*.md`** rolling assessment (`/audit`'s
  whole-context record) as point-in-time context.

## Findings

Review findings are filed as FIXMEs in `design/arch/fixmes/NNNN-name.md`,
classified Blocker / Important / Suggestion, and resolved by the owning skill.
Reviewed change sets become git history. There are no ring-completion reports.
