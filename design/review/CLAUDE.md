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
Nothing new is written here — findings are per-FIXME now (see below) — with
ONE exception: §"Standing change-set cues" below is live and extends the
assembled per-invocation standard.

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
- §"Standing change-set cues" below — live cues that extend the skill def's
  quality checks.

## Standing change-set cues (live)

Unlike the frozen records above, this section is a **live** part of the review
standard. Walk these cues on every change set, alongside the quality checks in
`.claude/commands/review.md`.

### Duplication — two distinct lenses

Duplication has two shapes, and they need different eyes. The first is already
in the standard; the second is the one diff-shaped review habitually misses.

**1. Mirror duplication** (existing lens — the P7/P8 class). Near-identical
copies: three-or-more near-identical sites, copy-pasted blocks, parallel
concept tables. Principle 7 (single source of truth) and Principle 8 (no
interim implementations) are the citations; the skill def's "repeated
patterns" quality check and the ring-era `checklist.md` §§5–6 are the
lineage. Mirrors *look alike* — reading the diff against the codebase finds
them by resemblance.

**2. Divergent / entry-point duplication** (this cue — what the mirror lens
misses). Ask of every change set:

> Does this diff introduce a **second way** to perform an operation the
> codebase already performs, or a **new entry point** (call-site-specific
> helper, per-variant lookup, mode-specific path) that **re-implements** an
> existing operation rather than routing to the single codepath?

The tells: a `*_or_X` / `*_for_Y` sibling of an existing helper; a
per-definition-form or per-mode branch that duplicates logic another branch
already has; a formatter/resolver twin. These are **not** near-identical —
each variant is locally reasonable, and a diff-fixated pass sees a sensible
patch. The *family* is the duplication, and the family is invisible in any
one diff unless you ask the question above.

- **Flag toward convergence on one codepath** — finding routed per the normal
  rules (`target: /dev` for the implementation, `/design` where the design
  doc licensed the variant).
- **On a third sibling, escalate to `/arch`** (`target: /arch`) — a third
  variant is past the consolidation threshold. Do not wave through "one more
  variant."

**Worked exemplar (S108): the `_or_prelude` variant family.** Six resolver
variants (`resolve_with_fallback`, `resolve_terminal_entry_or_prelude`,
`resolve_terminal_fq_or_prelude`, `resolve_current_or_prelude`,
`probe_current_or_prelude`, `lookup_trait_decl_or_prelude`) each landed
through a locally-reasonable review pass; the whole family was the same
operation (consult table, fall back to prelude) done six different ways from
six entry points, and convergence collapsed six to one
(`design/arch/prelude-import-convergence.md`). A per-diff cue catches the
(N+1)th variant *as it is proposed* — before it becomes a whole-context
finding.

**Three-altitude tie.** This cue is the per-diff altitude of a three-altitude
lens on the same category:

| Altitude | Skill | Lens |
|---|---|---|
| Per-diff | `/review` (this cue) | catch the (N+1)th variant as it is proposed |
| Rolling coverage | `/qa` | the "coverage by definition variants" standing category (`tests/plan/`) |
| Whole-context | `/audit` | the Duplication quality attribute (FIXME 0564: mirror + divergent + entry-point + spec-surface facets) — sweeps what per-diff review cannot see |

## Findings

Review findings are filed as FIXMEs in `design/arch/fixmes/NNNN-name.md`,
classified Blocker / Important / Suggestion, and resolved by the owning skill.
Reviewed change sets become git history. There are no ring-completion reports.
