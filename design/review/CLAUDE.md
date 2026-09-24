# design/review/

Standing change-set cues owned by `review`, extending the shared review role.
Historical checklists and reports are recoverable from Git checkpoint
`07f46769`. The remaining cache-packet `Send` cleanup is retained with the
[coordinated API baseline work](../../sprints/actions/ACT-0955-omit-auto-traits-from-public-api-baselines.md);
S122 discharged the other extracted points or corrected their current homes.

## Where the live review standard actually lives

The standard a change set is
reviewed against is assembled per invocation from:

- **`.agents/skills/review/SKILL.md`** — the `review` role contract: workflow,
  findings classification, quality checks and handoffs.
- **`design/arch/principles.md`** + **`design/arch/principles/NN-*.md`** — the
  architectural principles, cited by name in findings.
- **`design/{crate}/{crate}.md`** — the per-crate design intent the change is
  reviewed against.
- **`crates/{crate}/CLAUDE.md`** (or `src/CLAUDE.md`) — local conventions and
  API gotchas; drift from them is a finding.
- The crate's committed **`public-api.txt`** baseline + `design/arch/bounded-contexts.md`
  — the as-designed public surface for library crates with a tracked baseline
  (facade specs retired S69–S81).
- Open audit points in `sprints/actions/`, existing `design/arch/fixmes/`
  filings and the owning standing documents. Historical assessments are
  recoverable from the Git checkpoint cited by those records.
- §"Standing change-set cues" below — live cues that extend the skill def's
  quality checks.

## Standing change-set cues (live)

Walk these cues on every change set, alongside the quality checks in
`.agents/skills/review/SKILL.md`.

### Duplication — two distinct lenses

Duplication has two shapes, and they need different eyes. The first is already
in the standard; the second is the one diff-shaped review habitually misses.

**1. Mirror duplication** (existing lens — the P7/P8 class). Near-identical
copies: three-or-more near-identical sites, copy-pasted blocks, parallel
concept tables. Principle 7 (single source of truth) and Principle 8 (no
interim implementations) are the citations; the skill def's "repeated
patterns" quality check are the current authority. The ring-era checklist
lineage is recoverable at the Git checkpoint above. Mirrors *look alike* — reading the diff against the codebase finds
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

- **Flag toward convergence on one codepath** — route the finding per the normal
  rules (`dev` for the implementation, `design` where the design
  doc licensed the variant).
- **On a third sibling, escalate to `arch`** — a third
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
| Per-diff | `review` (this cue) | catch the (N+1)th variant as it is proposed |
| Rolling coverage | `qa` | the [coverage by definition variants](../../tests/CLAUDE.md) standing category |
| Whole-context | `audit` | the [Duplication quality attribute](../../audits/CLAUDE.md) (mirror + divergent + entry-point + spec-surface facets) — sweeps what per-diff review cannot see |

## Findings

Review findings follow the shared role's classification and handoff rules.
New retained filings go to `sprints/actions/`; existing `design/arch/fixmes/`
filings run down in place under the root guidance. Reviewed change sets become
Git history. Historical reports are not a standing documentation product.
