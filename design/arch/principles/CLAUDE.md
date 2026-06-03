# design/arch/principles/

Architectural Principles register. One file per Principle: `NN-{slug}.md` with frontmatter `number: NN, title: ...`. Index in `design/arch/principles.md`.

## When you author a new Principle

The Principle file alone is not enough. To make the new Principle visible to every `/arch` invocation **and to every triad invocation**, you MUST also:

1. Add the Principle to the index in `design/arch/principles.md`.
2. Add a corresponding `@design/arch/principles/NN-{slug}.md` line to the import block at the top of `.claude/commands/arch.md`.
3. Add the same `@design/arch/principles/NN-{slug}.md` line to the import block at the top of **each triad skill def** — `.claude/commands/design.md`, `.claude/commands/dev.md`, `.claude/commands/review.md`. The triad (`/design`/`/dev`/`/review`) applies the principles to per-crate work; a principle absent from their import block is invisible to them.

Without steps 2–3, the skill reads the skill def without the new Principle in its context — it makes decisions in a world where the Principle silently doesn't exist. The lapse is invisible (everything compiles; the file is on disk) but the consequence is real (every future decision is uninformed about the rule). The four import blocks (arch + the three triad files) MUST carry the identical principle set; they are audited together under the Configuration consistency rule.

This convention applies to the **filer of the Principle**, not to a follow-up sprint. If you can't update an import block in the same commit (e.g., the file is editable only via skill-creator), file the import update as a follow-up FIXME or at minimum flag it in the commit body for `/sprint` to chase.

Sprint 65 W4a follow-up flagged the arch-block gap during the first canonical-set audit pass under the new Configuration consistency rule (commit `0c5ad88`): Principles 14, 15, 16 were on disk but not in the arch import block. Sprint 76 seam-settle pass found the **triad** blocks had the same gap — they imported only Principles 1–13, so Principles 14–18 (including 15 facade-types-live-with-behavior and 17 module-locality, both load-bearing for the S76 resolve-primitive fold-in) were invisible to `/design`/`/dev`/`/review`. The triad blocks were brought to the full 1–18 set and step 3 added to this convention to prevent recurrence.

## Editing existing Principles

Principle text evolves through:
- Sprint Phase 7 review (per `.claude/commands/arch.md` § Sprint participation)
- Normal revision when a new architectural decision changes the criteria

When you edit a Principle, the Configuration consistency rule applies — audit the canonical set per the 6-step checklist in `.claude/commands/arch.md`.

## Retiring Principles

If a Principle no longer applies, retire by:
1. Deleting the file (rely on git history)
2. Removing from `design/arch/principles.md` index
3. Removing from `.claude/commands/arch.md` import block

The trio must move together. A retired Principle whose import line lingers wastes context on every `/arch` invocation.
