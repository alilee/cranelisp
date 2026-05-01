---
number: 0004
target: /arch
filed_by: /arch
filed_at: 2026-04-25
sprint_filed: 63
refers_to: design/arch/super-import-arbitration.md
status: open
---

# Migrate `super-import-arbitration.md` to `design/arch/decisions/NNNN-*.md`

## Issue

`design/arch/super-import-arbitration.md` (72 lines) is decision-shaped — it documents an arbitration `/arch` made about how `super` imports resolve in nested module trees. It is currently classified as "Subsystem" in the W2 triage but its shape (one decision, with context + alternatives + rationale) matches the `design/arch/decisions/NNNN-*.md` format better than a freestanding subsystem doc.

## Status — directory is live

`design/arch/decisions/` was created in S63 (M0 W2.5). The migration is now **unblocked**. The numbering convention is sequential `NNNN` starting at 0001; scan max + 1 at filing time.

## Proposed resolution

`/arch` migrates `super-import-arbitration.md` to `design/arch/decisions/NNNN-super-import-arbitration.md`:

1. Add frontmatter: `status: accepted`, `context`, `decision`, `consequences`, `sprint_filed` (the sprint where the original arbitration occurred — check git blame on the existing file).
2. Reformat the body to match the decision-log shape (rationale becomes the decision body; alternatives become an "Options considered" subsection if helpful).
3. Move via `git mv` so history is preserved.
4. Update any cross-references in `CLAUDE.md` / `bounded-contexts.md` / facade specs that pointed to the old path.

Can land in S63 if there's slack (cheap, ~15 minutes), or in S64 alongside other M3-adjacent work.

## Context

Surfaced during S63 W2 triage of `design/arch/`. Originally filed as M3-blocked; unblocked in W2.5 when the directory was created.
