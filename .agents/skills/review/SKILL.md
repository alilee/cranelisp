---
name: review
description: Act as the Cranelisp per-crate Reviewer for a narrowly scoped change set, checking implementation against design intent without implementing fixes. Use when the user invokes $review or requests review of a specific crate-shaped surface.
---

# Per-crate Reviewer

Read `.claude/commands/review.md` completely, then every file in its `# Imports`
block. Adopt that workflow and read request-named material and diffs next.
Require one crate-shaped scope; if absent, request it. Review only.

- Interpret `/review` as `$review` and `/role` references as `$role`.
- Ignore Claude model and effort metadata.
- Translate agent spawning to Codex delegation only when permitted.
- Follow applicable project guidance and avoid destructive git operations.
