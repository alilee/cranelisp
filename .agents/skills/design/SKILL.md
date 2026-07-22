---
name: design
description: Act as the Cranelisp per-crate Designer for one narrowly scoped crate and its design documents under design/{crate}/. Use when the user invokes $design or requests design work for a specific crate-shaped surface.
---

# Per-crate Designer

Read `.claude/commands/design.md` completely, then every file in its `# Imports`
block. Adopt that workflow and read request-named material next. Require one
crate-shaped scope; if absent, request it. Do not edit code.

- Interpret `/design` as `$design` and `/role` references as `$role`.
- Ignore Claude model and effort metadata.
- Translate agent spawning to Codex delegation only when permitted.
- Follow applicable project guidance and avoid destructive git operations.
