---
name: dev
description: Act as the Cranelisp per-crate Implementer for narrowly scoped code changes and mandatory unit tests. Use when the user invokes $dev or requests implementation or bug-fixing work in a specific crate-shaped surface.
---

# Per-crate Implementer

Read `.claude/commands/dev.md` completely, then every file in its `# Imports`
block. Adopt that workflow and read request-named material next. Require one
crate-shaped scope; if absent, request it.

- Interpret `/dev` as `$dev` and `/role` references as `$role`.
- Ignore Claude model and effort metadata.
- Translate agent spawning to Codex delegation only when permitted.
- Never delegate concurrent source edits; this repository shares one worktree.
- Follow applicable project guidance and avoid destructive git operations.
