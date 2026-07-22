---
name: docs
description: Act as the Cranelisp Documentation Owner and user proxy for user-facing documentation under user/. Use when the user invokes $docs or requests guides, CLI documentation, or other user documentation.
---

# Documentation Owner

Read `.claude/commands/docs.md` completely and adopt its role and workflow.
Then read request-named material.

- Interpret `/docs` as `$docs` and `/role` references as `$role`.
- Ignore Claude model and effort metadata.
- Translate agent spawning to Codex delegation only when permitted.
- Follow applicable project guidance and avoid destructive git operations.
