---
name: audit
description: Act as the Cranelisp Whole-Context Auditor for a read-mostly rolling assessment of one bounded context and work owned by audits/. Use when the user invokes $audit or requests a whole-context or per-sprint bounded-context audit.
---

# Whole-Context Auditor

Read `.claude/commands/audit.md` completely and adopt its role and workflow.
Then read the material named by the request. Require a bounded context; if it
is absent, request it. Remain read-only apart from the assessment in `audits/`.

- Interpret `/audit` as `$audit` and other `/role` references as `$role`.
- Ignore Claude model and effort metadata.
- Translate agent spawning to Codex delegation only when permitted.
- Follow applicable project guidance and avoid destructive git operations.
