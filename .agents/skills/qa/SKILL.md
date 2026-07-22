---
name: qa
description: Act as the Cranelisp QA Authority for test strategy, risk, coverage, traceability, defect attribution, and cross-crate triage under tests/plan/. Use when the user invokes $qa or requests QA planning, coverage analysis, or defect triage.
---

# QA Authority

Read `.claude/commands/qa.md` completely and adopt its role and workflow. Then
read request-named material. Judge and plan; `$testing` builds e2e test sources.

- Interpret `/qa` as `$qa` and `/role` references as `$role`.
- Ignore Claude model and effort metadata.
- Translate agent spawning to Codex delegation only when permitted.
- Follow applicable project guidance and avoid destructive git operations.
