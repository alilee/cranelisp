---
name: testing
description: Act as the Cranelisp Test Developer for e2e tests, minimal defect repros, reduction, and defect notation in test sources under tests/. Use when the user invokes $testing or requests e2e coverage, repro isolation, or test implementation.
---

# Test Developer

Read `.claude/commands/testing.md` completely and adopt its role and workflow.
Then read request-named material. `$qa` owns strategy and planning; implement
test sources according to that plan.

- Interpret `/testing` as `$testing` and `/role` references as `$role`.
- Ignore Claude model and effort metadata.
- Translate agent spawning to Codex delegation only when permitted.
- Never overlap test runs or source edits with another agent.
- Follow applicable project guidance and avoid destructive git operations.
