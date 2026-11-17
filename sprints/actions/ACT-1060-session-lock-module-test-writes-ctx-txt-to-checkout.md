---
id: ACT-1060
title: A session-lock module test writes `ctx.txt` into the repository root
status: open
priority: required
from: qa
to: dev
sprint: 124
filed_at: 2026-11-16
refers_to:
  - src/repl/mod.rs
  - src/repl/commands.rs
  - tests/plan/s124-evidence-delta.md
---

## Request

Make `src/repl/mod.rs::session_lock_admission_tests::locked_session_refuses_exactly_the_commands_that_run_program_code`
stop writing into the checkout. Its command table runs `/context ctx.txt`,
and `handle_context` writes the rendered agent request to that relative path,
which resolves against the test process's working directory: the package
root. Give the command a path inside the test's temporary directory.

## Evidence (qa, 2026-11-16, at `4b58ab93`)

- The untracked `ctx.txt` in the repository root is rewritten by every suite
  run. Its modification time moved when that one test ran alone, and did not
  move when its sibling `locked_session_refuses_every_code_turn_in_any_module`
  ran alone.
- It appeared at S123, when the `agent` feature joined the default set and
  `handle_context` began to compile in the default suite.
- The file is a request dump (primer and harvested session context). It
  holds no credential.
- Surface: `dev` narrow-deployed to `src/`. This is a test defect, not a
  compiler defect, so no reproduction is allocated.

## Completion evidence

After `cargo nextest run --no-fail-fast` on a tree with no `ctx.txt`,
`git status --short` lists no `ctx.txt`. The test still asserts that
`/context` is admitted while the session is locked. The existing stray file
is removed by whoever owns the working tree at that point.
