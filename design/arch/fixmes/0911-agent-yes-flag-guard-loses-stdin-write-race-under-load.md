---
number: 0911
target: /testing
filed_by: /qa
filed_at: 2026-07-26
sprint_filed: 118
refers_to: tests/agent.rs::yes_flag_errors_on_non_agent_build;
  tests/helpers/e2e.rs:365 (stdin write panic)
status: open
---

# The `--yes` rejection guard loses a stdin-write race against its immediately-exiting child under full-suite load

## Issue

W8 gate finding. `agent::yes_flag_errors_on_non_agent_build` failed in BOTH
full-suite runs (0.003s / 0.007s) with

```
Cranelisp::output failed: stdin write failed: Broken pipe (os error 32)
  at tests/helpers/e2e.rs:365
```

and PASSES focused. The test spawns the REPL with `--yes` on a non-agent
build — which now correctly exits 1 with a usage hint BEFORE reading stdin —
then pipes `.stdin("(add-i64 1 2)\n")`. Whether the harness's write lands
before the child's exit closes the pipe is a scheduling race: under full-suite
load the child wins (EPIPE, harness panic — the assertion never runs); focused
the write wins. Deterministic in cause (a real ordering race in the harness
usage, not "flakiness"): the guarded compiler behaviour (exit 1, hint naming
the flag, not `unknown flag`) is verified correct in the focused run.

Latent since the 0539 fix made the child exit-before-read; first surfaced at
the W8 double-run — the first full-suite runs since S115.

## Proposed resolution

Make the guard independent of the race: drop the stdin write for this
immediate-exit child (no input is needed to observe the rejection), or make
the harness's stdin write EPIPE-tolerant for children expected to exit
without reading (an explicit builder opt-in, not a blanket swallow — a
silent EPIPE on a child that SHOULD read stdin is a real failure). Sibling
`y_short_flag_errors_on_non_agent_build` passes today but has the same
structure if it writes stdin — sweep it in the same change-set. Delete this
file in the fixing change-set.
