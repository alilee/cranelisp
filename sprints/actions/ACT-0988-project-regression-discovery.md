---
id: ACT-0988
title: Define explicit test-harness mode and broader regression discovery
status: deferred
priority: advisory
from: sprint
to: spec
sprint: 122
filed_at: 2026-09-22
refers_to:
  - repl/spec/16-test-discovery.md
  - src/session_v4/test_runner.rs
  - src/repl/commands.rs
  - stdlib/testing/runner.cl
---

## Request

Consider broader test discovery for a project regression run in a future sprint.
The user explicitly deferred this uplift while retaining current discovery
behavior on 2026-09-22. Revisit at future sprint scope selection.

## Approved direction

The user subsequently confirmed that `--run` should expose the same language
capabilities as release execution. Execution and optimization strategies may
differ. Test-harness capabilities should be enabled through an explicit
`--test` mode rather than through ordinary `--run` execution. This is future
work, not a claim that the current compiler implements that boundary.

The REPL's test-harness availability remains undecided. Define that policy and
the test-mode invocation contract before implementation; the confirmed parity
direction does not choose those details.

## Discovery scope still to settle

The current empty-vector primitive selects the session's current module;
explicit vectors select named modules. The all-tests command is specified over
loaded project modules, excluding libraries. Neither promises to find every
project test module that has not yet been loaded.

Clarify the intended regression scope with the user: imported dependencies,
loaded project modules, or project test modules including those not yet loaded.
Then establish the discovery/loading requirements. No choice among those
scopes, detailed harness API, or change to empty-vector semantics is approved.

## Completion evidence

User-approved requirements define the normal-execution/test-harness boundary,
resolve the REPL policy, distinguish local discovery from the broader run,
and define module inclusion and library treatment. QA allocates evidence for
capability parity between normal execution modes, explicit harness availability,
omitted intended modules and unintended inclusions. Implementation and
documentation follow the approved scope. Include a reader-facing test-discovery
guide once the REPL policy is settled; retain any still-applicable cache/private
test-child limitation from filing0868 without claiming an unverified workaround.

Source verification: sprint read `discover_tests_extern`,
`discover_eligible_tests`, `handle_run_all_tests`, and the library runner before
filing. This records a deferred enhancement, not a reproduced defect.
