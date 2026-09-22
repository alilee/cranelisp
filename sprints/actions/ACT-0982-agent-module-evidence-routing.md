---
id: ACT-0982
title: Assess execution routing for agent module evidence
status: open
priority: normal
from: qa
to: qa
sprint: 122
filed_at: 2026-09-22
refers_to:
  - tests/plan/agent-testing-strategy.md
  - tests/scripts/run-agent-lane.sh
---

## Evidence limit

The isolated agent launcher runs the agent e2e target only. Feature-gated
module tests in the binary's agent modules are not selected by that launcher
or by the default feature-off suite. The S122 evidence record includes a
manual module run; absence from the launcher is not evidence they have never
run, nor a reproduced product defect.

## Disposition

QA assesses whether the current scheduled evidence runs adequately cover the
request-content claims that the strategy assigns to module evidence. If an
execution gap remains, coordinate the smallest routing correction with test,
retaining target-directory isolation and avoiding duplicate runs. Do not add
another gate merely because two launch paths exist. Record actual execution
and source provenance before claiming those conditions covered.

The source-read name `request_tools_are_read_only_allowlist` is misleading:
its body already asserts that `submit` is offered. Dev can correct the name
and stale commentary on the next visit; this observation alone does not
establish an assertion defect.

Provenance: QA session `d5f36ec9-f57c-449e-b1e4-8325dd7cbf1d`, S122 strategy
consolidation. No test execution or script change occurred in that pass.
