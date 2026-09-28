---
id: ACT-0988
title: Define explicit test-harness mode and broader regression discovery
status: open
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

Retain configurable test-module selection, broader discovery beyond the
approved import-chain default, and option-controlled failure diagnostics for
the shared CLI/REPL harness for a future sprint. The minimum automatic
`--test` runner is current-increment work under the 2026-09-28 ruling below.

## Approved direction

The user subsequently confirmed that `--run` should expose the same language
capabilities as release execution. Execution and optimization strategies may
differ. Test-harness capabilities should be enabled through an explicit
`--test` mode rather than through ordinary `--run` execution. The minimum runner is now current-increment work, not a claim that the
compiler already implements that boundary.

The REPL retains its test harness. The user requires `--test` and `/run-tests`
to share execution and reporting code; selection remains command-specific.

## Discovery scope still to settle

The current empty-vector primitive selects the session's current module;
explicit vectors select named modules. The all-tests command is specified over
loaded project modules, excluding libraries. Neither promises to find every
project test module that has not yet been loaded.

The initial automatic runner's scope is settled by the 2026-09-28 ruling
below. Configurable selection and discovery beyond the import chain remain
future work. The detailed harness contract is still being settled in the
current increment; empty-vector primitive scope is unchanged.

## Confirmed defect carried with this work

On 2026-09-27 the user explicitly approved carrying DT-1 from
[ACT-0986](ACT-0986-test-discovery-contract-and-eligibility-intake.md) with this
increment. Ordinary `--run` silently discovers zero tests in a module that
contains eligible tests. Resolve this when establishing the explicit harness
boundary, rather than adding temporary discovery capability to `--run`.
Retain the unignored failing regression named in ACT-0986. The carry does not
approve the empty result or decide the outstanding harness and REPL policy.

## Minimum brought forward (2026-09-28)

The user approved this sequence for S122:

1. Fix ACT-1002.
2. Deliver the minimum `--test` harness needed to replace the interim DT-1
   guard with correct positive and negative coverage.

Broader project-wide discovery remains deferred. That approval covers scope
only. It does not approve the invocation contract, the `--run` treatment,
the REPL policy or any requirement text. Those are pending user decisions,
presented one question at a time.

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
filing. The original filing recorded a deferred enhancement; DT-1 is the
subsequently reproduced defect explicitly carried with it.

## Current increment scope ruling — 2026-09-28

The user brought the minimum automatic `--test` runner into the current
increment. Its default test-module set follows the target's transitive
import chain, includes project-directory modules, and excludes modules on
library search paths. It does not mean every loaded module or a filesystem
scan. This resolves the module-selection question for the initial runner.

Future configuration may customize this selection. Such options remain
deferred here; the current increment does not add configuration knobs.
Other runner-contract decisions are tracked in the active sprint before
implementation. Existing empty-vector primitive scope remains unchanged.

The user additionally includes declared child modules (`mod` and `mod-`) in
the initial runner's reachability, even without an explicit import. Under
`--test`, `main` is neither required nor called. Future configuration remains
deferred; these defaults are current-increment requirements.

## Future failure diagnostics — 2026-09-28

The user proposes an improved failed-test experience controlled by harness
options, shared by `--test` and `/run-tests`. Define the options and their
behavior in a future increment. Keep current failure reporting and manual
tracing for this increment; automatic failure traces are not required.
