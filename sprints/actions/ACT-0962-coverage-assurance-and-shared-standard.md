---
id: ACT-0962
title: Establish trustworthy coverage reporting and converge through se-agentic
status: deferred
priority: required
from: sprint
to: qa
sprint: 122
filed_at: 2026-09-20
refers_to:
  - tests/plan/spec_coverage_reconcile.py
  - tests/plan/spec_link_check.py
  - tests/CLAUDE.md
  - .agents/skills/qa/SKILL.md
---

## S122 disposition (user-approved 2026-09-30)

Under the [approved S122 disposition](../../tests/plan/s122-evidence-delta.md#final-disposition-proposal-2026-09-30):

- **Carried to S123 (K11).** This action receives the evidence tails 0761, 0785, 0811, 0848, 0857, 0863, 0891, 0900, 0903, 0929, 0931 and 0747, and QA's L-B1 corpus decision. It was already a user deferral in S122, so this is a repeat carry, approved with the package; no count is otherwise recorded.

## Request

Schedule for the next increment. The user agreed to improve coverage assurance
across Cranelisp, feedback-dev and magic through the shared se-agentic package;
S122 continues document cleanup while this work is recorded for future scope.

- QA establishes the requirement inventory and distinguishes claim soundness,
  completeness/freshness, execution evidence and substantive adequacy. Reports
  name gaps; citation counts do not imply passing or adequate tests.
- Deliver Cranelisp's missing gap report with a planted-gap detection proof,
  repair broken test-to-document citations and integrate proportionate
  traceability checks into ordinary verification as maintenance checks.
- Assess pending coverage annotations that already have associated tests;
  restore claims only where assertions justify them. Use the resulting gaps to
  select behavioral tests by compiler correctness, language function and user
  experience risk.
- Coordinate arch and the shared-package contribution route to establish common
  meanings and reporting expectations in se-agentic. Preserve local requirement
  formats and runner integration. Extract common validation/reporting only when
  demonstrated across consumers; do not add a duplicate coverage register or
  require wholesale requirement-ID migration.

Source verified on filing: Cranelisp's reconcile checker parses `--gaps` but
does not consume it; check mode reports 812 live citations without a requirement
denominator. The reverse checker reports six mis-cited and four malformed
references. QA identified 98 pending annotations with associated test anchors;
anchor matches require adequacy judgment before promotion. Existing checks are
manual. Comparison runs show feedback-dev enumerates journey criteria and magic
enumerates confirmed requirements and checks claim currency at delivery; neither
claim inventory establishes assertion adequacy or joins passing execution to
each requirement. These are planning observations, to refresh at intake.

## Completion evidence

QA supplies a named gap inventory with explicit scope and inheritance rules,
verified detection of missing requirements and invalid claims, repaired citations
and an automatic maintenance-check invocation. Report reviewed annotation
dispositions separately from test execution and remaining behavioral gaps.
Shared-package proposals distinguish common semantics from local extraction,
demonstrate compatibility with all three projects and identify which reusable
code is earned by multiple consumers. No coverage-percentage target substitutes
for this evidence.

Runner-result joins, automated freshness and broader shared-tool extraction are
sequenced from the assessed gaps and cost at next-increment scoping. Filing this
action does not change compiler behavior, authorize a shared-package publication
or advance S122's phase.
