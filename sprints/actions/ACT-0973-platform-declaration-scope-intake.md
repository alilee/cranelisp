---
id: ACT-0973
title: Investigate non-entry platform declaration handling against the specification
status: deferred
priority: normal
from: qa
to: qa
sprint: 122
filed_at: 2026-09-21
refers_to:
  - spec/10-io.md
  - src/process_form/platform.rs
  - src/process_form/cache_restore.rs
---

## S122 disposition (user-approved 2026-09-30)

Under the [approved S122 disposition](../../tests/plan/s122-evidence-delta.md#final-disposition-proposal-2026-09-30):

- **Carried to S123 (K6, C2).** First deferral.

## Observation and limit

Spec §10.9.1 requires a compile-time error for a platform declaration in a
non-entry module. During the S122 citation pass, QA read handling that silently
skips a declaration when the module path contains a dot, including a comment
claiming that behavior follows the spec. A root-level non-entry module may
instead take the load path. These are source-read hypotheses, not attributed
runtime failures; the attempted scratch probe was refused by the execution gate.

## Required disposition

Verify the requirement and current source first. Allocate a minimal entry/child
fixture containing the platform declaration in the child, paired with an entry
placement control; distinguish nested from root-level non-entry modules and
fresh from cache restore where needed for attribution. If confirmed, retain a
permanent failing, unignored spec-traced reproduction and route the correction
to the integration owner. Do not change the spec to match silent acceptance.

Provenance: QA session `1ff2b61c-dc4c-4017-b1f2-4f2bb9e4bcc5`, S122.
