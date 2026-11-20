---
id: ACT-1098
title: Typecheck maintenance-economy findings from the S124 audit (R2, R3, R4, R5)
status: open
priority: advisory
from: sprint
to: arch
sprint: 124
filed_at: 2026-11-20
refers_to:
  - audits/cranelisp-typecheck-s124.md §4
---

## Request

Carry four findings of the [S124 typecheck audit](../../audits/cranelisp-typecheck-s124.md)
to a future typecheck sprint. The user agreed this disposition on 2026-11-20;
it authorises no work now. The audit states each finding, its evidence and
its cost class; this action does not restate them.

- **R2** — monomorphisation discards an identity it has already selected and
  resolves it again.
- **R3** — an ownership analysis serving a future optimisation tier is
  computed, persisted and tested on the default path today.
- **R4** — settlement repeats work across several windows.
- **R5** — published explanations no longer describe the delivered context.

`arch` scopes them with `design`(typecheck) when a typecheck sprint is
planned, and decides which cross a crate boundary.

## Other findings of the same audit

- R1 is carried by the open typecheck defect filings (ACT-1071, 1073, 1074,
  1075, 1076, 1080, 1082).
- R6 is ACT-1097.
- R7 is with `spec`, to frame for the user's ruling.
