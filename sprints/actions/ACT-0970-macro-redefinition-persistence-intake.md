---
id: ACT-0970
title: Investigate macro redefinition persistence after a successful REPL turn
status: open
priority: normal
from: sprint
to: qa
sprint: 122
filed_at: 2026-09-21
refers_to:
  - repl/spec/18-redefinition.md
  - tests/repl_persist.rs
  - src/save.rs
---

## Observation and limit

During the S122 integration-document assessment, QA observed a successful
macro replacement used by a newly defined caller while the backing file still
held the old macro body. The observation recurred in three scratch sessions.
It is suspected, not an attributed defect: no restart leg or discriminating
control has established the failure yet.

QA session `8917f705-8a26-4eea-9410-f0f8d3cc447d` used the current debug binary
with no prelude. A macro initially expanded to `(one)` and was replaced with
an expansion to `(hundred)`; an existing caller returned 1 and a new caller
returned 100, but the saved macro retained `(one)`.

## Required disposition

Verify against REPL §18.8 in the referenced specification and current save
source first. Allocate a minimal reproduction with a function-redefinition
control and a fresh restart observation. If confirmed, retain a permanent
failing, unignored spec-traced test and attribute before routing a fix.
Otherwise record the discriminating evidence and retire this intake.

## Restart observation (2026-09-25)

The D1 cache-deferral test attempt reproduced the restart leg. A macro k
initially expands to quoted1; after an admitted replacement with quoted100,
the live REPL displays100, but mac.cl persists the old body as quasiquote1.
A no-cache batch restart using7 plus k exits8, not107. Three probe variants
showed the same result. The function-redefinition control remains unexecuted,
so mechanism attribution and a permanent minimal reproduction are still owed.

This also blocks the intended D1 macro-deferral comparison: the restart
trigger has no semantic change to distinguish stale cached code from fresh
compilation. Do not treat that unarmed comparison as refuting D1. Test session
`7c2ea103-8c63-4aef-bbc6-38733d8f079a` retained its local draft; no D1 defect
cell or tag was landed.
