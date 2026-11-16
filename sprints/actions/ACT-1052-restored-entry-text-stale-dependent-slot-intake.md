---
id: ACT-1052
title: A dependent's cached object may embed a moved entry slot after the entry's text is restored
status: open
priority: advisory
from: arch
to: qa
sprint: 123
filed_at: 2026-11-16
refers_to:
  - design/int/session-transaction.md
  - design/arch/symbol-table-lifecycle.md
  - sprints/s123-api-packet.md
---

## Observation

Unmeasured; raised by `arch` while deciding packet row P15 (S123 W4).

If an entry's source returns to identical text after ABI-changing edits in
one session, a dependent module's cached object can pass validation while
embedding an authored entry slot that has since moved. The tombstones from
those edits do not prevent it. The hazard exists with or without P15, and
P15 does not cause it.

## Request

Decide whether it is real, and if so allocate a minimal reproduction. A
candidate: a dependent module importing the entry is cached; in one session
the entry's definition changes ABI and is reverted to its original text; a
later launch loads the dependent from cache and calls the entry.

**Falsifier:** cache validation of the dependent fails, or the entry's
authored slot does not move under the ABI-changing edit.
