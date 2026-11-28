---
id: ACT-1115
title: Specify the reanchoring fallback when no form in the cluster expanded
status: open
priority: advisory
from: sprint
to: design
sprint: 126
filed_at: 2026-11-28
refers_to:
  - design/int/macro-diagnostic-reanchoring.md
  - src/process_form.rs
---

## Request

`design` on `src/` disposes of `review`'s S125 advisory on the reanchoring
repair ([§2.2](../../design/int/macro-diagnostic-reanchoring.md)).

Verified 2026-11-28: `src/process_form.rs::reanchor_finalize_error` has a
case for an error whose start matches no node in any expansion when every
form is unchanged. In that case it selects the first written form and appends
`in expansion of`, although no macro expanded. §2.2 does not define this case,
and no reachable compiler scenario has been established.

## Completion evidence

§2.2 states the outcome for this case, and a unit cell pins it. Alternatively,
the case is shown unreachable and the code says so.
