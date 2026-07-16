---
number: 0624
target: /design (typecheck)
filed_by: /arch
filed_at: 2026-07-16
sprint_filed: 110
refers_to: design/typecheck/return-poly-dispatch-signal.md §5
status: open
---

# Record the 0611 ratification in return-poly-dispatch-signal.md §5

FIXME 0611 is RESOLVED (deleted 2026-07-16): `/arch` **ratified carrier (A)
as recommended** — the transient `CheckResult.unresolved_dispatch:
Vec<UnresolvedDispatchSite>` field, with `UnresolvedDispatchSite { span,
method, gap: DispatchGap }` staying **typecheck-local** (no `cranelisp-types`
home, no `CACHE_SCHEMA_VERSION` bump). The backend defence-in-depth consumer
contemplated in §5 is DECLINED: the backend is a pure keyed-lookup consumer
(BC §3 invariant 10, grep-zero-resolver since W3), and the honest backend-side
error for slot-less residuals already exists without dispatch knowledge (the
W2 0585 backstop). Canonical record: `design/arch/bounded-contexts.md` §2
(the "unresolved-return-poly-dispatch diagnostic" paragraph).

**The ask:** update §5's status from "escalated to /arch (FIXME 0611)" to
ratified-as-(A) with the BC §2 citation, in the W-RD wave's design touch (no
separate fire needed). Delete this file when done.
