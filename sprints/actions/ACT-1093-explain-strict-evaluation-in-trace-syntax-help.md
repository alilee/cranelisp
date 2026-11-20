---
id: ACT-1093
title: Explain strict evaluation in the trace syntax help
status: open
priority: advisory
from: docs
to: dev
sprint: 124
filed_at: 2026-11-20
refers_to:
  - src/syntax/cheatsheet.txt
  - spec/04-expressions.md §4.12.2
  - spec/12-runtime.md §12.4.3
  - tests/trace.rs
---

## Request

For the next scheduled `dev` invocation on `src/`, add a short note to
`/syntax trace`: evaluation inside a trace is strict, so its elapsed time
does not measure the ordinary parallel execution of the same computation.
Keep the precise rules in spec §4.12.2 rather than copying them into help.

## Assessment evidence

`docs` opened the `trace` topic in `src/syntax/cheatsheet.txt` during the
S124 Phase 6a assessment against source checkpoint `46e195c7`. It shows
`nanos` as elapsed nanoseconds and explains nested tracing, but does not
mention the strict-evaluation exception. A reader using the help to time
a parallel computation cannot learn this qualification there.

The delivered exception is evidenced by
`tests/trace.rs::trace_records_every_call_of_spark_admitted_callee` and
`tests/trace.rs::s124_1038_untraced_sparks_control`, accepted in the
[S124 traceability assessment](../../tests/plan/s124-evidence-delta.md#11-the-traceability-band).
This assessment did not
rerun those tests. This is a help-content coverage finding, not a newly
discovered compiler defect or a request to change trace semantics.

The companion prose explanation is proposed for `user/` in the docs
Phase 6b plan. The static help asset belongs to the binary surface;
`docs` leaves it unchanged. This advisory can be scheduled separately
without blocking the prose change.

## Completion evidence

`/syntax trace` names the strict-evaluation qualification beside its timing
example and retains its existing normative reference. The owning role
checks the rendered topic with the existing syntax-help evidence.
