---
id: ACT-0984
title: Reconcile obsolete link-mode trace rejection test
status: open
priority: normal
from: arch
to: qa
sprint: 122
filed_at: 2026-09-22
refers_to:
  - spec/04-expressions.md
  - design/arch/tracing.md
  - tests/s68_primitives_uniform.rs
---

## Source-read evidence conflict

`tests/s68_primitives_uniform.rs::s68_trace_in_link_mode_rejected_at_link_time`
asserts link-mode rejection of tracing, contrary to the approved all-mode
behavior in the language spec and tracing architecture. Its diagnostic assertion
accepts output containing "trace", so success would not establish a valid
rejection. The test was not executed during documentation cleanup.

QA assesses its assertions and the existing positive evidence in
`tests/link.rs::link_traced_extern_primitives_appear_as_children_exit_42`.
Choose the smallest truthful disposition: retire a superseded redundant test,
or correct it if a distinct current obligation survives. Test owns the resulting
change and focused verification. Do not treat the old rejection expectation as
a language decision or infer conformance from a passing result.

Provenance: arch session `0dfbd0d5-5956-499a-b093-0f94fe15b56c`, consolidation
of decisions 0040, 0044 and 0048. This action preserves the unresolved evidence
question; no test or behavior was changed in that pass.
