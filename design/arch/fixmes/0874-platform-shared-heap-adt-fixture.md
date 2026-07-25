---
number: 0874
target: /dev
filed_by: /sprint
filed_at: 2026-07-25
sprint_filed: 118
refers_to: audits/cranelisp-platform-s117.md §R5;
  crates/cranelisp-platform/tests/cl_adt_products.rs;
  crates/cranelisp-platform/tests/cl_adt_sums.rs;
  crates/cranelisp-platform/tests/worked_examples.rs
status: open
---

# Share the raw heap-ADT integration fixture across platform test crates (audit R5)

Crate in scope: `cranelisp-platform` (test support only).

User-accepted S117 platform-audit recommendation R5 (2026-07-25, S118 Phase 1).
Quoting the assessment:

> The three integration binaries remain separate so their `GLOBAL_SCHEMA`
> lifetimes stay isolated, but import one private `tests/common` heap-layout
> fixture. The helper has one explicit layout contract and preserves the
> existing production API assertions. No new public test-support API is
> introduced.

Evidence: near-identical allocation layout at `tests/cl_adt_products.rs:51-71`,
`tests/cl_adt_sums.rs:39-63`, and `tests/worked_examples.rs:33-58` — modest
repetition sitting on the most dangerous byte-layout seam.

Cost: small. Scheduled: S118 platform slice (with 0870/0873).
