---
number: 0848
target: /dev
filed_by: /sprint
filed_at: 2026-07-22
sprint_filed: 116
refers_to: audits/cranelisp-intrinsics-s115.md §6 R-1; crates/cranelisp-intrinsics/src/diagnostics.rs; tests/ms_p6_mode_self_tests.rs
status: open
---

# Intrinsics diagnostic modes need production-path detection proofs

## Issue

Accepted S115 intrinsics-audit recommendation R-1. M1 quarantine and M2 scrub are asserted but unproven at the production funnels; M3 proves only its pure report function in committed tests; the A1–A4 release faces behind `CRANELISP_RC_DEC_CHECK` have no positive detection tests.

## Proposed resolution

Add an inert-unless-test fault-injection hook at the intrinsics allocator/diagnostics seam. Plant and detect faults through `alloc_with_rc`/`dealloc` for M1, M2, M3 and A1–A4, demonstrate fail-on-revert discrimination, and coordinate with `/testing` for the end-to-end M3 counter→atexit→abort cell. `/qa` regrades R8 only after the proofs land.
