---
number: 0215
target: /dev (intrinsics) or /qa
filed_by: /sprint
filed_at: 2026-05-17
sprint_filed: 68
refers_to: crates/cranelisp-intrinsics/src/heap_string.rs (test_alloc_string_null_ptr around line 208), spec/12-runtime.md §12.1.2
status: open
---

# `heap_alloc_string(null, 0)` SIGABRTs instead of producing empty heap string

## Issue

Wave 6 `/review (intrinsics)` surfaced an existing test failure:

`heap_string::tests::test_alloc_string_null_ptr` — SIGABRTs (null-deref) when calling `heap_alloc_string(null, 0)`.

Per `spec/12-runtime.md §12.1.2` (cited in the test's own comment per the reviewer report), null + zero-length should produce an empty heap string, NOT crash. The test was authored against the spec but the implementation has not been guarded.

Not introduced by Sprint 68 — `cranelisp-intrinsics` had no source changes this sprint. Either pre-existing or surfaced by per-crate isolated test run in Wave 6.

## Proposed resolution

Validate against spec per `memory/feedback_validate_tests_against_spec.md` — confirm the test's spec citation is accurate; then either:

1. `/dev (intrinsics)` adds null-guard in `heap_alloc_string` for the `(null, 0)` case, returns empty heap string per spec.
2. If the spec citation is wrong (test expectation drift), `/qa` revises the test to match spec.

Spec-first per memory rule.

## Operational implication / Context

Not blocking S68 deliverables (S68 made no `cranelisp-intrinsics` source changes). The test isn't in the s68_primitives_uniform suite; surfaced only when per-crate `cargo nextest run -p cranelisp-intrinsics` runs. Pre-existing or platform-dependent.

Should be triaged early in S69 to determine whether it's a real runtime defect or a test-authoring drift. If real, it's a spec-violation defect; if test-authoring drift, low-priority cleanup.
