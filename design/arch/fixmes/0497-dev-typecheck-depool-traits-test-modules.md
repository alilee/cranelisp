---
number: 0497
target: /dev
filed_by: /qa
filed_at: 2026-07-03
sprint_filed: 101
refers_to: crates/cranelisp-typecheck/src/traits/, sprints/METHOD.md §2.2, tests/plan/coverage-audit-s101.md §3.4
status: open
---

# Typecheck: de-pool `traits/` — per-submodule test modules for the mono/impl/dispatch cluster

**Crate**: cranelisp-typecheck (`/dev` narrow).

## Issue

cranelisp-typecheck is the project's organizational exemplar (per-submodule
`tests.rs`, ~480 attributable tests, strong negatives) — with one local instance
of the 0494 anti-pattern: the `traits/` cluster pools ~3,130 LOC of
strategy-dense code behind one 41-test `traits/tests.rs` (+8-test
`primitive_dispatch_tests.rs`), with **zero inline/sibling tests** in:

- `traits/monomorphise.rs` (1,070 LOC) — mono-instance emission
  (`register_mono_entry`, `finalize_mono_codegen_view`, inner-parametric hops);
  the most strategy-dense single module in the crate, and the crate-side neighbor
  of the 0488 missing-mono defect class.
- `traits/impl_check.rs` (842) — the S101 0472 seam (impl-method callee harvesting).
- `traits/type_resolve.rs` (453), `traits/dispatch.rs` (411),
  `traits/registry.rs` (357).

Also happy-path-only (0 negatives): `scheme.rs`, `cluster.rs` (SCC), `scope.rs`.

## Proposed resolution

Per METHOD §2.2: relocate/attribute the pooled `traits/tests.rs` tests to sibling
per-submodule test modules, then fill the taxonomy gaps ({complexity, edge,
negative}) — priority on `monomorphise.rs` (instantiation matrices: value-position,
FQ-reference, ≥2 instantiations — the crate-side pins for whatever share of 0488's
cure lands here) and negatives for scheme/cluster/scope.

## Operational implication / Context

Rides the next typecheck change-set (likely the 0488 isolation/fix in S102, which
will touch monomorphise/dispatch). Low urgency relative to 0495/0496; filed so the
per-crate thinness map has an owner for each flagged surface.
