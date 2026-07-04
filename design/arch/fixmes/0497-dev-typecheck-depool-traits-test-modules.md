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

## S102 Wave-8b-2 partial drain (`/dev`, the pass5 CS-1..4 visit)

**Drained this visit:**
- **`dispatch.rs`** — the 8-test `primitive_dispatch_tests.rs` pool relocated
  verbatim (content-unchanged) to a `dispatch/tests.rs` sibling reaching
  `primitive_for_trait_method` via its own `use super::*`; the traits-root
  test-only `pub(crate) use dispatch::*;` re-export retired. `dispatch.rs` now
  has an attributed sibling test module.
- **The new `ownership/` cluster is born-compliant** (0497's own goal for new
  code): CS-1..CS-4 each landed a per-submodule test module
  (`classify/tests.rs`, `transfer/tests.rs`, `confinement/tests.rs`,
  `fixpoint/tests.rs`, `publish/tests.rs`) with the §13.7 Principle-23 matrices
  (complexity/edge/negative), scenarios exercised through the pure seams — 53
  tests, strong negatives.

**Remainder, re-deferred with rationale (NOT by habit):**
- **`traits/tests.rs` (1293 LOC, ~41 tests) split** across
  `monomorphise`/`impl_check`/`type_resolve`/`registry`, and the
  `monomorphise.rs` instantiation-matrix gap-fill (step ii). Rationale: this is
  a large mechanical relocation orthogonal to the pass5 payload; folding it into
  the pass5 landing violates the one-change-set-at-a-time discipline, and (per
  §13.7 step ii) it is meant to **coordinate with `/qa`'s 0488 isolation**,
  which "may add the attribution test first" and "may land in `monomorphise.rs`
  mid-sprint" — doing the split before that isolation lands risks a merge
  collision on the same file in the shared working tree. Sequencing: rides the
  next `/dev` typecheck visit that touches `monomorphise.rs` (the 0488 fix or a
  dedicated de-pool visit), after/with `/qa`'s 0488 attribution.
- **`scheme.rs`/`scope.rs` negatives** — the capacity-gated tail 0497 itself
  names; re-deferred per its own terms.

Trigger for full drain + FIXME deletion: the next typecheck `monomorphise.rs`-
touching visit (coordinated with `/qa` 0488).
