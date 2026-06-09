---
number: 0303
target: /arch
filed_by: /sprint
filed_at: 2026-06-09
sprint_filed: 77
refers_to: crates/cranelisp-types/src/resolve.rs (substitute_module_alias — crate-private), src/worker.rs (resolve_module_alias — byte-identical re-impl)
status: open
---

# Promote `substitute_module_alias` to the `cranelisp-types` public surface (Principle 7 dedup)

## Issue

Sprint 77 W-Module (FIXME 0121 fix) added `src/worker.rs::resolve_module_alias`,
a byte-identical re-implementation of the crate-private
`cranelisp_types::resolve::substitute_module_alias` (the spec §8.6.6 longest-prefix
dot-segment module-alias substitution). The int side cannot call the original
because the FQ-autoload boundary in `recognize` runs before typecheck and the fn
is not exported.

Two copies of the §8.6.6 algorithm now age independently — exactly the
single-source-of-truth divergence Principle 7 warns against. Surfaced by the
W-Module `/review` gate (Important finding; not a commit blocker — the fix is
correct and the duplication is documented in `src/CLAUDE.md`).

## Proposed resolution

Promote `substitute_module_alias` (and any minimal supporting types) to the
public surface of `cranelisp-types` so both the typecheck consumer and the int
autoload-boundary `recognize` site share one implementation. Regenerate the
`cranelisp-types` baseline + cascade the facade/bounded-context note in the same
change-set (baseline-diff discipline). Then `src/worker.rs::resolve_module_alias`
deletes and calls the types fn.

## Operational implication / Context

Cross-crate public-surface change → `/arch`-owned. Stage 2/3 quality item (no
failing test; the behaviour is correct today). A types-crate public-API addition
is non-breaking (additive).
