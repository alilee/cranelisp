---
number: 0376
target: /design
filed_by: /arch
filed_at: 2026-06-16
sprint_filed: 84
refers_to: design/typecheck/monomorphisation.md, design/arch/bounded-contexts.md §2 + §7, design/arch/principles/20-model-invariants-by-representation.md, design/arch/fixmes/0374-*.md
status: open
---

# Re-ground monomorphisation.md on the structural-slot-gate-first model (S84 user ruling)

## Issue

The Phase-3 `design/typecheck/monomorphisation.md` (and `typecheck.md` §9.3/§10/§13) framed Tier-2 full-monomorphisation around an **ambiguity check + `Type::contains_var()`** as the primary concreteness enforcement, with the monomorphisation pass chasing coverage shape-by-shape. A user architectural ruling mid-S84-Phase-5 (Principle 20 S84 generalisation, BC §7 "Callability is structural", FIXME 0374 re-shape) **inverts the primacy**:

- **The GOT-slot-allocation gate is the structural primary.** A def has a slot ⟺ its type is fully concrete (`Type::is_concrete()`, no `Type::Var`). A non-concrete def is slot-less by construction and cannot reach codegen as a value. This is enforced at the typecheck slot-allocation gate (`program.rs:947`/`:1143`), which must test `is_concrete()` — NOT `constraints.is_empty()` (the as-built leak: "unconstrained" ≠ "concrete"; a generic-unconstrained def passed the gate and got a slot while carrying a `Type::Var`).
- **`Type::contains_var()` ambiguity check (0373 ii) is a SECONDARY backstop**, not the mechanism — it catches genuinely-ambiguous top-level forms, while the slot gate is what makes a residual `Type::Var` at codegen structurally impossible.
- **Coverage is forced by the representation, not chased shape-by-shape.** "Is this def concrete?" becomes "does it have a slot?" — a structural property of the data model (Principle 18). The pass mints a concrete slotted instance per *reachable* use; anything left slot-less is either never-used-as-a-value (fine) or the ambiguity error.

## Proposed resolution

Re-ground `design/typecheck/monomorphisation.md` (and the `typecheck.md` cross-refs) so the **structural slot gate is the primary concreteness guarantee** and the `contains_var` ambiguity check is named as the secondary backstop. Specifically:

1. State the invariant "slot ⟺ `is_concrete()`" as the spine, citing BC §7 + Principle 20 + `Type::is_concrete()` (`crates/cranelisp-types/src/types.rs`, landed by /arch S84).
2. Document the gate correction (`constraints.is_empty()` → `is_concrete()` at `program.rs:947`/`:1143` + reuse legs `:919`/`:1129`/`:1312`) and the slot-less `fn_state` arm (sibling to `Constrained`) for the determined-but-non-concrete unconstrained generic def — including the /design call on whether it is a distinct new `UserFnState` variant or a reuse (with the cache `CACHE_SCHEMA_VERSION` 5→6 bump consequence IF a new variant lands; coordinate with /backend).
3. Re-scope the Tier-2 deliverable to the **Wave-0-refined narrower gap**: the `(Box a)`-field-through-HOF instance (NOT the bare-Int HOF instances, which already mono cleanly and are GREEN-stay guards) — per `tests/plan/ledger.md` §Sprint-84-Wave-0.
4. Keep the 0344/0349 fold-accumulator over-monomorphisation as the pinned risk; the result-var gate relaxation must not re-collapse the accumulator's shape.

## Operational implication / Context

This is a /design(typecheck)-owned doc; /arch does not edit it (boundary). The arch-side manifestation sites are already updated: Principle 20 (S84 generalisation), BC §2 (structural-gate-primary paragraph) + §7 (slot ⟺ concrete), `interfaces.md` (§"Callability is structural" S84 paragraph), FIXME 0374 (re-shaped), FIXME 0375 (backstop-not-mechanism). `Type::is_concrete()` is landed in `cranelisp-types`. This FIXME re-grounds the per-crate design doc to match before /dev implements in Wave 1.
