---
number: 0931
target: /design (typecheck, backend)
filed_by: /arch
filed_at: 2026-07-28
sprint_filed: 119
refers_to: design/arch/total-concreteness.md §3.1;
  crates/cranelisp-types/src/lifecycle.rs;
  crates/cranelisp-types/src/module.rs;
  src/bootstrap.rs;
  crates/cranelisp-typecheck/src/adt.rs;
  crates/cranelisp-typecheck/src/traits/monomorphise.rs;
  tests/plan/s122-evidence-delta.md
status: open
---

# Constructor templates are slotless — one evidence tail remains

## Current state (verified 2026-09-25)

- **Delivered.** A non-concrete constructor is a slotless template; value-
  position demand mints a concrete instance through the one canonical mangler.
  Source carries the boundary structurally: `Life::Template` has no slot or
  view, `Life::Concrete` carries the `CallableSlot`
  (`crates/cranelisp-types/src/lifecycle.rs`), and the settlement funnels
  install either state. `src/bootstrap.rs` and `crates/cranelisp-typecheck/src/adt.rs`
  build slot-free constructor recipes; monomorphisation mints instances
  through `InstanceLink`. The contract is
  `design/arch/total-concreteness.md` §3.1.
- **The original mechanism is superseded.** The proposed separate constructor
  state sum, its slot-mint vocabulary and its dedicated schema window were not
  built; the unified lifecycle replaced them. Do not restore either or add a
  second mangler. Git retains the original commission.
- **QA dispositioned the measurements on 2026-09-10**
  (`tests/plan/s122-evidence-delta.md`): MEASURE-C1 and MEASURE-C2 belonged
  to the superseded migration and are retired, and instances are placed in the
  caller module rather than accumulating in `primitives`. Existing unit
  companions pass: `adt::tests::polymorphic_constructors_are_slotless_templates`,
  `traits::monomorphise::tests::rechecked_bare_constructor_value_mints_and_carries_its_concrete_instance`
  with its imported-caller twin, and
  `module::tests::concrete_to_template_conserves_and_never_reissues_prior_slot`.

## Remaining obligation

No current executing observation covers the **whole bootstrap constructor
population** (the retained NC-1 sweep) or the numeric **R17 constructor
partition** in [safety invariants](../safety-invariants.md). The typecheck and
backend design owners either identify an existing witness using the
bootstrap-table and corpus/CLIF facilities, or record a source-backed
supersession. No source defect is attributed; do not recreate kind-specific
machinery to preserve an obsolete test label.

## Closure

A current witness or recorded supersession exists for both populations, and
`design/arch/total-concreteness.md` §3.1 drops its open bullet.
