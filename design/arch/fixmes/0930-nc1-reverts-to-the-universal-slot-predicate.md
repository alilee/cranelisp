---
number: 0930
target: /qa
filed_by: /arch
filed_at: 2026-07-28
sprint_filed: 119
refers_to: design/arch/total-concreteness.md §1/§2/§4;
  tests/plan/s119-test-plan.md §3.7 NC-1 (the fdea7e29 kind-partition table);
  design/arch/safety-invariants.md §4 R11;
  src/bootstrap.rs:884-905 (bind is slot-less PrimitiveExtern), :1129-1160
  (catch-runtime-error likewise);
  crates/cranelisp-primitives/src/declarations.rs:660-671 (vec-len, the one
  slotted polymorphic primitive)
status: open
---

# NC-1 reverts to the universal slot predicate — the kind-partition table is superseded and its counterexamples are factually wrong

The user overruled the S119 kind-partition as end state
(`design/arch/total-concreteness.md` §0); `/arch` has re-ruled the slot
invariant target-universal (§2 I-CONC): for every entry,
`callable_got_slot().is_some() ⇒ scheme.ty.is_concrete()` — whole-table, no
kind licences.

Two things for `/qa` to action in `tests/plan/s119-test-plan.md` §3.7 before
`/testing` authors NC-1:

1. **Factual correction.** The table's motivating counterexamples — "`bind :
   ∀a b.…` and `catch-runtime-error : ∀a.…` are polymorphic slotted primitives
   from bootstrap" — are wrong at source: both are slot-less
   `DefKind::PrimitiveExtern`, by-name `Linkage::Import` (FIXME 0360;
   `callable_got_slot()` → `None` structurally). A universal sweep does NOT
   RED on them. The error originates in `/arch`'s own `f5d30808` and
   propagated; `/arch` has corrected its copies (BC §7, `interfaces.md`,
   `module.rs` rustdoc, R11).

2. **Form reversion.** NC-1 becomes the single universal predicate, with the
   transitional slotted-polymorphic populations as **intentional REDs against
   open items** (the failing-not-ignored convention): (a) the two `UserFn`
   hand-mints — flips with CS-1/P-1 this sprint; (b) every generic-ADT ctor
   template incl. `IO.Bind` — RED against FIXME 0931 (S120 ctor tranche);
   (c) `vec-len` — RED against FIXME 0932 (S120 de-slot). A pinned allow-list
   spelling (each expected-RED entry citing its FIXME) is acceptable and is
   `/qa`'s choice. Partner cell: the I-ABI roster pin (`total-concreteness.md`
   §3.3) — the slot-less polymorphic import roster (`bind`, `race`, `select`,
   `catch-runtime-error`) enumerated exactly; a new member REDs until
   declared. NC-5 is unchanged.

Delete this file when the plan row is corrected.
