---
number: 0533
target: /design
filed_by: /sprint
filed_at: 2026-07-06
sprint_filed: 103
refers_to: design/int/session-transaction.md §7.1 (slot policy), §10 (T1 trigger), src/redefine.rs::is_t1_downgrade
status: open
---

# Confirm: a deftype ctor arity-change stays uncured T1 residue under the F2 slot-refinement

## Issue
S103 Wave 4's F2 slot-refinement gates the T1 trigger on
`(new_slot.is_none() || old_slot.is_none())` — a slotted→slotted redefinition does NOT
trigger the reload, on the rationale that a reused slot with an in-place patch late-binds
correctly.

The Wave-4 /review (Lens 2) noted one edge the "reused slot late-binds correctly" rationale
does not cover: a `deftype` ctor **arity change** (`Point [x]` → `Point [x y]`) is
slotted→slotted (both slots `Some`) → excluded → no reload and no report, yet it late-binds
to an **incompatible arity**. If the §7.1 slot policy allocates a *fresh* slot for that ABI
change, both slots are `Some` and the case is silently excluded — a residual silent
split-world with no report.

This is design-acknowledged T1 residue (not introduced by Wave 4), but it was never
explicitly confirmed as intended-uncured.

## Proposed resolution
`/design` (session-transaction) to confirm whether a ctor arity-change is:
- (a) intended to stay uncured T1 residue (document it as such in §10, with the rationale
  that arity-changing a ctor is a rarer/harder case deferred with the rest of the T1
  residue), OR
- (b) a case the F2 predicate should NOT exclude (i.e. the slot policy should signal it so
  the trigger fires and the reload cures it).
If (b), the predicate needs a companion signal (an ABI-surface delta, not just slot
identity) — coordinate with the §7.1 slot policy.

## Operational implication / Context
Low-frequency case (arity-changing an existing ctor mid-session). Confirmation-level, not a
shipped-defect. If it should be cured, it is a small predicate refinement; if intended
residue, it is a one-line §10 documentation pin. Relates to [[0507]] (T1 design holes) and
the F2 slot-refinement landed in Wave 4.
