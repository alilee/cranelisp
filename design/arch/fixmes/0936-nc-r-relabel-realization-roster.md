---
number: 0936
target: /qa
filed_by: /arch
filed_at: 2026-07-28
sprint_filed: 119
refers_to: design/arch/concreteness-types-first.md §1.3 (the ruling);
  tests/plan/s119-test-plan.md §3.7 NC-R;
  design/arch/total-concreteness.md §2 I-ABI + §3.3 (superseded record)
status: open
---

# NC-R survives mechanically but its rationale is re-labelled: the backend uniform-realization roster, not an I-ABI licence class

Per the user-directed re-ruling (R-25/R-27; I-ABI → I-EMIT,
`concreteness-types-first.md` §1), the four by-name callables are no longer a
sanctioned class of "polymorphic callables at the typecheck boundary". NC-R's
**mechanical assertion is unchanged and still wanted at HEAD** — the
`DefKind::PrimitiveExtern` entries with non-concrete schemes are exactly
{`bind`, `race`, `select`, `catch-runtime-error`}; a silent fifth member REDs
— so `/testing` may build the cell now. What `/qa` re-labels in the plan row
(and the cell's rustdoc, via `/testing`):

1. **Meaning**: the cell pins the **backend uniform-realization roster** — the
   set of hand-written bodies one compiled body of which serves multiple
   concrete call-site instantiations — each member carrying its declared
   representation dependencies. Not a licence; an enumerated backend-interior
   contract.
2. **Trajectory**: `bind`/`race`/`select` LEAVE the set at their inline
   re-kind (S120/S121 wash — the cell's expected set shrinks in that
   change-set); `catch-runtime-error` remains the standing member. `vec-len`
   joins only if 0932 chooses spelling (b); `/arch`'s recorded preference is
   (a) Inline, keeping the roster at one.
3. The I-ABI citation in the row's provenance text is replaced by
   `concreteness-types-first.md` §1.3.

Delete this file when the plan row and cell rustdoc carry the new label.
