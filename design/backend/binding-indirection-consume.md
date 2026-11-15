# The binding-indirection consume contract (0668) — retired

**Owner:** `design`, narrow-deployed to `cranelisp-backend`. **Subordinate to:**
[backend.md](backend.md).

**Status:** retired at S123 W2 by [uniform counting](uniform-counting.md). This
was the S114 contract that decided each consume position's RC accounting by
tracing its operand's provenance root. Under uniform counting every position
consumes and no rule reads operand provenance, so the contract has no subject.
The full text is in Git history.

The file remains only because tests cite the section numbers below. It is
deleted once those citations point at uniform counting.

## 1. The seam verdict

Retired. It found that consume-position accounting was decided by local node
syntax; the provenance classifier replaced that, and uniform counting replaced
both.

## 2. The contract — consume-position × operand-provenance

Retired. A variable operand moves at its binder's last use and duplicates
otherwise; a temporary transfers
([uniform counting](uniform-counting.md) §1, §4).

## 4. The family matrix and the F4 ownership boundary

Retired. The family's faults are mapped in
[uniform counting](uniform-counting.md) §6. The analysis-on escape-fact face
it excluded was typecheck's; the COW producer no longer reads the escape fact.

## 5. Dev-wave work items

Retired. The per-site work items are deleted with the provenance classifier.

The two leak-direction siblings this contract recorded, F-R1 (entry-`main` IO
teardown) and MS-P8 (`conj`/`assoc` in a loop), both pass, and no mechanism was
ever recorded for either. If either repro regresses, attribute it afresh: the
seams it named no longer exist.
