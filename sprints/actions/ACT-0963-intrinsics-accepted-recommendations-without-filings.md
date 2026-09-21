---
id: ACT-0963
title: Deliver the two accepted intrinsics audit recommendations that never received a filing
status: open
priority: required
from: audit
to: arch
sprint: 122
filed_at: 2026-09-21
refers_to:
  - crates/cranelisp-intrinsics/src/lib.rs
  - crates/cranelisp-intrinsics/src/catalog.rs
  - crates/cranelisp-intrinsics/src/catalog/tests.rs
---

## Request

Provenance: the S115 `cranelisp-intrinsics` whole-context assessment
([historical assessment](https://github.com/alilee/cranelisp/blob/57253cf2/audits/cranelisp-intrinsics-s115.md), §6 R-2 and R-4, §7
trail). The user accepted both on 2026-07-22 as "FIXME 0849" and "FIXME 0851".
Neither file was ever added (`git log --all --diff-filter=A -- 'design/arch/fixmes/0849*' 'design/arch/fixmes/0851*'`
is empty), so both accepted items lapsed without an owner. This action is that
missing filing; it approves nothing new.

1. **Catalog-count recurrence (R-2).** `crates/cranelisp-intrinsics/src/lib.rs`
   crate rustdoc still states "16 core + the 12 `cranelisp_trace_*` family +
   `catch-runtime-error`" and cites `name_set_is_exactly_the_expected_29`; the
   live test is `name_set_is_exactly_the_expected_38`
   (`crates/cranelisp-intrinsics/src/catalog/tests.rs`). This finding was closed
   once (S87 HIGH-1) and recurred because the cited symbol's name encodes the
   count. The accepted cure is at the mechanism: a count-free test name, and
   rustdoc that states composition with no integer and no number-bearing symbol,
   leaving `EXPECTED_NAMES.len()` as the only count.
2. **`IntrinsicEntry::is_runtime` (R-4, remaining half; S87 F4 before it).**
   The field is `pub` (`crates/cranelisp-intrinsics/src/catalog.rs`) with no
   reader outside the crate's own derivation test; the only other hit is a
   prose mention in `crates/cranelisp-backend/src/jit.rs`. The other half of
   R-4 (`reset_counts`/`bytes_peak`) is gone from non-test source. Narrowing or
   removing a `pub` field changes `public-api.txt`, so it passes the
   inter-crate public-API user gate through `arch` before `dev` edits.

## Completion evidence

- No integer catalog count and no count-bearing symbol name in crate rustdoc
  or the catalog test name; the name-set test still pins the exact set.
- `is_runtime` is either non-public (baseline regenerated in the same
  change-set, user-confirmed diff) or has a named production consumer; if the
  user instead declines, the decline and its reason are recorded here before
  this action is deleted.
