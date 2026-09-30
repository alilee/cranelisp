---
id: ACT-0963
title: Narrow the public IntrinsicEntry::is_runtime field or name its production consumer
status: deferred
priority: required
from: audit
to: arch
sprint: 122
filed_at: 2026-09-21
refers_to:
  - crates/cranelisp-intrinsics/src/catalog.rs
---

## S122 disposition (user-approved 2026-09-30)

Under the [approved S122 disposition](../../tests/plan/s122-evidence-delta.md#final-disposition-proposal-2026-09-30):

- **Carried to S123 (K11, public-API baseline batch).** First deferral of
  this S122 filing; the S115 recommendation it restores lapsed unfiled, with
  no recorded deferral. It lands in one `arch` batch with ACT-0955 and
  ACT-0971, under the pre-implementation API gate.
- Source on 2026-09-30: `pub is_runtime` is still in `catalog.rs`. The only
  `.is_runtime` reads are in its module test `is_runtime_classification`
  (`catalog/tests.rs`); the remaining mentions are prose in
  `crates/cranelisp-intrinsics/src/lib.rs` and
  `crates/cranelisp-backend/src/jit.rs`.

## Request

Provenance: the S115 `cranelisp-intrinsics` whole-context assessment
([historical assessment](https://github.com/alilee/cranelisp/blob/57253cf2/audits/cranelisp-intrinsics-s115.md), §6 R-4, §7
trail), accepted by the user on 2026-07-22 as "FIXME 0851", which was never
filed. This action is that missing filing; it approves nothing new.

**`IntrinsicEntry::is_runtime` (R-4, remaining half; S87 F4 before it).** The
field is `pub` (`crates/cranelisp-intrinsics/src/catalog.rs`) with no reader
outside the crate's own derivation test. The other half of R-4
(`reset_counts`/`bytes_peak`) is gone from non-test source. Narrowing or
removing a `pub` field changes `public-api.txt`, so it passes the inter-crate
public-API user gate through `arch` before `dev` edits.

## Completion evidence

- `is_runtime` is either non-public (baseline regenerated in the same
  change-set, user-confirmed diff) or has a named production consumer; if the
  user instead declines, the decline and its reason are recorded here before
  this action is deleted.
