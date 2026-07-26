---
number: 0910
target: /testing
filed_by: /qa
filed_at: 2026-07-26
sprint_filed: 118
refers_to: tests/s117_ownership_witnesses.rs::{r2_alias_of_string_identity_has_production_clif_transfer,
  r2_borrowed_scalar_result_has_production_clif_polarity};
  design/backend/transitive-drop-glue.md §7 (W3 release-site collapse);
  tests/fixtures/clif_baseline/MANIFEST.md §Re-baselines (S118 entry, drift class 1)
status: open
---

# Two S117 CLIF-witness oracles grep for the pre-W3 inline release and are stale against canonical glue

## Issue

W8 gate finding (both full runs, deterministic; also fail focused). Two
`s117_ownership_witnesses` cells pin their ownership invariants through the
TEXTUAL signature of the legacy inline release — `atomic_rmw.i64 sub` at the
wrapper's final owner release. The S118 W3 consumer migration
(`2df95c41..966d298e`) collapsed exactly that sequence into ONE canonical
glue call (`call fnN(ptr)`, `fnN = colocated u0:NN`, void `(i64)` signature),
so both oracles now fail on text while their invariants hold:

1. `r2_borrowed_scalar_result_has_production_clif_polarity` — asserts the
   conservative all-Owned arm contains `atomic_rmw.i64 sub` and the precise
   arm does not. **Verified at gate**: the precise arm ends `return v16` with
   NO release (Borrowed elision intact); the conservative arm carries exactly
   one `call fn0(v1)` glue release. The precision-vs-conservative difference
   the cell exists to pin is alive; only the release's spelling moved.
2. `r2_alias_of_string_identity_has_production_clif_transfer` — asserts
   `store notrap aligned` (the protect) AND `atomic_rmw.i64 sub` (the
   transfer release). **Verified at gate**: protect present, and the
   transferred argument is released exactly once via `call fn0(v1)`.

NOT a compiler regression: the behavioral siblings
(`r2_*_all_modes`) pass, backend 527/527, and the glue-call shape matches the
MANIFEST S118 drift class 1 certification.

## Proposed resolution

Re-express both release-side expectations in terms of the canonical glue
call (e.g. exactly one `call fnN(` on the release path where a release is
required, and its ABSENCE on the Borrowed-precise arm), keeping the
protect/retain (`atomic_rmw.i64 add` / `store notrap aligned`) halves as-is.
Do not weaken polarity: the precise-vs-conservative DIFFERENCE assertion must
survive the re-expression. Delete this file in the fixing change-set.
