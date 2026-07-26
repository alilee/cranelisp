---
number: 0908
target: /testing
filed_by: /qa
filed_at: 2026-07-26
sprint_filed: 118
refers_to: tests/clif_golden_lane.rs::clif_golden_lane_no_drift;
  tests/golden_clif_w0b.rs::golden_clif_w0b_synth_accessor;
  tests/fixtures/clif_baseline/golden/ (11 frames); tests/fixtures/clif_w0b/;
  tests/plan/PLAN.md §I.3 (L-B1 lane certification); s118-test-plan.md §11
status: open
---

# Golden CLIF lanes owe a SCOPED + ATTRIBUTED re-baseline for the W3 canonical-glue emission change

## Issue

Two golden cells are RED at HEAD on **verified expected-output drift** from
the S118 W3 consumer migration (change-set `2df95c41..966d298e`), not on a
behaviour defect:

1. `clif_golden_lane::clif_golden_lane_no_drift` — **11 frames drifted**:
   `01_adt_construct_match`, `02_closures_fn_as_value`, `03_auto_curry`,
   `04_vec_cow_loop`, `05_string_externs`, `07_trait_dispatch`,
   `08_adt_in_vec_projection`, `f1_machinery`, `f2_contention`,
   `f3_inverted_search`, `f4_sudoku`.
2. `golden_clif_w0b::golden_clif_w0b_synth_accessor` — the `02_synth_accessor`
   lenient-class golden.

## `/qa` drift verification (2026-07-26, pre-gate pass)

Every inspected hunk is the same release-site reshape, in both lanes: the
inline guarded-dec sequence (`iadd_imm ptr,8; atomic_rmw sub; icmp eq; brif;
fence; call <dealloc/embedded-glue>` and the inline `iconst.i64 1024` nullary
guards / `DROP_GLUE_PTR` loads at +24) is replaced by ONE call to the
canonical named per-concrete drop glue (`fn = colocated u0:NN` with void
`(i64)` signature — the dec/guard/teardown now live inside the glue body,
which is exactly `transitive-drop-glue.md`'s design). Signature-table and
value-renumbering deltas are consequences of the removed instructions. No
arithmetic, allocation, dispatch, or control-flow hunk outside the release
family was found. Corroborating behaviour evidence: backend 527/527; all
consumer-family guards green; W3 armed acceptance legs balanced both
toggles; three-round delegated review GATE PASS.

## Action (`/testing`)

Re-capture BOTH lanes scoped and attributed per the S102 §6.2 discipline
(`tests/scripts/clif_golden.sh capture` for the 11 named frames; the w0b
golden per `tests/fixtures/clif_w0b/MANIFEST.md`), citing the W3 change-set
`2df95c41..966d298e` as the emission-affecting change in the commit body.
Do NOT re-capture wholesale-blindly: eyeball each frame's diff for the
glue-call shape above before accepting it — a hunk outside the release
family is a finding, not a baseline.

**Sequencing recommendation:** land before W8's full-suite gate run so the
gate's failure set carries no rebaseline noise.
