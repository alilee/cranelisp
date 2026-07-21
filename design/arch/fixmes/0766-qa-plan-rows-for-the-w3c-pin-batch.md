---
number: 0766
target: /qa
filed_by: /testing (S115 W3c)
filed_at: 2026-07-21
sprint_filed: 115
refers_to: tests/rc_escape_release_0763.rs; tests/adt_wrapped_supersede_leak_0720.rs; tests/shadowing_scope_lookup.rs; tests/ms_p6_mode_self_tests.rs; tests/plan/s115-test-plan.md §8
status: open
---

# PLAN rows owed for the W3c pin batch (10 new cells, 1 retirement, 2 upgrades)

## Severity
Minor (traceability bookkeeping — the tests are committed and GREEN; the
spec→test bridge rows are `/qa`'s to author).

## Issue

W3c landed the FIXME-0763 e2e pins and the §8 riders. Every test carries its
`// spec:` anchor (`spec/12-runtime.md` §12.3.1 for the RC cells,
`spec/04-expressions.md` §4.6.3 for the auto-curry control), but the
`tests/plan/PLAN.md` rows are `/qa`'s and are not authored here.

**New cells (all GREEN, `tests/rc_escape_release_0763.rs`)** — the escape-axis
RC-balance matrix; each asserts EXACT `allocs == deallocs` in BOTH ownership
toggle states, the A-group additionally through `--link`:

- `curried_local_closure_applied_immediately_balances` (A, control)
- `curried_local_closure_let_bound_in_same_frame_balances` (B, control)
- `curried_local_closure_escaping_its_frame_balances` (C, was 201/1)
- `curried_escaping_closure_with_string_capture_balances` (C2, was 301/1)
- `lambda_returned_through_nested_lets_balances` (D, was 301/101)
- `vec_literal_returned_through_let_balances` (E, was 201/101)
- `lambda_capturing_a_closure_balances` (F, was 301/1)
- `adt_wrapped_vec_argument_balances_both_toggles` (0753, was ON 3/2)
- `adt_wrapped_string_argument_balances_both_toggles` (0753 twin)

**New cell (`tests/shadowing_scope_lookup.rs`)** — §8.4 rider 2:
`local_closure_auto_curry_non_trait_control_resolves_to_local` (born green;
the coverage-by-definition-variants twin of the trait-shadowed auto-curry cell).

**Upgraded (`tests/adt_wrapped_supersede_leak_0720.rs`)** — the two 0720 pins
now assert EXACT balance at N ∈ {1, 2, 200, 400} in both toggles instead of the
weaker "residue ≤ 8 / does not scale"; the bare-vec control gained the toggle
axis. If a PLAN row records the old (non-scaling) acceptance wording it needs
re-wording to exactness.

**Retired (`tests/ms_p6_mode_self_tests.rs`)** —
`m3_parity_catches_planted_leak`, per your §8.2 fallback ruling; its PLAN row
(if any) retires with the in-file §4.1 tombstone as the record.

**New cells (`tests/capture_drop_glue_strands_nested_heap_0760.rs`, W3c
addendum)** — 3 intended REDs + 4 GREEN controls, all attributed to the OPEN
FIXME 0760 (`/design`(backend) ruling pending, `/dev`(backend) implements):
`closure_capturing_vec_of_strings_does_not_leak` (K, 401/201),
`closure_capturing_adt_with_string_field_does_not_leak` (L, 301/201),
`nested_adt_chain_past_glue_depth_limit_does_not_leak` (the
`MAX_DROP_GLUE_DEPTH=4` truncation, cliff measured at depth 5),
`closure_capture_controls_balance_green`,
`borrowed_argument_twins_of_k_and_l_balance_green`,
`adt_wrapping_vec_of_adts_balances_green` (the nested `solve-range` exemplar
shape — GREEN),
`nested_adt_chain_up_to_glue_depth_limit_balances_green`.

## Proposed resolution

`/qa` adds/updates the rows and the spec-side `[Tested …]` annotations. Two
observations offered as input rather than requests:

1. `spec/12-runtime.md` §12.3.1 now carries a substantial exact-balance corpus
   across the escape axis; it may warrant `[Tested+Neg]` given the pins assert
   both polarities (a leak AND an over-correction into an under-count both fail
   an `assert_eq!`).
2. The escape-axis matrix these nine cells sample by hand is the shape FIXME
   0761's lane should generate — see the W3c instrumentation answer in the wave
   report.
