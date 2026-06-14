# S82 harvest disposition — examples.rs + examples_run.rs + exemplar.rs + exemplar_solver_correctness.rs

- **Files:** `examples.rs` (138 LOC, 15), `examples_run.rs` (199 LOC, 1), `exemplar.rs` (84 LOC, 3), `exemplar_solver_correctness.rs` (310 LOC, 2)
- **Owner:** `/port` (deletion is `/qa`'s tree)
- **FIXME:** 0143 (verified subsumed by /port S81 W-I-2)
- **Prior audit:** /port inspection (FIXME 0143 body) — this wave VERIFIED per-test.

## Disposition

The S81 W-I-2 /port claim — every load-bearing shape subsumed by
un-ignored carry-forwards in `tests/{examples,exemplar,regression}.rs` —
was VERIFIED per-test this wave (active tests read and confirmed to
assert the same behaviour, not rubber-stamped).

| File | Disposition |
|---|---|
| `examples.rs` (15 `example_NN_*`) | 15 COVERED — `tests/examples.rs::every_example_runs_with_documented_exit` (table-driven umbrella; exit codes match verbatim, carry-tag present) |
| `examples_run.rs` (1 umbrella) | 1 COVERED — `tests/examples.rs::every_example_runs_with_documented_exit` (same table, signal-aware exit normalization carried) |
| `exemplar.rs` (3 batch) | 3 COVERED — `tests/exemplar.rs::{batch_const_macro_in_main, batch_cross_module_function_import, batch_cross_module_adt_export_and_pattern_match}` (same shapes, inlined to drop stdlib dep) |
| `exemplar_solver_correctness.rs` (2) | 2 COVERED — `tests/exemplar.rs::t_s2_1_eliminate_contract_on_given_returns_none` + `tests/regression.rs::t_s2_2_inline_adt_arg_wrapping_vec_preserves_len` (both **REGRESSION-GUARD**, S61 Slice 2 defect lineage) |

## Summary

- **examples.rs: 15 tests: 15 covered / 0 gap / 0 obsolete**
- **examples_run.rs: 1 test: 1 covered / 0 gap / 0 obsolete**
- **exemplar.rs: 3 tests: 3 covered / 0 gap / 0 obsolete**
- **exemplar_solver_correctness.rs: 2 tests: 2 covered / 0 gap / 0 obsolete** (2 reg-guards, both active)

REGRESSION-GUARD among GAP: 0 (both reg-guards are COVERED/active).

## Exit checklist
- [x] (a) dispositioned; [ ] (b) no GAP; [ ] (c) deleted (Wave 2); [ ] (d) README rows; [ ] (e) FIXME 0143 closed
