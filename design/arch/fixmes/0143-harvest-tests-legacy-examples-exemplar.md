---
number: 0143
target: /qa
filed_by: /qa
filed_at: 2026-05-05
sprint_filed: 64
verified_subsumed_by: /port (S81 W-I-2)
refers_to: tests/legacy/examples.rs, tests/legacy/examples_run.rs, tests/legacy/exemplar.rs, tests/legacy/exemplar_solver_correctness.rs, tests/examples.rs (NEW), tests/exemplar.rs (NEW), tests/regression.rs (NEW)
status: open
---

## S81 W-I-2 /port verification — re-targeted /port → /qa

`/port` reviewed the four quarantined legacy files by inspection and
confirms every load-bearing test shape is ALREADY subsumed by the
un-ignored carry-forwards in `tests/{examples,exemplar,regression}.rs`
(the 6a finding). No shape needs re-authoring. Because the legacy-file
DELETION lives in `tests/` (`/qa`'s tree, not `/port`'s — per S81 W-H
precedent), this FIXME is re-targeted to `/qa`. Per-file subsumption:

- `tests/legacy/examples.rs` (15 `example_NN_*` row-tests) →
  **subsumed by** `tests/examples.rs` umbrella
  (`(carry: legacy/examples.rs::example_NN_* x15 + ...)`, line 174;
  the 15 rows were strictly subsumed by the examples_run umbrella per
  the Wave-6-batch-1 audit).
- `tests/legacy/examples_run.rs` (27-row subprocess umbrella +
  on-disk parity guard + signal-aware exit normalisation) →
  **subsumed by** `tests/examples.rs`
  (`(carry: legacy/examples.rs + legacy/examples_run.rs umbrella)`;
  `every_example_file_runs_under_examples_prelude` carried forward).
- `tests/legacy/exemplar.rs` (3 batch tests:
  `exemplar_batch_const_macro`, `exemplar_batch_cross_module_import`,
  `exemplar_batch_cross_module_adt`) → **all three subsumed by**
  `tests/exemplar.rs` (`batch_const_macro_in_main`,
  `batch_cross_module_function_import`,
  `batch_cross_module_adt_export_and_pattern_match`; carry tags present).
- `tests/legacy/exemplar_solver_correctness.rs` (2 tests) →
  `eliminate_on_same_value_given_returns_none` **subsumed by**
  `tests/exemplar.rs::t_s2_1_eliminate_contract_on_given_returns_none`
  (inline-rewritten, no exemplar/ dependency); and
  `inline_adt_arg_wrapping_vec_preserves_len` **subsumed by**
  `tests/regression.rs` (carry tag, line 42).

No genuinely-unsubsumed shape was found. Remaining action (for /qa):
delete `tests/legacy/{examples,examples_run,exemplar,exemplar_solver_correctness}.rs`
and remove the corresponding rows from the tests/legacy README. Leaving
`status: open` for /qa to action the deletion.

# Harvest tests/legacy/examples + exemplar files into /port-owned coverage

## Issue

Sprint 64 Wave 6 batch 1 quarantined four source files exercising
`examples/` and `exemplar/` subprocess execution. The new e2e
carry-forwards (tests/examples.rs umbrella + tests/exemplar.rs
batch-mode shapes + 1 regression entry) preserve the load-bearing
coverage; the legacy files retain finer-grained variant tests
that may be worth folding back as `/port` crate tests.

## Proposed resolution

`/port` reviews the quarantined files for any test-shape worth
preserving as `#[cfg(test)]` unit tests inside the exemplar/ or
examples/ project, OR for fold-back into the new
tests/examples.rs / tests/exemplar.rs e2e tests. Anything not
worth preserving is deleted with the legacy file when the
harvest is complete.

## Operational implication / Context

The legacy files have integration-tier dependencies on
exemplar/grid.cl + exemplar/solver.cl that the new e2e tests do
NOT (per `feedback_repro_handoff.md` — repros stand alone).
Harvest should preserve self-containment.
