---
number: 0130
target: /typecheck
filed_by: /qa
filed_at: 2026-05-04
sprint_filed: 64
refers_to: tests/legacy/ring4_trace_taxonomy.rs
status: open
---

# Harvest tests/legacy/ring4_trace_taxonomy.rs into cranelisp-typecheck + cranelisp-runtime unit tests

## Issue

The Sprint 64 test-port quarantined `tests/legacy/ring4_trace_taxonomy.rs`
(578 LOC, 31 tests). The file tests the `(trace expr)` special form
(spec/04-expressions.md §4.12) and the `/run-tests` slash command
(repl/spec.md §3 + appendix-a-builtins).

The carry-forward subset — `(trace expr)` returns a `Trace` ADT value
observable via REPL `:Type value` display; pattern match on `TraceCall`;
`/run-tests` reports pass/fail counts — is preserved as e2e tests in
`tests/spec_12_runtime.rs`. The quarantined remainder asserts on internal
`Type::ADT(FQTypeName, Vec<Type>)` shapes via `repl_eval_typed` (Rust API
returning the `Type` value alongside the eval result Int).

## Proposed resolution

Split by what's being asserted on:

- **`cranelisp-typecheck` `#[cfg(test)]`** — the bulk of the file asserts
  the inferred `Type` for trace-form sub-expressions:
  - `trace_returns_trace_type_*` — `(trace ...)` infers as
    `Type::ADT("Trace")`.
  - `trace_field_*_returns_*` — accessor functions (`name`, `params`,
    `result`, `nanos`, `children`) infer the correct field type
    (`Type::String`, `Type::ADT("SList", [String])`, etc.).
  - `trace_nested_*`, `trace_composability_*` — nested trace and
    let-binding still infer to `Type::ADT("Trace")`.
  - `trace_form_available_without_import`,
    `trace_type_requires_import_for_match`,
    `trace_type_*_importable_from_primitives` — the import resolution
    behaviour for the trace special form and the `Trace`/`TraceCall`
    types.

  Translate using `cranelisp_frontend::parse` + `build_program` per
  `tests/CLAUDE.md §"Isolating Cross-Crate Failures"`. Drive
  `tc.check(&program, ...)` and assert on the resulting `Scheme` /
  `Type` for the named def. ~25 tests fit this shape.

- **`cranelisp-runtime` `#[cfg(test)]`** — the runtime portion asserts on
  observable Trace value layout:
  - `trace_basic_fact` / `trace_is_value_not_effect` — the Trace value is
    a heap pointer (`val != 0`). Belongs alongside the Trace ADT layout
    code if such code lives in cranelisp-runtime (or backend if it's
    backend-side).

- **`/run-tests` slash-command unit coverage** — `run_tests_basic_pass`,
  `run_tests_basic_fail`, `run_tests_multiple_tests`,
  `run_tests_empty_no_tests`, `run_tests_mixed_pass_fail` — these test
  the `discover-tests` + `run-test` primitives plus the `/run-tests`
  formatter via direct `session.process_commands(...)`. The e2e form
  (REPL `/run-tests` substring on stdout) is preserved in
  `tests/spec_12_runtime.rs`. The internal-formatter precision tests
  (e.g., the exact `output.contains("3 passed")` shape) belong as
  `#[cfg(test)]` adjacent to the `/run-tests` formatter in `src/`.

## Operational implication / Context

This harvest is a coverage-preservation commitment from S64. Until it
lands, the file is inert. The e2e test suite covers user-observable Trace
behaviour; the quarantined Type-shape assertions are an implementation
contract layer below the user-visible spec.

Note on frontend integration: `Trace` and `TraceCall` are compiler-seeded
in the `primitives` module. The import-rejection tests
(`trace_type_requires_import_for_match`,
`trace_type_not_auto_imported`) blend frontend + typecheck concerns;
harvest target depends on which crate owns the import-resolution rule
(typecheck per Decision 38+ surface).

When complete, delete `tests/legacy/ring4_trace_taxonomy.rs` and remove
its row from `tests/legacy/README.md`. Git history preserves provenance.
