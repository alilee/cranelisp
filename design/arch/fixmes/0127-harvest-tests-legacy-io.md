---
number: 0127
target: /int
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: tests/legacy/io.rs, tests/legacy/io_minimal.rs, tests/legacy/sprint61_io_closure_regression.rs
status: open
---

# Harvest tests/legacy/io*.rs into runtime + backend + typecheck unit tests

## Issue

The Sprint 64 test-port quarantined three IO-related files:

- `tests/legacy/io.rs` (1,360 LOC, 76 tests) — IO surface tests using
  `compile_and_run_typed`, `batch_run` Rust API and direct
  `cranelisp_runtime::read_string_as_str` + `heap_dealloc` calls,
  asserting `Type::Int` / `Type::Bool` returned by the Rust pipeline.
- `tests/legacy/io_minimal.rs` (120 LOC, 5 tests) — Sprint 57 Wave 6
  SIGBUS reduction repros via `compile_and_run_typed` Rust API.
- `tests/legacy/sprint61_io_closure_regression.rs` (215 LOC, 2 tests) —
  Sprint 61 Wave 4 capture-return-inc regression guard, already
  e2e-shaped (subprocess invocation) but uses the bespoke
  `run_repro_with_env` helper instead of the new `Cranelisp` builder.

The user-observable spec assertions are fully covered by the new e2e
file:

- `tests/spec_10_io.rs` (26 tests) — Pure constructor wraps
  Int/Bool/String, bind primitive forms IO chains (single + nested +
  triple + named-defn-continuation), bind constructor / pattern
  rejection, IO type inference, REPL eval inline trampoline regression
  guards (Sprint 57 Wave 6 + Sprint 61 Wave 4 capture-return-inc),
  --run mode exit code from Pure / from bind chain, IO branch
  consistency, match on IO values, IO let-binding, capture-return-inc
  closure-double-free regression.

## Proposed resolution

For `io.rs`:

- Tests calling `cranelisp_runtime::read_string_as_str(value)` and
  `heap_dealloc(value)` directly translate into `#[cfg(test)]` modules
  inside `crates/cranelisp-runtime/src/string.rs` (or wherever
  `read_string_as_str` lives) — these are direct ABI surface tests.
- Tests asserting on `Type::Int` / `Type::Bool` via the Rust pipeline
  (most of the §10.4 inference tests) translate into
  `crates/cranelisp-typecheck/src/checker.rs` `#[cfg(test)]` modules
  using `cranelisp_frontend::parse` + `build_program` + `tc.check(...)`.
- Platform tests (`io_platform_print_hello_world`, `io_read_line_*`)
  testing the platform DLL load / fn call boundary translate into
  `crates/cranelisp-platform/src/lib.rs` `#[cfg(test)]` modules.
- IO trampoline tests (`io_trampoline_deep_bind_chain`) translate into
  `crates/cranelisp-runtime/src/trampoline.rs` (or equivalent module)
  `#[cfg(test)]` modules.
- `do` macro tests translate into `crates/cranelisp-typecheck/src/macro_expand.rs`
  for the desugaring shape, OR live in `tests/spec_11_stdlib.rs` if
  the test asserts the stdlib `do` macro specifically.

For `io_minimal.rs`:

- All 5 tests are Sprint 57 Wave 6 reduction guards. Translate into
  `crates/cranelisp-backend/src/lib.rs` (or wherever the per-eval JIT
  drop logic lives) `#[cfg(test)]` modules. The reduction structure
  (Levels 0–4) is informational and can be flattened into a single
  `mod jit_drop_regression { ... }` test module.

For `sprint61_io_closure_regression.rs`:

- Already e2e-shaped. Two paths:
  1. **Delete** — the regression intent is preserved in
     `tests/spec_10_io.rs::capture_return_inc_does_not_double_free`
     via the same 7-line minimum repro through the new harness.
  2. **Translate** the bespoke `run_repro_with_env` helper to the new
     `Cranelisp` builder, keeping the file as a sibling to
     `tests/spec_10_io.rs` if `/backend` wants the explicit
     environment-variation surface.
  Recommend path 1.

When complete, delete the three legacy files and remove their rows
from `tests/legacy/README.md`. Git history preserves provenance.

## Operational implication / Context

This harvest is a coverage-preservation commitment from S64. The
user-observable spec coverage is fully preserved by the new e2e file.
The bulk of harvested unit tests target `cranelisp-typecheck` (IO type
inference) and `cranelisp-runtime` (trampoline + ABI). Platform tests
have low priority for harvest — the e2e form already exercises
`platforms/test-capture/` indirectly through any `--run` test.
