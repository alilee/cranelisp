---
number: 0134
target: /int
filed_by: /qa
filed_at: 2026-05-04
sprint_filed: 64
refers_to: tests/legacy/e2e.rs, tests/legacy/ring0.rs, tests/legacy/ring1.rs, tests/legacy/ring2.rs
status: open
---

# Harvest tests/legacy/{e2e,ring0,ring1,ring2}.rs into per-crate unit tests

## Issue

The Sprint 64 Wave 5 test-port quarantined four large legacy conformance
files:

- `tests/legacy/e2e.rs` (2701 LOC, 309 tests) — original integration-tier
  e2e suite. Heavy use of `compile_and_run_simple()`, `compile_and_run()`,
  `compile_and_run_with_macros()`, inline `NUM_TRAIT_PRELUDE` etc.
  constants. Many tests already in subprocess shape but coupled to legacy
  helpers.
- `tests/legacy/ring0.rs` (1135 LOC, 216 tests) — Ring 0 conformance:
  core expressions, arithmetic, primitives, let, if, lambda, application.
- `tests/legacy/ring1.rs` (2253 LOC, 380 tests) — Ring 1 conformance:
  strings, ADTs with fields, closures, vec ops, IO.
- `tests/legacy/ring2.rs` (2484 LOC, 405 tests) — Ring 2 conformance:
  traits, operator dispatch, constrained polymorphism, modules, ADT
  trait impls.

All four files use `tests/helpers/mod.rs::{ReplSession, compile_and_run_*,
repl_session*, assert_type_error, assert_parse_error, assert_rc_balanced}`
— the integration-tier surface that Phase 3 (S65) will delete. Their
language-conformance assertions have been carried forward as REPL-canonical
e2e tests in:

- `tests/spec_03_types.rs` — type system surface
- `tests/spec_04_expressions.rs` — special forms / lenient eval
- `tests/spec_05_definitions.rs` — defn / deftype / deftrait / impl
- `tests/spec_06_pattern_matching.rs` — match patterns
- `tests/spec_07_traits.rs` — trait dispatch + operator-as-method
- `tests/spec_08_modules.rs` — module discovery + import / visibility
- `tests/spec_09_macros.rs` — defmacro + quasiquote
- `tests/spec_appendix_a_builtins.rs` — primitive functions

The carry-forward is spec-anchored — one e2e test per spec assertion. The
duplication across e2e.rs / ring0.rs / ring1.rs / ring2.rs (the same
assertion appearing in 2-4 source files) collapsed naturally as the new
suite is authored against the spec, not the source-file shape.

## Proposed resolution

Per the two-tier strategy (`memory/project_test_strategy.md`), the
remaining Rust-internal observations belong inside the owning crate as
`#[cfg(test)]` unit tests. Suggested partition:

### `crates/cranelisp-typecheck/src/`

- AST-shape regression tests using `cranelisp_frontend::parse +
  build_program` per `tests/CLAUDE.md §"Isolating Cross-Crate Failures"`.
- Type-inference assertions that go beyond REPL-observable surface
  (specific type-variable shapes, constraint-set composition).
- `assert_type_error(src, msg)` callsites — translate to direct
  `tc.check()` invocations.
- Multi-sig dispatch resolution — the symbol-table inspection currently
  done via `ReplSession::show_entry()`.

### `crates/cranelisp-backend/src/`

- `assert_rc_balanced(src)` callsites — translate into RC counter
  inspection adjacent to alloc/dec emission code. The `CRANELISP_RC_TRACE`
  parsing in tests/helpers/mod.rs is integration-tier; the `#[cfg(test)]`
  form can read counters directly.
- Closure-capture codegen invariants beyond e2e observability.
- Vec COW edge cases that need Cranelift IR inspection (use `CRANELISP_CODEGEN_TRACE`
  pattern but at unit-test layer).

### `src/` (binary crate, post-FIXME 0109 decomposition)

- Pipeline orchestration tests — multi-form REPL sessions where the
  Rust-API form is materially clearer than subprocess piping.
- `compile_both()` (batch / REPL parity) — the same source compiled both
  ways with `// spec:` annotated parity invariant.

### Use existing patterns

- `cranelisp_frontend::parse` + `build_program` for AST input — do NOT
  hand-construct AST.
- `tempfile::TempDir` per test for any file-system fixtures.
- `// spec:` annotations on each translated test naming the spec section.
- Per-test naming preserved where possible to allow git blame to trace
  the harvested assertion back to the original.

## Operational implication / Context

This is the largest single harvest commitment from S64 — ~1300 source
tests across 4 files. The harvest does not need to be a single sprint:
each crate's harvest is independent. Suggested sequencing:

1. **`/typecheck`** — AST/type-shape assertions; lowest churn.
2. **`/backend`** — RC + codegen assertions; depends on FIXME 0109
   landing first if the harvest also wants to reshape `Code{ptr}` access.
3. **`/int`** — pipeline tests; lowest priority because most pipeline
   tests have e2e analogues already.

When a file is fully harvested (its assertions translated, no longer
load-bearing in the legacy archive), delete the file and remove its row
from `tests/legacy/README.md`. Until then, the file is inert (not
compiled by Cargo's auto-discovery, which only scans `tests/*.rs` at the
top level).

The four-file consolidation under one FIXME reflects the shared
multi-skill ownership; resolving skills can split sub-tasks per-skill at
their own discretion when the harvest sprint(s) plan.
