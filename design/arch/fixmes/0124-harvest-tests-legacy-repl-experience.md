---
number: 0124
target: /int
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: tests/legacy/repl_experience.rs, tests/legacy/repl_negative_old.rs
status: open
---

# Harvest tests/legacy/repl_experience.rs + repl_negative_old.rs into REPL session unit tests

## Issue

The Sprint 64 test-port quarantined two files:

- `tests/legacy/repl_experience.rs` (3,120 LOC, 190 tests) — Ring 0/1/2A
  REPL experience tests using the `ReplSession` Rust API + direct
  `cranelisp_backend::display::format_result(value, &Type)` calls.
- `tests/legacy/repl_negative_old.rs` (917 LOC, 31 tests) — Ring 0/1/2
  negative-path tests reaching into `session.shared.symbol_tables` via
  `helpers::collect_list_categories(&session)` to simulate `/list`
  output without spawning the REPL binary.

Both test the REPL surface via Rust-internal-state inspection that has
no e2e equivalent in their current shape. The user-observable spec
assertions (display format, /list categorisation, error recovery) are
fully covered by the new e2e files:

- `tests/repl_introspection.rs` (39 tests) — display format, slash
  commands (/list, /imports, /sig, /doc, /info, /type, /help, /expand),
  defmacro display + bare lookup, /list category boundaries (negative).
- `tests/repl_lifecycle.rs` (29 tests) — banner, eval persistence,
  recursive defns, ADT lifecycle, redefinition, error recovery,
  /reset semantics, macro persistence.
- `tests/repl_negative.rs` (28 tests) — type errors, parse errors,
  unbound symbols, arity, constructor shape, defmacro shape errors,
  display format negative paths.

The Rust-internal portions belong as `#[cfg(test)]` unit tests inside
the owning crate(s). Per `memory/project_test_strategy.md` two-tier
strategy and `memory/feedback_unit_tests_with_dev.md`, these are
`/dev`-authored, not `/qa`-authored.

## Proposed resolution

For `repl_experience.rs`:

- Tests calling `format_result(value, &Type)` directly (display format
  shape) translate into `#[cfg(test)]` modules inside
  `crates/cranelisp-backend/src/display.rs`. These are pure-function
  unit tests of the formatter and don't need a REPL session.
- Tests using `ReplSession::new() + session.eval(form) + extract type`
  to assert inferred types translate into `#[cfg(test)]` modules
  inside `crates/cranelisp-typecheck/src/checker.rs` using
  `cranelisp_frontend::parse` + `build_program` + `tc.check(...)`.
- Tests asserting REPL-cycle behaviour (recursion, ADT lifecycle,
  multi-form sessions, error recovery between forms) are e2e-relevant —
  the carry-forward in `tests/repl_lifecycle.rs` covers the spec
  surface; the legacy form's value is the `ReplSession` API surface
  exercise, which moves into `src/session_v4.rs` `#[cfg(test)]` if
  REPL session unit tests are wanted.
- Inline trait-prelude constants (`NUM_TRAIT_PRELUDE`, etc.) and the
  `install_trait_prelude(session: &mut ReplSession)` helper retire —
  the e2e form uses `with_prelude(PreludeVariant::TestStandard)` from
  `tests/fixtures/preludes/test-standard.cl`.

For `repl_negative_old.rs`:

- The `classify_entry(sym, entry, module)` and
  `collect_list_categories(session)` helpers replicate `handle_list`'s
  classification logic in test code. They translate into
  `#[cfg(test)]` modules inside `src/session_v4.rs` (or its successor
  module post-FIXME-0109) adjacent to `handle_list`. Direct
  symbol-table inspection through `session.shared.symbol_tables`
  becomes idiomatic crate-internal access there.
- Display-format negative tests (`display_neg_*`) using
  `format_result` directly translate as above into
  `crates/cranelisp-backend/src/display.rs`.
- Module-resolution negative tests (`module_neg_*`) translate into
  `crates/cranelisp-typecheck/src/checker.rs` `#[cfg(test)]` modules.

When complete, delete `tests/legacy/repl_experience.rs` and
`tests/legacy/repl_negative_old.rs` and remove their rows from
`tests/legacy/README.md`. Git history preserves provenance.

## Operational implication / Context

This harvest is a coverage-preservation commitment from S64. Until it
lands, the assertions are inert (the files are not compiled by Cargo).
The user-observable spec coverage is fully preserved by the three new
e2e files; this FIXME exists to preserve the structural-shape and
type-inference assertions that need crate-level tooling.
