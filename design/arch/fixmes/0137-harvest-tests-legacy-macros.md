---
number: 0137
target: /frontend
filed_by: /qa
filed_at: 2026-05-04
sprint_filed: 64
refers_to: tests/legacy/macros.rs
status: open
---

# Harvest tests/legacy/macros.rs into cranelisp-frontend + cranelisp-typecheck unit tests

## Issue

The Sprint 64 Wave 5 test-port quarantined `tests/legacy/macros.rs`
(441 LOC, 58 tests). The file exercises the macro pipeline:

- defmacro registration in REPL + batch modes.
- Quasiquote expansion + unquote splicing.
- Multi-clause defmacro dispatch.
- begin / multi-form expansion.
- Bare-symbol expansion + bootstrapping order.
- Sexp constructor pattern matching.
- Macro persistence across REPL evals.
- Malformed macro errors + arity mismatches.

The language-observable subset has been carried forward into
`tests/spec_09_macros.rs` (REPL canonical) — defmacro registration,
quasiquote, multi-clause dispatch, errors, persistence.

The legacy file's remaining content is Rust-API observation:

- `repl_eval_display(&mut s, "(defmacro ...)")` — symbol-table display
  of the macro registration; partially observable in REPL but the test
  asserts on the bespoke display format.
- `helpers::collect_list_categories(&session)` — symbol-table inspection
  for `/list` category boundaries.
- Direct `cranelisp_frontend::macro_expand` invocation (where
  applicable).

## Proposed resolution

Translate into `crates/cranelisp-frontend/src/macros/` (or wherever the
expander lives) as `#[cfg(test)]` modules:

- **Expansion-shape tests** — drive
  `cranelisp_frontend::parse + build_program + macro_expand`, assert the
  expanded AST shape directly. Use `cranelisp-typecheck` as a
  dev-dependency for tests that need to run the typechecker on the
  expanded form.
- **Multi-clause dispatch tests** — pattern-matching on Sexp argument
  shape; assert the correct clause fires for each input shape.
- **Hygiene tests** — auto-gensym renaming; assert the renamed symbols
  in the expanded form do not collide with caller-introduced bindings.
- **Bootstrapping order tests** — macro defined-before-used; assert the
  macro is in the macro-env at the point of expansion of a later defn.

For tests that span macro expansion + type checking (e.g., macro that
expands to a typecheck-rejected program), use `crates/cranelisp-typecheck`
co-owner.

## Operational implication / Context

When complete, delete `tests/legacy/macros.rs` and remove its row from
`tests/legacy/README.md`.

Co-owner: `/typecheck` for tests where macro expansion + type checking
are jointly observed.
