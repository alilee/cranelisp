---
number: 0137
target: /qa
filed_by: /qa
filed_at: 2026-05-04
sprint_filed: 64
sprint_retargeted: 81
retargeted_by: /dev (cranelisp-frontend)
refers_to: tests/legacy/macros.rs, tests/spec_09_macros.rs
status: open
---

# Harvest tests/legacy/macros.rs into cranelisp-frontend + cranelisp-typecheck unit tests

## S81 W-B verification (/dev narrow on cranelisp-frontend, 2026-06-13)

Verified the harvest disposition against current source. Conclusion:
**no frontend-internal harvest is owed**; the residual is entirely /qa's
(one §9.2.3 negative + legacy-file deletion). Re-targeted /frontend → /qa.

**Coverage audit:**

- The legacy file's 29 tests are ALL e2e-shaped — they drive
  `repl_session`/`repl_eval`/`batch_run`, asserting language behaviour.
  NONE reach into frontend internals (`macro_expand`, `parse_defmacro`,
  `synthesize_macro_clause_defn`) with a Rust-API assertion. So there is
  nothing of frontend-internal value to port out of macros.rs.
- The frontend-internal macro surface is ALREADY thoroughly unit-tested in
  `crates/cranelisp-frontend/src/defmacro.rs` `#[cfg(test)]` (is_defmacro,
  parse_defmacro single/multi-clause/rest/private/docstring/bracket,
  synthesize_macro_clause_defn shape + SList/Sexp annotation, malformed
  errors) and `quasiquote.rs` `#[cfg(test)]`. No gap.
- The behavioural subset is carried forward in `tests/spec_09_macros.rs`
  (24+ tests, with explicit `(carry: legacy/macros.rs::...)` annotations
  covering identity, multi-clause dispatch, quasiquote, begin-splicing,
  defmacro-in-results, composition, error recovery, arity mismatch,
  expansion-depth-limit, rest+splice, runtime-error-during-expansion).

**The ONE genuine gap (confirmed):** a §9.2.3 negative where a macro body
*successfully typechecks to a non-`Sexp` type* (e.g. `(defmacro bad [x] 42)`
body = `Int`, or `... true` = `Bool`) and MUST be rejected because the
macro-body contract requires `Sexp`. This is DISTINCT from the cases the
active suite already covers:
- `spec_09_macros.rs::defmacro_malformed_no_params` — `(defmacro bad)` is a
  *parse* error (missing params), not a body-type error.
- `spec_09_macros.rs::repl_error_recovery_bad_macro` /
  `repl_error_recovery_no_partial_macro` — body `(add-i64 1 "hello")` is an
  *ill-typed* body (a type error in the body itself).
- `s76_macro_availability.rs::macro_clause_calls_imported_helper_ill_typed_rejected_neg`
  — an ill-typed `Int -> Int` helper called unquoted (also a type error).
None of these is the clean case where the body is a *valid program in
isolation that simply has the wrong (non-Sexp) result type*. The legacy
file's `neg_macro_non_sexp_return_type_batch` / `_repl` / `_return_bool_batch`
are that case; they are NOT yet reproduced in the active e2e suite.

Note: this rejection fires at the **typecheck** stage (the synthesized
clause-defn body fails to unify with `Sexp`), NOT at frontend parse —
`parse_defmacro` accepts `(defmacro bad [x] 42)` fine (body Sexp = `Int(42)`).
So there is no frontend unit-test to add for it either; it is an e2e
property best witnessed through `--run`/REPL. Hence /qa, not /dev.

## Residual work owed (target: /qa)

(a) Author the ONE §9.2.3 non-`Sexp`-macro-body negative in
    `tests/spec_09_macros.rs` — a macro body that successfully typechecks to
    `Int` (`(defmacro bad [x] 42)`) and a `Bool` variant
    (`(defmacro bad [x] true)`) MUST be rejected with a type error naming
    `Sexp`. `// spec: spec/09-macros.md §9.2.3`. Run through REPL +
    `--run` (NOT `--link` — intersects FIXME 0122 macro GOT alignment).
(b) Delete `tests/legacy/macros.rs` and remove its row from
    `tests/legacy/README.md` — coverage fully subsumed (24+ in
    spec_09_macros.rs + the frontend defmacro/quasiquote units, per the
    audit above).

Once (a)+(b) land, /qa deletes this FIXME.

## (Original issue, retained for provenance)

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
