---
number: 0125
target: /int
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: tests/legacy/ring3_repl.rs
status: open
---

# Harvest tests/legacy/ring3_repl.rs into REPL session + typecheck unit tests

## Issue

The Sprint 64 test-port quarantined `tests/legacy/ring3_repl.rs`
(825 LOC, 50 tests). The file tests the Ring 3 REPL macro surface
(`/expand`, `/imports`, defmacro display, /list / /info / /sig / /doc
on macros) through the `ReplSession` Rust API. ~16 tests are stub
placeholders (`#[test] fn r3_*() { let _s = repl_session(); }`)
pending E2E binary integration — those have inline `TODO` comments
naming the future shape.

The user-observable spec assertions (defmacro display, bare macro
lookup, multi-clause defmacro dispatch, /list-includes-Macros,
/expand expansion, /imports lists special forms) are fully covered
by the new e2e files:

- `tests/repl_introspection.rs` — defmacro display, multi-clause
  defmacro display, bare macro lookup, /list shows defmacro,
  /list MUST NOT classify defmacros as Fns (negative), /expand of
  user macro reveals body, /imports lists special forms.
- `tests/repl_lifecycle.rs` — defmacro persists across evals,
  multi-clause defmacro dispatches by arity.
- `tests/repl_negative.rs` — defmacro shape errors (missing params,
  numeric name, missing body), macro call wrong arity.

## Proposed resolution

- The 16 stub tests (`r3_list_macros_category_via_symbol_table`,
  `r3_list_neg_macros_not_in_functions`, `r3_info_macro_clause_count`,
  `r3_info_macro_docstring`, `r3_sig_macro_params`,
  `r3_sig_macro_variadic`, `r3_macro_no_docstring`, etc.) DELETE —
  the "TODO: Reaches into TC internals. Replace with /list output …
  or unit tests in typecheck crate" comments name the harvest target;
  the e2e form is now in `tests/repl_introspection.rs`.
- The non-stub tests testing internal `ModuleEntry::Macro`
  registration shape (`r3_macro_docstring_stored`,
  `r3_macro_no_docstring`, `r3_define_before_use_works`,
  `r3_neg_forward_reference_not_expanded`) translate into
  `#[cfg(test)]` modules inside
  `crates/cranelisp-typecheck/src/checker.rs` (macro environment
  registration) and `crates/cranelisp-typecheck/src/macro_expand.rs`
  (auto-gensym, fixed-point expansion).
- Tests using `s.session.format_eval_result(&result)` to assert
  display strings (`r3_bare_macro_lookup`, `r3_special_form_defmacro`)
  translate into `crates/cranelisp-backend/src/display.rs`
  `#[cfg(test)]` modules calling `format_result` directly OR are
  covered by the e2e form in `tests/repl_introspection.rs::bare_macro_lookup`.

When complete, delete `tests/legacy/ring3_repl.rs` and remove its row
from `tests/legacy/README.md`. Git history preserves provenance.

## Operational implication / Context

This harvest is a coverage-preservation commitment from S64. The
user-observable spec coverage is fully preserved by the e2e form.
This FIXME exists to preserve the macro-expansion-internal shape
assertions that need crate-level tooling. The 16 stub tests have
zero load-bearing assertion content — they should delete cleanly,
not transcribe to unit-tier.
