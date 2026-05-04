---
number: 0139
target: /int
filed_by: /qa
filed_at: 2026-05-04
sprint_filed: 64
refers_to: tests/legacy/sprint59_neg.rs
status: open
---

# Harvest tests/legacy/sprint59_neg.rs (optional — carry-forward complete)

## Issue

The Sprint 64 Wave 5 test-port quarantined `tests/legacy/sprint59_neg.rs`
(271 LOC, 12 tests). The file is the Sprint 59 Workstream D
module-boundary negative-coverage commission:

- §8.3 import-of-non-existent-name error.
- §8.3 super-at-top-level error (REPL-eval angle).
- §8.3 import-inside-let placement error.
- §8.3 imports-available-before-definitions positive-of-negative.
- Defect 8 latent gap: `program_needs_trace` parallel scan-gap regression
  guard for `defn` body containing `(trace ...)`.

The language-observable subset has been carried forward into
`tests/spec_08_modules.rs` (import errors, super-rejection,
non-existent name) and `tests/spec_04_expressions.rs::trace_returns_trace_type`
(trace observable behaviour).

The Defect 8 latent-gap test (`defn_body_with_trace_triggers_extern_registration_neg`)
is a regression guard against a specific scan-gap shape that may already
be addressed by the Defect 8 fix that landed. This harvest is optional
— the e2e carry-forward + the canonical spec_04 trace test together
provide the regression coverage.

## Proposed resolution

This FIXME is **optional**. The carry-forward is complete; the
remaining Rust-API content (import-inside-let placement test driven via
`helpers::batch_run_file`, REPL-driven `(import [super [*]])` rejection
via `repl_session()`) duplicates the new
`tests/spec_08_modules.rs::*_neg` tests.

If the harvest is pursued:

- Translate import-placement neg tests into
  `crates/cranelisp-frontend/src/module_extract.rs` `#[cfg(test)]`.
- Translate the `program_needs_trace` regression guard into
  `src/session_v4.rs` (or wherever the predicate moves
  post-FIXME-0109) as a unit test.

If the harvest is deferred indefinitely (recommended), delete
`tests/legacy/sprint59_neg.rs` at S65 cleanup time alongside the
ReplSession deletion.

## Operational implication / Context

Co-owner: `/frontend` for the import-placement subset (module_extract
is /frontend's territory).

When complete (or when verified that the carry-forward is sufficient),
delete `tests/legacy/sprint59_neg.rs` and remove its row from
`tests/legacy/README.md`.
