---
number: 0135
target: /backend
filed_by: /qa
filed_at: 2026-05-04
sprint_filed: 64
refers_to: tests/legacy/lenient.rs
status: open
---

# Harvest tests/legacy/lenient.rs into cranelisp-backend unit tests

## Issue

The Sprint 64 Wave 5 test-port quarantined `tests/legacy/lenient.rs`
(289 LOC, 32 tests). The file exercises lenient evaluation (Sprint 25
Wave 2) — automatic parallelisation of independent let bindings (spec
§12.4.3) and automatic IO scheduling via Par nodes (spec §10.12).

The language-observable subset (independent bindings produce correct
sums; dependent bindings remain sequential) has been carried forward
into `tests/spec_04_expressions.rs::lenient_*` (REPL canonical).

The legacy file's remaining content is Rust-API observation:

- `repl_eval(&mut session, "...")` direct value witness.
- `repl_eval_typed(&mut session, "...")` type witness.
- `CRANELISP_NO_LENIENT=1` opt-out flag — observable only via timing or
  internal counters in the unit-tier; e2e cannot distinguish parallel
  from sequential evaluation when results match.
- Sparkability heuristics (cheap-builtin detection, min-sparkable
  threshold) — the analysis is a backend pass, observable only by
  inspecting the IR or sparking counters.

## Proposed resolution

Translate into `crates/cranelisp-backend/src/lenient/` (or wherever the
sparkability analysis lives) as `#[cfg(test)]` modules:

- **Sparkability analysis tests** — drive
  `cranelisp_frontend::parse + build_program`, run typecheck, then
  invoke the analysis directly. Assert which let bindings are marked
  sparkable / which are filtered out.
- **Codegen tests** — IR inspection: assert Par nodes emitted for
  qualifying let blocks, no Par for dependent bindings.
- **`CRANELISP_NO_LENIENT=1` opt-out** — translate into a config-flag
  test on the sparkability pass.
- **Auto IO scheduling tests** — bind! independence detection; assert
  Par-node emission for commutative IO chains.

## Operational implication / Context

The language-observable subset is already in `tests/spec_04_expressions.rs`
— users get the regression guard regardless of when this harvest lands.
The harvest preserves the optimiser-internal coverage that catches
regressions in the analysis pass before they manifest in observable
behaviour.

Co-owner: `/runtime` if the IO scheduling assertions touch
`cranelisp-runtime` (Par-node execution).

When complete, delete `tests/legacy/lenient.rs` and remove its row from
`tests/legacy/README.md`.
