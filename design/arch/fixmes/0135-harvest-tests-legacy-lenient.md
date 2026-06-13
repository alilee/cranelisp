---
number: 0135
target: /backend
filed_by: /qa
filed_at: 2026-05-04
sprint_filed: 64
refers_to: tests/legacy/lenient.rs
status: open
---

> **S81 W-C — backend sparkability-analysis part harvested; spark-execution +
> env-var + IO-scheduling parts are 0109-adjacent. FIXME stays OPEN.** The
> cleanly backend-internal half — the sparkability *analysis* pass
> (`find_sparkable_bindings` / `is_worth_sparking`, `pub(crate)` pure fns in
> `crates/cranelisp-backend/src/compiler/control_flow.rs`) — is now unit-tested
> in that file's new `#[cfg(test)] mod sparkability_tests` (7 tests):
> - `two_independent_calls_are_sparkable` — two data-independent calls clear the
>   min-2 threshold.
> - `single_sparkable_below_threshold_returns_empty` — below threshold ⇒ empty
>   (sequential codegen).
> - `dependent_binding_is_not_sparkable` — dependency on an earlier binding
>   excludes it (the independent/dependent distinction the legacy `test_lenient_*`
>   correctness tests probed indirectly).
> - `cheap_builtins_are_not_sparkable` — `+`/`<`/etc. excluded (legacy
>   `test_lenient_cheap_builtins_not_sparked`).
> - `constructors_are_not_sparkable` — known ADT constructors excluded.
> - `literals_and_var_refs_are_not_sparkable` — non-Apply exprs never sparkable
>   (legacy `test_lenient_neg_literals_not_sparkable`).
> - `mixed_independent_and_dependent_returns_only_independent` — positional
>   independence (legacy `test_lenient_mixed_independent_dependent`).
>
> **Remainder (NOT W-C, stays OPEN — needs int worker/session, 0109-adjacent):**
> - All `test_lenient_*` value-correctness tests assert spark *execution* via
>   `repl_eval`/`repl_eval_typed` — they need a live session + runtime, not the
>   backend analysis pass. Their language-observable subset is already carried
>   e2e in `tests/spec_04_expressions.rs::lenient_*` (per the FIXME body).
> - The `CRANELISP_NO_LENIENT=1` opt-out is a process-global `LazyLock<bool>`
>   (`control_flow.rs` `LENIENT_DISABLED`) read once at first use — not
>   in-process togglable, so it cannot be unit-tested without a subprocess
>   (the legacy `test_lenient_no_lenient_env_var` already acknowledged it does
>   not exercise the flag). Leave for an e2e/int harvest.
> - The IO-scheduling Par-node emission tests (`test_io_schedule_*`) need the
>   test-capture platform DLL + runtime + session; co-owned with the int/runtime
>   wave.
>
> No further cleanly-backend-internal assertion remains to port this wave.

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
