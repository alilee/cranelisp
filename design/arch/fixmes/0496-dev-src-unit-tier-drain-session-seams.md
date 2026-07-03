---
number: 0496
target: /dev
filed_by: /qa
filed_at: 2026-07-03
sprint_filed: 101
refers_to: src/session_v4/lifecycle.rs, src/display.rs, src/save.rs, src/eval.rs, src/process_form/{cache_restore.rs,macro_resolution.rs,dependency.rs,form_dispatch.rs}, src/repl.rs, sprints/METHOD.md §2.2, tests/plan/coverage-audit-s101.md §3.3
status: open
---

# src/: unit-tier drain for the pre-S101 session/REPL strategy seams — the 6a defect surfaces

**Crate**: src/ (the cranelisp binary+lib; `/dev` narrow).

## Issue

The S101 coverage audit (`tests/plan/coverage-audit-s101.md` §3.3) shows src/ split
in two: seams built under recent-sprint discipline are well covered
(scheduler 52 tests, worker 34, redefine 11 incl. negatives), while the older
session/REPL strategy layer — where 8 of the 12 Phase-6a/6b defects live — is
bare:

- `session_v4/lifecycle.rs` — **1,918 LOC, ZERO unit tests**; the largest untested
  surface in the repo; home of the 0489 restart-lockout and the S101
  `*code = None` finding.
- `display.rs` — 24 tests, but ALL exercise primitive formatting;
  `format_adt_value`/`format_adt_heap_value` (the 0493 garbled nested-ADT render)
  have zero direct tests — the file looks covered, the strategy path isn't.
- `save.rs` — 27 tests; none aim at macro-definition regeneration (the D1
  directory-poison grammar: expansion artifact + original form co-persisted) or
  authorship fidelity (D2, §15.4.7).
- `eval.rs` (600 / 0), `process_form/cache_restore.rs` (448 / 0 — the D3 axis),
  `process_form/macro_resolution.rs` (617 / 0), `process_form/form_dispatch.rs`
  (368 / 0), `process_form/dependency.rs` (1,580 / 6 happy-only — the
  consuming-turn batch-derivation neighborhood, 0488's suspected src/ half).
- `repl.rs` (3,357 / 16) — tests target formatters, not handlers: `handle_sig`
  (0492), `handle_mod` display half (0487), `handle_source` undriven.
- `redefine.rs` report render tested, but synth-wrapper (`__expr`) exclusion (0491)
  unasserted; `index_worker.rs` bare-lookup source-*recording* trigger (0486
  mechanism) unasserted.

## Proposed resolution

Per METHOD §2.2 (unit test per fix + strategy-derived scenarios): the S102 /int
defect fixes for 0486/0487/0489/0491/0492/D1/D2/D3 each land their seam unit tests
in these modules — that alone drains most of the list, since the defect set and the
thin-seam set coincide. Beyond the per-fix obligation: (1) a direct test module for
`display.rs`'s ADT-value rendering (nested parameterized shapes, balanced-parens
invariant); (2) a regeneration-grammar test module for `save.rs`
(defn/deftype/import/defmacro/macro-defining-macro round-trip at unit grain);
(3) first tests for `lifecycle.rs`'s restore/reload decision paths (extract pure
seams if needed — the module's size suggests testability refactoring is part of
the drain).

## Operational implication / Context

This is the unit-tier half of the S102 /int defect wave (risk register §4 items
2, 5, 6, 8 in the audit doc) — not separate work. e2e lanes L-S1/L-S2/L-S3
(audit §2.4) are the /qa-side complement.

## /design (int) S102 Phase 3: scenario-space matrices named

Per Principle 23's role binding, the implementation strategy's scenario space for
this drain is named explicitly in `design/int/s102-defect-wave.md` §3 — Matrices
A (session lifecycle, `lifecycle.rs`), B (regeneration grammar, `save.rs`),
C (redefinition target-kind × artifact world, `redefine.rs`), D (module-turn
environment, install routes × env dimensions), E (introspection recording).
Derive the per-fix unit briefs from those matrices; the per-section change-set
plans (§1, §4–§7) name which cells each fix must pin.
