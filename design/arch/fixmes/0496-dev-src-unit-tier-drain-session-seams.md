---
number: 0496
target: /dev
filed_by: /qa
filed_at: 2026-07-03
sprint_filed: 101
refers_to: src/session_v4/lifecycle.rs, src/display.rs, src/save.rs, src/eval.rs, src/process_form/{cache_restore.rs,macro_resolution.rs,dependency.rs,form_dispatch.rs}, src/repl.rs, sprints/METHOD.md §2.2, tests/plan/coverage-audit-s101.md §3.3
status: open
---

## S103 Wave-4 update (/dev src/) — the lifecycle.rs HEADLINE is drained; residual narrowed

The FIXME's headline claim (`lifecycle.rs` — "1,918 LOC, ZERO unit tests") is
**stale as of S102/S103**: `lifecycle.rs` now carries a `degraded_startup_tests`
module covering the reload/regen-fidelity DECISION seams the T1 full cure
(§10 T1) depends on — `defined_symbol_of_form` (public + private defining heads,
structural/expression/malformed negatives), `render_startup_error_report`,
`append_failed_forms` (verbatim single + multi-form ordering + empty no-op),
`first_line`. Combined with the T1 driver's own pure seams unit-tested in
`redefine.rs` (`is_t1_downgrade` F2 slot-refinement incl. the ctor-reentry
negative cell, the `__expr`-only feed narrowing keeping macro-clause edges, the
`render_caller_base`/`macro_clause_base_name` fold, `stale_callers` folding a
macro clause to its owning macro), the session-lifecycle-seam coverage this
FIXME asked for at the reload path has landed.

Other files gained per-fix coverage during S102: `display.rs` (27), `save.rs`
(37), `repl.rs` (26), `dependency.rs` (6).

**Residual (kept open for a future wave):** `process_form/cache_restore.rs`
(0 tests — the D3 cache-restore axis), `process_form/macro_resolution.rs` (0),
`eval.rs` (2 — the Matrix-E recording seam only). These are not touched by the
T1 full-cure wave and stay as the narrowed remaining drain.

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

## /dev (src/) S102 Wave 5 (A-2): partial drain — cluster seams landed, remainder itemized

Drained with the persistence-integrity cluster (commits `98894d8`, `5f011b6`,
`85baa9c`, `172c57b`):

- **`lifecycle.rs` gains its first unit module** (`degraded_startup_tests`,
  Matrix A "backing BROKEN" row decision cells): `defined_symbol_of_form`
  (defining/structural/expression/malformed), `render_startup_error_report`
  (exact bytes, symbol-naming MUST), `append_failed_forms` (verbatim
  re-emission / no-op / all-failed) — the pure seams extracted per item 3.
- **`save.rs` regeneration-grammar cells** (Matrix B): D1 single-authority
  dedup (expansion-artifact origin ×1-emission, literal-begin multi-defn,
  distinct-forms negative), D2 source-first (`sexp_matches_source` 4-cell,
  verbatim shorthand emission, inconsistent-source fallback, docstring
  mismatch/consistent pair, rehydration verbatim slice).
- **`process_form/tests.rs`**: `register_macro_in_module` recording seam
  (Matrix E origin-authority + direct-authored negative).
- **`expander.rs`**: defmacro name-position shield pair.
- **`repl.rs`**: `is_repair_definition_turn` §14.4/§18.8 carve-out cells.
- **`redefine.rs`**: `outcome_clears_broken` T1-shape recovery cell (review F1).
- (`eval.rs` Matrix-E writer cells landed Wave 4 with 0486.)

**Precise remainder (this FIXME stays open):**

1. `display.rs` ADT-value rendering module (`format_adt_value`/
   `format_adt_heap_value`, nested parameterized shapes, balanced-parens
   invariant) — rides Wave 10 with the 0493 fix (proposed-resolution item 1).
2. `process_form/cache_restore.rs` (448/0 — the D3 axis) + the module-env
   install seams — rides Wave 7 (A-3, CS-D3a Matrix D grid).
3. `repl.rs` handler tests through the facade (`handle_sig` 0492,
   `handle_mod` 0487, `handle_source`) — rides Wave 7 CS-0487 + Wave 10 0492
   per `s102-defect-wave.md` §6.4.
4. `process_form/macro_resolution.rs` (617/0) and
   `process_form/dependency.rs` happy-only neighborhood — no in-sprint fix
   touches them after the 0488 attribution moved typecheck-side; drain when
   a fix next opens those seams.
5. `lifecycle.rs` restore-path decisions beyond the degraded loader
   (`introduce_module` 4-branch gate, `preload_entry_slot_assignments`
   validity gate) — natural rider on Wave 7's install-route work.

## /design (int) S102 Phase 3: scenario-space matrices named

Per Principle 23's role binding, the implementation strategy's scenario space for
this drain is named explicitly in `design/int/s102-defect-wave.md` §3 — Matrices
A (session lifecycle, `lifecycle.rs`), B (regeneration grammar, `save.rs`),
C (redefinition target-kind × artifact world, `redefine.rs`), D (module-turn
environment, install routes × env dimensions), E (introspection recording).
Derive the per-fix unit briefs from those matrices; the per-section change-set
plans (§1, §4–§7) name which cells each fix must pin.
