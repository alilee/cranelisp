---
number: 0491
target: /qa
filed_by: /docs
filed_at: 2026-07-03
sprint_filed: 101
refers_to: repl/spec.md §18.3 (recompiled/broken sets "MUST be exact"; related-symbols layout), design/int/session-transaction.md (TransactionReport rendering), src/redefine.rs
status: open
---

# Cascade report names the internal `__expr` wrapper — internal symbol leaks into `broken:`

## Issue

When a signature-changing redefinition runs after any bare **expression turn**
has been evaluated, the cascade report's `broken:` section names `__expr` — the
REPL's internal synth-def wrapper for the last expression — alongside real user
symbols. `repl/spec.md §18.3` requires the sets to name the symbols the
transaction recompiled/broke using the §1.1 related-symbols layout; an internal
wrapper name is not a user symbol and reads as noise (a user has no `__expr`
definition to fix). Writing-convention-wise it also collides with the project
principle of never exposing internal names to users.

## Repro (deterministic; verified 2026-07-03 on `target/debug/cranelisp`, fresh dir, no prelude)

```
user> (import [primitives [add-i64 mul-i64 str-len]])
user> (defn f [x] (add-i64 x 1))
user> (defn g [x] (f x))
user> (defn k [x] (f (mul-i64 x 2)))
user> (g 1)                          ; ← any expression turn arms it
:primitives/Int 2
user> (defn f [s] (str-len s))
:(Fn [primitives/String] primitives/Int) user/f ; defn
; recompiled:
;  g
; broken:
;  k — type error at 12..29: type mismatch: expected primitives/String, got primitives/Int
;  __expr — type error at 0..5: type mismatch: expected primitives/String, got primitives/Int
```

Without the `(g 1)` turn, the same session prints only `k` under `broken:`
(verified). The leak also fires on the *recovery* direction: reverting `f`
after an expression turn in the new world (`(g "hello")`) prints
`; broken:\n;  __expr — type error at 0..11: …` on the otherwise-all-green
revert turn.

## Proposed resolution

Narrow failing test pinning that cascade-report sections never name `__expr` /
`__macro_*` (filter the synth-def wrappers from `TransactionReport` rendering —
they are already gate-exempt for slot policy per `src/CLAUDE.md` §redefine.rs).
Owning skill for the fix: `/int` (redefine.rs report rendering).

## Operational implication / Context

Surfaced while verifying transcripts for `user/guide/live-development.md`
(S101 Phase 6b). The guide currently footnotes the `__expr` line as a filed
cosmetic defect; drop the footnote when this is fixed.

## /qa guard batch (S101 6b, 2026-07-03): guards LANDED — this file is now redundant as a record

2 RED guards in `tests/repl_redefinition.rs`, pinning BOTH angles:
`redefine_cascade_report_neg_no_internal_expr_wrapper_in_broken` (expression
turn before the breaking redefinition) and
`redefine_revert_after_expression_turn_neg_no_wrapper_broken_section` (the
/repl 6b sharpening — the wrapper rejoins later transactions on signature
change of anything it called, reverts included; the all-green revert turn
must print no broken: section at all). RED-first verified. Resolver /int.
Ledger: `tests/plan/ledger.md` §"Sprint 101 Phase 6a/6b defect set".
