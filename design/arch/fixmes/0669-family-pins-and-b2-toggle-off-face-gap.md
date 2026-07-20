---
number: 0669
target: /qa
filed_by: /review
filed_at: 2026-07-19
sprint_filed: 113
refers_to: tests/false_fresh_provenance_residual.rs (B-2/I-1 rows); FIXME 0668 (the family + evidence); tests/plan/s113-test-plan.md §2 (safety matrix)
status: open
---

# Pin the binding-indirection family (FIXME 0668 cells) + close the B-2 toggle-off coverage gap

## Severity

Important

## Issue

1. **The B-2 toggle-off face silently lost its pin.** The committed B-2 repro
   (`match_scrutinee_cow_var_pattern_{repl,link}`) flipped GREEN via the W5b
   typecheck escape-recording fix — but only analysis-ON. Verified 2026-07-19:
   the same shape under `CRANELISP_NO_OWNERSHIP=1` (`--run`, clean dir, 3/3
   runs) returns per-run-varying garbage — the toggle-off COPY branch mints a
   temp scrutinee, the match decs it after the arm, and the var-pattern arm
   forwards the alias (protect-inc comes AFTER the dec; rc hits 0 first). The
   file header's own claim ("B-2 also FAILS toggle-off") is again true, but no
   committed face covers it, so the differential-oracle acceptance
   ("analysis-on == analysis-off == correct") narrowed without a RED. R14's
   count-truth holds AT the COW site (the copy fires); the count is then dropped
   at the match consume seam — 0668 failure-direction 2.
2. **The 0668 family cells need committed failing-not-ignored pins** (the
   defect-closure rule): the two probe cells the W5b reviews found (nested-match
   COW; let-indirected COW-into-container) plus the ownership-independent
   minimal twins that prove the family is pre-COW (`(let [q [7 8 9]] [q])`
   project; `(match (match v [r r]) [q q])`; `(let [q v] [q])`) — a variant ×
   {on,off} × {repl,--run,--link} matrix per the coverage-by-definition-variants
   standing category. Small cells; exact sources + observed exits in FIXME 0668.

## Proposed resolution

/testing batch: one file (sibling of `false_fresh_provenance_residual.rs` or a
new `binding_indirection_consume.rs`) carrying the matrix, each RED attributed
to 0668's seam; add the toggle-off face rows for B-2. `/qa` disposition on
whether the I-1 capture face joins the same family attribution (its committed
locus comment currently points at typecheck `transfer.rs`; 0668's evidence says
the all-Owned face is backend consume-seam).

## Context

S113 W5b review adjudication; companion to FIXME 0668 (the seam + fix-shape
estimate). Filed for the Phase-5 ship-vs-carry evidence set.
