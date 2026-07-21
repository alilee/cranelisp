---
number: 0723
target: /dev (typecheck deployment)
filed_by: /sprint
filed_at: 2026-07-20
sprint_filed: 115
refers_to: crates/cranelisp-typecheck/CLAUDE.md (§"Concrete-boundary
  codegen_view population" falsified contract; :92-96 0590 "STILL OPEN"
  paragraph; dead traits.rs/program.rs seam references ×3+;
  has_impl_with_state named as live verification path; §callees
  "resolved_targets" name) vs program/support.rs:282-288 (the live
  Result<Option<..>, CranelispError> contract) + traits/dispatch.rs:75
  (has_impl_in_home, the live path)
status: open
---

# Crate CLAUDE.md currency sweep (audit S114 R-4, accepted at S115 Phase 1; merges the R-1 CLAUDE.md rider)

## Issue

`audits/cranelisp-typecheck-s114.md` §2.7, accepted by the user at S115
Phase 1: the crate memory file carries four falsified/dead claims where the
code moved fastest — most safety-relevant, it describes
`build_concrete_codegen_view` as "best-effort: Some on success, None on
failure" when the S114 carrier flip deliberately widened it to
`Result<Option<..>, CranelispError>` where `Unresolved` PROPAGATES and only
`NotConcrete` falls back (conflating them re-opens the check-gate-leak class
one level up). Also: the 0590 "STILL OPEN" paragraph (zombie — deleted at
S115 Phase 1), dead file references from the S87/S109 splits, and
`has_impl_with_state` narrated as the live verification path (test-only;
zero production callers).

## Proposed resolution

Audit R-4 Done criteria: every load-bearing claim in the file verifies
against current source; the codegen_view section states the post-flip
`ViewBuildError` contract explicitly (Unresolved-propagates /
NotConcrete-falls-back); the 0590 paragraph corrected to record the S110
convergence; no dead file references; §callees names the typed
`var_refs`/`apply_refs` carriers. Rides the same typecheck /dev wave as 0722.
