---
number: 0677
target: /dev
filed_by: /sprint
filed_at: 2026-07-20
sprint_filed: 114
refers_to: audits/frontend-s113.md §3 R2 (evidence §2.3); crates/cranelisp-frontend/src/ast_builder.rs:1725/:1741/:1905; cranelisp_types::resolve::split_qualified
status: open
---

# Audit R2 — one qualified-name splitter; retire the compensating re-split with 0589

Accepted at S114 Phase 1 (user, 2026-07-20) from `audits/frontend-s113.md` §3 R2.
Narrow-deploy: cranelisp-frontend. `/arch` sign-off required only if the consolidation
target is the types-crate splitter (cross-crate).

From the assessment: three in-file `rsplit_once('/')` implementations mirroring
`cranelisp_types::resolve::split_qualified`; the third exists to compensate the 0589
mis-classification.

**Done**: "one splitting primitive in the crate (or direct use of the types-crate one);
`type_expr_to_trait_ref` no longer re-splits; a unit test pins that a slash-bearing
`TypeVar` cannot reach it (the structural fence outliving the 0589 fix)."
