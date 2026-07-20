---
number: 0678
target: /dev
filed_by: /sprint
filed_at: 2026-07-20
sprint_filed: 114
refers_to: audits/frontend-s113.md §3 R3 (evidence §2.4; S87 F4+F7, third audit carry); crates/cranelisp-frontend/src/ast_builder/tests.rs:13/:66
status: open
---

# Audit R3 — single head classifier + tests call production

Accepted at S114 Phase 1 (user, 2026-07-20) from `audits/frontend-s113.md` §3 R3 —
third audit carry, accepted rather than declined-permanently. Narrow-deploy:
cranelisp-frontend.

From the assessment: head vocabulary in three prod sites + a verbatim test mirror.
One `classify_head(head) -> HeadKind` consumed by `is_top_level_form_sexp`,
`build_form_inner`, and `parse_def_visibility`; the test adapter calls the prod
functions and handles the `None` arm explicitly.

**Done**: "adding a top-level head requires exactly one edit; the test router cannot
drift from the prod router."
