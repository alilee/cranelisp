---
number: 0679
target: /dev
filed_by: /sprint
filed_at: 2026-07-20
sprint_filed: 114
refers_to: audits/frontend-s113.md §3 R4 (evidence §2.4; S87 F2 / 04-23 #4, third carry — oldest open finding in the crate); crates/cranelisp-frontend/src/quasiquote.rs:75-162; crates/cranelisp-frontend/src/defmacro.rs:537-607
status: open
---

# Audit R4 — shared synthetic-Sexp kit

Accepted at S114 Phase 1 (user, 2026-07-20) from `audits/frontend-s113.md` §3 R4 —
third audit carry, accepted rather than declined-permanently. Narrow-deploy:
cranelisp-frontend. Cost: medium.

From the assessment: two constructor DSLs over one implicit shape-lock with
`ast_builder`.

**Done**: "one crate-internal `synth` module owns the primitive constructors
(`sym`/`int`/`str`/`list`/`bracket`/`cons`/`nil`); module-specific composites layer
on top."
