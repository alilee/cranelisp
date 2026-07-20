---
number: 0681
target: /dev
filed_by: /sprint
filed_at: 2026-07-20
sprint_filed: 114
refers_to: audits/frontend-s113.md §3 R6; crates/cranelisp-frontend/src/module_extract.rs:454-522 (×4 dead); crates/cranelisp-frontend/src/defmacro.rs:103; crates/cranelisp-frontend/src/ast_builder.rs:411-433, 1321-1338 (Ring 3/4 messages)
status: open
---

# Audit R6 — hygiene batch: dead retained sub-parsers + retired-Ring diagnostics

Accepted at S114 Phase 1 (user, 2026-07-20) from `audits/frontend-s113.md` §3 R6.
Narrow-deploy: cranelisp-frontend. Cost: small.

From the assessment: five `#[allow(dead_code)]` speculatively-retained functions
waiting on REPL wiring that has not arrived in ~47 sprints; user-facing
"(Ring 3)"/"(Ring 4)" messages naming an axis retired S64.

**Done**: "dead functions deleted (git history is the archive; re-derive from
`parse_import` etc. if the REPL need materialises); NYI messages say what to write
instead ('not yet supported; use `(fn [x] …)`'), no ring numbers."
