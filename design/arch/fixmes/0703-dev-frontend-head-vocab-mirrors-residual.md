---
number: 0703
target: /dev
filed_by: /review
filed_at: 2026-07-20
sprint_filed: 114
refers_to: crates/cranelisp-frontend/src/defmacro.rs::is_defmacro/is_begin; crates/cranelisp-frontend/src/module_extract.rs:114-134; crates/cranelisp-frontend/src/ast_builder.rs::classify_head
status: open
---

# R3 residual: two head-vocabulary mirrors survive outside `classify_head`

## Severity
Important (small cost)

## Issue

Audit R3's accepted Done criterion (FIXME 0678, resolved at `8b2c3e20`) is
"adding a top-level head requires exactly ONE edit". The three audited sites
converged, but two crate-internal predicates still re-derive `classify_head`
vocabulary arms (Principle 7):

1. **`defmacro.rs:43-46` `is_defmacro`** — `head == "defmacro" || head == "defmacro-"`,
   a verbatim mirror of the `HeadKind::Defmacro` arm. It is a **public**,
   int-consumed predicate (`src/process_form.rs:935`, `form_dispatch.rs:185`,
   `index_worker.rs:1204`), so drift here mis-routes real dispatch, not just tests.
2. **`defmacro.rs:56-60` `is_begin`** — mirror of the `HeadKind::Begin` arm.
3. **`module_extract.rs:114-134`** — the peel dispatch re-lists
   `"mod" | "mod-" | "import" | "export" | "platform"`, now mirrored by
   `classify_head`'s `HeadKind::StructuralDecl` arm (which this change-set
   introduced). A head added to one side but not the other is either peeled but
   rejected by `build_form_inner`, or never peeled and rejected as
   "must be peeled" — a confusing skew either way.

## Proposed resolution

(1)/(2): delegate — `matches!(classify_head(head), HeadKind::Defmacro)` /
`HeadKind::Begin` (same crate, one-line each; keeps the public signatures).
(3): either give `StructuralDecl` a payload (`Mod(Visibility)`/`Import`/…) that
`module_extract` consumes, or record a one-line decline in the crate `CLAUDE.md`
naming the two sites as a deliberate pair (module_extract needs per-decl
dispatch that `classify_head` deliberately collapses). Cross-crate sibling for
awareness only (NOT this FIXME's scope): `src/expander.rs:919` hand-rolls an
inline `is_defmacro_form` `matches!` instead of calling the exported
`cranelisp_frontend::is_defmacro` — int surface, flag when int is next deployed.

## Context

Found during /review of `8b2c3e20` (S114 W6) mirror scan. The R3 consolidation
is otherwise genuine: `parse_def_visibility` deleted, `build_form_inner` +
`is_top_level_form_sexp`/`head_is_top_level_form` + the test adapter all route
through `classify_head`.
