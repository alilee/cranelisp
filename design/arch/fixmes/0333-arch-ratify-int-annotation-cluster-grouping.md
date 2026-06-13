---
number: 0333
target: /arch
filed_by: /sprint
filed_at: 2026-06-13
sprint_filed: 81
refers_to: design/arch/bounded-contexts.md §6 (annotation-pairing is frontend-driven), src/worker.rs (build_program_compat, pass2_check_bodies_with_expansion, leading_annotation_len), src/session_v4.rs (eval / process_form_cluster)
status: open
---

# Ratify the int-side annotation cluster-grouping (refinement of the "call-site swap only" ruling)

## Issue

The S81 annotation-pairing fix (FIXME 0329, resolved) was ruled by `/arch` as:
all pairing lives in the frontend; int's side is a **call-site swap only**
(`build_program_compat` delegates to `cranelisp_frontend::build_forms`).

In implementation this proved insufficient: **two other int per-sexp loops** split
a leading `:Type` from its bound form before any builder saw them, so they had to
group the annotation+form cluster before delegating:
- `worker::pass2_check_bodies_with_expansion` (macro expansion is inherently per-form),
- `session_v4::eval` (the REPL sequence loop).

The int dev added `worker::leading_annotation_len` (`pub(crate)`, recognition-only —
mirrors the frontend's `try_consume_annotation` shape) so each split point knows the
cluster boundary, then hands the cluster to the frontend, which still owns the actual
`Expr::Annotate` construction. No pairing/construction logic was re-implemented in int.

## Proposed resolution

`/arch` confirms (or refines) `bounded-contexts.md §6`: the int boundary is not a
single call-site swap but **"wherever int splits the sexp stream per-form, it must
group a leading `:Type` cluster before delegating; the frontend constructs the
annotation."** Decide whether the recognition helper (`leading_annotation_len`)
belongs in int (current) or should be a frontend-exposed predicate so the cluster
boundary is also defined in one place (Principle 7 tension: the boundary recognition
is now in int while construction is in frontend). Update BC §6 wording to match the
as-built reality and rule on the recognition-helper placement.

## Operational implication / Context

NOT blocking — the fix is landed and green (1252/0/1). This is a post-implementation
ratification of a ruling refinement, per the cross-skill protocol. No test rides on it.
