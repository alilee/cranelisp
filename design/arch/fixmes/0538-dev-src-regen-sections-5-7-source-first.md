---
number: 0538
target: /dev (src/)
filed_by: /design
filed_at: 2026-07-08
sprint_filed: 105
refers_to: src/save.rs::{generate_traits,generate_types,render_decl_sexp,introspection_sexp_and_source}, design/int/session-transaction.md §10 T1 I-4 regen-fidelity note
status: open
---

# Extend the source-first regen discipline to save.rs sections 5–7 (traits/types)

## Origin

Successor to FIXME 0530 (`target: /design`, filed by `/dev` S103), whose `/design` half is
resolved: `design/int/session-transaction.md` §10 T1's I-4 regen-fidelity checkpoint now
records the verification result + the ruling. This FIXME carries the **code half** to
`/dev (src/)`.

## The ruling (design input — already recorded in §10 T1 I-4)

`save.rs` regeneration sections 5–7 (`generate_traits` / `generate_types`, `save.rs:648/669`)
render each `TraitDecl` / `TypeDef` from its **stored sexp** via `render_decl_sexp` — a
structural pretty-printer (`render_decl_sexp_indented` / `render_decl_flat`) that desugars
reader shorthand and reformats whitespace. They have **no source-first branch**, unlike
section 8 (`generate_fns_and_macros`), which emits the verbatim `Introspection.source` slice
when it re-parses to the recorded sexp (`sexp_matches_source`) and falls back to
`pretty_print` only on mismatch.

**Reach is narrow, severity cosmetic:** a T1 fn-downgrade in a module that *also* declares
traits/types reloads the whole module and reformats the co-resident trait/type declarations.
`render_decl_sexp` is structurally faithful (drops nothing, corrupts nothing; the reloaded
module typechecks identically) — the loss is the user's original formatting + reader
shorthand, a fidelity regression, not data loss. **Not a T1-cure blocker.**

`/design` ruled the source-first cure **IN** (Principle 7 single source of truth; Principle 6
— the machinery is already shared, so extending it is low-cost, not premature).

## The change-set (for `/dev (src/)`)

Extend `generate_traits` and `generate_types` to prefer the **consistency-gated verbatim
`Introspection.source` slice**, exactly as section 8 does: the
`introspection_sexp_and_source` + `verbatim_slice` machinery already exists and is shared.
Emit the verbatim source slice when it re-parses to the recorded sexp; fall back to
`render_decl_sexp` only on mismatch. Land with **round-trip unit tests** (METHOD §2.2 seam
grain): a trait/type decl with non-canonical formatting + reader shorthand round-trips
through regen byte-identically when the sexp matches, and falls back to the pretty-printer
when it does not.

## Scope boundary

- `src/save.rs` interior only — no cross-crate interface, no ABI, no facade, no public-API
  change.
- **Non-blocking** — a trait/type-bearing module's T1 reload is semantically sound today;
  this is fidelity polish. Deferrable past S105.

## Relationship to FIXME 0537

Both 0537 and this are regen-fidelity gaps under the T1 reload path, but distinct: 0537 is
section 8's `__expr` non-definition leak + its reload coupling; this is sections 5–7's
pretty-print-from-sexp reformatting. Same file (`save.rs`), same source-first discipline —
`/dev (src/)` may co-schedule them, but they are separately actionable.

Delete this FIXME when the `save.rs` sections 5–7 source-first change lands with its
round-trip unit tests.
