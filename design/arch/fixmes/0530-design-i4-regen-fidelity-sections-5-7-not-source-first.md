---
number: 0530
target: /design
filed_by: /dev
filed_at: 2026-07-06
sprint_filed: 103
refers_to: design/int/session-transaction.md §10 T1 addendum 8 / I-4, src/save.rs::{generate_traits,generate_types,render_decl_sexp}, design/int/s102-defect-wave.md §4.2 (D1/D2 source-first)
status: open
---

# I-4 checkpoint: regen sections 5–7 (traits/types) are NOT source-first — a T1 reload of a trait/type-bearing module reformats the user's trait/type source

## Issue

The §10 T1 addendum-8 (I-4) precondition asked `/dev` to confirm, before CS-1
reloads a trait/type/impl-bearing module, that `save.rs` regeneration sections
5–7 share the source-first + dedup invariant the D1/D2 cure established for
section 8 (fns/macros), or are provably exempt.

**Result: they do NOT share it.** `generate_traits` and `generate_types`
(`save.rs:648/669`) render each `TraitDecl`/`TypeDef` from its STORED SEXP via
`render_decl_sexp` — a structural pretty-printer (`render_decl_sexp_indented` /
`render_decl_flat`) that desugars reader shorthand and reformats whitespace.
Section 8 (`generate_fns_and_macros`) is source-first: it emits the verbatim
`Introspection.source` when it re-parses to the recorded sexp
(`sexp_matches_source`), falling back to `pretty_print` only on mismatch. Sections
5–7 have no such source-first branch — they always pretty-print from the sexp.

**Reachability under the F2-refined T1 trigger.** deftype ctor re-entry
(slotted→slotted) and deftrait redefinition (prior is a `TraitDecl`, not a `Def`)
do NOT trigger the cure, so the *target* is never a trait/type. But a
template/`Overloaded` FN downgrade (a live T1 trigger) in a module that ALSO
declares traits/types reloads the WHOLE module, regenerating its trait/type
sections through this pretty-printer. So the exposure is real but narrow: a T1
fn-downgrade in a trait/type-bearing module reformats the co-resident trait/type
declarations on reload.

**Severity: cosmetic, not a semantic poison.** `render_decl_sexp` renders the
full declaration faithfully in STRUCTURE — it does not drop the decl or corrupt
its semantics (unlike the D1 double-persist / dropped-form class). The reloaded
module typechecks identically. What is lost is the user's original trait/type
formatting and reader shorthand — a fidelity regression, not data loss.

## Proposed resolution

`/design` to rule whether sections 5–7 warrant the source-first cure (extend
`generate_traits`/`generate_types` to prefer the consistency-gated verbatim
`Introspection.source` slice, exactly as section 8 does — the
`introspection_sexp_and_source` + `verbatim_slice` machinery already exists and is
shared). If ruled in, `/dev` (src/) lands it in `save.rs` with round-trip unit
tests (the METHOD §2.2 seam grain). If ruled cosmetic-tolerable at stage M,
record the exemption in §10 T1 I-4 so a future reader does not re-open the
checkpoint.

## Operational implication / Context

Not a blocker for the T1 full cure (per the I-4 checkpoint framing — "flag if
not, it's a checkpoint"). The cure ships; a trait/type-bearing module's T1
reload is semantically sound. This FIXME records the fidelity gap so it is not
mistaken for the D1/D2 cure being complete across all regen sections.
