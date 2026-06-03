---
number: 0245
target: /design
filed_by: /arch
filed_at: 2026-06-02
sprint_filed: 76
refers_to: design/arch/macro-expansion-ownership.md §2.2 §4 §4.3, design/arch/bounded-contexts.md §2 (invariant 11), crates/cranelisp-types/src/macro_expander.rs
status: open
---

# Typecheck-interior macro-recognition algorithm — author `design/typecheck/macro-recognition.md`

## Issue

S76 W-Macro moves macro **recognition** (and driving the expansion fixpoint + structural-form re-classification) into typecheck, with execution delegated to int via the injected `cranelisp_types::MacroExpander` callback. The cross-crate ownership, the boundary type, and the structural-form re-entry resolution are settled by `/arch` in `design/arch/macro-expansion-ownership.md` + BC §2 invariant 11.

The **typecheck-interior** algorithm is `/design (typecheck)`'s to author — it is below the cross-crate boundary `/arch` owns:

1. The within-form descent that finds macro heads (walk order relative to the existing two-pass `check_forms` shape).
2. ~~The macro-vs-fn discrimination via the module-local lookup primitives (Principle 17 shapes 1/2) — replacing the retired frontend skeleton's bare-name "probe every module" loop with the current-module-view lookup.~~ **SUPERSEDED by the resolution-primitive fold-in (2026-06-03):** macro-vs-fn discrimination is now the `cranelisp-types` primitive `cranelisp_types::resolve_macro_head` (a types query, not a typecheck-interior walk) — recognition has **left typecheck's surface entirely**. typecheck's within-form descent (item 1) *calls* this primitive with its staging-aware view; int's Pass-1 loop calls it with the committed view. The discrimination logic is single-sourced in `crates/cranelisp-types/src/resolve.rs`. See `macro-availability-model.md` §0.9 + `bounded-contexts.md` §7 "Resolution primitive". /design (typecheck) wires `resolve_*` (and the descent's recognition call) onto the primitive; it does not re-author the discrimination.
3. The clause-arity match (the `clause_matches` logic moving conceptually to typecheck's recognition side, while the int-side `MacroExpander::invoke` impl owns the actual clause selection for execution — settle the split precisely).
4. The expansion fixpoint loop + its depth bound (the `EXPANSION_DEPTH_LIMIT` that moves out of frontend).
5. The structural-form re-classification mechanics (spliced `defmacro`/`defn` registering into the same cluster staging frame).

## Proposed resolution

`/design (typecheck)` authors `design/typecheck/macro-recognition.md` capturing the above, and in particular **pins the §4.3 interior-factoring choice**: does typecheck re-walk the expansion result inside `check_forms`, or does the expand+build fixpoint run in `process_cluster` (int) driven by a typecheck recognition predicate? `/arch`'s recommendation (macro-expansion-ownership.md §4.3) is the second shape — it keeps `build_form` in int so typecheck adds no `cranelisp-frontend` dependency, keeps the `MacroExpander` callback a pure `Sexp→Sexp` primitive, and reuses the existing `process_cluster` retry envelope for the fixpoint. Either shape uses the identical `MacroExpander` boundary; the choice is interior.

Coordinate with the /dev (int) brief — the chosen shape determines whether int's `process_cluster` loop or typecheck's `check_forms` body hosts the build_form-of-expansion-result step.

## Operational implication / Context

This is the per-crate elaboration of an `/arch`-settled cross-crate design — file, not block. The `MacroExpander` type is authored now (S76 Phase 3); the interior factoring is the /dev design wave's to pin before implementation. No code lands until both this interior doc and the /dev wave agree on the §4.3 shape.
