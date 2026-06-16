---
number: 0386
target: /dev
filed_by: /arch
filed_at: 2026-06-16
sprint_filed: 84
refers_to: crates/cranelisp-typecheck/src/program.rs §is_codegen_ambiguous_type (:1594) §find_ambiguous_value_position (:1702) §expr_is_direct_constructor_value (:1674), crates/cranelisp-types/src/types.rs §is_representation_undetermined, design/arch/concrete-boundary-type.md §1.4 §3.1, spec/03-types.md §3.11.1
status: open
---

# §3.11.1 check verdict → full concreteness; remove direct-constructor skip; retire `is_representation_undetermined()`

## Issue

The tightened §3.11.1 (commit `2290aa9`) removed the representation-based
exemption: typecheck produces only concrete types, and a residual `Type::Var` in
ANY codegen-reaching value form is a type error — `(Vec a)`, `(Fn [a] a)`,
`(Option a)`, `[]` are all errors when unpinned, even when their machine shape is
determinate. The current §3.11.1 position-complete check
(`cranelisp-typecheck::program::is_codegen_ambiguous_type`, `program.rs:1594`)
uses the WRONG verdict: it calls `Type::is_representation_undetermined()`, which
returns `false` for `(Vec a)`/`(Fn a)` (admitting them), then refines with a
`Mixed`-shape gate. Both embody the rejected representation-determinacy notion.

The 5 failing-first acceptance guards `/qa` committed in `3fedb6b`
(`tests/regression.rs`) are RED against this:
`mono_vec_free_var_value_rejected_neg`, `mono_fn_free_var_value_rejected_neg`,
`mono_is_some_unannotated_none_rejected_neg`,
`mono_vec_empty_annotation_pins_and_compiles_pos`,
`mono_bare_annotated_value_pins_and_compiles_pos`.

## Proposed resolution

Per `design/arch/concrete-boundary-type.md` §3.1 (the /arch spec):

1. **Replace the verdict.** `is_codegen_ambiguous_type(state, ty)` returns `true`
   iff `!ty.is_concrete()` (equivalently `ConcreteType::from_type(ty).is_err()`) —
   rejecting ANY residual free var at a codegen-reaching value position. Delete the
   `adt_type_is_mixed_shape` helper + its `Mixed`-gate (the representation-determinacy
   refinement) and the bare-`Var`/`TyConApp` `_ => false` exclusion arm. KEEP the
   callee-position carve-out (`callee_span` — dispatch position, not a value
   position; §4.2, not a representation exemption).

2. **Remove the `(is-some None)` direct-constructor skip.** Delete the
   `&& !self.expr_is_direct_constructor_value(state, child)` guard
   (`program.rs:1755`) + the `expr_is_direct_constructor_value` method
   (`:1674`) + `symbol_is_constructor` if it has no other caller. The FIXME-0382
   carve-out admitted `None`/`(Some x)` because the constructor (hence
   tag-vs-pointer) was statically known despite a free var — a representation
   argument the tightening rejects. After removal, `(is-some None)` with `None`
   unpinned is the clean §3.11.1 ambiguity error (the spec's own worked example),
   not the downstream "undefined function: is-some" codegen error.

3. **Retire `is_representation_undetermined()`.** Once steps 1–2 land, the only
   live call (`program.rs:1595`) is gone. Remove the predicate from
   `crates/cranelisp-types/src/types.rs` (the `/arch`-owned crate — coordinate:
   either /dev removes it in the same change-set, or files back to /arch to action
   the removal + `public-api.txt` removal line once the call site is dead). The
   backend `heap.rs` references are comments only (the FIXME-0375/0381 backstop is
   deferred, never armed) — they need no change.

4. **Coordinate with FIXME 0385 (same wave).** Rejecting `(id [])` requires a
   working `:(Vec Int) []` escape — but `:(Vec Int)` currently fails with
   "unknown type 'Vec'" (0385, /dev, type-expr resolution). The §3.11.1 rejection
   and the `Vec`-annotation fix MUST land together; the two positive guards
   (`mono_vec_empty_annotation_pins_and_compiles_pos`, the Vec leg of
   `mono_bare_annotated_value_pins_and_compiles_pos`) only flip green when both land.

## Operational implication / Context

- Preserves the definition-admit + REPL-display dispositions: the check fires only
  at codegen-reaching value positions (the `for_each_child_expr` value-producing
  children, excluding the callee). A named polymorphic definition with result-only
  free vars (§3.11.3), a template, and a bare REPL value (§3.11.2) are NOT
  codegen-reaching value positions and stay admitted — the verdict change narrows
  *what verdict* is returned, not *where* the check fires.
- The new verdict agrees with the `ConcreteType` boundary type by construction
  (both full concreteness, no `Vec`/`Fn` carve-out) — when the concrete-boundary
  arc's Phase 3 lands, this standalone scan is subsumed by `MonoExpr::from_expr`.
- Mandatory unit test per fix (CLAUDE.md §Testing): a unit test pinning the
  full-concreteness verdict (an unpinned `(Vec a)`/`(Fn a)`/direct-`None` value at
  a codegen-reaching position is rejected; a concrete-or-pinned value is admitted).
  The 5 e2e guards are the integration witnesses.
- After the predicate removal, update `crates/cranelisp-types/public-api.txt`
  (removal line) + the two-update discipline (the predicate has no facade — its
  surface is the source rustdoc, already carrying the retirement note).
