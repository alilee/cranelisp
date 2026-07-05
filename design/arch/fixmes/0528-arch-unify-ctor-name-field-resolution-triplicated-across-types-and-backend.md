---
number: 0528
target: /arch   # promoting a shared ctor-resolution helper into cranelisp-types is a new cross-crate public surface (baseline-diff discipline) + an interface-shape ruling both the types predicate and the two backend classifiers must delegate to — cross-boundary, so /arch rules the shape, then /dev (cranelisp-backend) implements the delegation as the Wave-3 emergent refactor
filed_by: /arch   # S103 Wave 1, while landing the R5 value_layout carrier
filed_at: 2026-07-05
sprint_filed: 103
refers_to: crates/cranelisp-types/src/heap.rs (type_ctor_names + ctor_field_concrete_types), crates/cranelisp-backend/src/heap.rs:642 (is_mixed_adt), crates/cranelisp-backend/src/heap.rs:785 (classify_adt)
status: open
---

# Ctor-name / field-type resolution is now triplicated — unify a shared cranelisp-types helper (Principle-7 mirror)

## Issue

The S103 Wave-1 `value_layout` carrier added `type_ctor_names` +
`ctor_field_concrete_types` to `crates/cranelisp-types/src/heap.rs`. These resolve,
from a `ModuleEntry`:
- the constructor name-list for a type (via `TypeDef.info.constructors`, or a
  single-ctor product ctor `Def`'s `type_def` facet), and
- a constructor's field types (from `scheme.ty`'s `Fn(params, _)`).

That is the **third** copy of the same ctor-name/field-shape resolution. The other
two live in the backend heap classifiers:
- `crates/cranelisp-backend/src/heap.rs:642` — `is_mixed_adt`
- `crates/cranelisp-backend/src/heap.rs:785` — `classify_adt`

This is the recurring "duplicate heap classification" class — a Principle-7 mirror
(`memory/feedback_review_root_cause_and_duplication.md`). Three independently
maintained readers of the same `ModuleEntry`→(ctors, fields) shape drift
independently; a change to how a single-ctor product stores its constructors (the
S79 Option 3a `type_def` facet, the TypeDef-vs-Def split) must be mirrored in all
three or the classifiers disagree — which for a soundness-coupled predicate like
`value_layout` is a latent unsound-divergence, not merely inconsistent output
(`design/arch/ownership-inference.md` §6.3 single-sourcing rationale).

## Proposed resolution

Do **NOT** add a 4th reader. Unify **with Wave 3** (the backend R5 classifier work),
as a mandatory in-sprint emergent refactor:

1. `/arch` rules the shape of a shared ctor-resolution helper promoted into
   `cranelisp-types` (beside `HeapHeader` / `value_layout`): where it lives, its
   signature (given a `SymbolTable` + `FQTypeName`, yield ctor names and per-ctor
   field types), and its return type. New public surface ⇒ `cranelisp-types`
   `public-api.txt` baseline regen + `interfaces.md` / BC §7 cascade
   (baseline-diff discipline).
2. `value_layout`'s `type_ctor_names` + `ctor_field_concrete_types` collapse into
   delegators over the shared helper.
3. The backend `is_mixed_adt` (`heap.rs:642`) and `classify_adt` (`heap.rs:785`)
   delegate to the same helper for their ctor-name/field resolution, keeping only
   their classifier-specific logic on top.

Net: one ctor-resolution reader in `cranelisp-types`; three consumers delegate.

## Operational implication / Context

- This is Wave-3 work; **do NOT fix it in Wave 1**. The Wave-1 carrier lands the
  two helpers as-is (they are correct — they are just a mirror). This FIXME is the
  durable record so Wave 3 picks it up rather than adding a fourth reader when the
  backend classifiers start delegating to `value_layout`.
- Scope note: the cycle guard added to `layout_words`/`adt_layout_words` in Wave 1
  (visited-set, compiler-DoS bound) is `value_layout`-internal and is NOT part of
  this dedup — the shared helper is the ctor-name/field-shape resolution only, not
  the recursive word-count walk.
- Filed by /review (S103 Wave-1 review of the carrier), second finding, gated to
  Wave 3 (the first finding — unbounded recursion — was fixed in the Wave-1
  change-set).
