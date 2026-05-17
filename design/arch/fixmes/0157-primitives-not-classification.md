---
number: 0157
target: /arch
filed_by: /design (primitives)
filed_at: 2026-05-07
sprint_filed: 66
refers_to: design/primitives/implementation-slice-s66.md §6 Q3, design/arch/facades/primitives.md §"Boolean primitives" line 51, crates/cranelisp-runtime/src/primitives/bool.rs, spec/appendix-a-builtins.md, design/arch/decisions/0054-spec-add-not-primitive-appendix-a.md (if present — referenced indirectly)
status: open
---

# `not` placement: primitive in `cranelisp-primitives`, or stdlib fn?

## Issue

`design/arch/facades/primitives.md` line 51 enumerates `not(b: i64) -> i64` under §"Boolean primitives" as part of the as-designed public surface for `cranelisp-primitives`. However, current source at `crates/cranelisp-runtime/src/primitives/bool.rs` (47 LOC) contains only `bool_to_string`; there is no `pub extern "C" fn not` anywhere in the runtime crate (`grep -n "pub extern" crates/cranelisp-runtime/src/primitives/*.rs` confirms 13 extern fns total — `bool_to_string`, `int_to_string`, `parse_int`, `float_to_string`, plus 10 `cranelisp_op_*`; no `not`).

Two readings:

- **Reading A — facade is target-stating.** `not` SHOULD be a primitive per spec. This slice's row 8 (greenfield named-primitive authoring) authors it alongside `add_i64` etc. The cycle 1 effort estimate already accounts for it.
- **Reading B — facade over-specified.** `not` is implemented in stdlib as `(impl Not Bool …)` (or `(defn not [b] …)` directly), and the facade should be revised to remove line 51. In this case the slice's row 8 does NOT author `not` and the facade gets a corrective edit.

Spec evidence (`spec/appendix-a-builtins.md`) per FIXME 0150 line 79 names `appendix-a-builtins.md` as the authority on the primitive list; the existence of `design/arch/fixmes/0054-spec-add-not-primitive-appendix-a.md` (per the fixmes register filename pattern) suggests `not` was added to the appendix at some point as a primitive — but the runtime source never absorbed the change.

## Proposed resolution

`/arch` rules on Reading A vs Reading B by checking `spec/appendix-a-builtins.md` directly. If A: confirm row 8 of the primitives slice authors `not(b: i64) -> i64` per facade; this slice closes the FIXME with no edit. If B: amend `design/arch/facades/primitives.md` line 51 to remove `not`; this slice's row 8 reduces by 1 fn; close FIXME with the facade edit.

`/design (primitives)` tentatively prefers Reading A (matches the facade as-written; consistent with the spec's primitive surface; trivial to author — 3 LOC). But the slice cannot bind unilaterally because the facade is /arch-owned.

## Operational implication / Context

Until resolved, the primitives slice row 8 lists `not` as part of the greenfield set (slice §1a "Greenfield symbols" line 4) but the count is provisional. Resolving before Phase β (Wave 3) lands removes ambiguity from the named-primitive authoring batch. Low-risk either way; high-priority for slice authoring clarity.

Filed during S66 Phase 3 design refresh of `design/primitives/implementation-slice-s66.md`.
