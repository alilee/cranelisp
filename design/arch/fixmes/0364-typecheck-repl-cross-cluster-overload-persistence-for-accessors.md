---
number: 0364
target: /design
filed_by: /dev
filed_at: 2026-06-15
sprint_filed: 83
refers_to: crates/cranelisp-typecheck/src/program.rs (state.overloads / resolved_overloads population), crates/cranelisp-typecheck/src/infer.rs (~:387 infer_apply overload deferral), crates/cranelisp-typecheck/src/adt.rs (fold_accessor_into_overload), tests/spec_05_definitions.rs::accessor_cross_type_duplicate_field_name
status: open
---

# Cross-type duplicate field-name accessors don't dispatch across REPL clusters (overload tables are per-check, not symbol-table-backed)

## Issue

Spec §5.2.6: two product types with the same field name (`(deftype Box [:Int
v])` + `(deftype Cup [:Int v])`) each synthesise an accessor `v`; they must
coexist (no duplicate-definition error) and dispatch by argument type: `(v (Box
5))`→5, `(v (Cup 9))`→9.

S83 Wave 2 implements this by folding the colliding accessors into the existing
`DefKind::Overloaded` multi-sig mechanism (`adt.rs::fold_accessor_into_overload`):
the first accessor `v` is promoted to a mangled `v$Box` concrete variant, the
second registers `v$Cup`, and an `Overloaded` base under `v` carries both
`OverloadVariant`s. **This works in `--run` mode (single cluster):** the
`(v (Box 5))` call site defers via `infer_apply`'s `state.overloads.contains_key`
check and `resolve_pending_overloads` picks the matching mangled variant by arg
type (verified: single-cluster `--run` typechecks `(v (Box 5))` to `Int` with NO
`user/Cup vs user/Box` mismatch). The mangled `v$Box`/`v$Cup` names contain `$`,
so int's codegen batch (`derive_codegen_batch`, the `name.contains('$')` leg)
DOES compile them — so the cross-type case is codegen-ready (unlike the plain
single accessor, FIXME 0363 Gap A).

**It fails in REPL mode (the guard's harness — `repl_prims`, one cluster per
line):** the overload dispatch tables `CheckState::overloads` /
`resolved_overloads` are populated during the deftype's type-registration
cluster but are **per-check** — they do not persist to the later `(v (Box 5))`
cluster. In that cluster `state.overloads` is empty, so `infer_apply` does NOT
defer; it unifies the arg against the `Overloaded` base scheme (the last
variant, `(Fn [Cup] Int)`) and reports `type mismatch: user/Cup vs user/Box`.

This is the known REPL cross-cluster overload-state issue (analogous to the
multi-sig defn case, which DOES survive across clusters — `(g 5)` then `(g 5
6)` dispatch correctly in separate REPL inputs — so there IS a working
symbol-table-backed path for defn overloads that the accessor fold is not
reusing/triggering). The accessor `Overloaded` base + mangled variants persist
in the symbol table across clusters; only the in-`CheckState` dispatch tables
are lost.

## Proposed resolution (design question for /design → /typecheck)

Make overload dispatch read its variants from the persisted symbol-table
`DefKind::Overloaded { variants }` entry rather than (only) the per-check
`state.resolved_overloads`, so a call to an `Overloaded` base in a later cluster
re-derives the candidate set and defers correctly. This likely means:
`infer_apply` should defer when the callee resolves to a `DefKind::Overloaded`
entry (not just when `state.overloads.contains_key`), and
`resolve_pending_overloads` should fall back to the entry's `variants` when the
base is absent from `state.resolved_overloads`. This benefits multi-sig defn
dispatch uniformly, not just accessors. /design to confirm the seam (this is a
cross-form/cross-cluster typecheck-state-rehydration question that touches the
overload model, beyond a point fix).

Until then, the cross-type duplicate-field accessor is SAFE in REPL (no crash;
the second deftype registers without a duplicate-def error — the fold succeeds;
only the *call-site dispatch* mismatches) but does not satisfy the guard's
`(v (Box 5))`→5 / `(v (Cup 9))`→9 assertions. The guard
`accessor_cross_type_duplicate_field_name` stays red, attributed here.

## Operational implication / Context

S83 Phase 5 Wave 2. Companion to FIXME 0363 (/int codegen + warning surfacing)
and 0362 (/frontend self-qualified type split). The fold logic is committed and
unit-covered (`adt.rs::cross_type_duplicate_field_folds_into_overload` asserts
the `Overloaded` base + both mangled `v$Box`/`v$Cup` concrete variants are
registered). The remaining work is the cross-cluster dispatch rehydration.
