---
number: 0878
target: /qa
filed_by: /design (cranelisp-backend, S118 Phase 3)
filed_at: 2026-07-25
sprint_filed: 118
refers_to: tests/plan/s118-test-plan.md §4.3 (the ruling-10 structural fence);
  crates/cranelisp-backend/src/compiler/vec_codegen.rs:1054,1137
  (build_elem_dec_fn, build_adt_drop_glue_fn);
  crates/cranelisp-backend/src/compiler/resolution.rs:263 (adt_drop_glue_name);
  design/backend/transitive-drop-glue.md §1.1, §8
status: open
---

# The ruling-10 structural fence would pass with a second named-glue identity home alive

## Issue

`s118-test-plan.md` §4.3 specifies the ruling-10 fence as:

- grep-zero `MAX_DROP_GLUE_DEPTH` and `drop_glue_depth` in
  `crates/cranelisp-backend/src/`;
- absence of the inline recursive drop-glue emission path in `rc_emission.rs`
  (asserted on its named seam).

That is exactly right for the *inline* emitter. But the backend mints deep
release from **two** other type-directed mechanisms today, and one of them is
the same class as the emitter being deleted:

`vec_codegen::build_adt_drop_glue_fn` (`:1137`) and
`vec_codegen::build_elem_dec_fn` (`:1054`) emit a **named, per-instantiation
ADT drop-glue function**, keyed by the backend-local
`resolution::adt_drop_glue_name` / `adt_instantiation_mangle` mangle with
`Linkage::Local` — a second identity home for the concept S116 arch ruling 9
gave exactly one authority (`cranelisp_types::drop_glue_symbol_name`,
`Linkage::Export`). It is the `drop-glue-underkey` class (FIXME 0633) with a
second key scheme, and the canonical registry already supplies its replacement:
`drop_glue.rs::define_vec_elem_adapter` wraps canonical glue in the established
`vec_drop` `(i64) -> i64` callback ABI.

A W3 change-set that deletes the inline emitter and keeps this pair passes the
fence as written while leaving two type-directed glue mechanisms and two
identity schemes alive — the state ruling 10 exists to prevent.

(The third mechanism, `lambda.rs::emit_capture_dec_glue`, is **not** in scope
here: it owns closure *capture layout*, not type identity, and survives the
migration by design — `transitive-drop-glue.md` §1.1 M4/M5.)

## Proposed resolution

Extend the §4.3 fence cell with grep-zero over `crates/cranelisp-backend/src/`
for:

- `build_adt_drop_glue_fn`
- `build_elem_dec_fn`
- `adt_drop_glue_name`

(`adt_instantiation_mangle` may retain non-glue consumers — check before adding
it.) Same construction as the existing cell: RED today, flips at the W3
migration change-set.

`/qa` may decline: the design carries the constraint independently
(`transitive-drop-glue.md` §8's delete list + §11's no-interim list, with
`/review` rejecting a surviving second identity home). The ask is only that the
*structural* fence match the *architectural* condition, so the guard survives
after this sprint's reviewers have moved on.

## Context

Filed by `/design`(backend) during the S118 Phase-3 refresh of
`transitive-drop-glue.md`, while enumerating the exact symbols the atomic
deletion covers (§8).
