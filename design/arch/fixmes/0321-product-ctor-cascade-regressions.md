---
number: 0321
target: /dev
filed_by: /qa
filed_at: 2026-06-12
sprint_filed: 79
refers_to: crates/cranelisp-typecheck/src/checker.rs §pattern-ctor chokepoint, crates/cranelisp-typecheck/src/resolve.rs §FQ type-leaf, src/platform.rs §fqize_type_expr, src/display.rs §product-ctor display, tests/regression.rs::s79_quasiquote_macro_resolves_macros_scons_in_clause_body, tests/regression.rs::s79_fq_field_type_primitives_int_resolves_without_import
status: open
---

# S79 product-ctor dual-facet cascade regressed ~104 e2e tests

## Issue

The S79 Option-3 product-ctor-as-`Def` correction (FIXME 0319) cascaded across
cranelisp-types → typecheck → backend → src/(int). `cargo check -p cranelisp`
went GREEN (the cascade compiles), but a full `cargo nextest run -j2
--no-fail-fast` (SHA `3339e2d` + uncommitted cascade) is **1090 passed / 105
failed / 8 skipped** — a regression of ~104 tests from the committed baseline
(suite was 1175/1175 green at SHA `9bbdf65`). Only ONE of the 105 is the
intended-RED forcing test (`batch_main_pure_int_return_is_rejected`). The other
104 are real cascade regressions.

`cargo check` does NOT run tests, so the "compiles green" verification did not
surface this. The regression is e2e-observable only.

### Root breakdown (105 unique failing tests, classified against stderr + spec)

| Root | # | Signature | Minimal repro |
|---|---|---|---|
| **A** | ~89 | `unknown constructor in pattern: macros/SCons` | `tests/regression.rs::s79_quasiquote_macro_resolves_macros_scons_in_clause_body` |
| **B-prim** | 2 | `unknown type \`primitives\` (from module '')` | `tests/regression.rs::s79_fq_field_type_primitives_int_resolves_without_import` |
| **B-shapes** | 6 | `unknown type \`shapes/Rectangle\` (from module '')` | `tests/spec_platforms_adt.rs::platform_adt_roundtrip_run` (+5 siblings) |
| **C** | ~3 | product-ctor display: `user/user/Point.Point` + value renders raw pointer not `(Point 3 4)` | `tests/repl_introspection.rs::data_constructor_product_no_dot_notation_display` |
| **D** | 1 | intended-RED forcing test (NOT a regression) | `tests/spec_10_io.rs::batch_main_pure_int_return_is_rejected` |

Clusters by suite: spec_11_stdlib 54, spec_09_macros 19, spec_platforms_adt 6,
s76_macro_availability 6, repl_introspection 5, repl_persist 2, repl_lifecycle 2,
regression 2, spec_fqtypename_boundary 2, spec_05_definitions 2, build_confidence
1, examples 1, process_form_dispatch 1, repl_negative 1, spec_10_io 1.

### Root A — macro/SList SUM-ctor pattern resolution (DOMINANT, ~89)

A single quasiquote macro (`(defmacro inc [x] \`(add-i64 ~x 1))`) fails in
`--run`/batch with `unknown constructor in pattern: macros/SCons` (synthetic span
`1000003`). The macro expander lowers the quasiquoted template into `SList`
values; the clause fn's compiler-generated pattern-match over `SList` cannot
resolve `macros/SCons`. `SCons`/`SNil` are SUM ctors — `bootstrap.rs::
register_synth_adt` registers them as `Def { kind: Constructor { type_def: None } }`
plus a separate `TypeDef` (verified correct in source). So the regression is in
the **pattern-constructor resolution chokepoint** FIXME 0319/0317 touched —
`lookup_constructor_type_with_state` / `is_internal_constructor_check_with_state`
in `crates/cranelisp-typecheck/src/checker.rs` — NOT the product path itself.
Because quasiquote underlies essentially every macro AND the prelude/stdlib
(`text.string` etc.) is macro-heavy, this single root takes out 85% of the
regression. **Fix this first** — it likely clears the bulk.

### Root B — FQ type-leaf split (8: 2 prim + 6 shapes)

Two manifestations, same symptom class (a slashed FQ type leaf is mis-split, the
error names module `''`):

- **B-prim** (typecheck/resolve, 2): `(deftype Box (ABox [:primitives/Int n]))`
  fails with `unknown type \`primitives\``. Spec §3.1 says an FQ type ref needs no
  import; this was GREEN cement (`spec_fqtypename_boundary`) before the cascade.
  The FQ leaf `primitives/Int` resolves with the wrong module/name partition.
- **B-shapes** (src/platform.rs, 6): `fqize_type_expr` (platform sig FQ-leaf
  repair) produces `TypeRef::new(None, TypeName::from("shapes/Rectangle"))` —
  module `None`, name = the WHOLE slashed string — so `check_type_expr` looks up a
  type literally named `"shapes/Rectangle"` in module `""` and fails. It must
  split on `/` into `module: Some("shapes"), name: "Rectangle"` (cf. the
  `TypeRef` doc: `(option/Option Int)` → `{ module: Some("option"), name:
  "Option" }`). This blocks every `spec_platforms_adt` round-trip/hash-gate test
  AND the schema-regen step (the platform cannot load to drive `/platform-schema
  shapes`). NOTE: the IO-wrapped sig (FIXME 0318) means the round-trip's exit-12
  witness may also need the `main` to force the `IO` — reconcile after the FQ-leaf
  fix unblocks loading.

B-prim and B-shapes may share an underlying cranelisp-types FQ-split helper, or be
two sites; isolate per `tests/CLAUDE.md §"Isolating Cross-Crate Failures"`.

### Root C — product-ctor display (~3)

`(deftype Point [:Int x :Int y])` now displays its def entry as
`:(Fn …) user/user/Point.Point ; deftype` (double `user/`, spurious `.Point`
dot-notation) and a product value `(Point 3 4)` renders as `:user/Point
<rawptr>` instead of `(Point 3 4)` (repl/spec §1.5). The product ctor is now a
`Def` (not a `TypeDef`), and `src/display.rs` (def-entry display + value
formatter) was not updated for the dual-facet. int boundary.

## Proposed resolution

`/dev`, narrow-deployed per crate, in this order (cheapest-first, root A clears
the most):

1. **typecheck** — Root A: restore `macros/SCons` (SUM-ctor) pattern resolution
   at the FIXME-0319/0317 chokepoint. Write an isolating unit test in
   `crates/cranelisp-typecheck/src/checker.rs` that a qualified SUM ctor
   `macros/SCons` resolves in a pattern in a macro-clause-body context.
2. **typecheck/types** — Root B-prim: restore FQ type-leaf split for
   `primitives/Int` in field-type position. Unit test in resolve.
3. **int (src/platform.rs)** — Root B-shapes: fix `fqize_type_expr` to split the
   slashed leaf into `TypeRef { module: Some, name }`.
4. **int (src/display.rs)** — Root C: product-ctor def-entry + value display.

Each fix is validated against the named e2e repro (failing-not-ignored, already
in the suite). The two TIGHT minimal guards (`s79_quasiquote_macro_…`,
`s79_fq_field_type_…`) are committed in `tests/regression.rs`.

## Operational implication / Context

This is the R2.3 green-up; it is NOT green. Per the failing-not-ignored
discipline the 104 regressions stay RED until `/dev` resolves them — the failing
tests ARE the durable record + the trigger. The cascade should NOT be committed
as a green close; it carries ~104 open regressions tracked here + ledgered. The
schema-regen step (S79 task 2) and the platform ADT round-trip (task 4) are
BLOCKED on Root B-shapes — the platform cannot load until `shapes/Rectangle`
resolves, so `/platform-schema shapes` cannot be driven and the committed
placeholder `platforms/shapes/src/shapes.platform-schema` (correct `w`/`h` field
body, sentinel layout-hash) cannot be regenerated this wave.
