---
number: 0319
target: /arch
filed_by: /dev
filed_at: 2026-06-12
sprint_filed: 79
refers_to: crates/cranelisp-types/src/check.rs §TypeDefInfo, crates/cranelisp-types/src/module.rs §ModuleEntry::TypeDef, crates/cranelisp-typecheck/src/adt.rs §register_type_def_with_ctor_infos, design/arch/bounded-contexts.md §7
status: open
---

# Product-type field names are dropped from the symbol table — backend schema R2 cannot recover them

## Issue

Wave A task R2 asked `/dev` (cranelisp-backend) to fix the schema generator so a
single-ctor **product type** (`(deftype Rectangle [:Int w :Int h])`) emits the
REAL declared field names (`w`/`h`) instead of positional `_0`/`_1`. The task
preferred a **schema.rs-local** solution reading existing metadata, and directed
`/dev` to STOP and file a blocker if the names are genuinely unreachable without
a `cranelisp-types` change.

**They are unreachable.** The declared field names of a product type are not
present anywhere in the `symbol_tables` the backend schema generator receives.
The loss happens in the symbol-table model + the typecheck registration, both
upstream of cranelisp-backend:

1. The symbol table is a single `symbols: HashMap<Symbol, ModuleEntry>`
   (`crates/cranelisp-types/src/module.rs:102`), keyed by `Symbol`. A product
   type's TypeDef and its same-named constructor Def **collide on one key**
   (`"Rectangle"`).

2. In `crates/cranelisp-typecheck/src/adt.rs::register_type_def_with_ctor_infos`,
   `register_constructors` (line ~168) inserts the constructor `ModuleEntry::Def`
   under key `"Rectangle"` with `param_names = ["w","h"]` (built at adt.rs:303-304,
   attached at adt.rs:349). Then line ~182 **overwrites** key `"Rectangle"` with
   the `ModuleEntry::TypeDef`. The Def — and its `param_names` — is clobbered. For
   sum/enum types each ctor has a distinct key, so their Defs survive; only the
   product (type-name == ctor-name) case loses its Def.

3. What survives is `ModuleEntry::TypeDef { info: TypeDefInfo,
   constructor_scheme: Some(Scheme), .. }`. `TypeDefInfo`
   (`crates/cranelisp-types/src/check.rs:182`) has only `name`, `type_params`,
   `constructors: Vec<Symbol>` — **no per-field name list**. `constructor_scheme`
   is a `Scheme` whose `ty` is `Type::Fn([Int, Int], Rectangle)` — field **types**
   only, **no names**.

4. No other store reachable from the schema generator's
   `symbol_tables: &DashMap<ModuleFullPath, SymbolTable>` retains the names
   (no mangled/internal alternate key; `Introspection` is REPL-only and carries
   no field-name metadata; the synthesised ctor AST `Expr::ConstrADT` lived on the
   clobbered Def). The schema generator's existing positional `_0`/`_1` fallback
   (`crates/cranelisp-backend/src/schema.rs` product branch, ~228-249) is therefore
   the *only* thing it can emit from the data it has.

Downstream impact (the original `/platform` report): a platform DLL's
`read_field("w")` cannot resolve against a schema that names the fields `_0`/`_1`.

## Proposed resolution

A `cranelisp-types` (+ `cranelisp-typecheck`) change is required to retain the
product type's declared field names somewhere reachable from the surviving
`TypeDef` entry. `/arch` to choose the shape; options observed from the source:

- Add an ordered per-field name list (e.g. `field_names: Vec<Symbol>`, or a
  `fields: Vec<(Symbol, ...)>`) to `TypeDefInfo` (or to the `TypeDef` entry next
  to `constructor_scheme`), populated at registration in
  `register_type_def_with_ctor_infos`/`register_constructors` from the same
  `ctor.fields` that already feed `param_names`. This is the minimal-data option
  and keeps the single-source-of-truth on the TypeDef the product ctor resolves
  through.
- OR retain the product constructor Def under a non-colliding key so its
  `param_names` survive (larger blast radius — touches every product-ctor lookup
  that currently resolves through `constructor_scheme`).

This is squarely cross-crate (`cranelisp-types` is `/arch`-owned; the
registration is in `cranelisp-typecheck`), so it is out of scope for a
backend-narrow `/dev`.

## Operational implication / Context

- `/dev` (cranelisp-backend) made **NO source edits** this wave — the fix is not
  achievable schema.rs-locally, per the task's STOP-and-report directive.
- The Wave A unit-test flip (`product_type_schema_lists_typed_fields` asserting
  `((w ...) (h ...))`) is **deferred** until the upstream change lands — flipping
  it now would assert behaviour the backend cannot produce, leaving a red test in
  cranelisp-backend that no backend change can green. Once `/arch` makes the names
  reachable, the schema.rs product branch reads them (a one-line change replacing
  the `_{i}` synthesis) and the test flips green in the same change-set.
- Once resolved, re-deploy `/dev` narrow to cranelisp-backend to: (1) read the
  real names in schema.rs's product branch, (2) flip the unit test, (3) run the
  release gate. The blocker is purely the data-availability upstream.
