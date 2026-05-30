---
number: 0242
target: /int
filed_by: /sprint
filed_at: 2026-05-30
sprint_filed: 72
refers_to: src/session_v4.rs:1072 (register_builtins call), src/platform.rs:703 (register_builtins call), crates/cranelisp-typecheck/src/builtins.rs (legacy assembly reference), design/arch/fixmes/0241-arch-synthetic-module-assembly-leaves-typecheck-builder-vocabulary.md, design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md
status: open
---

# Replace `register_builtins` call with synthetic-module table mounting

## Issue

`cranelisp_typecheck::register_builtins` was severed from the typecheck public
interface this sprint (FIXME 0241 — synthetic-module assembly leaves typecheck's
bounded context). `int`'s two call sites can no longer reach it:

- `src/session_v4.rs:1072` — production session init.
- `src/platform.rs:703` — test fixture.

The break is currently masked by `int`'s pre-existing S70/S72 `cranelisp-types`
cascade errors (import-resolution aborts before name-resolution reaches the
call), and will surface once those are repaired. The disconnect is intentional —
the forcing function for this migration, per `feedback_facade_first_migration`.

## Proposed resolution

**Blocked by FIXME 0241** (the `cranelisp-types::SymbolTable` builder vocabulary +
the static source builders must exist first). Once they land:

1. Replace the `register_builtins(&symbol_tables, &next_type_id)` call at
   `session_v4.rs:1072` with the synthetic-module mount sequence — mount the
   substrate tables (special forms, intrinsic scalars, extern primitives) then
   the expressible-ADT tables (macros/Option/IO/Trace/TestResult), exactly as
   `int` already Arc-mounts `PRIMITIVES_TABLE` a few lines above
   (`session_v4.rs:1064`). Advance `next_type_id` past each mounted table's
   type-var high-water mark via `advance_next_id_past_table` to preserve
   monotonicity.
2. Update `platform.rs:703` (test fixture) to the same mount path, or to the
   `TestSource` builder per FIXME 0239.
3. Confirm the startup ordering invariants the legacy body relied on
   (`builtins.rs` is the reference): `primitives` seeded before special-form
   metadata; `macros/Sexp` field types resolvable before any `.cl` parse; root
   `""` exists before special-form registration.

## Operational implication / Context

- The legacy `register_builtins` body is retained `pub(crate)` +
  `#[allow(dead_code)]` in `crates/cranelisp-typecheck/src/builtins.rs` as the
  authoritative assembly reference — read it for the exact entry shapes,
  cross-module field FQ-types, and the `next_id` threading the mount must
  reproduce. Typecheck deletes that body (per 0241 step 4) only after this
  migration lands.
- Sequencing: S73 (with 0241). Not S72 — workspace-green is out of S72 scope and
  `int` is already red from the upstream cascade.
- This is part of `int`'s broader S72 cascade repair (HeapCategory /
  ConstructorInfo / retired ModuleEntry variants); the `register_builtins`
  replacement should fold into that wave so `int` reaches green once.
