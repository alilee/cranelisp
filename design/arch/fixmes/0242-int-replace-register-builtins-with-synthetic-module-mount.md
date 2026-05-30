---
number: 0242
target: /int
filed_by: /sprint
filed_at: 2026-05-30
sprint_filed: 72
refers_to: src/session_v4.rs:1072 (register_builtins call), src/platform.rs:703 (register_builtins call), crates/cranelisp-typecheck/src/builtins.rs (DELETED — assembly reference recoverable from git history), design/arch/facades/typecheck.md §"Builtin registration — removed from typecheck", design/arch/fixmes/0241-arch-synthetic-module-assembly-leaves-typecheck-builder-vocabulary.md, design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md
status: open
---

# Replace `register_builtins` call with synthetic-module table mounting

## Issue

`cranelisp_typecheck::register_builtins` — and the entire
`crates/cranelisp-typecheck/src/builtins.rs` synthetic-module assembly body — is
**deleted** from typecheck (FIXME 0241 — synthetic-module assembly leaves
typecheck's bounded context; user-arbitrated 2026-05-30). `int`'s two call sites
can no longer reach it:

- `src/session_v4.rs:1072` — production session init.
- `src/platform.rs:703` — test fixture.

The break is currently masked by `int`'s pre-existing S70/S72 `cranelisp-types`
cascade errors (import-resolution aborts before name-resolution reaches the
call), and will surface once those are repaired. The disconnect is intentional —
the forcing function for this migration, per `feedback_facade_first_migration`.

## Proposed resolution

**Not blocked.** The approved decision is narrower than the original 0241 premise:
no `cranelisp-types::SymbolTable` builder vocabulary is built first. `int`
reconstructs the mount sequence **directly**, using the deleted `register_builtins`
body (recoverable from git history — the commit that removes
`crates/cranelisp-typecheck/src/builtins.rs`) as the assembly reference. There is
no in-tree `pub(crate)` copy to read; pull the body from git.

1. Replace the `register_builtins(&symbol_tables, &next_type_id)` call at
   `session_v4.rs:1072` with the synthetic-module mount sequence — mount the
   substrate tables (special forms, intrinsic scalars, extern primitives) then
   the expressible-ADT tables (macros/Option/IO/Trace/TestResult), exactly as
   `int` already Arc-mounts `PRIMITIVES_TABLE` a few lines above
   (`session_v4.rs:1064`). Advance `next_type_id` past each mounted table's
   type-var high-water mark via `advance_next_id_past_table` to preserve
   monotonicity. `int` reconstructs the entry shapes, cross-module field
   FQ-types, and `next_id` threading from the git-history `builtins.rs` body.
2. Update `platform.rs:703` (test fixture) to the same mount path.
3. Confirm the startup ordering invariants the legacy body relied on (read from
   git history): `primitives` seeded before special-form metadata; `macros/Sexp`
   field types resolvable before any `.cl` parse; root `""` exists before
   special-form registration.

## Operational implication / Context

- The legacy `register_builtins` body is **deleted** from
  `crates/cranelisp-typecheck/src/builtins.rs` (no in-tree `pub(crate)` copy
  retained). The authoritative assembly reference is **git history** — the commit
  that removes the file. Recover it from git for the exact entry shapes,
  cross-module field FQ-types, and the `next_id` threading the mount must
  reproduce. (Typecheck no longer waits on this migration to delete — the deletion
  is the forcing function, not a follow-on.)
- Sequencing: S73. Not S72 — workspace-green is out of S72 scope and `int` is
  already red from the upstream cascade.
- This is part of `int`'s broader S72 cascade repair (HeapCategory /
  ConstructorInfo / retired ModuleEntry variants); the `register_builtins`
  replacement should fold into that wave so `int` reaches green once.
