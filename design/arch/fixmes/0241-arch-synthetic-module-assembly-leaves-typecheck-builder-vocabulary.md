---
number: 0241
target: /arch
filed_by: /sprint
filed_at: 2026-05-30
sprint_filed: 72
refers_to: crates/cranelisp-typecheck/src/builtins.rs (register_builtins + assembly body — DELETED from typecheck), design/arch/facades/typecheck.md §"Builtin registration — removed from typecheck", design/arch/bounded-contexts.md §2 (typecheck) §4a (primitives), design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md, design/arch/fixmes/0239-arch-instantiate-module-symbol-table-from-source-facade.md, design/arch/fixmes/0242-int-replace-register-builtins-with-synthetic-module-mount.md
status: open
---

# Synthetic-module assembly leaves typecheck (deferred: shared `cranelisp-types` builder vocabulary)

## Decision (approved 2026-05-30, user-arbitrated) — narrower than this FIXME's original premise

The original premise of this FIXME was that synthetic-module assembly should leave
typecheck's bounded context *into a shared `cranelisp-types::SymbolTable` builder
vocabulary* (the `declare_intrinsic_type` / `declare_adt` / `declare_special_form` /
`declare_def` helpers proposed below). **That generalization is deferred.** The
approved motion is narrower:

1. `cranelisp_typecheck::register_builtins` and the entire
   `crates/cranelisp-typecheck/src/builtins.rs` synthetic-module assembly body are
   **DELETED** from typecheck — not retained `pub(crate)`. Git history preserves the
   body (the commit that removes it is the reference). Removing assembly from
   typecheck is correct on bounded-context grounds (content construction is not
   type-checking, BC §2) and does not depend on a replacement vocabulary existing.

2. **No `cranelisp-types` builder vocabulary is built now.** Instead, `int`
   reconstructs whatever mount sequence it needs in its own wave (FIXME 0242),
   pulling the assembly reference from git. No `cranelisp-types` change in this
   motion; no `declare_*` helpers added.

The facade has been reconciled: `design/arch/facades/typecheck.md` §"Builtin
registration — removed from typecheck" states the removal and points `int` at git
history + FIXME 0242 for the mount. BC §2's "Out of scope" already names "module
loading" as `int`'s, so no BC edit was owed.

## Why a shared builder vocabulary was NOT adopted now

- The boundary correction (assembly leaves typecheck) is achievable by deletion +
  `int` reconstruction alone. A shared types-crate builder is an *additional*
  generalization with its own design surface (builder ergonomics, who owns each
  synthetic module's source-of-truth, bootstrap-ordering encoding). Coupling it to
  the deletion would have widened a single-edge motion into a cross-crate vocabulary
  design — out of proportion to the immediate need.
- Only `int` consumes the mount today. A shared builder pays off when a *second*
  consumer needs to be generic over synthetic-module sources. Until then, `int`'s
  direct reconstruction (mirroring how it already Arc-mounts `PRIMITIVES_TABLE`) is
  the minimum mechanism (Principle 2 / minimum-mechanism).

## Deferred rationale (preserved for if/when a shared builder is wanted)

Should a shared synthetic-module builder vocabulary later be justified (e.g. a
second consumer, or the `int`-side reconstruction proving to duplicate enough
shape to warrant extraction), the original analysis stands as the design input:

1. **Builder vocabulary on `cranelisp-types::SymbolTable`** — kind-shaped helpers
   (`declare_intrinsic_type`, `declare_adt`, `declare_special_form`, `declare_def`)
   that encapsulate the `ModuleEntry` shape per kind, over the existing low-level
   primitives (`new_with_params`, `insert`, `allocate_got_slot`). They would live in
   the types crate (manipulate only types-crate data; multi-consumer per BC §7).
   This is the home FIXME 0239's `ModuleSymbolTableSource` concept resolves to —
   prefer a lightweight builder convention + shared methods over a trait until a
   consumer needs to be generic over sources.

2. **Static source builders.** The user's "static builders, orchestrated by /int"
   framing and the earlier "substrate-Rust vs expressible-.cl" sketch compose: both
   tiers become static `SymbolTable` builders, differing only in owning crate.
   Bootstrap ordering is decisive — `macros/Sexp` references `primitives/Int`, macro
   expansion needs Sexp/SList resolvable *before the first `.cl` parses*, and IO's
   `Bind` is existential (unexpressible in HM) — so static builders are the default
   over `.cl` source for everything currently in `register_builtins`.

   Per-step classification (the 8 `register_builtins` steps):

   | Step | Disposition |
   |---|---|
   | special forms (root `""`) | substrate → static builder (metadata for `/info`) |
   | intrinsic scalars (Int/Bool/Float/String) + Vec | substrate → static builder; scalars candidate for `cranelisp-primitives` per 0239 Option A; Vec is a noted smell |
   | `macros` (Sexp/SList + sconcat) | mixed; ADT shape expressible but bootstrap-ordered → static builder, `provenance: macros` |
   | Option | expressible → static `declare_adt` builder |
   | IO (Pure/Effect/Bind) | mixed; Bind substrate → static builder |
   | bind primitive | substrate (inline CLIF) → with the externs |
   | Trace | already owned by Decision 0040 (relocates to `/int` in full) |
   | TestResult + test special forms | ADT expressible; the two fns already int-owned JIT intrinsics |

3. **`/int` orchestrates the mount** — startup mounts substrate tables →
   expressible-ADT tables → prelude `.cl`, exactly as it already mounts
   `PRIMITIVES_TABLE`. Reuse `advance_next_id_past_table` for type-var high-water
   monotonicity (static builders must pre-allocate within a range or expose their
   high-water mark).

## Status / disposition

- **The boundary correction is captured** (facade reconciled; `int` owns the mount
  via FIXME 0242). The *immediate* actionable content of this FIXME is therefore
  satisfied by the deletion + `int` reconstruction — no `/arch` builder authoring is
  owed this sprint.
- **This FIXME remains open** only as the home for the deferred shared-builder
  rationale + the FIXME 0239 generalization. Close it (folding any still-live FIXME
  0239 substance) once it is decided either (a) the shared builder is wanted — at
  which point it becomes actionable `/arch` work — or (b) `int`'s reconstruction has
  settled and a shared builder is confirmed unnecessary, in which case 0239 closes
  with it.
- **Relationship to FIXME 0239**: 0239 ("instantiate a module symbol table from a
  source") is the broader generalization; it is no longer blocked-on by anything
  here and is likewise deferred pending a second consumer.
- Coordinate with FIXME 0240 (adjacent int↔typecheck startup-seam threading:
  module_aliases A1/A4).
