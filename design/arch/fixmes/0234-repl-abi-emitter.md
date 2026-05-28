---
number: 0234
target: /repl
filed_by: /dev (platform)
filed_at: 2026-05-28
sprint_filed: 71
refers_to: design/platform/sprint71-redesign.md §1.3 (polymorphic-instantiation naming), §12 (Next skills)
status: open
---

# `/abi <TypeName>` REPL emitter implementation

## Issue

Sprint 71 Wave 2 lands the cranelisp-S-expr schema DSL grammar +
polymorphic-instantiation naming convention (`OptionInt`-style
concatenated-UpperCamel per design §1.3). The DSL is now stable
enough for a REPL-side emitter to produce schema-arm-ready text from
a cranelisp `deftype` declaration.

A future REPL slash-command `/abi <TypeName>` would:
1. Look up `TypeName` in the current REPL session's symbol-table.
2. Emit the corresponding schema-DSL text (per §1) that a DLL author
   would paste into their `declare_platform!` `schema:` arm.
3. Suggest the matching `schema_types: [...]` entries.

This closes the loop between cranelisp ADT declaration and DLL-side
schema authoring — currently the DLL author hand-translates from
cranelisp deftype to the schema-DSL form.

## Proposed resolution

Add `/abi <TypeName>` to the REPL slash-command surface in
`repl/spec.md`; implement in `src/repl.rs` (or wherever slash-command
dispatch lives post-migration).

Emitter contract:
- Reads from the symbol-table — no recomputation.
- Outputs the schema-DSL text per §1 BNF: `(TypeName ((FieldType field) ...))`
  for products; `(TypeName V1 (V2 ((FieldType field) ...)) ...)` for sums.
- Polymorphic instantiation per §1.3: `(Option Int)` → `OptionInt`;
  `(Map String Int)` → `MapStringInt`. The emitter materialises the
  monomorphised form (since the schema is at the monomorphised layer,
  per §1.3 rationale).
- Reserves the CL-wrapper names (`CLInt` etc.) — if the cranelisp type
  is named `Int`, the emitter outputs `CLInt`; if it's `String`,
  outputs `CLString`; etc.

Worked example output (cranelisp `(deftype Point [Int x Int y])`):

```
(Point ((CLInt x) (CLInt y)))

schema_types: [Point]
```

## Operational implication / Context

This is a pure ergonomic improvement — no impact on the platform
ABI itself. The emitter is purely client-side (REPL-only); it does
not affect DLL load, cache, or typecheck.

Pairs with FIXME 0233 (platform-as-module) loosely — once platform
modules are first-class, the emitter could integrate with `/info`,
`/sig`, and `/exports` for a given platform module's declared types.
