---
number: 0231
target: /typecheck
filed_by: /dev (platform)
filed_at: 2026-05-28
sprint_filed: 71
refers_to: design/platform/sprint71-redesign.md §12 (Next skills), crates/cranelisp-typecheck/, FIXME 0230, FIXME 0233
status: open
---

# Typecheck entry point for platform `type_sig` validation

## Issue

The platform-as-module migration (FIXME 0233) intends to flow each
`PlatformFn.type_sig` through the canonical typecheck pipeline so the
DLL's declared signature is unified into the same symbol-table view
that user code sees.

Currently, the int-side `parse_type_sig` translates the S-expr text
into a synthetic AST that bypasses typecheck — the platform fn is
registered with a pre-typechecked Type. The host-wiring sprint
replaces this with a frontend+typecheck call so:

1. Type expressions referring to schema-declared ADTs (e.g.
   `(Fn [Rectangle] Int)`) resolve through the typecheck symbol-table.
2. Inconsistencies between the DLL's claimed type and the
   schema-declared shape surface as typecheck errors at DLL load.

## Proposed resolution

`cranelisp-typecheck` exposes:

```rust
/// Typecheck a standalone type expression against an existing symbol
/// table — used by int's platform loader to validate
/// PlatformFn.type_sig (FIXME 0233 — replace parse_type_sig with
/// frontend+typecheck path).
pub fn check_type_expr(
    expr: &TypeExpr,
    ctx: &CheckContext,
    symbol_tables: &SymbolTables<...>,
) -> Result<Type, CheckError>;
```

The function reuses the existing infer pass for type expressions; the
FIXME is the named public binding + sufficient context-aware
dispatch (the platform-sig case is a single type expr, not a program
form).

## Operational implication / Context

This pairs with FIXME 0230 (frontend exposes `parse_type_expr`) and
FIXME 0233 (int reroutes its platform-sig path through them).
Coordinated landing in the host-wiring sprint.

This FIXME's resolution also enables the schema-validation callback
(FIXME 0229 step 2) — the host validator cross-references schema
ADT names against the typechecked symbol-table, exact same path the
type expressions use.
