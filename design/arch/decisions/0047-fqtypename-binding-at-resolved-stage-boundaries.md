---
number: 0047
title: FQTypeName is binding as the cross-crate boundary type for resolved-stage type identifiers
status: pre-implementation
filed: sprint 67 (Phase 3 Wave 0 — second user-challenge scope amendment)
canonical_location: design/arch/facades/types.md §"Resolved type system" + §"FQTypeName migration plan (Sprint 67)"
amends: []
amended_by: []
retracts: []
reframes: []
filed_by_fixme: 0151
---

# 0047 — FQTypeName is binding as the cross-crate boundary type for resolved-stage type identifiers

Every API past frontend's resolution stage that names a type uses `FQTypeName`; bare `TypeName` is reserved for syntactic-stage uses inside the frontend (parser output, AST surface, `TypeExpr` shape).

This Decision formalises the binding commitment lifted from aspirational to binding in Sprint 65 W2 (per `sprint-65-reshape-phase-2-review.md` §4.1 — the grep-and-classify pass that produced the lift). The `facades/types.md` text states the commitment; this Decision is the operative register entry that names the close-out + the two narrow exceptions.

## Exceptions

The binding rule has exactly two principled exceptions, neither of which is extendable without `/arch` review:

1. **Reverse-lookup helpers on `Type`** — `from_name(&TypeName) -> Option<Type>` for primitive recognition and `type_name(&Type) -> Option<TypeName>` for primitive emission. These operate on the small set of built-in non-ADT types (`Int`, `Bool`, `String`, `Float`) where the unqualified name IS unique workspace-wide. There is no ambiguity for these to resolve against.

2. **Receiver-pinned lookups** — APIs whose receiver itself supplies the module context. `SymbolTable::get_type(&TypeName)` is keyed by bare `TypeName` because the `&self` receiver IS the module; wrapping the local-to-this-table key in `FQTypeName` would re-encode information already pinned by the receiver. The fully-qualified identity is reconstructible by the caller as `FQTypeName::new(module_of(&self), name.clone())` if needed downstream.

The producer/consumer split is:

- **Producer**: frontend emits `TypeExpr` carrying bare `TypeName` (no resolution context).
- **Lift site**: `cranelisp_typecheck::resolve::*` performs the `TypeName → FQTypeName` lift when a `TypeExpr::Named(name)` is resolved against the current scope plus imported modules.
- **Consumer**: typecheck, backend, intrinsics, primitives, platform, int — all consume only `FQTypeName` at public surfaces past typecheck.

## Status pointer — Sprint 67 close

S67 close — FQTypeName binding lands in source. The pre-S67 state had the facade-binding commitment but un-migrated source (FIXME 0151 status: open). S67 W0 enumerates every resolved-stage boundary API across typecheck/backend/intrinsics/primitives/platform/int and classifies each against the two exceptions (`facades/types.md` §"FQTypeName migration plan (Sprint 67)"). S67 W3 (per /dev per crate) executes the per-API conversions.

Per the W0 enumeration:

- **typecheck**: ~7 PIF conversions; 3 syntactic-lift-site keeps; ~5 receiver-pinned keeps. Largest /dev burden.
- **backend**: 1 PIF (`primitives_inline::*` trait-method target type); ~13 test-code keeps.
- **intrinsics, primitives**: 0 changes (no boundary hits).
- **platform**: 0 changes (single reverse-lookup keep at IO marker emission).
- **int**: 0 changes (all keeps justified by exceptions — parse-time conversions, REPL introspection, IO marker emission).

Wave 5 `/review` acceptance criterion: every API at a resolved-stage boundary uses `FQTypeName`; remaining bare `TypeName` hits MUST cite an exception by name in a code comment (e.g., `// FQTypeName exception 2 (receiver-pinned: &self IS module N)`).

FIXME 0151 closes alongside Wave 5 acceptance.

## Cross-references

- `facades/types.md` §"Resolved type system" — the canonical statement of binding
- `facades/types.md` §"FQTypeName migration plan (Sprint 67)" — per-API enumeration + per-crate disposition
- `design/arch/fixmes/0151-types-fqtypename-implementation.md` — the open implementation tracker (closed by S67 W5)
- `design/arch/principles.md` Principle 2 (narrow interfaces — fully-qualified identity at every boundary past the lift site)
- `design/arch/principles.md` Principle 17 (module locality — type names without module context are syntactic-stage only)
- `sprint-65-reshape-phase-2-review.md` §4.1 — the binding lift's rationale

## Rationale

- Principle 2 (narrow interfaces) — boundary types carry full identity; no caller-side context required to disambiguate.
- Principle 7 (single source of truth) — each type has exactly one fully-qualified name workspace-wide; bare `TypeName` cannot resolve to two different types in different modules at a boundary.
- Principle 11 (single pipeline) — uniform identity for ADT references across the resolved pipeline; no module-implicit shortcuts at cross-crate edges.

## Canonical location

`crates/cranelisp-types/src/newtype.rs` (`FQTypeName` definition); `facades/types.md` §"Resolved type system" (binding commitment + exception list); `facades/types.md` §"FQTypeName migration plan (Sprint 67)" (per-API close-out enumeration). Owner: `/arch` files Decision + facade text; `/dev` (per crate) executes per-API conversions in S67 Wave 3.
