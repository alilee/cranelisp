---
number: 0589
target: /dev
filed_by: /review
filed_at: 2026-07-14
sprint_filed: 109
refers_to: crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr (TypeVar mint arm) + crates/cranelisp-frontend/src/ast_builder.rs::parse_annotation_name
status: open
---

# Qualified-lowercase annotation (`:user/int`) silently mints a type variable

## Severity
Important — over-broadening hole in the W6 fix's discrimination guard; a
genuinely-wrong annotation that errored before e401cce9 is now silently
accepted as polymorphic.

## Issue

Live repro (REPL, HEAD = e401cce9):

```
(defn f [:user/int x] x)   ; → :(Fn [a] a) user/f   ← silently polymorphic
```

Pre-change this errored `unknown type user/int` (TypeVar var_map miss →
TypeNotFound). Post-change the mint arm quantifies it.

Root cause is split across two crates:

- Frontend `parse_annotation_name` (ast_builder.rs) discriminates
  case on the segment AFTER the final slash (`is_uppercase_start("user/int")`
  → false) but then constructs `TypeExpr::TypeVar("user/int")` carrying the
  FULL qualified string. The comment above `is_uppercase_start` claims "The
  slash itself is rejected by the reader for type-variable names" — the live
  repro shows it is not.
- Typecheck's new mint arm (resolve.rs `TypeVar` + `mint_free_var: Some`)
  mints on ANY `TypeVar` miss, including one whose name contains `/`.

Spec §3.3: type variables are bare "lowercase identifiers" (`a, b, elem, f`).
A module-qualified name can never be a type variable — `:mymod/int` is either
a (nonexistent) qualified type reference or a typo, and must error.

The §L PIN family (FV-13) guards only the UPPERCASE unknown (bare + nested);
no cell covers the qualified-lowercase shape, so this regressed invisibly.

## Proposed resolution

1. `/dev` (typecheck, in-crate, safe either way the frontend question lands):
   the mint arm refuses to mint a `TypeVar` name containing `/` — falls to the
   existing `TypeNotFound` error. Unit test alongside u4.
2. Frontend half (cross-crate — needs its own routing): `TypeVar` should
   structurally never carry a qualified string; either reject
   qualified-lowercase annotations at parse with a targeted diagnostic, or
   route them as `Named` so the unknown-type error names the module. That is a
   `/dev`-on-frontend change; `/qa` attributes.
3. `/qa`: add the missing §L negative cell — `(defn f [:m/x v] v)` must error,
   never quantify (sits beside FV-13 as the third over-broadening guard).

## Context

Found by `/review` on e401cce9 (S109 W6), probing the priority-3
"cannot be tricked" boundary of the structural case discrimination. The
discrimination IS structural (TypeVar vs Named) — but the frontend's TypeVar
constructor is looser than the spec's type-variable lexical class, so the
typecheck-side capability inherits the looseness (Principle 18: enforce
invariants structurally — the invariant "a TypeVar is a bare lowercase
identifier" is currently enforced nowhere).
