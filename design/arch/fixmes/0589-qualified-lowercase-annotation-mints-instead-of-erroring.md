---
number: 0589
target: /dev
filed_by: /review
filed_at: 2026-07-14
sprint_filed: 109
sprint: S110
refers_to: crates/cranelisp-frontend/src/ast_builder.rs::parse_annotation_name (TypeVar carrying a qualified string) — the frontend leg only; folds into 0590
status: deferred
---

# Qualified-lowercase annotation (`:user/int`) — frontend `TypeVar`-routing leg

## Status (S109 → deferred S110)

**In-crate typecheck backstop LANDED S109.** The mint arm in
`resolve::resolve_type_expr` refuses to mint a `TypeVar` whose name contains
`/` (a type var is a BARE lowercase identifier, spec §3.3) — it falls to the
existing `TypeNotFound` error. Live repro at HEAD now errors correctly:

```
(defn f [:user/int x] x)   ; → type error: unknown type `user/int`   ← NO longer mints
```

Guarded by `resolve::tests::u8_qualified_lowercase_name_does_not_mint`
(a `:user/int` `TypeVar` errors even with a `mint_free_var` allocator present;
a bare `:a` sibling still mints — the guard fences minting to bare-lowercase).

**No live bug remains** once the in-crate backstop holds. This FIXME stays open
ONLY to track the remaining FRONTEND structural-cleanliness leg.

## Remaining leg (deferred to S110, folds into 0590)

Frontend `parse_annotation_name` (`ast_builder.rs`) still constructs
`TypeExpr::TypeVar("user/int")` carrying the FULL qualified string — a `TypeVar`
should structurally never carry a `/`-qualified name (Principle 18: enforce
invariants structurally — "a `TypeVar` is a bare lowercase identifier" must be
enforced where type-var-ness is decided, not merely backstopped downstream).
Either reject qualified-lowercase annotations at parse with a targeted
diagnostic, or route them as `Named` so the unknown-type error names the module.

This is the SAME "where type-var-ness / mint-on-miss is decided" family as
**FIXME 0590** (S110 resolver-mirror convergence — four hand-rolled mint-on-miss
sites). The frontend `TypeVar`-routing leg folds into that P7 single-source
refactor rather than a standalone frontend excursion. `/qa`: the §L negative
program-seam cell `(defn f [:m/x v] v)` must error (sits beside FV-13 as the
third over-broadening guard) — the in-crate seam is already pinned by u8; the
program-seam cell rides on 0590's convergence.

## Context

Found by `/review` on e401cce9 (S109 W6), probing the priority-3 case
discrimination boundary. The discrimination IS structural (TypeVar vs Named);
the frontend's `TypeVar` constructor is looser than the spec's type-variable
lexical class, so any typecheck-side capability inherits the looseness. The
in-crate `!contains('/')` guard is the correct backstop; the structural fix
belongs at the frontend/resolver decision point (0590).
