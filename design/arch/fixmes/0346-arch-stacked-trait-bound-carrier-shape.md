---
number: 0346
target: /arch
filed_by: /sprint
filed_at: 2026-06-14
sprint_filed: 82
refers_to: crates/cranelisp-types/src/ast.rs (param slot Vec<(Symbol, Option<TypeExpr>)> on Lambda + DefnVariant), spec/03-types.md §3.9.2 (stacked annotations) + §3.9.3 (try-type-then-trait), crates/cranelisp-typecheck/src/program.rs:1856, design/arch/fixmes/0341-frontend-stacked-trait-bound-param-annotation-parse.md
status: open
---

# Carrier shape for N>1 stacked trait-bound param annotations (`[:Eq :Display a]`) — `cranelisp-types` boundary decision (blocks 0341 e2e)

## Issue (S82 Phase-3 /design frontend finding)

Defect 0341's frontend parse fix (accumulate a run of `:Trait` annotations onto the
following binder) flips the frontend **unit** guard, but the two **e2e** guards
(`tests/spec_07_traits.rs::stacked_trait_bounds_{single,two}_param(s)_compiles`)
cannot pass, because:

1. **No carrier for N>1 bounds.** The param slot is `Vec<(Symbol, Option<TypeExpr>)>`
   (one `Option<TypeExpr>` per binder, `ast.rs` Lambda ~:202 + DefnVariant ~:454).
   A run of 2+ bounds (`:Eq :Display a`) has no single-`TypeExpr` home.
2. **No constraint accumulation in typecheck.** `program.rs:1856` resolves a param
   annotation **strictly as a concrete type** (`resolve_type_expr_in_module`) — there
   is no try-type-then-trait fallback (§3.9.3) and no accumulation of a trait bound
   onto the type variable's `Scheme.constraints`. So even `[:Eq a]` does not today
   produce a constraint entry.

Phase-2 concluded "no `cranelisp-types` change in S82"; this finding overturns that
for 0341 specifically — the carrier is a boundary-type decision only `/arch` can make.

## Resolution — RULED: option (a), `TypeExpr::Bounds` variant (user, S82 Phase 3, 2026-06-14)

**Add a `TypeExpr` variant carrying the bounds set** — option (a). Sidecar (b) was
rejected: a param annotation is *either* a concrete type *or* a set of trait bounds,
never both (you cannot specify a concrete type and then constrain it), so a struct
carrying both `ty` and `bounds` models a state that cannot exist. The single
`Option<TypeExpr>` slot holding one-of {concrete type, bounds set} captures the
mutual exclusion by construction.

```rust
TypeExpr::Bounds(Vec<TraitRef>)   // "an unspecified type satisfying these traits"
```

Cascade (`/arch` owns the `cranelisp-types` change + interfaces.md narrative):
1. **`cranelisp-types`** — add `TypeExpr::Bounds(Vec<TraitRef>)`; the param tuple
   `Vec<(Symbol, Option<TypeExpr>)>` shape is UNCHANGED (minimum-mechanism — no
   call-site churn). Regenerate the `cranelisp-types` `public-api.txt` baseline.
2. **frontend** — `build_annotated_params` emits `Some(Bounds([...]))` from the
   accumulated annotation run (single bound → `Bounds([one])` for uniformity, or
   keep `Named` resolved-as-trait — frontend/typecheck agree on one).
3. **typecheck** — `program.rs:1856` gains try-type-then-trait resolution + a
   `Bounds` arm that accumulates the traits onto the type variable's
   `Scheme.constraints`. (Needed regardless of carrier — strict-concrete-type
   resolution is the second half of the defect.)

The two e2e guards (`tests/spec_07_traits.rs::stacked_trait_bounds_{single,two}_param(s)_compiles`)
are the joint acceptance across frontend + typecheck. The frontend parse-loop fix
flips the frontend unit guard independently.

## Progress — types-half DONE (S82 W0, /arch)

**Cascade step 1 (`cranelisp-types`) LANDED.** `TypeExpr::Bounds(Vec<TraitRef>)`
added to `crates/cranelisp-types/src/ast.rs` (doc-commented with the
one-of-{type, bounds} invariant); `cargo check -p cranelisp-types` green;
`crates/cranelisp-types/public-api.txt` regenerated (single added line:
`pub cranelisp_types::TypeExpr::Bounds(alloc::vec::Vec<cranelisp_types::TraitRef>)`);
`interfaces.md` updated with the `Bounds` narrative + invariant. The param tuple
`Vec<(Symbol, Option<TypeExpr>)>` is UNCHANGED (zero call-site churn). `head_ref`
already covers the new variant via its `_ => None` catchall; no other
`cranelisp-types` match/impl on `TypeExpr` exists.

**Frontend + typecheck cascade PENDING W2.** Blast radius (exhaustive `match` on
`TypeExpr` now needing a `Bounds` arm):

- **typecheck** (5 sites, all exhaustive — no catchall):
  - `crates/cranelisp-typecheck/src/form.rs:404` (`collect_type_var_ids`) — a `Bounds([..])` carries no type vars to collect; arm is a no-op `{}` (or fold the traits' module refs if needed for resolution).
  - `crates/cranelisp-typecheck/src/resolve.rs:34` (`resolve_type_expr`) — THE try-type-then-trait + constraint-accumulation site referenced by FIXME body / `program.rs:1856`; resolves the bounds and accumulates onto `Scheme.constraints`.
  - `crates/cranelisp-typecheck/src/traits.rs:1744`, `:1796`, `:1861` (three trait-sig type resolvers) — add a `Bounds` arm (likely an error/unsupported in trait-method-sig position, or the same constraint handling).
- **frontend** — NO exhaustive match breaks today; the cascade here is *emission*
  (`build_annotated_params` emits `Some(Bounds([..]))` from the accumulated
  annotation run), not a match-arm fix.
- **backend** — clean; backend has NO dependency on `cranelisp-typecheck` and
  does NOT match `TypeExpr` (it consumes typed AST, not `TypeExpr`). TypeExpr is
  frontend/typecheck-facing, as expected.
- **src/ (int)** — `src/platform.rs:446` (`fqize_type_expr`) matches `TypeExpr`
  but has an `other => other` catchall, so it compiles unchanged. No fix needed
  (a platform FQ-sig annotation would never be a bounds set; the catchall
  passing it through is correct).

## Operational implication / Context

In-sprint Phase-3 design gate (S82). The frontend unit-guard fix can land
independently; the e2e guards stay red until the carrier + typecheck halves land.
If the carrier decision is deferred, 0341 closes only at the unit tier this sprint
and the e2e guards carry forward with this FIXME.
