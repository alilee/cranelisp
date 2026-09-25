# Qualified trait references in `impl`

Owner: `design` narrow-deployed to typecheck. Subordinate to `typecheck.md` §9.1 and
`traits.md`; elaborates the conventional and higher-kinded `impl` registration seam
only. Required behaviour: `spec/07-traits.md` §7.3 (a declaration requires a
resolvable trait reference) and §7.3.4; `spec/05-definitions.md` §5.4.

## 1. Requirement and boundary

An `impl` head contains references, not declaration binders:

- conventional slot 1: `Trait` or `module/Trait`;
- HKT slot 1: `(Trait f)` or `(module/Trait f)`;
- HKT slot-2 pairing head: `(Trait Constructor)`, another reference that must
  resolve to the same trait as slot 1.

All three positions resolve under the ordinary module rules, so a bare and a
qualified spelling that reach one declaration denote one identity. A `deftrait`
head is a binder: it stays bare-only and frontend grammar rejects a qualified one
before typecheck sees it. Typecheck adds no compensating binder check and shares
no `impl`-reference helper with declaration parsing, so fixing reference
resolution cannot widen declaration syntax.

The seam is internal to `cranelisp-typecheck`. It uses the published `TraitRef`,
`FQTraitName`, trait declaration and impl records, `CheckError` and `check_forms`
unchanged; it adds no public item, cache schema or cross-crate interface.

## 2. Resolve once at the impl seam

`traits/impl_check.rs::register_trait_impl` begins with one resolution of the
complete as-written slot-1 reference:

```text
resolve_impl_trait_ref(state, written_ref, span)
    -> ResolvedImplTrait { fq: FQTraitName, decl: TraitDeclInfo }
```

- `ResolvedImplTrait` is private to the trait-implementation subsystem, and only
  the helper constructs it. `decl` is the declaration found at `fq`, so no caller
  can pair a declaration found through one spelling with a home found through
  another (Principle 24, **Resolve once**; Principle 18, **Enforce architectural
  invariants structurally where possible**).
- The helper resolves the full written reference (`module/name` when qualified)
  through `scope_resolve` exactly once, requires a terminal trait declaration, and
  mints `FQTraitName` from the resolved canonical module plus the declaration's
  name.
- Past this seam no impl-registration helper accepts `TraitRef`, `TraitName` or
  display text as the trait identity; each takes `&ResolvedImplTrait` or
  `&FQTraitName`.
- The helper is not public and does not belong in `cranelisp-types`: resolution
  behaviour is typecheck's, while `FQTraitName` is the shared vocabulary
  (Principles 2, **Narrow interfaces**, and 15, **Facade types live with their
  behavior**).

## 3. Canonical identity consumption

The resolved carrier is the single source for every identity-bearing action in the
impl transaction.

| Consumer | Input and behaviour |
|---|---|
| Kind and shape validation | Read `decl`; compare the HKT slot-1 shape and `con_var` binder spelling against it. |
| HKT pairing-head cross-check | Resolve the complete written pairing head through the same helper and compare `FQTraitName`s, never spellings. |
| Impl placement and key | Write the impl shell at `fq.module`, keyed from the resolved target and `fq`. |
| Stored metadata | Store `fq` as the impl's trait name. |
| Explicit and synthesised-default method mint | `mangle_trait_method(fq.name, method, fq_target)` for both; the as-written reference is never a mangle input. |
| Snapshot and rollback grain | The method-symbol set, enumerated by the same mangle before any method is checked. |
| Re-impl enrolment and final refresh | The checked impl-method `Defn`s registration returns under their canonical names, held in `ModuleCheckAccumulator.default_method_defns`. The field's name is historical: it holds explicit and synthesised methods. Finalization iterates those names and never reconstructs them from the top-level form. |
| Diagnostics | The written spelling appears only in source-facing error context; successful identity and display come from `fq`. |

The mangle's trait component is the canonical bare trait name; the module identity
is carried by placement and the impl key. A bare imported reference and a
qualified reference therefore mint the same method symbol while the impl shell
keeps the full trait home. This applies Principle 7, **Single source of truth**,
and Principle 26, **Record from settled state**.

## 4. Transaction order

1. Resolve slot 1 to `ResolvedImplTrait`.
2. Validate the slot-1 shape and HKT `con_var` spelling from `decl`.
3. For HKT, resolve the pairing head and compare canonical identities.
4. Resolve and kind-check the effective target to one `FQTypeName`.
5. Check collisions and required-method completeness.
6. Mint the complete canonical method-symbol set once.
7. Stage the impl shell at the trait home and snapshot the prior shell and method
   entries at the writer module.
8. Check synthesised defaults and explicit methods, passing the canonical trait
   identity to every method-check and mint seam.
9. On success, return the checked definitions, which are the enrolment record; on
   failure, restore exactly the shell and method-symbol set snapshotted at step 7.
10. Finalization refreshes only those settled names.

No provisional as-written mangle is published and repaired later. For HKT, the
target rewrite extracts the constructor only after the slot-1 and pairing-head
identities have settled, and it does not replace the resolved trait carrier.

## 5. Errors

Resolution failures are located at the impl span and keep the written reference:

- unknown module or name, or a terminal that is not a trait: `unknown trait:
  <as-written-reference>`;
- a qualified reference to a private trait: the ordinary resolver's visibility
  error at the impl span;
- an HKT pairing head that fails to resolve or resolves to another trait: the
  bad-pairing diagnostic;
- a slot-1 shape or `con_var` mismatch: the declaration-driven diagnostic, after
  resolution succeeds.

A failed qualified resolution never falls back to the bare name and never scans
other modules, so an invalid qualifier cannot bind an in-scope trait of the same
name. Errors occur before the shell or any method entry is staged.

## 6. Evidence

- **Module tier** (`crates/cranelisp-typecheck/src/traits/impl_check/tests.rs`):
  canonical identity and mangle for a qualified conventional impl and its
  synthesised default; failed re-impl restoring canonical entries without
  residue; an invalid qualifier not falling back to a same-named bare trait; and
  the HKT pairing-head matrix, qualified and bare.
- **Solution tier** (`tests/spec_07_traits.rs`):
  `qualified_impl_trait_reference_resolves_canonical_home_and_dispatches` and its
  `_neg_does_not_mint_written_qualifier_into_method_name` twin,
  `qualified_hkt_impl_trait_reference_resolves_canonical_home_and_dispatches`, and
  the `hkt_impl_pairing_head_qualified_*` and `deftrait_qualified_*` binder
  negatives. Coverage status is the spec-side annotation band, which `qa`
  maintains.

## 7. Open item — an unreachable builtin default arm

`generate_default_methods` skips every trait method without a default body, then
builds each body with a branch whose `else` arm calls `build_default_body` from the
bare declaration name. The guard makes that arm unreachable, so its correctness
rests on convention, not on the type. Removing the arm is a `dev` simplification;
no design decision is owed.
