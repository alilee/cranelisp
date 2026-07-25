# Qualified trait references in `impl`

Phase-3 design for Sprint 117 Track A. This document is subordinate to
`typecheck.md` and `traits.md`; it elaborates the conventional and
higher-kinded `impl` registration seam only.

## 1. Requirement and boundary

An `impl` head contains references, not declaration binders:

- conventional slot 1: `Trait` or `module/Trait`;
- HKT slot 1: `(Trait f)` or `(module/Trait f)`;
- HKT slot-2 pairing head: `(Trait Constructor)` where the head is another
  reference that must resolve to the same trait as slot 1.

All three reference positions resolve under the ordinary module rules. Bare
and qualified spellings that reach the same declaration denote one identity.
By contrast, a `deftrait` head is a `trait_binder`: it remains bare-only and
is rejected by frontend grammar before typecheck sees a `TraitDecl`. The
typechecker must not add a compensating binder check or share an
`impl`-reference helper with declaration parsing. This separation keeps a fix
for FIXME 0794/0836 from widening declaration syntax.

The crate boundary does not change. `TraitRef`, `FQTraitName`,
`ModuleEntry::TraitImpl`, `TraitDeclInfo`, `CheckError`, and `check_forms`
already provide the required carriers and entry surface. The implementation
is internal to `cranelisp-typecheck`; there is no `public-api.txt`, cache
schema, or cross-crate interface delta.

## 2. Resolve once at the impl seam

`register_trait_impl` begins with one operation over the complete as-written
slot-1 `TraitRef`:

```text
resolve_impl_trait_ref(state, written_ref, span)
    -> ResolvedImplTrait {
         fq: FQTraitName,
         decl: TraitDeclInfo,
       }
```

`ResolvedImplTrait` is crate-private and local to the trait implementation
subsystem. Its fields are private and it is constructed only by the resolver
helper: `decl` is the declaration fetched at `fq`, so callers cannot assemble
a mismatched `(fq, decl)` pair. The helper composes the full written reference
(`TraitRef::to_string()`, yielding `module/name` when qualified), calls
`scope_resolve` exactly once, requires a terminal `ModuleEntry::TraitDecl`,
and mints `FQTraitName` from `Resolved.home` plus `decl.name`. It does not call
the current `resolve_trait_decl`, whose `&TraitName` parameter has already
discarded the qualifier, or call `resolve_trait` a second time merely to
recover the home.

This replaces the current split:

1. `resolve_trait_decl(state, &impl_.trait_name.name)`, which discards the
   qualifier; and
2. `resolve_trait(state, bare_trait_name, span)`, which resolves the discarded
   bare spelling a second time.

Past this seam, no helper in impl registration accepts `TraitRef`,
`TraitName`, or display text as the trait identity. The required parameter is
`&ResolvedImplTrait` or `&FQTraitName`, depending on whether declaration
metadata is also needed. This is Principle 24, **Resolve once**, in its typed
carrier form; making the canonical carrier mandatory is Principle 18,
**Enforce architectural invariants structurally where possible**.

The helper is deliberately not public and does not belong in
`cranelisp-types`: resolution behavior belongs to typecheck, while
`FQTraitName` remains the stable shared vocabulary (Principles 2,
**Narrow interfaces**, and 15, **Facade types live with their behavior**).

## 3. Canonical identity consumption

The resolved carrier is the single source for every identity-bearing action
in the impl transaction.

| Consumer | Required input and behavior |
|---|---|
| Kind/shape validation | Read `resolved.decl`; compare HKT slot-1 shape and the `con_var` binder spelling against that declaration. |
| HKT pairing-head cross-check | Resolve the complete as-written pairing-head reference through the same resolver primitive into an `FQTraitName`; compare it to `resolved.fq`. Do not compare spelling. |
| Impl placement | Write the `TraitImpl` shell to `resolved.fq.module`. |
| Impl key | Mint `impl${FQTypeName}${FQTraitName}` from the resolved target and `resolved.fq`. |
| Stored metadata | Store `resolved.fq` in `ModuleEntry::TraitImpl::trait_name`. |
| Explicit-method mint | Call `mangle_trait_method(resolved.fq.name, method, fq_target)`. Never use `impl_.trait_name.to_string()`. |
| Default-method mint | Use that identical canonical mangle operation; synthesized and explicit methods must not have separate prefix rules. |
| Snapshot/rollback grain | Enumerate method symbols by the same canonical mangle operation before checking any method. |
| Re-impl enrollment/final refresh | Registration already returns the checked impl-method `Defn`s under their canonical mangled names. Consume those settled names from `ModuleCheckAccumulator.default_method_defns` (the field's legacy name includes explicit and synthesized impl methods). Never reconstruct from the original top-level form. |
| Echo/diagnostics | The source spelling may be retained only for source-facing error context. Successful identity and canonical display come from `resolved.fq`. |

The current mangle's trait component remains the canonical bare trait name;
the module identity is carried by placement and the `TraitImpl` key. Sprint
117 does not redesign the JIT-symbol ABI. What changes is the mint input:
`resolved.fq.name`, never qualified source text. This makes a bare imported
reference and an FQ reference mint the same method symbol while the impl shell
retains the full trait home.

`program/finalize.rs` must not independently build
`format!("{}.{}${}", ti.trait_name, ...)` from `TopLevel::TraitImpl`. That is a
post-settlement re-derivation from syntax and is already wrong for both the FQ
trait prefix and the FQ target suffix. The existing settled carrier is
`accumulator.default_method_defns`: `register_trait_impl` returns every checked
impl-method `Defn` under the exact symbol written to the writer module, and
`check_form_register` stores that vector in this accumulator field. Final
reannotation therefore iterates those `Defn.name` values directly. The
`TopLevel::TraitImpl` finalization arm is deleted; no new accumulator field,
`CheckResult` field, or crate-private enrollment DTO is needed. Renaming the
legacy accumulator field is outside this fix and would add churn without
changing the invariant.

This applies Principle 7, **Single source of truth**, and Principle 26,
**Record from settled state**: resolution precedes kind validation and target
settlement; symbols are minted only after both identities are final, and
later passes read that record.

## 4. Staging and transaction order

The existing impl transaction remains intact:

1. Resolve slot 1 to `ResolvedImplTrait`.
2. Validate slot-1 shape and HKT `con_var` spelling from `decl`.
3. For HKT, resolve the slot-2 pairing head and compare canonical identities.
4. Resolve and kind-check the effective target to one `FQTypeName`.
5. Check collisions and required-method completeness.
6. Mint the complete canonical method-symbol set once.
7. Stage the impl shell at the trait home and snapshot prior shell/method
   entries at the writer module.
8. Check synthesized defaults and explicit methods, passing the canonical
   trait identity into every method-check/mint seam.
9. On success, return the checked definitions, whose names are the canonical
   enrollment record already accumulated by `check_form_register`; on failure,
   restore exactly the shell and method-symbol set from step 7.
10. Finalization refreshes only the settled names in
    `accumulator.default_method_defns`.

No provisional as-written mangle is published and repaired later. The order is
important for HKT: the target rewrite extracts the constructor only after
slot-1 and pairing-head identities have settled, but it must not replace or
shadow the resolved trait carrier.

## 5. Errors

Resolution failures are located at the impl span and preserve the written
reference:

- unknown module/name or terminal non-trait: `unknown trait:
  <as-written-reference>`;
- qualified reference to a private/unreachable trait: the ordinary resolver's
  visibility error, projected to the impl span;
- HKT pairing head unresolved or resolving to another trait: the existing
  bad-pairing diagnostic, naming both written heads and the canonical slot-1
  trait;
- slot-1 shape or `con_var` mismatch: the existing declaration-driven
  diagnostic after successful resolution.

There is no fallback from failed qualified resolution to the bare name, and
no ambient module scan. An invalid qualifier must not accidentally bind an
in-scope same-named trait. Errors occur before the impl shell or method entries
are staged.

## 6. Testability and implementation sequence

The implementation is unit-testable through the existing `TestFixture` and
`check_forms` boundary. Sprint 117 W1 has already landed the failing-first
acceptance guards:

- `qualified_impl_trait_reference_resolves_canonical_home_and_dispatches`
  — conventional FQ slot 1 through Run, Link, and REPL;
- `qualified_impl_trait_reference_neg_does_not_mint_written_qualifier_into_method_name`
  — canonical method mint plus no writer-home/codegen leak;
- `qualified_hkt_impl_trait_reference_resolves_canonical_home_and_dispatches`
  — FQ HKT slot 1 and FQ pairing head converge on one identity.

Existing controls remain part of acceptance:

- `hkt_impl_pairing_head_qualified_resolves_to_slot1_trait_accepts_and_dispatches`;
- `hkt_impl_pairing_head_qualified_bad_module_rejected_no_dispatch_neg`;
- `hkt_impl_pairing_head_qualified_different_module_same_named_trait_rejected_not_registered_neg`;
- `deftrait_qualified_bare_head_rejected_binder_neg`;
- `deftrait_qualified_parenthesized_head_rejected_binder_neg`;
- `deftrait_qualified_method_name_rejected_binder_neg`;
- `trait_head_qualified_convar_rejected_binder_neg`.

`/dev(typecheck)` adds the narrower unit scenarios alongside the fix:

1. Resolver matrix:
   `{bare imported, FQ same trait, FQ same-spelled foreign trait, nonexistent
   module}` and assert the resulting canonical `FQTraitName` or located error.
2. Consumer matrix:
   `{explicit method, synthesized default, re-impl enrollment}` and assert
   one canonical method symbol and one trait-home impl key.
3. HKT matrix:
   slot 1 `{bare, FQ}` × pairing head `{bare same, FQ same, FQ different,
   missing}` while preserving verbatim `con_var` rejection.
4. Transaction negative:
   a later method failure restores the exact prior canonical grain and leaves
   no as-written-qualified method symbol.
5. Finalization:
   canonical registered symbols receive refresh; a syntax-derived
   `module/Trait.method$BareType` key is never consulted.

Then implement in this order:

1. Add the crate-private resolved carrier/helper in `traits/impl_check.rs`.
2. Replace the two slot-1 lookups with that one helper.
3. Thread `&FQTraitName` through default generation, explicit/HKT checking,
   mangling, snapshot, and rollback.
4. Replace finalization's `TopLevel::TraitImpl` syntax-derived lookup with
   direct iteration over the settled `Defn.name` values already held in
   `accumulator.default_method_defns`.
5. Run the narrow unit matrix, the QT e2e guards, then the required full
   `cargo nextest run --no-fail-fast`.

No concurrency, performance, ownership, instrumentation, or memory-layout
mechanism changes. Resolution remains bounded keyed lookup; the extra carrier
removes duplicate work rather than adding it. Observability improves because
all misses retain the written spelling while successful state exposes one
canonical identity.

## Next skills

- `/dev` — narrow to `cranelisp-typecheck`; implement the sequence and unit
  matrix after `/testing` lands QT-1/QT-2.
- `/review` — verify every identity-bearing impl consumer takes the canonical
  carrier and that declaration-binder negatives remain separate.
- `/qa` — re-evaluate the invalidated conventional and HKT coverage bands
  after the implementation and e2e evidence land.
- `/arch` — Phase-3 confirmation only; no public API or shared-interface
  change is requested by this design.
