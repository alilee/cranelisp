# Staging-aware value layout: exact API proposal

Status: implemented, independently reviewed and QA-passed, 2026-09-07. The user
approved the exact API ("ok") and confirmed its generated one-line addition
("yes"); both stages of [the repository API gate](../../CLAUDE.md#roles) are
complete. Owner: `arch`. The current contract lives in `heap.rs` rustdoc,
`interfaces.md` and `bounded-contexts.md`. Retain this packet at its existing path
until sprint and QA references are reconciled together; archive only after that
coordinated handoff.

The shared layout entry point accepts a binding lookup; the existing table API
is its wrapper. Typecheck asks the same layout algorithm
about the declarations it is checking, including staging. Backend continues to
ask that algorithm about the table supplied for code generation.

## Verified problem and intended result

The permanent reproduction
`src/worker/tests.rs::cache_preloaded_sum_projection_recheck_preserves_ownership`
checks identical source against fresh imports, restored metadata, and restored
metadata with the authored functions removed. The recorded run in
[the active sprint](../../sprints/SPRINT.md) finds Borrowed in the first case and
Copy in both restored cases, with equal schemes; the difference precedes the ABI
guard. No test was rerun for this proposal.

Pre-fix source inspection confirmed the cause at this seam:
`crates/cranelisp-typecheck/src/ownership/fixpoint.rs::compute_cluster_with_cap`
constructed `CopyClassifier` using only `env.modules()`, and
`UniqClusterEnv::layout_eligible` used the same published-only input.
`crates/cranelisp-typecheck/src/checker.rs::probe_module_entry_owned` already
provided the required staging-first point lookup. At that point, the shared
layout API accepted only `Option<&SymbolTables<C, L>>`. Both consumers now call
the private `checked_value_layout` adapter over the staging-first probe.

For `(deftype Customer (Addr [:Int a]))`, the shared rule already admits the
single constructor with its single scalar field. Reading the staged declaration
therefore yields Copy on the fresh path too. Acceptance is equal correct
ownership across fresh/cold/warm compilation, including the permanent cache
reproduction and example 35; the completed integration evidence is recorded below.

## Exact public delta

Add in `crates/cranelisp-types/src/heap.rs`:

```rust
pub fn value_layout_with_lookup<C, F>(
    ty: &ConcreteType,
    lookup: &F,
) -> Option<ValueLayout>
where
    C: CodeStore,
    F: Fn(&ModuleFullPath, &Symbol) -> Option<Binding<C>>;
```

Add only `value_layout_with_lookup` to the existing crate-root `pub use heap`
list in `crates/cranelisp-types/src/lib.rs`. The module stays private to the
crate. `F` is an ordinary sized generic closure, borrowed for this call; no
`Send`, `Sync`, `Clone`, `'static`, `FnMut`, or `LinkerStore` bound is added to
it. `C: CodeStore` is required by the existing `Binding<C>` carrier. There is
no new trait, DTO, error type, public helper or typecheck re-export.

Retain these signatures and bounds exactly:

```rust
pub fn value_layout<C, L>(
    ty: &ConcreteType,
    type_defs: Option<&SymbolTables<C, L>>,
) -> Option<ValueLayout>
where C: CodeStore, L: LinkerStore;

pub fn type_ctor_names<C, L>(
    table: &SymbolTable<C, L>,
    fqtn: &FQTypeName,
) -> Option<Vec<Symbol>>
where C: CodeStore, L: LinkerStore;
```

Forecast for `crates/cranelisp-types/public-api.txt`: exactly one added line,
zero removed or changed lines relative to the baseline at implementation entry:

```text
pub fn cranelisp_types::value_layout_with_lookup<C, F>(&cranelisp_types::ConcreteType, &F) -> core::option::Option<cranelisp_types::ValueLayout> where C: cranelisp_types::CodeStore, F: core::ops::function::Fn(&cranelisp_types::ModuleFullPath, &cranelisp_types::Symbol) -> core::option::Option<cranelisp_types::Binding<C>>
```

The generated types baseline matches that forecast exactly: one added line,
zero removals or changes (2026-09-07). Other crate baselines were not edited by
this implementation; final canonical comparisons pass across all seven crates.
The user confirmed this exact one-line addition ("yes", 2026-09-07).

## Semantics, ownership and producer/consumer changes

`lookup(module, key)` returns an owned clone of the binding at that exact module
and storage key, or `None` when absent. It performs no language name resolution,
alias following, prelude fallback, enumeration or publication. The caller supplies
a coherent declaration view for the duration of the calculation. The callback
does not escape; the result borrows nothing. Each probe releases its table or
staging borrow before returning, and the layout walk drops owned metadata after
extracting the concrete fields and before recursively looking up another ADT.
No DashMap guard or RefCell borrow crosses a recursive lookup.

The algorithm remains in `heap.rs`: scalar base cases, Vec exclusion,
single-constructor and exactly-one-field restriction, already-concrete field
projection, path-scoped cycle detection, and the existing word limit. Missing
or unsuitable bindings still return `None`. No per-instantiation substitution
is introduced. The distinct substituting `ctor_field_types_at` API is unchanged.

The defined-type versus product-constructor-facet switch and canonical
`member_key(Type, Ctor)`-exists-else-bare rule remain one private projection
shared by the new walk and `type_ctor_names`. Factor that projection over a
borrowed binding and a key-existence callback, so the existing `type_ctor_names`
table wrapper can retain borrowed reads. The layout recursion and concrete-field
projection each likewise have one implementation. Merely copying the existing
`type_ctor_names` match into the new walk would violate this proposal.

| Owner/function | Proposed operation |
|---|---|
| types: `value_layout_with_lookup` | Own the single layout walk over the supplied lookup. |
| types: `value_layout` | Adapt `Some(tables)` to exact keyed lookup returning `.cloned()`; adapt `None` to a lookup that always misses. Delegate to the new function. |
| types: `type_ctor_names` | Retain its API; delegate constructor projection to the shared private implementation. |
| typecheck: `compute_cluster_with_cap` | Supply the existing `probe_module_entry_owned` lookup to the shared function for `CopyClassifier`. |
| typecheck: `UniqClusterEnv::layout_eligible` | Use the same private layout adapter, preserving its String/ADT restriction and `.is_none()` polarity. |
| backend: `HeapCategory::classify` | Continue consuming `value_layout` with its existing supplied tables; no new direct consumer edge. |

The new inter-crate consumer edge is typecheck →
`cranelisp_types::value_layout_with_lookup`; its two uses replace the two
published-table layout calls. Typecheck's existing scalar-only test helper can
continue using `value_layout(_, None)`. The private typecheck adapter supplies:

```rust
cranelisp_types::value_layout_with_lookup(ty, &|module, key| {
    env.probe_module_entry_owned(module, key.as_ref())
})
```

For the staging module, a present staged binding wins even when its shape is
ineligible; only an absent staged key falls through to published state. Other
modules use published state. This is exactly the existing probe's contract,
including nested field types in other modules. The shared function does not
know which storage implementation provides it.

## Compatibility and cost

The Rust API is additive. There is no crate dependency, technology, deployment,
platform `ABI_VERSION`, FFI layout, GOT/slot, lifecycle, serialization shape or
ownership-summary meaning change. The existing live-redefinition ABI comparison
and refusal remain intact. Correcting which declarations feed inference can
change newly inferred summaries; it does not license rebinding an incompatible
live slot or disregarding a persisted summary mismatch.

No cache schema bump is proposed: layout rules and persisted field meanings
are unchanged. The existing build-ID stale-cache check remains the compiler
revision boundary (`crates/cranelisp-backend/src/cache/mod.rs::BUILD_ID`). Caches
produced by the defective compiler may contain different inferred summaries;
this proposal does not promise their cross-revision reuse or migrate them. A
dirty rebuild at the same Git revision can retain the same build ID. Verification
must exercise a real cold-to-warm cycle of the repaired compiler; it must not
hide the original defect by disabling caching or weakening the ABI guard.

The cost is transient clones of queried bindings in the layout walk, including
their existing payloads, plus closure monomorphization. Only queried declarations
are cloned, and `CodeStore::clone` retains any existing owner until that clone
drops; the calculation never creates executable state. This reuses typecheck's
established guard-release discipline. No full table/world clone, registry,
overlay materialization or lifecycle/slot construction is needed.

A new public view trait adds an implementation contract without another required
consumer. Replacing the existing signature unnecessarily breaks backend and
scalar-only callers. Exporting constructor or field projection helpers separately
would make typecheck assemble layout policy across the boundary. The one lookup
entry point keeps the same boundary one would choose inside a single crate:
the caller supplies declaration access, and shared layout code owns the answer.

## Evidence and handoff

Types evidence is complete: the new API consumers first failed to compile with
E0425; focused layout tests pass 27/27 and the package passes 279/279. A temporary
inversion of canonical-key preference fails the named constructor-key test; the
fault was removed before the final package run. Existing explicit layout
expectations now also compare the lookup entry point with the table wrapper.
The self-cycle control now uses one field so it reaches the recursion guard.
All-target check and scoped formatting pass. Clippy reports seven warnings in
untouched files and none in the changed files; its strict warning-denial run
therefore fails on that existing set. Typecheck's implemented shared adapter
feeds both Copy and uniqueness consumers. The owner reports 860/860 typecheck
tests and 758/758 root tests passing, including the original cache-reconstruction
probe and three live-publication controls. The probe passed unchanged before its
diagnostic prints became permanent assertions. Independent types and typecheck
reviews found no issues. Integration evidence passes: uncached, cold and warm
cache-reproduction runs return 40, with warm metadata preload positively observed;
example 35 is unchanged and returns 100 cold and warm. A warm-only no-cache fault
plant retains output 40 but fails the preload observation, proving the witness
detects bypassed restoration. The observation uses an opt-in trace event after
successful entry-metadata installation. Final independent integration review is
clear and QA's final adequacy verdict is PASS.

No implementation or approval remains for this change. Reconcile references
before archiving this packet.
The current types contract lives in source rustdoc, `interfaces.md` and BC §7;
their R5 eligibility statements retain the mandatory exactly-one-field condition.
