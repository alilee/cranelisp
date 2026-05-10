---
number: 0045
title: TraitImpl storage placement — writer's module is canonical; importers discover via import-chain walk
status: pre-implementation
filed: sprint 66 (Phase 3 FIXME 0168 resolution)
canonical_location: design/arch/facades/types.md §"`ModuleEntry::TraitImpl`"; design/arch/facades/typecheck.md §"Bounded-context invariants" item 10; crates/cranelisp-types/src/module.rs `ModuleEntry::TraitImpl` doc-comment
amends: []
amended_by: []
retracts: []
reframes: []
filed_by_fixme: 0168
---

# 0045 — TraitImpl storage placement: writer's module canonical

## Statement

When `(impl Trait Type method-defns…)` is parsed in module M, the resulting `ModuleEntry::TraitImpl { trait_name: FQTraitName, impl_type: FQTypeName, methods }` entry is written to **M's symbol table** under the synthetic key `impl$FQTypeName$FQTraitName`. The trait's defining module and the type's defining module are NOT mutated by the impl write; only M is.

Importers discover the impl by walking M's symbol table when M is in the importer's import closure (per Principle 17 — Module locality in typecheck — and per `/spec`'s resolution of FIXME 0169 on the transitive-import-visibility rule). Impl resolution at a typecheck call site searches the current module's transitive import closure for an entry under `impl$FQTypeName$FQTraitName`; the first match wins.

The associated method `Defn` entries (the impl's bodies) are also written to M as ordinary `ModuleEntry::Def` entries with mangled names (e.g., `Display.show$Option$Int`); the `TraitImpl` entry's `methods: Vec<Symbol>` lists their local names so importers can dereference back to the bodies in M.

## Rationale

Four placement options were considered:

- **(a) Writer's module M.** Local update only. *Selected.*
- **(b) Trait's defining module.** Non-local mutation; cluster atomicity needs to stage every trait-home module that an in-flight cluster's impls might touch.
- **(c) Type's defining module.** Same shape as (b).
- **(d) Global impl-registry.** Parallel store outside per-module symbol tables.

Option (a) is canonical because:

1. **Principle 1 (Decoupling).** Typecheck never reaches across module boundaries to write. Every write goes through `ctx.current_symbol_table_mut()` (Decision 44), which targets the writer's module by construction.

2. **Principle 7 (Single source of truth).** Options (b) and (c) require either non-local mutation (multiple modules' tables mutated by one cluster) or a separate "where to put the impl" lookup that depends on parsing-time context. Option (d) is a parallel store outside `SymbolTable`, the canonical store. Option (a) keeps the canonical store the single source — every entry lives in exactly one module's table, the one whose source produced it.

3. **Principle 17 (Module locality in typecheck).** Importers locate impls by walking the current module's import closure (a bounded set), not by scanning every module for matching `(Trait, Type)` pairs. The visibility rule the spec states (`spec/05-definitions.md §5.11` — "wherever both trait and type are in scope") is encoded by the import-chain walk. Discovery is `O(|imports|)`, not `O(|modules|)`.

4. **Cluster atomicity (Decision 44).** With placement (a), staging in cluster mode is M's `SymbolTable` — the same one Pass 1 / Pass 2 already mutate via `current_symbol_table_mut()`. An impl write is structurally identical to a defn write: stage on Pass 1 or Pass 2, drain on cluster commit, drop on cluster failure. No cross-module staging is needed.

5. **Wave 0 facade shape (`facades/types.md` and `crates/cranelisp-types/src/module.rs:531`).** `ModuleEntry::TraitImpl` already keys both names FQ — `trait_name: FQTraitName, impl_type: FQTypeName`. The keying is consistent with placement (a) (the entry self-describes both names; readers don't need to know which module declared the trait or the type to interpret it). Pre-S66 source comments asserted "Always public (spec §5.11: impls are visible wherever both trait and type are in scope)" — this Decision pins how that visibility is realized: by storing in M and discovering via import-chain walk.

## Consequences

### Spec-side coupling

The visibility rule is named in `spec/05-definitions.md §5.11` ("wherever both trait and type are in scope"). The traversal mechanism that realizes the rule — direct vs transitive vs re-export-aware — is `/spec`'s arbitration (FIXME 0169). The recommended reading is **Reading 2 (transitive)**: an impl in module L is visible to N when L is in N's transitive import closure, with re-exports of a trait or type implicitly carrying the trait's / type's impls. This Decision is compatible with whichever reading `/spec` lands on; the writer's-module placement does not depend on the choice. If `/spec` selects a reading that requires re-export gestures for impls to propagate, the import-chain walk simply consults each transitively-imported module's `exports` to determine reachability; the storage location does not change.

### Triage of pre-S66 cross-module writes

The Sprint 66 Wave 3a audit (2026-05-12) identified ~6 direct mutating writes in `crates/cranelisp-typecheck/src/builtins.rs` and `crates/cranelisp-typecheck/src/checker.rs` that appear to land impl entries in foreign modules — patterns (b)/(c). These are vestigial from before the FQ migration and are inconsistent with this Decision. They are flagged as **Wave 3a-α refactor targets** (see Decision 0046): each cross-module impl write becomes a write to the current module (the writer's module M, per `ctx.current_symbol_table_mut()`), with discovery rewritten on the read side as an import-chain walk. No spec change is needed; the source as it stands is structurally inconsistent with both Principle 17 and this Decision, and was the proximate blocker on Wave 3a's third re-attempt.

### Cluster-atomic semantics for impls

An impl `(impl Trait Type ...)` is a single `ParsedEntry::TraitImpl` produced by `build_form` and processed by both passes of Decision 44's two-pass typecheck. Pass 1 stages a signature-only `TraitImpl` shell into M's staging table (via `current_symbol_table_mut()`); Pass 2 stages the body-checked impl with method `Def` entries (mangled names) into the same staging table. Cluster commit drains all of M's staging into M's live table atomically; cluster failure drops staging. No other module's table is touched.

### Discovery cost and caching

A typecheck call site that needs to resolve a trait method walks the current module's import closure (bounded; the closure is finite and known at typecheck time) to find a matching `impl$FQTypeName$FQTraitName` entry. For deeply-imported workloads, an option-(ii) per-module "visible impls" index could be derived at module-load time and cached on `SymbolTable` (e.g., `imports_resolved_impls: HashMap<(FQTraitName, FQTypeName), ModuleFullPath>`). This is an implementation optimization, not part of the architectural contract; the contract is the placement and the discovery shape. If a workload demands the index, it is added to `SymbolTable` (one cell per import-graph mutation) without changing this Decision.

## Cross-references

- `design/arch/facades/types.md` §`ModuleEntry::TraitImpl` — placement and discovery doc-comment update; Wave 3a's refactor lands the read-side import-chain walk.
- `design/arch/facades/typecheck.md` §"Bounded-context invariants" item 10 — module-locality invariant; impl resolution access pattern.
- `crates/cranelisp-types/src/module.rs` `ModuleEntry::TraitImpl` — source-level doc-comment makes placement explicit.
- `design/arch/decisions/0044-cluster-atomic-typecheck-orchestrator-staging.md` §"Sequencing" — Wave 3a-α/β split (locality refactor before triad re-fire).
- `design/arch/decisions/0046-wave3a-locality-refactor-precedes-triad.md` — the α/β split as its own Decision.
- `design/arch/principles/17-module-locality-in-typecheck.md` — the access-pattern principle that this placement realises.
- `design/arch/fixmes/0169-spec-impl-visibility-import-chain-traversal.md` — `/spec` twin (transitive vs direct vs re-export-aware traversal).
- `spec/05-definitions.md §5.11`, `spec/07-traits.md`, `spec/08-modules.md` — visibility rule grounding.

## Sequencing

This Decision precedes Wave 3a-α (locality refactor) — see Decision 0046. The placement is fixed; Wave 3a-α retargets the existing direct-mutating-write sites to the writer's-module table and rewrites the cross-module read sites as import-chain walks.
