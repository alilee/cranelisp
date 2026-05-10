---
number: 0045
title: TraitImpl storage placement — trait's defining module is canonical; importers discover via per-symbol chain-follow
status: pre-implementation
filed: sprint 66 (Phase 3 FIXME 0168 resolution; superseded by Wave 3a-α post-mortem 2026-05-10)
canonical_location: design/arch/facades/types.md §"`ModuleEntry::TraitImpl`"; design/arch/facades/typecheck.md §"Bounded-context invariants" item 10; crates/cranelisp-types/src/module.rs `ModuleEntry::TraitImpl` doc-comment
amends: []
amended_by: []
retracts: []
reframes: []
filed_by_fixme: 0168
---

# 0045 — TraitImpl storage placement: trait's defining module canonical; chain-follow discovery

## Statement

When `(impl Trait Type method-defns…)` is parsed in module M, the resulting `ModuleEntry::TraitImpl { trait_name: FQTraitName, impl_type: FQTypeName, methods }` entry is written to the **trait's defining module** — the module whose symbol table holds the canonical `ModuleEntry::Trait` for `Trait`. The entry is keyed by the synthetic name `impl$FQTypeName$FQTraitName`. Neither the writer's module M nor the type's defining module are mutated by the impl write; only the trait's home is.

Importers discover the impl by **point-to-point chain-follow** on the trait member's per-symbol binding. From the current module N's view, looking up the trait `Display` yields either:

- `ModuleEntry::Trait { … }` directly — N IS the trait's home; probe N's symbol table for `impl$FQTypeName$FQTraitName`.
- `ModuleEntry::Import { source: FQSymbol, … }` or `ModuleEntry::Reexport { source: FQSymbol, … }` — follow `source.module` one edge at a time, repeating the lookup, until a `ModuleEntry::Trait` is reached. That terminating module IS the trait's home; probe its symbol table for `impl$FQTypeName$FQTraitName`.

The walk is per-symbol, per-edge, terminating; no graph traversal, no cycle detection, no closure walk over the import set. From the trait's home, an impl is either present (the impl is reachable iff the trait is reachable, by spec §5.11.1) or absent.

The associated method `Defn` entries (the impl's bodies) live as ordinary `ModuleEntry::Def` entries with mangled names (e.g., `Display.show$Option$Int`); the `TraitImpl` entry's `methods: Vec<Symbol>` lists those names. They live in the **same module** that holds the `TraitImpl` entry — i.e., the trait's defining module — so importers that have already chain-followed to the trait's home find both the `TraitImpl` shell and its method bodies in one table.

## Rationale

Four placement options were considered:

- **(a) Writer's module M.** Local update only; importers enumerate "all writers reachable from N" by graph closure walk over the import set with cycle detection.
- **(b) Trait's defining module.** Per-symbol chain-follow on the trait's import binding back to its home module; probe that one module for the impl. *Selected.*
- **(c) Type's defining module.** Same shape as (b) but follow the type's import binding instead of the trait's.
- **(d) Global impl-registry.** Parallel store outside per-module symbol tables; universe scan to discover.

Option (b) is canonical because:

1. **Navigation primitive is point-to-point chain-follow.** Lookup from the current module to the trait's home is a single recursive walk along per-symbol `Import`/`Reexport` bindings — one edge at a time, terminating when a `Trait` entry is reached. No graph traversal; no cycle detection; no enumerable closure of "all reachable writers"; no per-call-site bookkeeping. The user's verbatim arbitration (Sprint 66 Wave 3a-α post-mortem, 2026-05-10):

   > "to find the trait's module, you don't search imports. you look for the symbol for the trait member in the symbol table and follow it back through importing modules recursively, until you find the defining module. IFF the trait is defined for the type, then it will be there."

   The lookup primitive is the chain-follow, not the import set.

2. **Principle 17 (Module locality in typecheck).** Closure walks over the import graph are the wrong shape — they require cycle detection, visited-sets, and per-call-site enumeration of an unbounded-shape edge set. Per-symbol chain-follow is exactly the access pattern Principle 17 names as legitimate (shape 1 — "follow Import bindings to FQ home"). Pattern (b) realizes the spec's visibility rule (`spec/05-definitions.md §5.11.1`, `spec/07-traits.md §7.11.1`) — an impl is visible from N iff `Trait` and `Type` are reachable from N — by exploiting the fact that *if `Trait` is reachable from N, the chain-follow terminates at its home*. Reachability of the trait IS reachability of its impls, encoded structurally.

3. **Principle 7 (Single source of truth).** Every impl entry lives in exactly one module's table — the trait's home. There is no "all modules that ever wrote an impl for this trait" set to maintain or query; the trait's home is THE place to look.

4. **Cluster atomicity (Decision 44).** Cluster-atomic semantics still hold: a `(impl Trait Type ...)` form's writes go through the orchestrator's accessor `ctx.current_symbol_table_mut()` — but `current` here is the trait's home (which IS the current module when the impl is written in the trait's home file, and is otherwise resolved by the writer chain-following the trait reference at write time, identically to the read side). The orchestrator stages the write into the appropriate module's staging table; cluster commit drains it.

   *Note*: the "current module" wording in Decision 44 is preserved by re-interpreting current-module-for-this-write as the chain-followed home, not the file the impl source lives in. The orchestrator-staging shape is unchanged; only the target table is named via the chain-follow rather than via the writer's file.

5. **Spec preservation.** The visible *set* of impls is identical under patterns (a), (b), and (c) — the spec's reachability rule (§5.11.1, §7.11.1, §8.4.6, §8.6.7) is invariant under storage choice. What differs is the lookup mechanism. Pattern (b) reduces the mechanism to its minimal shape.

## Rejected alternatives

- **(a) Writer's module.** Required `transitive_import_closure(N) → Set<ModuleFullPath>` enumeration: a graph traversal over `imports` + per-symbol `ModuleEntry::Import` / `Reexport` entries with cycle detection, called once per impl-resolution query. Wave 3a-α's first attempt (commit `ab068e2`) embodied pattern (a) and introduced exactly such a `transitive_import_closure` function; that commit is rolled back and redone under pattern (b). Pattern (a)'s lookup mechanism is more elaborate than the spec's intent: the spec says "wherever both trait and type are in scope" — scope is per-name, not per-graph. Pattern (b) preserves the per-name framing.

- **(c) Type's defining module.** Symmetrical to (b) but follows the type's import binding instead of the trait's. Rejected because the trait's home is the natural lookup primitive: at a typecheck call site `(method-name x …)` where `method-name : Trait.method`, the resolver already has the trait identity in hand (from method resolution); the type identity may not yet be a single concrete name (it can be a type variable awaiting unification, or an ADT applied to type variables). Following the trait's chain is unconditional; following the type's would require waiting for type unification to finalize. Pattern (b) fits the inference flow.

- **(d) Global impl-registry.** Universe scan to enumerate; parallel store outside `SymbolTable`. Violates Principle 7 (canonical store is per-module symbol tables) and Principle 17 (universe scan is forbidden).

## Consequences

### Spec-side coupling

The visibility rule is named in `spec/05-definitions.md §5.11.1`, `spec/07-traits.md §7.11.1`, `spec/08-modules.md §8.4.6`, `§8.6.7`. The traversal mechanism is `/spec`'s arbitration (FIXME 0169 — Reading 2 transitive). Pattern (b) is compatible with whichever reading `/spec` lands on; the chain-follow terminates at the trait's home regardless of how the trait reaches N (direct, transitive, or re-export-aware).

### Triage of pre-S66 cross-module writes

The Sprint 66 Wave 3a audit (2026-05-12) identified ~6 direct mutating writes in `crates/cranelisp-typecheck/src/builtins.rs` and `crates/cranelisp-typecheck/src/checker.rs` that landed impl entries in modules other than the writer's module — which, under the original Decision 45 (pattern (a)), were vestigial. Under the present Decision (pattern (b)), the writes' *target* selection becomes the question: each cross-module impl write should land in the trait's home, not the writer's home, not a foreign module chosen by hand.

Wave 3a-α's original pass (commit `ab068e2`, 2026-05-13) retargeted these sites to the writer's module under pattern (a). That commit needs **rollback + redo under pattern (b)** — retarget to the trait's home, and replace the introduced `transitive_import_closure` function with a chain-follow primitive. The redo is implementation work tracked separately (Wave 3a-α second pass).

### Synthetic modules

`primitives` and `macros` are compiler-seeded synthetic modules with no source forms; their `imports` and `exports` are empty `Vec`s by invariant (Principle 17). When a builtin trait `Display` is defined in (say) `primitives`, the impl `(impl Display Int …)` registered programmatically in `builtins.rs` writes to `primitives` directly — `primitives` IS the trait's home, so the chain is length-zero, the write target is unambiguous, and no defensive synthetic glob import is required. α's first-pass `(import [macros [*]])` injection into `primitives.imports` (a workaround for pattern (a) + closure walk over an empty import set) is removed in the redo.

### Cluster-atomic semantics for impls

A `(impl Trait Type ...)` form is a single `ParsedEntry::TraitImpl` produced by `build_form`. Pass 1 stages a signature-only `TraitImpl` shell into the trait's home staging table (resolved by chain-follow at staging time, via `ctx.current_symbol_table_mut()` after the orchestrator selects the target table); Pass 2 stages the body-checked impl with method `Def` entries into the same staging table. Cluster commit drains the trait's home's staging into its live table atomically; cluster failure drops staging. Other modules' tables are never touched.

### Discovery cost and caching

A typecheck call site that resolves a trait method does one chain-follow on the trait reference (per-edge cost = `O(1)` lookup; chain depth = number of intermediate import/reexport edges, bounded by the user's import topology, typically ≤ 3); at the trait's home it does one synthetic-key lookup `impl$FQTypeName$FQTraitName` (`O(1)`). Total cost per query is `O(chain depth)`, not `O(|imports|)` or `O(|modules|)`. No closure-walk cache is needed.

## Cross-references

- `design/arch/facades/types.md` §`ModuleEntry::TraitImpl` — placement and discovery doc-comment update; redo lands the read-side chain-follow.
- `design/arch/facades/typecheck.md` §"Bounded-context invariants" item 10 — module-locality invariant; impl resolution access pattern updated to chain-follow.
- `crates/cranelisp-types/src/module.rs` `ModuleEntry::TraitImpl` — source-level doc-comment makes placement explicit (updated by `/typecheck` redo).
- `design/arch/decisions/0044-cluster-atomic-typecheck-orchestrator-staging.md` §"Sequencing" — Wave 3a-α/β split (locality refactor before triad re-fire).
- `design/arch/decisions/0046-wave3a-locality-refactor-precedes-triad.md` — the α/β split as its own Decision; α's redo retargets to trait's home and replaces closure walk with chain-follow.
- `design/arch/principles/17-module-locality-in-typecheck.md` — the access-pattern principle; chain-follow as the canonical navigation primitive.
- `design/arch/fixmes/0169-spec-impl-visibility-import-chain-traversal.md` — `/spec` twin (transitive vs direct vs re-export-aware traversal).
- `spec/05-definitions.md §5.11.1`, `spec/07-traits.md §7.11.1`, `spec/08-modules.md §8.4.6`, `§8.6.7` — visibility rule grounding.

## Sequencing

This Decision precedes Wave 3a-α's second pass (locality refactor redo) — see Decision 0046. The placement is fixed; the redo retargets the existing direct-mutating-write sites to the trait's home and replaces the read-side closure walk with a per-symbol chain-follow primitive.
