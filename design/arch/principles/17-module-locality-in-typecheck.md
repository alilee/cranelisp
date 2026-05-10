---
number: 17
title: Module locality in typecheck
---

# Principle 17 — Module locality in typecheck

**Statement.** Typecheck never iterates the universe of modules to resolve a name, a type, an impl, or a method. Cross-module access happens only via fully-qualified references whose target module is named, or via a bounded walk of the current module's import chain. Bulk introspection (`all_type_defs`, `all_macros`, etc.) operates on the current module only; broader views are composed at the session/REPL layer, not from inside a typecheck pass.

**Rationale.** A "search every module for a short name" pattern is module-system-shaped wrong: the language's visibility rules already decide which names are reachable from the current module, and an unbounded scan disregards them. Concretely, the prototype carried 40+ direct `self.modules.X` accesses across `crates/cranelisp-typecheck/src/{checker,infer,traits,builtins}.rs` (Sprint 66 Wave 3a /dev third re-attempt audit, 2026-05-12) — short-name lookups iterating every loaded module, `find_impl_for_type` scanning the whole module set, `all_methods_of_type` iterating across modules, mutating writes landing in foreign modules. Each of these violates the visibility rule the spec already states (`spec/05-definitions.md §5.11`, `spec/08-modules.md §8.3`); each blurs the cluster-atomic surface (Decision 44) by introducing reads and writes that aren't governed by the orchestrator's `ClusterContext`. The remediation is to encode the visibility rule in the access pattern: a name is reachable from the current module iff it is local, imported, or imported transitively — and the typechecker walks that bounded set rather than the universe.

**Consequence.** Typecheck has four legitimate access-pattern shapes; every cross-module lookup must fit one of them:

1. **Unqualified short-name lookup** — `view.lookup(name)` against the current module's view (staging ∪ live, per Decision 44). If the entry is `ModuleEntry::Import { source: FQSymbol }`, follow the FQ to its home module via `symbol_tables.get(&source.module)` and read the resolved entry. Never iterate `self.modules`.
2. **Qualified (FQ) lookup** — `symbol_tables.get(&fq.module).get(&fq.symbol)`. Direct, single module; the path is named.
3. **Impl resolution** — given a `(Trait, Type)` pair, walk `current_module.imports.iter()` (and, per `/spec` resolution of FIXME 0169, the transitive import closure for impl visibility) and probe each named module's table for the synthetic `impl$FQTypeName$FQTraitName` key. Bounded by the import set, not the universe.
4. **Bulk introspection** — current-module-only scan. Accumulating "everything reachable from the current module" is the orchestrator's job (session / REPL layer composes per-module slices), not the inside of `check_form_signatures` / `check_form_body`.

Mutating writes are governed by Decision 44: every write goes through `ctx.current_symbol_table_mut()` (i.e., into staging or live for the current module). A typecheck pass MUST NOT mutate a foreign module's table. TraitImpl entries are written to the impl's *writer's module* (Decision 0045), discovered by importers via the import-chain walk above; impl placement is therefore consistent with this principle by construction.

This principle is the structural prerequisite for Decision 44's cluster-atomic shape. The `ClusterContext` accessor surgery only buys atomicity if every read and write actually flows through it; an orphaned `self.modules.X` pierce does the wrong thing in cluster mode (it would read live during a cluster, ignoring staging) and silently weakens the live-table invariant. Compliance with this principle and compliance with Decision 44 are the same property viewed from two angles.
