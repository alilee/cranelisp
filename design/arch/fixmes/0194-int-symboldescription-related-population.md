---
number: 0194
target: /dev (int)
filed_by: /dev (int)
filed_at: 2026-05-16
sprint_filed: 67
refers_to: design/arch/facades/int.md §"Introspection records" L403, repl/spec.md §3.6, src/session_v4.rs:611-622 (SymbolDescription), src/session_v4.rs:1364-1416 (describe_symbol)
status: open
---

# `SymbolDescription.related` population — defn / impl / match-arm cross-refs

## Issue

`facades/int.md` L403 prescribes a `related: Vec<FQSymbol>` field on
`SymbolDescription`, populated from defn / impl / match-arm cross-refs per
`repl/spec.md` §3.6's related-symbol comment lines (`; defn:`, `; impl:`,
`; match:`).

Sprint 67 Wave 4 added the field per Cluster C3 of the edge-settlement audit,
but population is stubbed to `Vec::new()` because the source-side cross-ref
machinery (impl→trait, type→defn, match-arm→constructor) is not yet
trivially reachable from the read-side accessor sitting on `shared`. The
universal-display format paths in REPL slash commands compute related
symbols via a separate route; the facade target is for `describe_symbol` to
return them directly so callers do not duplicate the lookup.

## Proposed resolution

Walk:

- **defn-related**: from a Constructor / Macro / Trait FQ, locate the
  defining type / defmacro / deftrait FQ in the same module table.
- **impl-related**: from a Trait FQ, scan `shared.symbol_tables[trait_module]`
  for `ModuleEntry::TraitImpl` keys per Decision 45 (`impl$FQTypeName$FQTraitName`)
  and collect the implementing types.
- **match-related**: from a Type FQ with constructors, list the constructor
  FQs (already present as `ModuleEntry::Constructor` siblings).

Wire those collectors as private helpers on the same `impl CompilerSession`
block and populate `related` at the `Some(SymbolDescription { .. })`
construction site (`src/session_v4.rs:1409`).

## Operational implication / Context

Until populated, `describe_symbol` returns an empty `related` vector even
when the universal-display format paths around `/info` etc. compute and show
related symbols. The shape compatibility is preserved (callers reading
`description.related.iter()` simply see no entries), but the facade-prescribed
behaviour is unmet.

Also covers: thread the original parse-time `ImportSpec` (alias, span,
multi-name) through to `module_imports` — currently each binding produces a
single-name `Specific([local])` spec with `span = Span::SYNTHETIC`. Source
for the original spec is in the structural-decls pipeline (`worker.rs`'s
import registration) and would need a sidecar store on `SymbolTable` per
module (or per import).
