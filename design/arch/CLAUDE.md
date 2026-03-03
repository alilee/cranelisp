# design/arch/

Architecture deliverables for the Cranelisp reimplementation. Owned and maintained by the `/arch` skill.

## Files

- `architecture.md` — Overall architecture: 7-crate DAG, single pipeline principle, CompiledModule decomposition, macro mini-pipeline resolution, audit findings addressed
- `interfaces.md` — Complete Rust type signatures for all pipeline boundary types (the design book)
- `roadmap.md` — Ring-by-ring phased progression roadmap with per-skill deliverables and acceptance criteria

## Key Decisions (Phase B)

1. **7-crate DAG**: `cranelisp-types` (data-only), `cranelisp-frontend`, `cranelisp-typecheck`, `cranelisp-backend`, `cranelisp-runtime`, `cranelisp-platform`, `cranelisp` (binary)
2. **`cranelisp-types` is data-only** — all boundary types, no logic. Every other crate depends on it.
3. **Span is a struct** — `struct Span { start: u32, end: u32 }`, not `type Span = (usize, usize)`
4. **TypeId is u32** — narrowed from `usize`, 4 billion type vars sufficient
5. **No `meta: Option<SymbolMeta>`** on `ModuleEntry::Def` — `DefKind` is the sole classification
6. **`Type::from_name()` / `type_name()`** — centralizes 9 duplicate primitive-name mappings
7. **`CompileMode` enum** — batch and REPL share `compile_unit()`, no dual pipelines
8. **`MacroExpander` trait** — dependency inversion breaks frontend->backend circular dep
9. **CompiledModule decomposed** into `SymbolTable` + `ModuleCodegenState` + `ModuleStructure` + `CacheMetadata`

## Cross-References

- `design/reimplementation.md` — Full strategy: skill definitions, ring model decision, phase sequence, risk analysis
- `src/CLAUDE.md` — Cross-cutting source conventions (error handling, code structure, naming)
- `sketch/audits/*.md` — Structural debts to avoid (59 findings: 15 HIGH, 23 MEDIUM, 21 LOW)
- `sketch/src/` — Prototype source as reference oracle

## Conventions

- Interface types define the contract between pipeline stages; changes require `/arch` review
- Any compiler skill that needs an interface change proposes it here; `/arch` evaluates impact and updates
- Dependency graph must be acyclic — Cargo enforces this at build time
- All types in `cranelisp-types` derive `Serialize` + `Deserialize` for module caching
