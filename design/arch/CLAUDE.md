# design/arch/

Architecture deliverables for the Cranelisp reimplementation. Owned by `/arch`.

Per `sprints/METHOD_PROPOSED.md` §14.1, this `CLAUDE.md` carries domain-local content only — local conventions, the Decisions index, and pointers to canonical documents. Methodology rules live in `METHOD_PROPOSED.md`; architectural principles live in `principles.md`; skill workflows live in `.claude/commands/arch.md`.

## Canonical documents (the target documentation set)

| File | Purpose |
|---|---|
| `overview.md` | Bridge document — the newcomer entry point. How the language is realized through the surfaces, tested by `/qa`'s integration suite, embodied in the crates. |
| `principles.md` | Architectural principles — index. Each Principle is one file at `principles/NN-{slug}.md`. Auto-imported by `.claude/commands/arch.md`. |
| `principles/` | Architectural Principles register; one file per Principle; index in `principles.md`. |
| `bounded-contexts.md` | Per-surface bounded-context full statements (Frontend, Typecheck, Backend, Runtime, Platform, Binary/int, plus types crate). |
| `facades/{crate}.md` | Per-surface facade specs — as-designed public surface. One file per surface. |
| `interfaces.md` | Narrative companion to `crates/cranelisp-types/`. |
| `decisions/` | Decisions register; one file per Decision; index in this CLAUDE.md (see "## Decisions" below). |
| `fixmes/` | FIXMEs register; one file per FIXME (`design/arch/fixmes/NNNN-name.md`). |
| `sequences/` | Current target sequence diagrams (`.mmd` + rendered `.svg`). |

## Sorting buckets

| Directory | Purpose |
|---|---|
| `legacy/` | Documents not part of the approved configuration but kept for reference. `/arch` and the per-crate `/design` skills pull back content (or re-author from it) when needed; otherwise files here are triaged into top-level (if they prove still load-bearing) or down to `archive/` (if confirmed superseded). Not a permanent home. |
| `archive/` | Frozen historical content — superseded by canonical work, kept for context only. See "## Archive" below. |

## Archive (`archive/`)

Historical pipeline designs (v1, v2, v3) and superseded migration artefacts. Reference only — not the target architecture.

- `archive/v1/` — v1 architecture, interfaces, pipeline orchestration, sketch audit
- `archive/pipeline-v2.md` — v2 pipeline design (stages, unified multi-pass check)
- `archive/pipeline-v3.md`, `archive/pipeline-v3-roadmap.md` — v3 migration (complete)
- `archive/pipeline-convergence-review.md` — Sprint 26 dual-pipeline defect analysis (origin of principles 11–13)
- `archive/pipeline-convergence-playbook.md` — convergence execution plan
- `archive/session-restructure.md` — session restructure target data model (phases A–F complete)
- `archive/per-module-got-cleanup.md` — GOT unification design
- `archive/sprint-40a-design.md` — cancelled Sprint 40a design
- `archive/codegen-convergence.md` — Sprint 54 Wave 3a; superseded by Decisions 22, 23, 25 (S63 archive)
- `archive/ast-annotation-examples.md` — Sprint 55 Step 1b annotation spec (S63 archive)

## Decisions

Each Decision is one file at `decisions/NNNN-{slug}.md`. Index:

The active register holds Decisions whose outcome is NOT yet fully embodied in the architecture (facade + BC + sequence diagrams + Principles). Once a Decision's commitment lands fully into the architecture, the Decision becomes vestigial and moves to `legacy/decisions/` (or deletes if also retracted/superseded). The principle: re-derivation from the canonical set + Principles should be sufficient for fully-landed work; explicit Decisions persist only for environmental constraints, pre-implementation commitments, and forward handoffs.

- [0008](decisions/0008-macroexpander-trait.md) — `MacroExpander` trait (retracted; cited from FIXME 0098 + frontend design)
- [0010](decisions/0010-base-pointer-abi.md) — Base-pointer ABI (environmental — captures rejected interior-pointer alternative)
- [0011](decisions/0011-embedded-drop-glue-ptr-in-closures.md) — Embedded drop_glue_ptr in closures (environmental — captures rejected side-table alternative + cross-module closure constraint)
- [0016](decisions/0016-jit-mangling-trait-method-type.md) — JIT mangling: `Trait.method$Type` (operative)
- [0018](decisions/0018-replcheckresult-gains-ring-2-fields.md) — `ReplCheckResult` gains Ring 2 fields (operative)
- [0019](decisions/0019-constraint-propagation-in-generalize.md) — Constraint propagation in `generalize` (operative)
- [0027](decisions/0027-g8-lands-before-g9.md) — G8 lands before G9 (environmental — borrow-checker sequencing rationale)
- [0030](decisions/0030-form-by-form-scheduler-mutual-imports.md) — Form-by-form scheduler deadlocks on mutual imports (environmental — coordination constraint future readers will hit)
- [0031](decisions/0031-one-jitmodule-per-compile-batch.md) — One `JITModule` per compile batch; `Arc<Jit>` on `ModuleEntry::Def.code`; custom `Drop` calls `unsafe free_memory()` (environmental — Cranelift `Memory::drop` evidence; amended Sprint 64 per Decision 41)
- [0035](decisions/0035-code-enum-integration-layer.md) — `Code` enum location (operative; amended Sprint 64 per Decision 41 — Code now in `cranelisp-backend`)
- [0040](decisions/0040-runtime-trace-io-trace-relocate-to-int.md) — `trace.rs` and `io_trace.rs` relocate to int; runtime keeps `IoObserver` callback contract; BC §4 unchanged (pre-implementation; tracked by FIXME 0098)
- [0041](decisions/0041-compile-to-module-per-symbol-jit-direct-writes.md) — `compile_to_module` per-symbol JIT cardinality; `Code` moves to `cranelisp-backend`; backend writes shared state directly; `Result<(), CompilationError>` (pre-implementation; amends 31, 35)
- [0042](decisions/0042-platform-error-adopts-error-location.md) — `PlatformError` is a `cranelisp-types`-hosted enum with `ErrorLocation` carriers per variant; surfaces via `CranelispError::Platform` (pre-implementation)

Legacy Decisions (outcome fully embodied in architecture; preserved in `legacy/decisions/` for narrative continuity) — `0001`–`0006`, `0009`, `0012`–`0013`, `0021`–`0026`, `0029`, `0032`–`0034`, `0036`–`0039`. Retracted/superseded Decisions deleted (rely on git for history): `0007`, `0014`, `0015`, `0017`, `0020`, `0028`.

## Cross-References

- `principles.md` — architectural principles (index; per-Principle bodies in `principles/NN-*.md`; auto-imported by `.claude/commands/arch.md`)
- `bounded-contexts.md` — per-surface full statements
- `facades/{crate}.md` — per-surface facade specs (as-designed)
- `overview.md` — newcomer entry point bridging spec ↔ tests ↔ design ↔ code
- `sprints/METHOD_PROPOSED.md` — methodology
- `.claude/commands/arch.md` — `/arch` skill definition (the workflow layer)
- `sprints/reimplementation.md` — full reimplementation strategy (historical; M11 considers archive)
- `src/CLAUDE.md` — cross-cutting source conventions (error handling, code structure, naming)
- `sketch/audits/*.md` — structural debts to avoid (59 findings: 15 HIGH, 23 MEDIUM, 21 LOW)
- `sketch/src/` — prototype source as reference oracle (solutions to language-level problems, NOT pipeline structure — the sketch has the same dual-pipeline debt)
- `archive/pipeline-convergence-review.md` — dual-pipeline defect analysis (origin of principles 11–13)

## Architectural Principles

Extracted to `principles.md` (S63). That file is the single canonical home and is auto-imported by `.claude/commands/arch.md`. Cite principles by name from `principles.md`; do not re-summarise the list here.

## String Newtypes

**Hard rule**: All identifier fields in boundary types MUST use the appropriate newtype, never bare `String`. This prevents accidental mixing of identifiers across semantic categories (e.g., passing a module path where a symbol name is expected).

| Newtype | Semantic meaning | Examples |
|---|---|---|
| `Symbol` | Local identifier — variable, function, operator, constructor name | `"foo"`, `"+"`, `"Some"`, `"_"` |
| `TypeName` | Type name (uppercase) — ADT, builtin, constructor | `"Int"`, `"Option"`, `"Color"` |
| `TraitName` | Trait name (uppercase) | `"Num"`, `"Display"`, `"Eq"` |
| `ModuleName` | Single module component (no dots) | `"core"`, `"option"`, `"math"` |
| `ModuleFullPath` | Dotted module path | `"core.option"`, `"user"` |
| `LinkerSymbol` | JIT linker name (mangled) | `"add$Int+Int"` |
| `FQSymbol` | Fully qualified: module + symbol | `{ module: "core.option", symbol: "Some" }` |

**When in doubt**: if a `String` field identifies something in the language (a name, a type, a module), it should be a newtype. The only bare `String` fields allowed are:
- Error messages
- Documentation strings
- Source text
- User-visible descriptions (e.g., `SpecialForm.description`)

All newtypes are generated via `string_newtype!()` which derives the standard trait set and implements `Deref<Target=str>`, `From<String>`, `From<&str>`, `AsRef<str>`, `Display`.

## Conventions

- All types in `cranelisp-types` derive `Serialize` + `Deserialize` for module caching
