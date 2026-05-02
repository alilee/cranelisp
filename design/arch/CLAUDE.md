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

- [0001](decisions/0001-7-plus-1-crate-dag.md) — 7+1 crate DAG (operative)
- [0002](decisions/0002-cranelisp-types-is-data-only.md) — `cranelisp-types` is data-only (operative)
- [0003](decisions/0003-span-is-a-struct.md) — Span is a struct (operative)
- [0004](decisions/0004-typeid-is-u32.md) — TypeId is u32 (operative)
- [0005](decisions/0005-no-meta-option-symbolmeta.md) — No `meta: Option<SymbolMeta>` (operative)
- [0006](decisions/0006-type-from-name-type-name.md) — `Type::from_name()` / `type_name()` (operative)
- [0007](decisions/0007-compilemode-enum.md) — `CompileMode` enum (retracted)
- [0008](decisions/0008-macroexpander-trait.md) — `MacroExpander` trait (retracted)
- [0009](decisions/0009-compiledmodule-decomposed.md) — CompiledModule decomposed (operative)
- [0010](decisions/0010-base-pointer-abi.md) — Base-pointer ABI (operative)
- [0011](decisions/0011-embedded-drop-glue-ptr-in-closures.md) — Embedded drop_glue_ptr in closures (operative)
- [0012](decisions/0012-strings-opaque-to-backend.md) — Strings opaque to backend (operative)
- [0013](decisions/0013-atomic-rc-from-ring-1.md) — Atomic RC from Ring 1 (operative)
- [0014](decisions/0014-typecheck-emits-traitmethod.md) — Typecheck emits `TraitMethod`, backend maps to primitives (operative)
- [0015](decisions/0015-ring-0-1-builtinfn-coexists.md) — Ring 0-1 `BuiltinFn` coexists with Ring 2 `TraitMethod` (operative)
- [0016](decisions/0016-jit-mangling-trait-method-type.md) — JIT mangling: `Trait.method$Type` (operative)
- [0017](decisions/0017-core-traits-registered-at-startup.md) — ~~Core traits registered at startup, not from files~~ — RESOLVED (Sprint 11) (operative)
- [0018](decisions/0018-replcheckresult-gains-ring-2-fields.md) — `ReplCheckResult` gains Ring 2 fields (operative)
- [0019](decisions/0019-constraint-propagation-in-generalize.md) — Constraint propagation in `generalize` (operative)
- [0020](decisions/0020-split-calling-convention-for-rc.md) — Split calling convention for RC (superseded-by-0024)
- [0021](decisions/0021-tc-sourced-call-graph.md) — TC-sourced call graph with per-symbol persistence on ModuleEntry (operative)
- [0022](decisions/0022-defined-symbols-shared-predicate.md) — `defined_symbols()` is the shared codegen-compilable predicate (operative)
- [0023](decisions/0023-uniform-codegen-mode-as-module-property.md) — Uniform codegen; mode is a Module property, not a compile_to_module parameter; two-GOT model (operative)
- [0024](decisions/0024-uniform-consuming-calling-convention.md) — Uniform consuming calling convention across all call types (operative)
- [0025](decisions/0025-compiled-code-on-moduleentry-def-code.md) — Compiled code lives on `ModuleEntry::Def.code` as a `#[serde(skip)]` field; cache stores both `.meta.json` and `.o` (operative)
- [0026](decisions/0026-platform-fn-pointers-on-moduleentry-def.md) — Platform function pointers on `ModuleEntry::Def.platform_fn_ptr`; `scheduling_class` is a variant field (operative)
- [0027](decisions/0027-g8-lands-before-g9.md) — G8 lands before G9 (platform-registry deletion before persistent workers) (operative)
- [0028](decisions/0028-priority-worker-jit-per-worker.md) — Priority-worker JIT is per-worker, not per-session (G10) (superseded-by-0031)
- [0029](decisions/0029-io-trampoline-shallow-dec-runtime-primitive.md) — IO trampoline shallow dec uses a `cranelisp-runtime` primitive (`rc::dec_shallow_io`) (operative)
- [0030](decisions/0030-form-by-form-scheduler-mutual-imports.md) — Form-by-form scheduler deadlocks on mutual imports; `super` safe for non-mutual patterns (operative)
- [0031](decisions/0031-one-jitmodule-per-compile-batch.md) — One `JITModule` per compile batch; `Arc<Jit>` on `ModuleEntry::Def.code`; custom `Drop` calls `unsafe free_memory()` (operative)
- [0032](decisions/0032-codestore-and-linkerstore-empty-marker.md) — `CodeStore` and `LinkerStore` are empty marker traits in `cranelisp-types` (with `Clone` super-bound) (operative)
- [0033](decisions/0033-structural-decls-on-symboltable.md) — Structural declarations live as fields on `SymbolTable`, not as a parallel `ModuleStructure` (operative)
- [0034](decisions/0034-cache-schema-versioned.md) — Cache schema is versioned by an explicit `schema_version: u32` field (operative)
- [0035](decisions/0035-code-enum-integration-layer.md) — `Code` enum lives in `src/` and unifies JIT-backed and Linker-backed compiled code (operative)
- [0036](decisions/0036-function-symbol-naming-linkage.md) — Function symbol naming + linkage: bare names + `Linkage::Local` uniformly (operative)
- [0037](decisions/0037-cache-hit-integration-inside-register-module.md) — Cache-hit integration lives inside `register_module`'s recursive flow (operative)
- [0038](decisions/0038-sharedstate-formal-worker-shareable-subset.md) — `SharedState` is the formal worker-shareable subset of `CompilerSession` state (operative)
- [0039](decisions/0039-per-defn-source-on-introspection.md) — Per-defn source lives on `Introspection.source`; `SymbolTable.defn_order: Vec<Symbol>` preserves canonical ordering (operative)
- [0040](decisions/0040-runtime-trace-io-trace-relocate-to-int.md) — `trace.rs` and `io_trace.rs` relocate to int; runtime keeps `IoObserver` callback contract; BC §4 unchanged (operative)
- [0041](decisions/0041-compile-to-module-per-symbol-jit-direct-writes.md) — `compile_to_module` per-symbol JIT cardinality; `Code` moves to `cranelisp-backend`; backend writes shared state directly; `Result<(), CompilationError>` (operative); amends Decisions 31, 35
- [0042](decisions/0042-platform-error-adopts-error-location.md) — `PlatformError` is a `cranelisp-types`-hosted enum with `ErrorLocation` carriers per variant; surfaces via `CranelispError::Platform` (operative)

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
