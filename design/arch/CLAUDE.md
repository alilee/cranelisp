# design/arch/

Architecture deliverables for the Cranelisp reimplementation. Owned and maintained by the `/arch` skill.

## Files

- `architecture.md` — Overall architecture: 7-crate DAG, single pipeline principle, CompiledModule decomposition, macro mini-pipeline resolution, audit findings addressed
- `interfaces.md` — Complete Rust type signatures for all pipeline boundary types (the design book)
- `roadmap.md` — Ring-by-ring phased progression roadmap with per-skill deliverables and acceptance criteria
- `design-space.md` — Forward-looking analysis in two parts: Part 1 (§1–9) analyzes Ring 1 decisions against NFRs; Part 2 (§10–14) examines beyond-ring resilience: three-mode compilation, WASM/target portability, collection extensibility, concurrent channels, peer language patterns

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

## Key Decisions (Ring 1)

10. **Base-pointer ABI** — heap pointers point to the start of the allocation (offset 0 = alloc_size, offset 8 = rc, offset 16+ = payload). Positive offsets throughout. Departing from the sketch's interior-pointer convention.
11. **Closure drop via side-table** — per-lambda drop functions stored in a `HashMap<*const u8, *const u8>` (code_ptr → drop_fn) rather than inline in the closure struct. Avoids an extra pointer-width field per closure and simplifies the calling convention.
12. **Strings opaque to backend** — `HeapString` layout is owned by `cranelisp-runtime`. Backend never reads/writes string bytes — all string operations go through extern functions. Enables future rope upgrade as a runtime-only change.
13. **Atomic RC from Ring 1** — reference count operations use `atomic_rmw` (Release for dec, Acquire for inc) even though Ring 1 is single-threaded. This avoids a breaking ABI change when concurrency arrives in Ring 4, per NFR C.4.1.

## Cross-References

- `sprints/reimplementation.md` — Full strategy: skill definitions, ring model decision, phase sequence, risk analysis
- `src/CLAUDE.md` — Cross-cutting source conventions (error handling, code structure, naming)
- `sketch/audits/*.md` — Structural debts to avoid (59 findings: 15 HIGH, 23 MEDIUM, 21 LOW)
- `sketch/src/` — Prototype source as reference oracle

## Architectural Principles

The criteria `/arch` uses to evaluate every design decision. These are derived from the prototype's complexity analysis (59 audit findings across 4 modules):

1. **Decoupling over convenience.** Each crate should be independently compilable, testable, and replaceable. If adding a feature requires modifying three crates, the boundaries are wrong. The prototype's `CompiledModule` was convenient (everything in one place) and catastrophic (133 references, 18 files, untestable in isolation).

2. **Narrow interfaces.** Boundary types should be the minimum surface area needed. `CheckResult` carries exactly what the backend needs from the typechecker — not the typechecker's internal state. Adding a field to a boundary type has O(n) impact across skills; adding an internal type has O(1) impact. Interface changes require `/arch` review.

3. **Dependency flows toward stability.** `cranelisp-types` is the most stable crate (data definitions, no logic). Everything depends on it; it depends on nothing. When you need to decide where a type lives, put it in the most stable crate that makes sense. This is why `SymbolTable` is in types (stable data) while `ModuleCodegenState` is in backend (volatile runtime state). The dependency graph must be acyclic — Cargo enforces this at build time.

4. **Parallel development is a first-class constraint.** The architecture must enable skills to work concurrently within a ring without blocking each other. This means: clear ownership (one skill per crate), interface stubs (typecheck can test without backend), and no shared mutable state between crates.

5. **Testability is structural.** If a component can't be unit-tested without constructing the entire pipeline, the boundaries are wrong. Each crate must be testable with stubs at its boundaries. The prototype had 6192 lines of codegen with zero unit tests — not because of laziness, but because the code was structurally untestable (everything depended on everything).

6. **Complexity has a budget.** Every abstraction, indirection, or generalization must justify the complexity it introduces against the coupling it removes. The ring model exists so that Ring 0 code carries zero heap complexity. `CompileMode` exists so that batch/REPL share one pipeline instead of two. But a premature abstraction that serves no current ring is debt, not architecture.

7. **Single source of truth.** When a concept (ISA flags, heap classification, primitive type names) appears in two places, it will diverge. The prototype had 3 ISA constructions and 9 duplicate primitive-name mappings. Every concept gets one authoritative location; other sites reference it.

8. **No interim implementations of later-ring capabilities.** If a feature will arrive in a later ring with its proper mechanism, do NOT build a temporary version in an earlier ring. Instead, use the primitives that already exist at the current ring level and defer the user-facing syntax until the real mechanism is ready. Example: Ring 0 should not implement `+` with a bespoke operator dispatch table when Ring 2 will introduce `Num.+` via trait dispatch — instead, Ring 0 should expose named primitives (`add-i64`, `add-f64`) and let `+` wait for traits. Interim implementations create throwaway infrastructure that couples into multiple crates and must be unpicked later. The test is: "will this code survive into the ring where the real mechanism arrives?" If not, don't build it.

9. **Rings are accretive.** Each ring adds code, tests, and capabilities — it should not replace or delete work from earlier rings. Earlier-ring tests remain as-is; later rings add new tests for the new mechanism. This provides diagnostic isolation: if `(+ 1 2)` (trait dispatch, Ring 2) fails but `(add-i64 1 2)` (primitive, Ring 0) passes, the bug is in dispatch, not codegen. The same applies to implementation: primitives survive as the foundation that higher-level mechanisms dispatch to.

## String Newtypes

**Hard rule**: All identifier fields in boundary types MUST use the appropriate newtype, never bare `String`. This prevents accidental mixing of identifiers across semantic categories (e.g., passing a module path where a symbol name is expected).

| Newtype | Semantic meaning | Examples |
|---|---|---|
| `Symbol` | Local identifier — variable, function, operator, constructor name | `"foo"`, `"+"`, `"Some"`, `"_"` |
| `TypeName` | Type name (uppercase) — ADT, builtin, constructor | `"Int"`, `"Option"`, `"Color"` |
| `TraitName` | Trait name (uppercase) | `"Num"`, `"Display"`, `"Eq"` |
| `ModuleName` | Single module component (no dots) | `"core"`, `"option"`, `"math"` |
| `ModuleFullPath` | Dotted module path | `"core.option"`, `"user"` |
| `JitSymbol` | JIT linker name (mangled) | `"add$Int+Int"` |
| `FQSymbol` | Fully qualified: module + symbol | `{ module: "core.option", symbol: "Some" }` |

**When in doubt**: if a `String` field identifies something in the language (a name, a type, a module), it should be a newtype. The only bare `String` fields allowed are:
- Error messages
- Documentation strings
- Source text
- User-visible descriptions (e.g., `SpecialForm.description`)

All newtypes are generated via `string_newtype!()` which derives the standard trait set and implements `Deref<Target=str>`, `From<String>`, `From<&str>`, `AsRef<str>`, `Display`.

## Conventions

- All types in `cranelisp-types` derive `Serialize` + `Deserialize` for module caching
