# design/arch/

Architecture deliverables for the Cranelisp reimplementation. Owned and maintained by the `/arch` skill.

## Files

### Active (target architecture)

- `CLAUDE.md` — this file: principles, key decisions, conventions
- `roadmap.md` — Delivery tracking (phases, rings, sprints)
- `interfaces.md` — boundary type definitions with Rust signatures
- `pipeline-v4.md` — target pipeline design: scheduler-driven concurrent compilation
- `pipeline-v4-roadmap.md` — migration status and remaining work
- `concurrent-pipeline.md` — scheduler design: module pools, priority queue, worker interfaces

### Archive (`archive/`)

Historical pipeline designs (v1, v2, v3) and migration artefacts. Reference only — not the target architecture.

- `archive/v1/` — v1 architecture, interfaces, pipeline orchestration, sketch audit
- `archive/pipeline-v2.md` — v2 pipeline design (stages, unified multi-pass check)
- `archive/pipeline-v3.md`, `archive/pipeline-v3-roadmap.md` — v3 migration (complete)
- `archive/pipeline-convergence-review.md` — Sprint 26 dual-pipeline defect analysis
- `archive/pipeline-convergence-playbook.md` — convergence execution plan
- `archive/session-restructure.md` — session restructure target data model (phases A–F complete)
- `archive/per-module-got-cleanup.md` — GOT unification design
- `archive/sprint-40a-design.md` — cancelled Sprint 40a design

## Key Decisions (Phase B)

Decisions 1–9 established the initial architecture. The pipeline v4 migration resolved the structural defects. Current status of each:

1. **7+1 crate DAG**: 7 pipeline crates + 1 build artifact. Surviving — crate boundaries stable.
2. **`cranelisp-types` is data-only** — all boundary types, no logic. Surviving.
3. **Span is a struct** — `struct Span { start: u32, end: u32 }`. Surviving.
4. **TypeId is u32**. Surviving.
5. **No `meta: Option<SymbolMeta>`** on `ModuleEntry::Def`. Surviving.
6. **`Type::from_name()` / `type_name()`**. Surviving.
7. **`CompileMode` enum** — failed. Replaced by scheduler-driven pipeline with no mode parameter. `CompileMode` deleted (Sprint 31). See `archive/pipeline-convergence-review.md` for history.
8. **`MacroExpander` trait** — superseded. Trait deleted (Sprint 43); expansion is a free function in `src/expander.rs`.
9. **CompiledModule decomposed** — evolved. `ModuleCodegenState` and `ModuleStructure` deleted during session restructure. Now: `SymbolTable` (in TypeChecker DashMap) + `TypecheckProduct` + `CodegenProduct` + `Introspection` on `SharedState`.

## Key Decisions (Ring 1)

10. **Base-pointer ABI** — heap pointers point to the start of the allocation (offset 0 = alloc_size, offset 8 = rc, offset 16+ = payload). Positive offsets throughout. Departing from the sketch's interior-pointer convention.
11. **Embedded drop_glue_ptr in closures** — Each closure carries a `drop_glue_ptr` at offset 24 in the closure struct (`HeapClosure` layout: `[header(16) | code_ptr(8) | drop_glue_ptr(8) | captures...]`, `CAPTURES_START = 32`). The drop glue function is a per-lambda generated function that dec's all heap-typed captures; null for closures with no heap captures. This replaced an earlier side-table design (`code_ptr → drop_fn` HashMap) which was rejected during Ring 2 because cross-module closures cannot look up the creating module's side table, and the embedded pointer makes closure dec a self-contained operation. See `design/backend/ring2-rc.md` §1.3 and §9.1, and `design/arch/interfaces.md` §HeapClosure.
12. **Strings opaque to backend** — `HeapString` layout is owned by `cranelisp-runtime`. Backend never reads/writes string bytes — all string operations go through extern functions. Enables future rope upgrade as a runtime-only change.
13. **Atomic RC from Ring 1** — reference count operations use `atomic_rmw` with sequentially-consistent ordering (Cranelift's default for `atomic_rmw`) even though Ring 1 is single-threaded. A separate Acquire fence is emitted on the free path (when `old_rc == 1`) before reading object fields for drop glue. This avoids a breaking ABI change when concurrency arrives in Ring 4, per NFR C.4.1. See `design/backend/ring2-rc.md` §2.1.

## Key Decisions (Ring 2A)

14. **Typecheck emits `TraitMethod`, backend maps to primitives** — the typecheck crate always emits `ResolvedCall::TraitMethod` for trait-dispatched operators. The backend recognizes known primitive impls (e.g., `Num.+$Int` → `iadd`) via a static `(TraitName, Symbol, TypeName) → PrimitiveOp` mapping. This keeps typecheck clean and backend-optimizable.
15. **Ring 0-1 `BuiltinFn` coexists with Ring 2 `TraitMethod`** — named primitives (`add-i64`, etc.) retain their `BuiltinFn` resolution path. Operators (`+`, `-`, etc.) gain a new `TraitMethod` path. Both paths coexist per principle 9.
16. **JIT mangling: `Trait.method$Type`** — trait method implementations use `Num.+$Int` format. Constrained fn specializations use `name$Type1+Type2` format.
17. **~~Core traits registered at startup, not from files~~ — RESOLVED (Sprint 11).** `register_core_trait_decls()` and `register_core_trait_impls()` are removed from `builtins.rs`. Traits (`Num`, `Eq`, `Ord`, `Display`) and their impls are ordinary Cranelisp defined in prelude `.cl` files (`stdlib/core/numerics.cl`, `stdlib/core/formats.cl`), loaded through the standard module pipeline. `import_primitives_into_user()` is retained for genuine primitives only (types, named functions, special forms). Tests that need operators must either load the prelude or define traits inline. See `design/arch/pipeline-orchestration.md` §5.
18. **`ReplCheckResult` gains Ring 2 fields** — `constrained_fn_names`, `mono_defns`, `default_method_defns` added to match `CheckResult`. Three-location atomic change.
19. **Constraint propagation in `generalize`** — `Scheme.constraints` populated by collecting trait constraints from active type variables during generalization. Non-empty constraints → constrained polymorphic function.

## Key Decisions (Ring 2B)

20. **RETRACTED (Sprint 56 Step 2c, superseded by Decision 24).** **Split calling convention for RC** — User functions use consuming convention (callee owns heap params, dec's them at scope exit; caller inc's variable args before the call). Builtins/externs use borrowing convention (caller dec's temporaries after the call; callee has no RC responsibility). Data constructors use plain arg lists (field values stored directly into the ADT; ADT drop glue handles recursive field dec at destruction time). The convention is determined statically at each call site based on the callee's `ResolvedCall` classification. The typecheck crate is entirely unaware of calling conventions — this is a backend-only concern. See `design/backend/ring2-rc.md` §3 for the full decision table.

## Key Decisions (Pipeline v4)

21. **TC-sourced call graph with per-symbol persistence on ModuleEntry** — The per-symbol call graph (callee list) is extracted during typechecking from method resolutions and stored persistently on `ModuleEntry`. `ModuleEntry::Def` and `ModuleEntry::Macro` each gain `callees: Vec<FQSymbol>`. `FormCheckResult.call_graph_edges` carries `Vec<(Symbol, FQSymbol)>` (caller is local, callee is fully qualified). `finalize_check_result()` groups edges by caller and writes to `ModuleEntry` in the `SymbolTable`. Cross-module queries use the existing `tc.symbol_table(module).get(name)` path — same as type resolution. `CheckResult` also carries a transient `call_graph: CallGraph` (rich, with tail-position/span) for within-module codegen/analysis. Codegen-sourced call graph rejected: the scheduler needs pre-codegen callee visibility for parallel macro dep compilation (§3.2 of `pipeline-v4.md`); codegen doesn't discover callees typechecking didn't resolve (Principle 7); building codegen-sourced now and replacing later violates Principle 8.

22. **`defined_symbols()` is the shared codegen-compilable predicate** — One filter, exposed as `SymbolTable::defined_symbols()`, returns entries where `ast.is_some() AND kind != Overloaded AND kind != UserFn { constrained_fn: Some(_) }`. Both the caller (priority worker in `/int`) and the backend internal loop consume this iterator. No alternative filter — `compile_to_module` trusts the contract: if a name in `names` resolves to an entry with `ast: None`, it returns a `CodegenError` rather than falling back to synthesis. Defined during Sprint 56 (Phase 2, Wave 0) to eliminate the split between base-defn program iteration and symbol-table lookup. Canonical location: `crates/cranelisp-types/src/module.rs` (SymbolTable impl). Rationale: Principle 7 (single source of truth — no two filters can diverge) + Principle 11 (single pipeline, mode parameters — the predicate is identical for JIT and object paths).

23. **Uniform codegen: mode is a Module property, not a compile_to_module parameter** — `compile_to_module<M: Module>(module_path, names, symbol_tables, module)` has four parameters and no mode discriminator. Object vs JIT differs only in how the passed-in `Module` implementation resolves `Linkage::Import` data symbols at finalize time: `ObjectModule` emits relocations; `JITModule` queries a caller-registered `JITBuilder::symbol_lookup_fn`. The backend emits byte-identical CLIF IR in both modes — `global_value` against `__cranelisp_got_{module}` data symbols declared as `Linkage::Import`. GOT bases are resolved per mode at finalize, not at codegen. Rejected designs: `CompilationEnv` trait with JIT/Object impls (re-enshrines the dual-pipeline divergence Principle 11 exists to prevent); thin `compile_to_module_jit`/`_object` wrappers over a crate-private core (two public entry points invite divergence regardless of internal structure); `CodegenTarget` enum parameter (a mode discriminator is what we're eliminating). Defined Sprint 56 Phase 2. Canonical location: `crates/cranelisp-backend/src/lib.rs`. Rationale: Principle 11 (single pipeline; mode as Module property, not function parameter) + JIT pays one extra memory load per cross-module call vs structural simplicity — most code runs from cached object files anyway.

24. **Uniform consuming calling convention across all call types** — Every function call site compiles identically for RC management: the caller transfers ownership of heap-typed arguments to the callee via inc-before-call for non-last-use vars (to preserve caller-side liveness) or direct transfer for last-use vars and temporaries. The callee owns its heap parameters and is responsible for dec'ing anything it does not return. Data constructors, user functions, trait methods, builtins, and externs all follow the same rule — there is no "borrowing" classification, no `CompileContext.dealloc_func_id: Option<...>` conditional, no caller-side post-call `dec_temporary_args`. Extern primitives implemented in Rust (`str-concat`, `string-length`, Vec ops, Sexp marshaling, IO trampolines, etc.) MUST dec any heap argument they do not return — their implementation becomes responsible for RC balance, not the caller. Rejected alternatives: (a) the Sprint 56 Step 2c predecessor split convention (Decision 20, retracted) which classified calls at the backend emit site and produced divergent code paths; (b) per-extern attribute annotations on typecheck-side classification, which would complicate the AST without removing the divergence. Defined Sprint 56 Step 2c. Canonical locations: `crates/cranelisp-backend/src/compiler/apply.rs` (call emission), every extern's Rust implementation. Rationale: Principle 11 (single pipeline, mode parameters — the caller-vs-callee responsibility split IS the mode parameter, expressed uniformly) + Principle 7 (single source of truth — one rule, applied everywhere).

## Cross-References

- `sprints/reimplementation.md` — Full strategy: skill definitions, ring model decision, phase sequence, risk analysis
- `src/CLAUDE.md` — Cross-cutting source conventions (error handling, code structure, naming)
- `sketch/audits/*.md` — Structural debts to avoid (59 findings: 15 HIGH, 23 MEDIUM, 21 LOW)
- `sketch/src/` — Prototype source as reference oracle (solutions to language problems, NOT pipeline structure — the sketch has the same dual-pipeline debt)
- `design/arch/archive/pipeline-convergence-review.md` — Dual-pipeline defect analysis and convergence plan (historical)

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

10. **Parser keywords are for distinct syntax only.** The AST builder recognizes a form as a special form (building a distinct `Expr` variant) only when its syntax differs from a function call — i.e., its arguments cannot be parsed as expressions. `(let [x 1] body)` MUST be a parser keyword because `[x 1]` is a binding vector, not a Vec literal. `(if c t e)` MUST be a parser keyword because it has short-circuit semantics that require a distinct AST node. But forms with regular call syntax — `(trace expr)`, `(platform "name")` — SHOULD flow through the module system as ordinary names that the typechecker or later passes recognize. This keeps the parser small and the module system authoritative: a name is available only if it's in scope. New special forms added in later rings should default to the module-scoped approach unless they genuinely need distinct syntax.

11. **Single pipeline, mode parameters.** There is one compilation pipeline. Batch, REPL, and module-loading all flow through the same stages with the same types. Where modes genuinely differ (direct vs GOT-indirect calls), the difference is a parameter on a shared function, not a separate function or a separate type. Duplicate types at a pipeline boundary (e.g., `TopLevel`/`ReplInput`) and adapter functions between them (e.g., `build_check_for_backend`) are architectural violations. Note: type-checking does NOT differ by mode — the multi-pass pipeline (register all signatures, then check all bodies) works identically on any input size (see `pipeline-v2.md` §5). *(Added Sprint 26 — see `pipeline-convergence-review.md` for the defect that motivated this.)*

12. **Design for the full spec surface.** Pipeline stage interfaces are designed against all language features the spec defines, not against the current sprint's needs. Every variant of a boundary type that the spec requires should exist from the start, with `todo!()` bodies if not yet implemented. This prevents accretive growth where each sprint adds variants and match arms to whichever function is closest, eventually producing parallel paths nobody designed. A `todo!()` is visible and compiler-enforced; a missing arm in a parallel function is silent. *(Added Sprint 26 — the ring model's accretive delivery pattern caused the dual-pipeline defect.)*

13. **`interfaces.md` is auditable.** The design book must be validated against architectural principles, not merely documented. If `interfaces.md` contains structurally identical types, adapter functions, or parallel pipeline entry points, that is an architectural violation — not a feature to document. Every gate review must include an `interfaces.md` coherence check. *(Added Sprint 26 — `interfaces.md` enshrined the `TopLevel`/`ReplInput` duplication as legitimate architecture for 25 sprints.)*

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
