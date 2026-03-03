# Reimplementation Design

## Introduction

The cranelisp prototype is a working compiler (~34K lines of Rust, ~8K lines of language specification, ~950 tests, 25 examples) that proves the language design. It covers the full surface area: Hindley-Milner type inference, algebraic data types, traits, macros, closures, reference counting, monadic IO, modules, platform DLLs, caching, REPL, and standalone executable generation.

The prototype's value is the design it proves and the specification it generated. Its structural debts — a god object (`CompiledModule`, 133 references across 18 files), monolithic functions, dual batch/REPL pipelines with divergent code paths, string-based dispatch between typechecker and codegen — are typical of sketch code and not worth incrementally fixing.

The reimplementation starts from the extracted specification and architecture, not from copying code. The prototype remains available as a reference oracle: when the spec is ambiguous, run the prototype and observe.

### What to preserve

- The language specification (`docs/spec/`, 16 files)
- The standard library (`lib/`, written in cranelisp — ports directly)
- The example programs (`examples/`, 25 files)
- Integration tests as acceptance criteria (~470 tests encoding actual behavior)
- The platform DLL contract (`cranelisp-platform` crate)
- Design documents for context and rationale

### What to replace

- All Rust source code in `src/`
- The module and crate structure
- Internal data representations and interfaces between pipeline stages
- The REPL implementation
- The caching and linking infrastructure

## Knowledge Architecture

Two layers of knowledge support the reimplementation, with no duplication between them.

### Claude skills (how to work)

Each skill is a Claude Code slash command (`/spec`, `/arch`, `/frontend`, etc.) backed by a skill definition file. Skills capture **process knowledge**: what role the agent plays, what workflow it follows, what artifacts it produces, how it coordinates with other skills. Skills are invoked per-session to set the agent's working mode.

A skill file references the relevant CLAUDE.md files rather than duplicating their content. For example, the `/frontend` skill says "read `src/reader/CLAUDE.md` for parser conventions" rather than repeating those conventions.

### CLAUDE.md files (what is there)

CLAUDE.md files live in the repository near the source code they describe. They capture **domain knowledge**: data structures, invariants, patterns, naming conventions, interface contracts. Any skill working in a directory reads its CLAUDE.md.

Placement strategy:
- **Project root** (`CLAUDE.md`): cross-cutting conventions — naming, error handling, git workflow, build commands
- **Per source directory** (e.g., `src/typechecker/CLAUDE.md`): local data structures, algorithm descriptions, invariants, known gotchas
- **Documentation directories** (`docs/CLAUDE.md`, `docs/spec/CLAUDE.md`): documentation conventions and authority rules
- **Test directories** (`tests/CLAUDE.md`): test helper patterns, fixture conventions
- **Standard library** (`lib/CLAUDE.md`): prelude structure, naming conventions, module organization

CLAUDE.md files are living documentation — updated as implementation proceeds. When code changes make a CLAUDE.md entry stale, the developer who made the change updates it.

## Skill Definitions

### Compiler skills (6)

These skills build the compiler pipeline. Each owns a pipeline stage with clear input/output types.

#### `/spec` — Language Specification Owner

**Owns**: `docs/spec/` (16 files, ~8K lines)

**Role**: Defines what the language does. Arbitrates ambiguity. Maintains the spec as the authoritative record of language behavior.

**Artifacts**:
- Spec files with EBNF grammar, typing rules, evaluation semantics
- Testable examples for every semantic rule
- Gap analysis documents when features are underspecified

**Interfaces**:
- All other skills reference the spec for behavioral requirements
- `/arch` consults `/spec` when interface types need to represent language features
- User-proxy skills report spec gaps when they encounter underspecified behavior

**Workflow**: When a spec ambiguity arises, `/spec` first checks the prototype's behavior (run the example), then records the behavior as normative or proposes a change.

#### `/arch` — Compiler Architect

**Owns**: Interface types, module boundaries, crate structure, CLAUDE.md scaffolding

**Role**: Defines how the compiler is structured. Owns the boundary types that flow between pipeline stages. Makes module decomposition decisions.

**Artifacts**:
- `docs/arch/interfaces.md` — boundary type definitions with Rust signatures
- `docs/arch/modules.md` — crate decomposition with dependency DAG
- `docs/arch/data-flow.md` — data transformations at each pipeline stage
- CLAUDE.md files scaffolded for each source directory

**Interfaces**:
- All compiler skills implement against the interfaces `/arch` defines
- Interface changes must go through `/arch` review
- `/spec` informs when language features require new interface types

**Workflow**: When a compiler skill needs an interface change, it proposes the change to `/arch`. The architect evaluates impact on other skills, updates the interface definition, and notifies affected skills.

#### `/frontend` — Frontend Developer

**Owns**: Reader, macro expander, AST builder (pipeline stages 1–3)

**Role**: Text in, AST out. Implements parsing, macro compilation, macro expansion, and AST construction.

**Artifacts**:
- S-expression reader (source text → `Sexp`)
- Macro expander (compiled `defmacro` + recursive expansion)
- AST builder (`Sexp` → `Expr`, `TopLevel`)
- Unit tests for each stage

**Interfaces**:
- **Input**: source text (String)
- **Output**: `Vec<TopLevel>` (AST defined by `/arch`)
- Consumes spec sections 1 (lexical), 2 (grammar), 9 (macros)
- Macro expansion requires a mini-pipeline internally (parse → typecheck → compile → execute)

**Workflow**: Implement reader first (smallest, most self-contained). AST builder second. Macro system last (most complex at ~2K lines in the prototype, requires internal mini-pipeline).

#### `/typecheck` — Typechecker Developer

**Owns**: Type inference, traits, constrained polymorphism, monomorphisation (pipeline stage 4)

**Role**: AST in, typed environment out. Implements Algorithm W, trait declarations/implementations, method resolution, and constrained polymorphism.

**Artifacts**:
- Type inference engine (Algorithm W with unification)
- Trait registry and method resolution
- Constrained polymorphism detection and monomorphisation
- Exhaustiveness checking for pattern matching
- Unit tests for inference, unification, traits, monomorphisation

**Interfaces**:
- **Input**: `Vec<TopLevel>` (AST), `ModuleSymbolTable` (symbol tables from previous modules)
- **Output**: `CheckResult` { method_resolutions, expr_types, constrained_fn_names, mono_defns }
- Consumes spec sections 3 (types), 4 (expressions), 5 (definitions), 6 (pattern matching), 7 (traits)

**Workflow**: Start with core inference (literals, variables, let, if, apply, lambda). Add ADTs and pattern matching. Add traits and method resolution. Add constrained polymorphism and monomorphisation last.

#### `/backend` — Backend Developer

**Owns**: Codegen, JIT, linker, cache, executable generation (pipeline stages 5–6)

**Role**: Typed AST in, executable code out. Translates typed AST to Cranelift IR, manages JIT compilation, implements caching and linking.

**Artifacts**:
- Cranelift IR codegen for all expression forms (Tier 1: interactive JIT)
- Reference counting emission (inc/dec, drop glue, consuming/borrowed conventions)
- Closure compilation and auto-curry wrappers
- JIT module lifecycle
- Object file caching and linking
- Standalone executable generation
- Release compiler backend (Tier 2: LLVM or C emission for optimized builds)
- Unit tests for IR generation, RC emission

**Interfaces**:
- **Input**: `Vec<TopLevel>` (AST), `CheckResult` (typed environment), `ModuleSymbolTable`
- **Output**: executable code (function pointers or `.o` files)
- Consumes spec section 12 (runtime model)
- Cranelift 0.125 API (pin version for stability)
- Two-tier strategy: Cranelift for REPL speed, LLVM/C-emission for release builds (see `docs/backend-selection.md`)

**Workflow**: Start with expression codegen for simple types (Int, Bool). Add String and heap allocation with RC. Add closures. Add ADTs and pattern matching codegen. Add IO model and platform calls. Add caching and linking. Release compiler is a post-Ring-4 deliverable.

#### `/qa` — Quality Assurance

**Owns**: Integration tests, E2E tests, performance benchmarks, REPL, batch orchestration

**Role**: Wire the pipeline end-to-end and validate that everything works together. Own the batch and REPL entry points.

**Artifacts**:
- Migrated integration tests (from prototype's ~470 integration tests)
- E2E transcript tests (from prototype's 4 `.cl`/`.out` pairs)
- Performance regression benchmarks
- Batch-mode pipeline orchestrator (`batch.rs`)
- REPL implementation (`repl/`)
- Test plan mapping spec sections to tests

**Interfaces**:
- Consumes output from all compiler skills
- Owns the top-level orchestration that wires stages together
- Reports test failures back to the responsible compiler skill

**Workflow**: Start with batch mode (simpler, no interactive state). Port integration tests as pipeline stages connect. Build REPL last (depends on everything). Port E2E transcript tests. Establish performance baselines.

### Review skill (1)

#### `/review` — Code Reviewer

**Owns**: Code quality standards across all compiler skills; ring-completion review

**Role**: Review code written by compiler skills for simplicity, adherence to CLAUDE.md conventions, and avoidance of the structural patterns documented in `audits/`. Provides timely feedback to prevent the prototype's structural debts from re-accumulating in the rewrite.

**Artifacts**:
- Inline review comments or a `docs/review/ring-N.md` report for each ring
- Per-ring quality summary before advancing to the next ring
- Additions to relevant CLAUDE.md files when a recurring pattern deserves a standing rule

**Interfaces**:
- Invoked by any compiler skill after completing a significant unit of work, or at ring boundaries
- Reports findings to the skill that owns the code
- Escalates architectural concerns to `/arch`
- Has no blocking authority — findings are advisory; skills decide whether to act immediately or defer

**Workflow**:
1. Read the `audits/` document for the modules being reviewed (e.g. `audits/codegen.md` when reviewing codegen work)
2. Check that HIGH-severity audit findings are not reintroduced (e.g. duplicate heap classification logic, ISA constructed separately from the JIT path, panics in non-test code)
3. Verify adherence to the relevant CLAUDE.md conventions (naming, error handling, module boundaries)
4. Check for: over-engineering, premature abstraction, god functions (>100 lines), repeated patterns that should be extracted, `.unwrap()` in non-test code, stringly-typed patterns
5. At ring completion, write a brief ring summary and confirm `/arch`'s interface types remain clean

### User-proxy skills (4)

These skills exercise the language from the user's perspective. They validate usability and provide feedback that flows back to compiler skills. User-proxy skills begin work once a usable language subset exists — they do not wait for the pipeline to be complete.

#### `/stdlib` — Standard Library Developer

**Owns**: `lib/` — prelude, core modules, standard library functions

**Role**: Build the standard library as a user of the language. Validate that the type system, traits, and macros are expressive enough for real library code.

**Artifacts**:
- `lib/prelude.cl`, `lib/core.cl`, `lib/core/*.cl`
- Trait definitions (Num, Eq, Ord, Display, Functor, Unchecked)
- Collection functions (map, filter, fold, etc.)
- IO helpers (pure, do, bind!)
- Prelude macros (list, vec, cond, case, threading)

**Feedback to compiler skills**: Reports when type inference is too restrictive, when macro expansion has edge cases, when trait resolution is surprising, or when error messages are unhelpful for library authors.

#### `/examples` — Example Developer

**Owns**: `examples/`, tutorial programs, demonstration code

**Role**: Write idiomatic programs that showcase the language. Surface usability issues from a programmer's perspective.

**Artifacts**:
- Example programs for all language features
- Multi-file project examples
- Programs that exercise error paths (compile errors with good messages)
- Idiomatic patterns guide

**Feedback to compiler skills**: Reports when error messages are confusing, when REPL feedback is unhelpful, when language constructs are awkward to use in practice.

#### `/platform` — Platform Developer

**Owns**: `platforms/`, `cranelisp-platform/`, `cranelisp-runtime/`

**Role**: Build platform DLLs that extend the language with IO capabilities. Validate the FFI boundary, marshalling, and IO model from an extension author's perspective.

**Artifacts**:
- `cranelisp-platform` shared crate (C-ABI contract, safe wrappers)
- `cranelisp-runtime` (Rust-side runtime primitives)
- `platforms/stdio/` (reference platform)
- `platforms/test-capture/` (test harness platform)

**Feedback to compiler skills**: Reports when the C-ABI contract is awkward, when marshalling is error-prone, when the IO model leaks abstractions, when `CLOwned` / `CLString` / `CLInt` wrapper ergonomics need improvement.

#### `/docs` — Documentation Owner

**Owns**: All user-facing documentation — tutorials, language guide, reference material

**Role**: Validate the learning path. Ensure concepts build logically for new users. Maintain reference documentation beyond the spec.

**Artifacts**:
- Language tutorial (progressive introduction)
- Language guide (feature-by-feature reference for practitioners)
- Getting started guide (installation, first program, REPL orientation)
- Error message catalog with explanations

**Feedback to compiler skills**: Reports when the learning curve has gaps, when concepts require too much prerequisite knowledge, when terminology is inconsistent between spec and user-facing docs.

## Extraction Phase

Before the rewrite begins, extract the prototype's value into reusable artifacts.

### Step 1: Complete the language spec

**Skill**: `/spec`

Review each spec file against prototype behavior. Fill gaps:
- **Section 12 (Runtime)**: RC header layout, consuming vs borrowed calling conventions, drop glue structure, COW semantics for Vec ops, IO trampoline mechanics
- **Section 3 (Types)**: Monomorphisation algorithm for constrained polymorphism, cross-module specialization rules
- **Section 4 (Expressions)**: Auto-currying dispatch rules, multi-sig disambiguation
- **Section 7 (Traits)**: Derive mechanism (structural trait impl generation for Eq, Ord, Display)
- **New section or subsection**: Parallelism constructs (par-let, par-bind!)
- **Section 1 (Lexical)**: Full reader shortcut semantics (`'expr`, `x#`, `#(...)`)

**Acceptance criteria**: Every spec example runs against the prototype and produces the documented result.

### Step 2: Extract architecture contracts

**Skill**: `/arch`

Read prototype source. Extract:
- **Interface types**: Rust type definitions for all pipeline boundary types (Sexp, Expr, Type, Scheme, CheckResult, MethodResolutions, ModuleEntry)
- **CompiledModule decomposition**: Design the split into separate concerns (SymbolTable, ModuleGraph, CodegenState, CacheMetadata)
- **Crate dependency DAG**: New crate structure enforcing clean boundaries via Cargo
- **Naming conventions**: From `src/primitives/CLAUDE.md` and `src/CLAUDE.md`

**Acceptance criteria**: Interface document defines every type that crosses a pipeline stage boundary, with field-level documentation.

### Step 3: Extract QA plan

**Skill**: `/qa`

Catalog prototype tests:
- Map each of the ~470 integration tests to the spec section it validates
- Classify as spec-validation (port directly) vs implementation-specific (rewrite)
- Document the test helper pattern (`compile_and_run_simple`, `compile_and_run`, `compile_and_run_with_macros`)
- Identify the 6 documented test coverage gaps from KNOWN_ISSUES.md
- Capture performance baseline from prototype for regression comparison

**Acceptance criteria**: Test catalog spreadsheet with spec-section mapping, portability classification, and priority ranking.

### Step 4: Known issues triage

**Skills**: `/arch` + `/spec`

For each of the 27 items in KNOWN_ISSUES.md, decide:
- **Fix in rewrite**: The architectural change makes this tractable (e.g., trait method resolution bypass → collapse the multi-step string-based pipeline)
- **Defer**: Not worth addressing now (e.g., polymorphic recursion)
- **Accept**: Language-defined behavior, document in spec (e.g., `do` is IO-specific)

**Acceptance criteria**: Every known issue has a disposition with rationale.

### Step 5: Scaffold skills and CLAUDE.md

**Skill**: `/arch`

Produce:
- Skill definition files for all 11 skills
- CLAUDE.md files for each source directory in the new crate structure
- Root CLAUDE.md with cross-cutting conventions

## Delivery Strategy

### Decision: Feature-Ring Model

The reimplementation uses a **feature-ring model** — concentric rings of capability, each stable before the next begins. This was chosen over vertical slices, pipeline-first, and spec-section approaches after evaluating all four against the prototype's lessons.

| Ring | Capability | Key property |
|------|-----------|-------------|
| 0 (core) | Expressions, types, functions, let, if, match | No heap allocation, no RC |
| 1 (heap) | Strings, ADTs, closures, reference counting | Heap management established |
| 2 (abstraction) | Traits, modules, imports, constrained polymorphism | Name resolution and dispatch |
| 3 (meta) | Macros, derive, standard library | Metaprogramming layer |
| 4 (effects) | IO model, platforms, parallelism, caching, REPL | Side effects and build infrastructure |

### Rationale

The ring model's key advantage is that each ring establishes a stable foundation. Ring 0 proves the pipeline works without any heap complexity. Ring 1 adds heap management as a clean layer. This matches the prototype's hardest lesson: reference counting interacts with everything, and getting it right requires a clean separation between heap and non-heap concerns.

Within each ring, skills deliver vertically — they don't complete an entire pipeline stage before starting the next. Instead, each stage implements enough to support the current ring's features, validates end-to-end, then extends for the next ring.

Ring 0 defines the full `Type` enum (including `ADT`, `Fn`, `Var`) from the start even though it only exercises `Int`, `Bool`, `Float`, and simple `Fn`. This prevents rework when later rings add types — the transition from ring N to ring N+1 is additive, not a redesign.

User-proxy skills engage progressively:
- **Ring 0**: `/examples` writes simple integer/boolean programs; `/docs` drafts the getting-started tutorial
- **Ring 1**: `/examples` writes string and ADT programs; `/platform` begins the runtime crate
- **Ring 2**: `/stdlib` begins trait definitions and collection functions; `/platform` implements stdio platform
- **Ring 3**: `/stdlib` completes the prelude using macros; `/docs` writes the language guide
- **Ring 4**: All user-proxy skills validate the full language

For the detailed per-skill progression with acceptance criteria, see `design/arch/roadmap.md`.

## Implementation Workflow

### Phase sequence

```
Phase A: Extract (parallel)
  /spec    — complete language spec gaps
  /arch    — extract interface types, design crate structure
  /qa      — catalog tests, create test plan
  /arch + /spec — triage known issues

Phase B: Scaffold (architect leads, blocking)
  /arch    — create crate structure, define boundary types, write CLAUDE.md files
  All skills review interface contracts

Phase C: Ring 0 — Core (parallel implementation)
  /frontend   — reader + AST builder (no macros yet)
  /typecheck  — core inference (Int, Bool, Float, simple Fn, let-polymorphism)
  /backend    — codegen for core types (no heap, no RC)
  /qa         — batch pipeline wiring, basic integration tests
  /examples   — simple programs
  /docs       — getting started tutorial
  /review     — ring-completion quality pass before Phase D begins

Phase D: Ring 1 — Heap (parallel, extends each stage)
  /frontend   — (no changes)
  /typecheck  — ADT type checking, pattern matching, exhaustiveness
  /backend    — heap allocation, RC, closure codegen, drop glue
  /qa         — RC tests, ADT integration tests
  /examples   — string and ADT programs
  /platform   — runtime crate, begin platform contract
  /review     — ring-completion quality pass (focus: RC correctness, drop glue, no unwrap in heap paths)

Phase E: Ring 2 — Abstraction (parallel)
  /frontend   — (no changes)
  /typecheck  — traits, method resolution, constrained polymorphism, modules
  /backend    — mangled dispatch, GOT-based cross-module calls
  /qa         — module graph tests, trait dispatch tests
  /stdlib     — begin trait definitions, collection functions
  /platform   — stdio platform DLL
  /review     — ring-completion quality pass (focus: name resolution complexity, GOT/symbol-table separation)

Phase F: Ring 3 — Meta (parallel)
  /frontend   — macro system (mini-pipeline: parse → typecheck → compile → execute)
  /typecheck  — (macro-generated code feeds into existing checking)
  /backend    — (macro-generated code feeds into existing codegen)
  /qa         — macro integration tests, prelude tests
  /stdlib     — complete prelude using macros
  /docs       — language guide
  /review     — ring-completion quality pass (focus: macro pipeline internal structure, no god functions)

Phase G: Ring 4 — Effects (parallel)
  /frontend   — (no changes)
  /typecheck  — IO ADT, par-let/par-bind! type checking
  /backend    — IO trampoline, platform calls, parallel evaluation, caching, linker, exe generation
  /qa         — IO tests, platform tests, E2E tests, performance benchmarks, REPL
  /stdlib     — IO helpers, complete standard library
  /platform   — test-capture platform, platform documentation
  /docs       — complete tutorials, error catalog
  /examples   — IO programs, multi-file examples
  /review     — ring-completion quality pass (focus: JIT/cache path parity, no duplicate ISA construction)

Phase H: Release Compiler (after pipeline stable)
  /backend    — Tier 2 release backend (LLVM via inkwell or C code emission)
  /qa         — release build correctness tests (same semantics as JIT), performance benchmarks
  /docs       — release build documentation, deployment guide
```

Phase H is optional — it depends on the full pipeline being stable and is not required for language development. The two-tier strategy (Cranelift JIT for development, LLVM/C-emission for release) is documented in `docs/backend-selection.md`.

### Parallel work within a ring

Within each ring, compiler skills work in parallel against interface stubs:
- `/frontend` produces stub AST for `/typecheck` to test against
- `/typecheck` produces stub `CheckResult` for `/backend` to test against
- `/backend` can test IR generation without a real typechecker by constructing typed AST manually

When a stage is ready, `/qa` wires it to adjacent stages and runs integration tests.

### Feedback loops

User-proxy skills provide feedback that flows back to compiler skills:

```
/stdlib finds: "type inference gives wrong error for this pattern"
  → files issue → /typecheck investigates
  → if spec gap → /spec arbitrates
  → if implementation bug → /typecheck fixes

/examples finds: "error message mentions internal type var names"
  → files issue → /backend or /typecheck fixes display formatting

/platform finds: "CLOwned ergonomics are awkward for multi-capture closures"
  → files issue → /arch evaluates interface change
  → /backend implements

/docs finds: "trait concept has no good introduction path from simpler concepts"
  → feeds back to /spec for terminology consistency
  → writes tutorial section
```

## Coordination Model

### Change control

| Change type | Owner | Process |
|-------------|-------|---------|
| Interface type change | `/arch` | Proposal → impact assessment → update interface doc → notify affected skills |
| Spec ambiguity | `/spec` | Check prototype behavior → record as normative or propose change → update spec |
| Test failure | `/qa` | Triage → assign to responsible compiler skill → verify fix |
| User experience issue | User-proxy skill | File issue → compiler skill fixes → user-proxy validates |
| Code quality issue | `/review` | Flag to owning skill → skill decides to fix now or defer → update CLAUDE.md if recurring |

### Shared artifacts

All skills reference but do not own:
- The language spec (`docs/spec/`) — owned by `/spec`
- Interface type definitions (`docs/arch/interfaces.md`) — owned by `/arch`
- CLAUDE.md files — owned by the skill that owns the directory's code, updated by anyone who changes the code

### Communication via artifacts

Skills communicate through files in the repository, not through out-of-band channels:
- Issues and decisions are documented in the relevant spec, arch, or CLAUDE.md file
- Test failures are documented in the test plan
- Feedback from user-proxy skills is documented as issues in a tracking file or as KNOWN_ISSUES entries

## Risk Analysis

### CompiledModule decomposition (HIGH)

The prototype's `CompiledModule` is referenced 133 times across 18 files. It conflates symbol tables, module graph data, codegen artifacts, and cache metadata. The rewrite must decompose this cleanly before any skill can begin implementation.

**Mitigation**: This is the `/arch` skill's first deliverable in Phase B. The decomposition should produce separate types: `SymbolTable` (types, schemes, visibility), `ModuleGraphNode` (imports, exports, dependencies), `CodegenState` (GOT, code pointers, func IDs), `CacheMetadata` (hashes, file paths). Each type lives in the crate that owns its concern.

### Macro system complexity (MEDIUM-HIGH)

The macro system (~2K lines in the prototype) requires a mini-pipeline within itself: parse macro body → typecheck → compile to native code → execute at expansion time. This creates a circular dependency between the frontend (which needs macros) and the backend (which macros need for compilation).

**Mitigation**: Implement macros last within the frontend (Phase F). All earlier rings work without macros — the standard library's macro-based forms (`list`, `do`, `bind!`, `vec`) are replaced by direct AST construction or are simply unavailable until ring 3. The macro system's internal pipeline can reuse the already-built typecheck and codegen stages.

### REPL state management (MEDIUM)

The prototype's REPL (~2K lines) has deeply interleaved state: TypeChecker, MacroEnv, JIT, FileWatcher, project root, module loading, save-to-file. It depends on every other subsystem.

**Mitigation**: Build batch mode first (Phase C). The REPL is implemented last (Phase G) when all subsystems exist. The REPL is architecturally a thin loop over the batch pipeline stages with persistent state between iterations.

### Spec–implementation divergence (MEDIUM)

The spec may describe idealized behavior that differs from the prototype. The prototype has 27 documented known issues.

**Mitigation**: Before the rewrite begins (Phase A), run every spec example against the prototype. Annotate divergences. The spec documents current behavior, not aspirational behavior — fix the spec or fix the prototype, but don't leave disagreements.

### Cross-ring rework (LOW-MEDIUM)

Features in later rings may require changes to code written in earlier rings. For example, adding traits (ring 2) may require changes to how types are represented (ring 0).

**Mitigation**: The prototype proves which representations work. Ring 0 should use the full `Type` enum (including `ADT`, `Fn`, `Var`) from the start, even though ring 0 only exercises `Int`, `Bool`, `Float`, and simple `Fn`. Design for the full feature set; implement incrementally.

## Success Criteria

The reimplementation is complete when:

1. **Spec conformance**: Every testable example in `docs/spec/` produces the documented result
2. **Test suite**: All portable integration tests from the prototype pass (~470 tests)
3. **E2E tests**: All transcript tests pass (`tests/e2e/`)
4. **Standard library**: `lib/` compiles and all library tests pass
5. **Examples**: All 25 example programs run correctly
6. **Platforms**: Platform DLLs load and pass platform tests
7. **Performance**: Within 2x of prototype on representative benchmarks
8. **Quality**: `cargo test` green, `cargo clippy` clean, no `unwrap()` in the pipeline
9. **Documentation**: User-facing tutorial, language guide, and getting-started guide exist
10. **Self-documenting REPL**: Every symbol and expression produces useful feedback at the REPL
