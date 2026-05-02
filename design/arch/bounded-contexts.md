# Bounded Contexts — per-surface target shape

`/arch` commits to six crate-shaped surfaces plus the cross-crate types crate. Each is a **bounded context**: the stable demarcation of what the crate is responsible for. The triad (`/design`, `/dev`, `/review`) narrow-deploys to one surface per invocation; the surface's bounded context is what the triad reads to do its work.

This file is the canonical home for the per-surface full statements. The skill def (`.claude/commands/arch.md` §The crate-shaped surfaces) carries the one-line summaries and points here. The facade specs (`design/arch/facades/{crate}.md`) cite this file rather than restate the bounded context.

This document is conceptual. Each section answers: *what is this crate's responsibility, why does the boundary lie here, what crosses it.* It does not specify *how* responsibilities are implemented (per-crate design carries that) or *which decisions bind* the implementation (the boundary itself is the decision; cross-cutting principles live in `principles.md`).

Each section: bounded context (essence + why); in-scope (responsibilities, conceptually); out-of-scope (what belongs elsewhere by responsibility); what crosses the boundary (value-passing surfaces and, where applicable, window types). The int section additionally enumerates internal cadences and inter-cadence handoffs.

---

## 1. Frontend — `crates/cranelisp-frontend/`

**Bounded context.** Source text becomes structured data. The frontend reads source bytes into S-expressions, expands macros, and builds the AST. It is purely structural: it does not know types, code, or semantics — only shape. This narrows the contract the rest of the pipeline depends on: every downstream stage consumes the same well-formed tree shape, regardless of whether the input came from a file, the REPL, or another macro.

**In-scope.**
- Lexing and parsing source into S-expression trees
- Macro expansion (multi-clause defmacro and quasiquote desugaring)
- AST construction from expanded S-expressions
- Module-identity normalisation (super resolution, structural-declaration extraction)
- Synthetic-span allocation for macro-generated forms

**Out of scope.**
- Type inference (typecheck)
- Code generation (backend)
- Module loading orchestration (int)
- Spec definition (`/spec`)

**What crosses the boundary.**
- **Inputs**: source text.
- **Outputs**: AST values (expression trees, top-level forms, structural declarations) defined in `cranelisp-types`.
- **Window types**: none.

---

## 2. Typecheck — `crates/cranelisp-typecheck/`

**Bounded context.** Untyped AST becomes typed AST plus populated symbol tables. Typecheck infers types, resolves traits, classifies polymorphism, and analyses match exhaustiveness. Its results land in two places: directly on AST nodes (each node carries its inferred type and resolution choices), and in the per-module symbol-table view supplied by the caller. The crate carries no shared session state and no cadence; it is invoked synchronously, one form at a time, by the integration layer.

**In-scope.**
- Type inference (Hindley-Milner) over every AST variant
- Trait declaration, impl recording, method resolution
- Constrained-polymorphism detection and monomorphisation analysis
- ADT exhaustiveness checking
- Per-symbol callee extraction (writes into the symbol table for downstream scheduling)

**Out of scope.**
- AST construction (frontend)
- Code generation (backend)
- Pipeline scheduling, module loading, REPL session (int)
- Runtime helpers (runtime)

**What crosses the boundary.**
- **Inputs**: AST values; a symbol-table view supplied by the caller.
- **Outputs**: in-place AST annotations; symbol-table writes; transient warnings.
- **Window types**: typecheck consumes a symbol-table-view window passed by the caller; it exposes no windows of its own.

---

## 3. Backend — `crates/cranelisp-backend/`

**Bounded context.** Typed AST becomes executable code. The backend translates symbol-table entries into Cranelift IR and produces compilation artefacts: in-memory machine code for direct execution, object files for linking, and the cache pair (metadata + object) for re-use across sessions. There is one compilation entry point regardless of mode; mode (in-memory vs object) is a property of the Cranelift module supplied by the caller, not a parameter on the entry point. The crate has no cadence; multiple compilations may run concurrently with disjoint inputs.

**In-scope.**
- IR emission for every spec-defined construct
- RC discipline at the call boundary (callee owns its heap parameters)
- In-memory artefact production with reclaim on drop
- Object-file production
- Cache read and write
- Per-module link binding for cross-module call indirection

**Out of scope.**
- Type inference (typecheck)
- Macro expansion (frontend)
- Pipeline scheduling (int)
- Runtime helpers (runtime — backend declares them as imports)

**What crosses the boundary.**
- **Inputs**: a symbol-table view; a Cranelift module to emit into.
- **Outputs**: a per-batch artefact carrying a retention root for the produced code plus per-symbol code addresses (for the integration layer to wrap in its concrete code carrier); for object mode, the object artefact and the cache pair.
- **Window types**: none.

---

## 4. Runtime — `crates/cranelisp-runtime/`

**Bounded context.** What a running cranelisp program needs to execute. The runtime is the C-ABI surface JIT-emitted code calls into: heap allocation, reference counting, drop glue, string and vector primitives, the IO trampoline, fork-join evaluation cells. It has no knowledge of compilation, scheduling, REPL, or development tooling. Its job is to provide the language's runtime semantics in a way that depends only on the running program — not on how that program was loaded, who is observing it, or what process structure surrounds it. Diagnostic and observability surfaces are explicitly out: those are development concerns, not part of running a program.

**Internal cadence.** Runtime hosts the **runtime cadence** — atomic RC operations interleaved with normal execution; fork-join scopes during parallel evaluation. This cadence is invisible outside the running program; it produces no handoffs to compilation or REPL.

**In-scope.**
- Heap memory model (allocation, layout)
- Reference counting primitives
- Drop glue helpers
- String and vector runtime
- IO trampoline
- Fork-join evaluation cells
- Marshal between language Sexp values and host Rust values
- Panic intrinsic for match exhaustiveness failure

**Out of scope.**
- Code generation (backend)
- Diagnostics, tracing, observability (int — development concerns) — per Decision 40, the historical `trace.rs` and `io_trace.rs` modules relocate from runtime to int via an `IoObserver` callback contract; this BC entry is reaffirmed by the relocation, not revised by it. Runtime keeps only a ~50-line extension-point API parallel to `register_alloc_callback`.
- Platform DLL loading and lifecycle (int)
- Pipeline state (int)

**What crosses the boundary.**
- **Outward**: an `extern "C"` symbol surface plus a small set of host-callback structures used for inversions of control (e.g., when platform DLLs need runtime services).
- **Inward**: layout constants from `cranelisp-types`; nothing else.
- **Window types**: write-once evaluation cells held by the runtime cadence. The C-ABI surface itself is value-passing — heap pointers cross as integers, opaque to the consumer.

---

## 5. Platform — `crates/cranelisp-platform/`

**Bounded context.** The shared interface contract between the cranelisp host binary and platform DLLs. Both the host and every platform DLL link against this crate; that is its purpose. It defines the C-ABI types, the wrappers that present those types safely in Rust, the layout constants both sides must agree on, and the macro DLLs use to publish their manifests. The crate owns no runtime state and no cadence.

**In-scope.**
- C-ABI contract types (platform manifest, function descriptor, host-callback table)
- Safe wrappers over the C-ABI representation
- Layout constants shared between host and DLL
- The DLL manifest macro
- Host-side conversion of manifests into safe Rust descriptors

**Out of scope.**
- DLL session lifecycle and retention (int)
- IO trampoline implementation (runtime)
- Per-DLL platform implementations (separate downstream crates)
- Spec definition of IO semantics (`/spec`)

**What crosses the boundary.**
- **Outward**: the C-ABI types, wrappers, constants, and macro to both host and DLL consumers.
- **Inward**: a small set of layout types from `cranelisp-types`.
- **Window types**: none.

---

## 6. Binary / int — `src/` + `crates/cranelisp-exe-bundle/`

**Bounded context.** The integration layer wires the other surfaces into a deployable artefact and into a working REPL. It hosts three internal cadences with distinct execution shapes — compilation, REPL, watcher — coordinates the typed handoffs between them, owns all development tooling (slash commands, tracing, observability, introspection), and is the only crate that knows the concrete carrier of compiled code. The two crate paths (`src/` and `cranelisp-exe-bundle`) are one surface for triad purposes: a change touching both is one design/development/review cycle.

### 6.1 Internal cadences

**Compilation cadence.** Workers consume work packets off internal queues. Each worker claims a packet, processes it, publishes results into compilation-cadence windows, and notifies the scheduler. Closed-loop within the compilation subsystem; no external clock.

**REPL cadence.** Turn-based, synchronous to user input. One prompt → one parse → one submission to the compilation cadence → wait for result → display. Owns input handling, slash-command dispatch, prompt formatting, display, and the diagnostic surface (tracing, observability, introspection). Does not own compilation state — interacts with compilation only through handoffs.

**Watcher cadence.** OS file-change notifications arrive on a callback thread; the watcher captures them. The cadence is open-loop — its timing is dictated by the operating system. Captured changes do not act directly on compilation; they cross to the REPL cadence at a poll point and from there to the compilation cadence as re-register requests.

### 6.2 Inter-cadence handoffs

Handoffs are how cadences communicate. The pattern matters; the int facade pins the typed objects. Three patterns suffice:

- **REPL → compilation**: the REPL submits work (an evaluation, a module load) and waits. Compilation signals when ready.
- **Compilation → REPL**: each evaluation completes with either a displayable result or an error. The REPL formats and prints.
- **Watcher → REPL → compilation**: file-change events do not flow directly into compilation. They are polled by the REPL at prompt boundaries (avoiding mid-input interleave) and become re-register requests.

The runtime cadence (inside running programs) produces no handoffs to other cadences.

### 6.3 Within-cadence access

Each cadence accesses shared state only through typed handles owned by the cadence-relevant subsystem. There is no ambient session-state god-handle that any consumer can reach into; the access primitive is the window, and the windows are partitioned along cadence lines so that REPL state, compilation state, and watcher state cannot cross-contaminate. The int facade enumerates the windows; this document fixes the partitioning principle.

### In-scope

- The three cadences and their handoffs
- The compiler-shared state (symbol tables, code-pointer carriers, retention roots) decomposed into cadence-scoped windows
- Scheduler and worker subsystem (one ownership boundary, both priority and background work)
- REPL session, slash-command dispatch, prompt formatting, display
- Development tooling: tracing, observability, introspection
- Module loading orchestration; cache writer; save/regenerate
- File watcher
- DLL session lifecycle (handles retained for the session)
- The integration-layer concrete code carrier (the only crate that names it)
- CLI argument parsing
- Exe-bundle: link-target re-exports and the standalone-binary startup stub

### Out of scope

- Source parsing (frontend)
- Type inference (typecheck)
- Code emission (backend)
- Runtime helpers (runtime)
- Platform ABI contract (platform)

### What crosses the boundary

- **Inward**: the public surfaces of all five other crates.
- **Outward**: nothing for other crates — the integration layer is the application root. The exe-bundle exposes a startup stub used only by the system linker.
- **Window types**: cadence-scoped. Not exposed to other crates.

### Known architectural constraints

- **Mutual-import deadlock**: two modules that import from each other deadlock the scheduler under the current scheduling strategy. A test-scaffolding workaround exists for the common case; lifting the constraint is module-system work and is out-of-scope here.

---

## 7. Cross-crate types — `crates/cranelisp-types/`

**Bounded context.** The single home for everything that crosses crate boundaries. The crate is *data and contract*: data types that flow by ownership across the workspace, and trait contracts that downstream crates implement to participate in cross-crate generic shapes. It depends on nothing within the workspace, and nothing outside is allowed to invert that direction. The crate is `/arch`'s own; consumers file `target: /arch` to add or change shapes.

**In-scope (catalog by family).**
- AST: expression trees, top-level forms, definitions, patterns, type expressions, trait declarations and impls, visibility
- Types: type representation, schemes, substitutions, identifiers
- Sexp: the s-expression value type and its marshal tag constants
- Symbol table: per-module symbol tables (generic over per-symbol code carrier and per-module link carrier), entry variants, definition kinds, primitive classifications, structural declarations, import/export specifications, macro clause information
- Heap layout: header type, heap classification
- GOT runtime memory: per-module code-pointer table
- Operator catalog: descriptor type and registry for the named primitive functions the language exposes
- Marshal: tag constants
- Scheduling: scheduling-class enum
- Identifier newtypes: symbols, type names, trait names, module names, fully-qualified variants
- Span and error: source spans, error and warning types
- Constants: shared sizes and thresholds

**Trait contracts (marker traits for cross-crate windows).** The crate hosts empty marker traits that downstream crates implement to supply concrete types where the boundary is generic. Concrete window types live in the owning crate, not here, so this crate stays ignorant of backend and runtime concrete state.

**Out of scope.**
- Anything that would invert the dependency graph (Cranelift types, JIT/linker types, the integration-layer code carrier)
- Pipeline orchestration (int)
- Runtime intrinsics (runtime)
- Per-form transient typecheck-internal state

**What crosses the boundary.**
- Every type in this crate is a boundary type by definition. The crate IS its surface.

---

## Cross-references

- `principles.md` — architectural principles
- `facades/{crate}.md` — per-surface facade specs (as-designed public surface)
- `interfaces.md` — narrative companion to `crates/cranelisp-types/`
- `spec/` — language definition
