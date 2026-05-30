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
- **Inputs**: source text; the session-level `SymbolTables<C, L>` + `ModuleAliases` for macro lookup (read-only — see invariant 6).
- **Outputs**: AST values (expression trees, top-level forms, structural declarations) defined in `cranelisp-types`; per-form `ParsedEntry` transients; `ExtractedDeclarations` bundles; `Sexp` values from macro expansion.
- **Window types**: none.

**Public surface (canonical enumeration).** The crate-root rustdoc (`crates/cranelisp-frontend/src/lib.rs` //! preamble) is the single source of truth for the frontend's as-designed public boundary; `crates/cranelisp-frontend/public-api.txt` is the authoritative as-built enumeration, gated at PR time per the baseline-diff discipline (see `design/arch/CLAUDE.md` §"Baseline-diff discipline"). Per-item rustdoc on each public item (`pub fn expand`, `pub fn parse`, `pub struct ExtractedDeclarations`, `pub enum ExpansionError`, etc.) carries the per-item contract — visit them with `cargo doc -p cranelisp-frontend --no-deps`.

The four free-function form-by-form boundary — `parse`, `extract_module_declarations`, `build_form`, `build_expr`, plus `expand` for macro expansion — is the operative public-API summary; see the lib.rs preamble §"Public surface — the form-by-form boundary" for signatures and the rationale for the shape (per-form, no AST union enum).

**Bounded-context invariants.** These hold across sprints — the contract `cranelisp-frontend` makes with the rest of the workspace:

1. **No type inference.** Types in the frontend are `TypeExpr` (syntactic), not `Type` (resolved). Type resolution is `cranelisp-typecheck`'s job. The frontend never names `Type`, `Scheme`, or `TypeId`.
2. **No code generation.** Macro bodies are AST nodes that `int` compiles via the backend; the frontend never invokes Cranelift and never names `cranelisp-backend`, `cranelisp-primitives`, or `cranelisp-intrinsics`.
3. **`super` resolved at frontend.** Per `design/arch/super-import-arbitration.md`: `ImportSpec.module_path` NEVER contains the literal `"super"` past `parse` (specifically past `parse_import_sexp`). All `super`-resolution happens at parse time against the parsing module's own path.
4. **Synthetic spans are unique.** `next_synthetic_span` issues monotonically increasing spans for compiler-generated forms. No two synthetic spans collide within a session.
5. **`expand` is re-entrant.** May invoke registered macros which may themselves expand further. Whether the implementation imposes a defensive depth limit (and what value) is the implementing crate's call — not a BC concern; the published `EXPANSION_DEPTH_LIMIT` is an operational safeguard, not a contract.
6. **`expand` is side-effect-free for dependency resolution.** When an FQ ref's target isn't ready, expand returns `Err(ExpansionError::Gap(ResolutionGap::MacroInMem(fq)))` — never calls the scheduler, never registers modules, never blocks. The frontend has no `Sess` / `CompileScheduler` dependency (Principle 3). The orchestrator (`int::process_form`) handles dispatch + retry.
7. **`#[non_exhaustive]` DTOs include all error types.** `ExpansionError` is `#[non_exhaustive]` so adding new gap kinds or genuine error variants is non-breaking.
8. **Form-by-form, not pre-pass.** Per FIXME `sprints/fixmes/0005-spec-macro-availability-form-by-form.md`: there is NO defmacro pre-pass extraction. Each form is processed in source order; macros become available to subsequent forms only after their `defmacro` form is itself processed. The "module-wide availability" model in `spec/09-macros.md` §9.3.4 is to be revised — until then, the frontend does not implement it.

**FIXME 0175 — marshal-deps gap on `expand` invocation.** The `expand` function performs the structural traversal (children recursion, macro-head detection, depth-limit enforcement, quasiquote expansion) but does NOT call into the JIT'd macro body — it returns `Err(ExpansionError::Gap(ResolutionGap::MacroInMem(fq)))` for every macro head encountered. The live invocation path remains in `src/expander.rs` until `/arch` resolves FIXME 0175 (`design/arch/fixmes/0175-arch-frontend-expand-invocation-gap.md`): `cranelisp_runtime::heap_alloc` + signal handling cannot be reached from `cranelisp-frontend` under the current BC §1 dep-allowance, and the target invocation requires them. Likely resolution: a new `cranelisp-marshal` crate. When resolved, `expand` gains the body call and the `src/expander.rs` implementation deletes; the signature and uniform-Gap contract above stand and need no revision.

**Relationship to consumer crates.** Frontend's outputs are consumed by `cranelisp-typecheck` (`ParsedEntry` vectors fed into `check_forms` — see §2 + Decision 44) and by the integration layer (`src/cluster.rs::process_cluster` consumes per-clause `Defn`s built via `synthesize_macro_clause_defn` per Decision 21). Macro-resolver helpers (`parse_defmacro`, `synthesize_macro_clause_defn`, et al.) are pub-at-root for these two consumers and narrow back at FIXME 0098 Phase 2 close; the quasiquote helpers (`expand_quasiquotes`, `expand_quote_template`, `next_synthetic_span`) remain pub at root as the standing public quasiquote API used by user-authored macros and REPL `/expand`. See the lib.rs preamble §"Macro-resolver helpers — internal-but-exposed" for the disposition history.

**Per-surface documentation.** Like `cranelisp-types` (§7), this surface has no separate `facades/frontend.md` document — the source-side rustdoc (crate-root `//!` narrative in `crates/cranelisp-frontend/src/lib.rs` plus per-item `///` comments) IS the facade. Retired in S70 Phase B group B3-C following the S69 Sub 42 precedent per Principle 7 (single source of truth) and lived-experience cost of dual-maintenance. The `public-api.txt` baseline gates the surface at PR time; rustdoc-coverage is the source-side equivalent of the per-crate facade-compliance test for the other crates.

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
- Runtime helpers (intrinsics — §4b)

**What crosses the boundary.**
- **Inputs**: AST values; a symbol-table view supplied by the caller.
- **Outputs**: in-place AST annotations; symbol-table writes; transient warnings.
- **Window types**: typecheck consumes a symbol-table-view window passed by the caller; it exposes no windows of its own.

**Module-locality invariant.** Typecheck never iterates the universe of modules to resolve a name, type, or impl (Principle 17). Cross-module access happens via fully-qualified references (one named module) or via per-symbol point-to-point chain-follow along `ModuleEntry::Import` bindings back to the symbol's defining module (no closure walk, no cycle detection). `Import` covers both private (`(import …)`-form) and public (`(export [foreign-sym])`-form, formerly `Reexport`) edges — visibility is a per-entry orthogonal axis (`visibility: Visibility` on every variant), not a separate variant (see `bounded-contexts.md` §7 "Visibility is per-entry" + "Two complementary stores, two purposes"). Chain-follow walks `Import` edges regardless of visibility. `ModuleEntry::TraitImpl` is written to the **trait's defining module** per Decision 0045; importers discover impls by chain-following the trait reference back to its home module and probing for `impl$FQTypeName$FQTraitName`. This invariant is the structural prerequisite for Decision 44's cluster-atomic two-pass shape; see `facades/typecheck.md` invariant 10 for the access-pattern shapes.

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
- Runtime helpers (intrinsics — backend declares them as imports; §4b) and user-callable primitives (primitives — §4a)

**What crosses the boundary.**
- **Inputs**: a symbol-table view; a Cranelift module to emit into.
- **Outputs**: for JIT mode (per Decision 41 per-symbol cardinality — typecheck cluster commit followed by N parallel backend workers, each calling `compile_to_module` for one assigned symbol), direct writes via `SymbolTable::write_code` + per-symbol GOT-slot population plus a value-returned `CompilationArtifacts` carrying the always-created introspection contributions (`clif_ir`, `code_size`, `compile_duration`) for the caller to retain or drop; on-demand disassembly via the separate `produce_disasm(fq, symbol_tables)` free function (per the S70 Phase B amendment to D41 — backend does not name the integration-layer `Introspection` type at its boundary; the value-returned artefact replaces what would have been a third direct-write that inverted the DAG). For object mode (per-module), the object artefact and the cache pair.
- **Window types**: none.

---

## 4a. Primitives — `crates/cranelisp-primitives/`

**Bounded context.** Spec-defined operations callable from user code via the `primitives/<name>` module path. Primitives are language-level: they appear in the symbol table, they have GOT slots, they are addressable as values (`(let [f +] (f 1 2))` reads a fn pointer from the GOT slot and indirect-calls it). Backend MAY substitute inline CLIF at known direct call sites via a name-keyed substitution table; the named fn pointer is a legitimate fallback for indirect call sites. The crate has no trait knowledge; trait dispatch resolves at typecheck/stdlib level, and the resolved target — an impl body — calls primitives by name. Per Decision 43 the previous combined `cranelisp-runtime` BC retires; this section and §4b replace it.

**Internal cadence.** None. The crate is a leaf — extern fns called from JIT-emitted code or from user code via GOT-indirect call. No state machine; no scheduling.

**In-scope.**
- Integer / float / bool primitive operations (arithmetic, comparison, logical)
- Primitive type conversions (`int_to_string`, `parse_int`, `float_to_string`, `bool_to_string`, …)
- The named `extern "C"` form is *the* addressable backing for each primitive; no `cranelisp_op_*` parallel form (per Decision 43's Phase 4 deletion)

**Out of scope.**
- Code generation (backend)
- Backend-emitted-call targets (intrinsics — §4b)
- Trait dispatch knowledge (typecheck + stdlib)
- Symbol-table seeding logic (int — int reads `cranelisp-types::primitives()` at session init)

**What crosses the boundary.**
- **Outward**: an `extern "C"` symbol surface — primitives by their kebab-case symbol name.
- **Inward**: identifier newtypes from `cranelisp-types` (for the seeding helper); nothing else from the workspace.
- **Window types**: none.

**Evolution driver.** Spec-driven — new primitives appear when the spec requires them.

---

## 4b. Intrinsics — `crates/cranelisp-intrinsics/`

**Bounded context.** Backend-emitted-call targets — runtime support code with stable ABI contracts called by JIT-emitted code or by the IO trampoline. Intrinsics are NOT callable from user code; not in any symbol table; not in any GOT. The ABI is tightly coupled to backend's codegen choices. The crate has no knowledge of compilation, scheduling, REPL, or development tooling; its job is to provide the language's runtime semantics in a way that depends only on the running program — not on how that program was loaded, who is observing it, or what process structure surrounds it. Diagnostic and observability surfaces are explicitly out: those are development concerns, not part of running a program. Per Decision 43 the previous combined `cranelisp-runtime` BC retires; this section and §4a replace it.

**Internal cadence.** Intrinsics hosts the **runtime cadence** — atomic RC operations interleaved with normal execution; fork-join scopes during parallel evaluation. This cadence is invisible outside the running program; it produces no handoffs to compilation or REPL.

**In-scope.**
- Heap memory model (allocation, layout — base-pointer convention per Decision 11)
- Reference counting primitives
- Drop glue helpers (consume_shallow, consume_io_tree, dec_shallow_io)
- String and vector runtime
- IO trampoline
- Fork-join evaluation cells (IVar)
- Marshal between language Sexp values and host Rust values
- Panic intrinsic for match exhaustiveness failure
- IO observer registration API (per Decision 40 — the registration site lives here; observer state lives in int)

**Out of scope.**
- Code generation (backend)
- User-callable primitives (primitives — §4a)
- Diagnostics, tracing, observability state (int — development concerns) — per Decision 40, the historical `trace.rs` and `io_trace.rs` modules relocate from runtime/intrinsics to int via the `IoObserver` callback contract. Intrinsics keeps only a ~50-line extension-point API parallel to `register_alloc_callback`.
- Platform DLL loading and lifecycle (int)
- Pipeline state (int)

**What crosses the boundary.**
- **Outward**: an `extern "C"` symbol surface plus a small set of host-callback structures used for inversions of control (e.g., when platform DLLs need runtime services); plus the `IoObserver` registration API.
- **Inward**: layout constants and identifier newtypes from `cranelisp-types`; the `IO_TAG_*` consts and `HostContext` from `cranelisp-platform` (consumed by the IO trampoline).
- **Window types**: write-once evaluation cells (IVar) held by the runtime cadence. The C-ABI surface itself is value-passing — heap pointers cross as integers, opaque to the consumer.

**Evolution driver.** Backend-driven — new intrinsics appear when backend codegen needs them; existing intrinsics evolve in lock-step with backend's emitted-call shapes.

**Cross-crate dependency edges (post-D43).** Backend depends on `cranelisp-primitives` (for symbol-table seeding via `cranelisp-types::primitives()`) AND on `cranelisp-intrinsics` (for emitted-symbol declarations); backend does NOT depend on the retired `cranelisp-runtime`. `int` depends on both — primitives for seeding, intrinsics for JIT registration of fn ptrs and for the trace/io_trace consumer side post-FIXME 0103.

---

## 5. Platform — `crates/cranelisp-platform/`

**Bounded context.** The shared interface contract between the cranelisp host binary and platform DLLs. Both the host and every platform DLL link against this crate; that is its purpose. It defines the C-ABI types, the wrappers that present those types safely in Rust, the layout constants both sides must agree on, and the macro DLLs use to publish their manifests. The crate owns no runtime state and no cadence.

**External audience — Principle 15 exception.** `cranelisp-platform` is the only implementation crate with an explicitly external audience: out-of-tree DLL authors (`cranelisp-stdio`, `cranelisp-fs`, etc.) depend only on this crate and would not otherwise see `cranelisp-types`. Per Principle 15's external-audience exception, the facade lives with the source rustdoc — Sprint 71 retired the standalone `design/arch/facades/platform.md` and folded its narrative into the crate-root `//!` preamble + per-item `///` docs (3rd data point of the facade-retirement pattern after `types.md` S69 + `frontend.md` S70). Audit F9 (S69) verified the exception's scope health: `SchedulingClass` and `PlatformError` are the only re-exports, both grounded in named multi-consumer + external-audience criteria.

**In-scope.**
- C-ABI contract types (`PlatformManifest`, `PlatformFn`, `HostCallbacks`) — all `#[repr(C)]`, layout-governed by `ABI_VERSION` per Principle 14
- Safe wrappers over the C-ABI representation (`CLInt`/`CLBool`/`CLFloat`/`CLString`/`CLIO`/`CLAdt`/`CLOwned`) — all `#[repr(transparent)]` over `i64`
- Layout constants shared between host and DLL (`ABI_VERSION`, `HEAP_HEADER_SIZE`, `STRING_HEADER_BYTES`, `IO_TAG_*`, `IO_EFFECT_RESOURCE_OFFSET`)
- The DLL manifest macro (`declare_platform!`) — the DLL-author entry point
- Host-side conversion of manifests into safe Rust descriptors (`manifest_to_descriptors`, `OwnedPlatformFnDescriptor`)
- Schema parser + marker-type pattern (Sprint 71) — `Schema`, `SchemaParseError`, `CLAdtType`, `AnyAdt`, `GetSchema`; the `declare_platform!` `schema:` arm auto-emits one marker type per declared ADT plus a `LazyLock<Schema>` static parsed once per DLL

**Out of scope.**
- DLL session lifecycle and retention (int — see §6)
- IO trampoline implementation (intrinsics — §4b)
- Per-DLL platform implementations (separate downstream crates)
- Spec definition of IO semantics (`/spec`)
- Type-signature parsing (`int`-side because it requires `cranelisp-typecheck` vocabulary that platform must not depend on per Principle 3 + FIXME 0155)
- Sig grammar routed through frontend+typecheck — Sprint 71 deferred; tracked by FIXMEs 0230 + 0231 + 0233
- Platform-as-module registration (each loaded platform getting its own `SymbolTable`+`GotTable`) — Sprint 71 deferred; tracked by FIXME 0233
- `.meta.json` schema for platform symbol-table caching — Sprint 71 deferred; tracked by FIXME 0232
- `/abi <TypeName>` REPL command — Sprint 71 deferred; tracked by FIXME 0234

**What crosses the boundary.**
- **Outward**: the C-ABI types, wrappers, constants, and macro to both host and DLL consumers.
- **Inward**: a small set of layout types from `cranelisp-types` — `SchedulingClass`, `PlatformError`, `Symbol`, `Span`, `ErrorLocation`, `HeapHeader`.
- **Window types**: none.

### Cross-cutting RC discipline

All heap CL types (`CLString`, `CLAdt<T>`, `CLIO<T>`) store **alloc base pointers** (the address of the `[total_size: i64][rc: i64][...]` heap allocation), NOT payload pointers. This matches the compiler's convention (Decision 0013); JIT-emitted code, the `CLString::from(&str)` builder, and the `CLAdt::from_raw` constructor all agree on what an `i64` "heap reference" means. `inc_rc` / `dec_rc` (per `CLHeap`; method-name asymmetry preserved per audit F5 R3) use `Ordering::SeqCst` to match Cranelift's `atomic_rmw` semantics — `Relaxed` is unsound for both directions (allows reordering relative to field reads, producing potential read-after-free).

`CLOwned<T>` is the host-side RAII wrapper for cross-callback RC discipline; the consuming variant `CLHeap::into_owned_consuming` is the consuming calling convention per Decision 0024 (used by platform externs that capture a heap parameter into an Effect closure — see `design/backend/ring2-rc.md` §10.4).

### Schema mechanism + marker-type pattern (Sprint 71 — layer 1)

`declare_platform!`'s optional `schema:` arm accepts a cranelisp-S-expression literal declaring ADT shapes. The macro auto-emits one zero-sized marker type per declared type (implementing `CLAdtType` with `const TYPE_NAME: &'static str = "..."`) plus a `LazyLock<Schema>` static parsed once at first access. DLL function signatures use `CLAdt<MarkerType>` for typed parameters; field access is `r.read_field::<CLInt>("w")` — the type-name comes from the marker via `T::TYPE_NAME`.

Layer 1 (the current sprint's scope) settles the schema format, marker-type pattern, `Schema` parser, `CLAdt<T>` wrapper, and the four field-access methods (`read_tag`, `read_field`, `own_field`, `construct`). **Layer 2** (deferred) is whatever ergonomic surface DLL authors get on top of layer 1 — a typed-newtype proc-macro generator, a `match-on-tag` macro, or stay-with-layer-1 if measurement shows the verbosity is acceptable. All three layer-2 options consume the same layer-1 schema this sprint settles.

### ABI versioning rationale

`ABI_VERSION: u32` is the single layout-discipline gate between host and DLL (Principle 14). Any layout-affecting change to a `#[repr(C)]` struct (`PlatformManifest`, `PlatformFn`, `HostCallbacks`) or a const the DLL reads by hard-coded offset (`HEAP_HEADER_SIZE`, `STRING_HEADER_BYTES`, `IO_TAG_*`, `IO_EFFECT_RESOURCE_OFFSET`, new `CL_TYPE_TAG_*` values) bumps the version. The host validates `abi_version` at DLL load and refuses mismatched DLLs with `PlatformError::AbiVersionMismatch`. Adding a method on `CLAdt` (no new `HostCallbacks` field, no new const) does NOT bump; adding a new pub `CL<T>` wrapper variant alone does NOT bump (Principle 14's `#[repr(transparent)]` exemption — the wrapper is a host-side typing convenience over an `i64`; the ABI is the `i64`). See `crates/cranelisp-platform/src/lib.rs` `ABI_VERSION` rustdoc for the full bump-rule enumeration.

Sprint 71 bumped `ABI_VERSION` from 1 to 2: `HostCallbacks` grew by `alloc_with_tag` + `validate_schema` for the ADT-marshaling surface.

### Future host-wiring story (forward-looking commitment)

Sprint 71 lands the platform-side API but defers the host-side wiring of `alloc_with_tag` / `validate_schema` callbacks. `HostCallbacks` is initialised with the in-crate **named-null callbacks** (`null_alloc_with_tag` panics with FIXME 0229 message; `null_validate_schema` returns 0). The construction path (`CLAdt::construct`) gates on the alloc callback via R1 wired-or-panic; read paths are callback-free (DLL-local schema lookup + transmute) and fully functional.

The host-wiring sprint (tracked as **FIXMEs 0229–0235**) lands:

- **0229** (`/int`) — populate `alloc_with_tag` + `validate_schema` callbacks; removes the R1 named-null-callback gates
- **0230** (`/frontend`) — expose `parse_type_expr` as a named API for platform sig parsing
- **0231** (`/typecheck`) — sig typechecking entry point against the importing platform's resolution context
- **0232** (`/backend`) — `.meta.json` schema extensions for platform module symbol-table caching
- **0233** (`/int`) — replace `parse_type_sig` with the frontend+typecheck path; register platforms as normal modules with their own `SymbolTable` + `GotTable`
- **0234** (`/repl`) — `/abi <TypeName>` emitter implementation against the schema DSL spec
- **0235** (`/qa`) — round-trip integration tests once host-side wiring lands

When `Fn a b` lands on the spec §10.10.1 platform-ABI permitted-types list (currently future work; not in this sprint's scope), `HostCallbacks` widens further with `rc_inc` / `rc_dec` / `invoke_closure` per Decision 0031's "Callback support (forward commitment)". The widening is a binary-incompatible ABI bump.

### Conformance triad coverage holes (audit C1–C5)

The S69 audit identified five conformance coverage holes the current triad (compile-time check + `cargo-public-api` baseline + facade compliance test) does not catch:

- **C1** — `CLHeap` method receiver/arity drift
- **C2** — `#[non_exhaustive]` annotation appearance/removal
- **C3** — `declare_platform!` macro arm drift (the F6 category, generalised; partially mitigated S71 Wave 2 by the new schema:-arm compile-fixture tests T17–T21)
- **C4** — `#[repr(C)]` struct field-order changes
- **C5** — `unsafe impl Send/Sync` removal on `PlatformFn` (the F3 category)

All five are tracked by FIXMEs 0224–0228 (`target: /qa`, deferred to a future conformance-triad-enhancement sprint).

### Bounded-context invariants

These hold across sprints — the contract `cranelisp-platform` makes with the rest of the workspace:

1. **Platform fn pointers live in `SymbolTable.got()`, indexed by `ModuleEntry::Def.got_slot`** (Decision 0026, S66 amendment + rollback `1dc57ae` — GOT is the single source of truth for callable addresses). Per spec §8.9.3, `(platform <name>)` registers a synthetic module at `symbol_tables["platform.<name>"]`; per-fn `ModuleEntry::Def` entries (with `kind: Primitive { primitive_kind: PlatformEffect { … } }` distinguishing the platform origin) live in that synthetic module's `symbols`. The DLL handle is the lifecycle owner, retained on the platform module's own `SymbolTable.dll: Option<D>` field (per `crates/cranelisp-types/src/module.rs` `SymbolTable` rustdoc — `D: DllStore` generic). Drop semantics: dropping the platform module's SymbolTable drops the DLL. `scheduling_class` lives inside `PrimitiveKind::PlatformEffect { scheduling_class }` — ill-formed states unrepresentable.

2. **Stable C ABI at the DLL boundary.** `PlatformManifest`, `PlatformFn`, `HostCallbacks` are `#[repr(C)]`. Layout changes require an `ABI_VERSION` bump. `load_manifest` (int-side) validates the version on load and refuses mismatched DLLs with `PlatformError::AbiVersionMismatch`.

3. **Heap closures via GOT, not raw code pointers (Decision 0031 callback support — forward commitment).** When `Fn a b` is added to spec §10.10.1 (currently future work), platform fn arguments of fn type will pass as the heap closure address (Decision 0011 layout: `[header | code_ptr | drop_glue_ptr | captures...]`), NOT raw code pointers. Platforms will invoke retained closures via `HostCallbacks::invoke_closure` which dispatches through the GOT — so REPL redefinition retargets future invocations transparently. Retention requires `rc_inc` on storage, `rc_dec` on release.

4. **Marshaling tags shared with intrinsics.** The `CLType` impls use the same `i64` layout the intrinsics helpers expect. `CLString.0` is an alloc-base pointer to an intrinsics-allocated `HeapString` (Decision 0012 — string layout owned by `cranelisp-intrinsics`; Decision 0043 — intrinsics is the post-runtime-split host); `CLOwned<CLString>` participates in RC via `HostCallbacks.alloc` and the intrinsics-side dec path. There is one `i64` representation per CLType, agreed between platform and intrinsics via this crate's documented layout.

5. **`HostContext` initialised once per session.** `int` constructs `HostCallbacks` (with fn pointers into `cranelisp_intrinsics`) at `CompilerSession::new` and calls `HostContext::init` exactly once. Subsequent platform fn calls see the same callbacks for the session's lifetime. `HostContext` is `Send + Sync` by auto-derivation (`AtomicPtr<HostCallbacks>` is `Send + Sync`); `HostCallbacks` auto-projects `!Send + !Sync` (extern "C" fn pointers + raw allocations); `OwnedPlatformFnDescriptor` auto-projects `!Send + !Sync` (raw `ptr: *const u8`); `PlatformFn` carries explicit `unsafe impl Send + Sync` because the IO trampoline reads descriptors from multiple threads when dispatching Effect nodes (safety justified by BC §5 invariant 6 — no DLL unloading mid-session).

6. **No DLL unloading mid-session.** Once a platform DLL is loaded via `load_manifest`, it stays loaded until session shutdown. This is what makes the per-symbol GOT-slot pointer valid for the session — DLL pages are not unmapped while symbols reference them. Bounded leaks in `declare_platform!`'s `Box::leak` for `jit_name` bytes + per-fn parallel-array allocations are bounded by this invariant.

7. **`scheduling_class` declared by the DLL, consumed by the IO trampoline.** Per Decision 0026 — the IO trampoline reads `scheduling_class` off the destructured `PrimitiveKind::PlatformEffect` variant when it dispatches an Effect, and uses it to decide whether to spawn the work on the IO thread pool, the CPU thread pool, etc. Platform authors choose the class statically per fn via the `scheduling:` arm of `declare_platform!`.

8. **FQTypeName migration: zero-hit (Decision 0047).** Per Decision 0047 + §7 ("FQTypeName binding"), `cranelisp-platform` has zero public-surface changes and zero in-crate hits under the FQTypeName binding migration. The platform-DLL ABI uses S-expression type-signature strings (`PlatformFn.type_sig`) rather than resolved-stage type identifiers; resolution happens int-side downstream of `manifest_to_descriptors`. Migration disposition: no-op.

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
- Runtime helpers (intrinsics — §4b) and user-callable primitives (primitives — §4a)
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

**Visibility is per-entry.** `Visibility` lives once, on the entry. Every `ModuleEntry` variant carries `visibility: Visibility`; there is no parallel exports-set sidecar (the prior `Reexport` variant retired — public re-export edges are `Import { source, visibility: Public }`). Cross-module slot lookups consult the per-entry visibility field directly. The visibility-bearing entry NEVER duplicates `visibility` inside an embedded payload: `ModuleEntry::Def` carries direct `visibility` (the outer `Defn` AST wrapper retired from the runtime model) and `ModuleEntry::TraitDecl` carries direct `visibility` + a slimmed `info: TraitDeclInfo` payload (S72 Phase B — the embedded AST `TraitDecl`'s own `visibility` was a duplicate and is no longer embedded). Same pattern at adjacent layers: `ModuleAliasEntry`, form-level `Defn` / `TraitDecl` (the frontend AST node, which keeps its own source-recorded `visibility`/`docstring`/`span`) / `ModDecl` / `ImportSpec` / `ExportSpec`.

**Docstring is a direct entry field.** Symmetric with visibility: every introspection-bearing `ModuleEntry` variant — `Def`, `SpecialForm`, `TypeDef`, `TraitDecl`, `IntrinsicType` — carries `docstring: Option<String>` as a **direct top-level field**, never nested in an embedded payload struct (single source of truth, Principle 7). S72 Phase B un-nested two cases: `TypeDef` (docstring moved out of `TypeDefInfo` — which now carries only structural metadata: name, type-param binders, constructor names) and `TraitDecl` (docstring moved out of the embedded AST `TraitDecl` — the entry carries `TraitDeclInfo` with only `name`/`type_params`/`methods`). `IntrinsicType` gained a direct `docstring` it previously lacked, so intrinsic scalar types (`Int`, `Bool`, `Float`, `String`) are introspectable like any other symbol. The slimmed `*Info` payloads parallel the `Def`-narrows-`Defn` precedent: the entry owns the canonical metadata; the payload carries only what the symbol table structurally needs.

**Two complementary stores, two purposes** — the form-record on `SymbolTable.{imports,exports}` is NOT the same thing as per-entry `visibility` on `ModuleEntry`:

- **`SymbolTable.imports: Vec<ImportSpec>` and `SymbolTable.exports: Vec<ExportSpec>`** are **form-records**: append-only, source-order, only user-authored forms. They are the source-of-truth for `.cl` regeneration (`repl/spec.md` §15.4), duplicate-form warnings, and form-by-form parse-time classification. The form-record records *what the user wrote*.
- **Per-entry `visibility: Visibility` on `ModuleEntry`** is the source-of-truth for visibility decisions: used by cross-module resolution's visibility-filter step and by the `/exports M` REPL command. Per-entry visibility records *the effect on each symbol* — one symbol per `ModuleEntry` slot, with its own visibility.

Both are load-bearing; neither retires the other. A `(export [a b c])` form persists one `ExportSpec` row in the form-record and toggles `visibility = Public` on the three corresponding `ModuleEntry` slots; a `(import …)` form similarly persists an `ImportSpec` row and installs per-entry `Import { visibility: Private, .. }` bindings. The two stores stay structurally consistent by parse-time installer convention.

**Module aliases live at session level**, not on `SymbolTable`. `SymbolTable` holds a single per-key store — `symbols: DashMap<Symbol, ModuleEntry<C>>` for value/type/trait bindings. The module-path-namespace aliases introduced by spec §8.3.4 (import alias) and §8.4.4 (export mount) live in a **parallel session-level table** `ModuleAliases = DashMap<ModuleFullPath, ModuleAliasEntry>`, keyed by the alias's **full path**. Aliases are not symbols (they name parts of a module path, not value bindings); keying by full path lets §8.6.6 qualified-name resolution do a single-table longest-prefix-match against the queried `module_path` rather than segmenting and walking per-module alias sub-tables. The owning module of any alias entry is **derived from the key** (strip the last dot-separated segment, e.g., key `m.n.str` → owner `m.n`); it is not stored on `ModuleAliasEntry`. Three keying domains — `ModuleFullPath` (module / alias path), `Symbol` (in-module binding), `TypeName` (receiver-pinned ADT lookup) — three newtypes, no conflation.

**Per-namespace insertion-time conflict enforcement** (spec §8.6.4). Three conflict cases — two within-table, one cross-table:

- **Rename collision** (within `SymbolTable.symbols`) — two import/export entries producing the same local `Symbol` collide on insertion; structurally detected by a second `symbols.insert(sym, …)` for an already-occupied key.
- **Mount collision** (within session-level `ModuleAliases`) — two mounts at the same alias **inside the same owner module** collide; different owner modules mounting the same local alias name land at different `ModuleFullPath` keys and do not collide.
- **Mount-vs-submodule cross-namespace collision** (cross-table — `ModuleAliases` vs `SymbolTables`) — an alias path in `ModuleAliases` clashes with a real loaded module path in `SymbolTables`. NOT structural via the type system; the parse-time installer MUST perform an atomic cross-table check at insert time.

**Multi-legged authoring.** Some declarations author multiple `Def` entries from a single source form. The parent metadata `Def` carries the authored form (`sexp`, `source`); synthesized sub-entries derive from it. Pattern:

| Source form | Parent metadata `Def` | Synthesized sub-entries |
|---|---|---|
| `(defn name ([sig-1] body-1) ([sig-2] body-2))` (multi-sig) | `Def { kind: Overloaded { variants, sexp, source } }` | One `Def { kind: UserFn, ast, code }` per variant, mangled name (e.g., `add$Int+Int`) |
| `(defmacro name [pat-0] body-0 [pat-1] body-1)` | `Def { kind: Macro { clauses_meta, sexp, source } }` | One `Def { kind: UserFn, ast, code }` per clause body, mangled name `{name}$clause-{N}` |
| `(deftype (Name a) Ctor-0 Ctor-1)` | `Def { kind: TypeDef { … } }` | One `Def { kind: Constructor, ast, code }` per constructor (D49) |
| `(deftrait Name methods…)` | `Def { kind: Trait { … } }` | Methods stored per D45 (TraitImpl placement) |

The `sexp` + `source` fields live on the parent metadata `DefKind` variant, not on synthesized sub-entries. REPL `/source name` resolves through the parent metadata if a sub-entry is named (e.g., `/source thread-first$clause-0` resolves to the parent `thread-first`'s form). `ast` and `code` are sub-entry concerns — each clause body, constructor body, or multi-sig variant body has its own.

**Macros are Defs.** Macro clause bodies are stored as `Def { kind: UserFn { … } }` entries with mangled names `{macro-name}$clause-{N}`, dispatched via the normal GOT mechanism — uniform with multi-sig fn variants. Macro parent entries are `Def { kind: Macro { clauses_meta, sexp, source } }` carrying **metadata only**. Expansion-time dispatch walks `clauses_meta` to pattern-match the call sexp, then GOT-dispatches to the matched clause's mangled-variant Def. No sidecar `MacroEnv` table exists — clause-body lookup is the same GOT-dispatch path as any other callable.

**Trait-method addressing convention.** Trait methods are addressed by composite `Symbol` within the trait's defining module. For a trait method `Display.show` declared in module `core`: the canonical `ModuleEntry::Def` for the method lives in `core` keyed by `Symbol::from("Display.show")`. Per-method `ModuleEntry::Import` bindings injected by the prelude into user modules carry `source: FQSymbol { module: ModuleFullPath::from("core"), symbol: Symbol::from("Display.show") }`. Bare-name use sites (`(show 42)`) install the local Import binding under the bare `Symbol::from("show")`. The trait is **not** a distinct module namespace — `FQSymbol` remains two-component; any `FQSymbol` whose `symbol` field contains a `.` is a trait-method reference.

**TraitImpl storage.** Per Decision 0045, `(impl Trait Type method-defns…)` lands in the **trait's defining module** keyed by the synthetic name `impl$FQTypeName$FQTraitName`. Importers discover impls by chain-following the trait reference back to its defining module and probing for that synthetic key. No closure walk; no cycle detection; per-symbol point-to-point navigation only (Principle 17).

**FQTypeName binding** (Decision 0047). FQTypeName is binding as the cross-crate boundary type for resolved-stage type identifiers; two narrow exceptions — syntactic-lift sites (`check_form` resolving `TypeRef` → `FQTypeName`) and receiver-pinned helpers (e.g., `SymbolTable::get_type(name: &TypeName)` where `&self` IS the module context). Syntactic-stage qualification is captured structurally by `TraitRef` and `TypeRef` (both carrying `Option<ModuleFullPath>`) rather than letting a "bare name slip through" the AST.

**Field-level access on state types is discouraged outside the types crate.** State types (`ModuleEntry`, `DefKind`, `SymbolTable`) expose method-level accessors as their public contract — e.g., `ModuleEntry::arity()` (delegating to `Type::fn_arity()` on `scheme.ty`), `SymbolTable::get` / `get_type` / `defined_symbols` / `public_symbols`. Direct field access remains permitted on **data-record DTOs** (`NamedImport`, `ImportSpec`, `ExportSpec`, `ModDecl`, `PlatformSpec`, `Span`, `FQSymbol`, `FQTypeName`, `FQTraitName`, `TypeDefInfo`, `TraitDeclInfo`, `MethodResolutions`) where the field set IS the contract and serde round-trips structurally.

**Trait contracts (marker traits for cross-crate windows).** The crate hosts empty marker traits that downstream crates implement to supply concrete types where the boundary is generic. Concrete window types live in the owning crate, not here, so this crate stays ignorant of backend and runtime concrete state.

**Out of scope.**
- Anything that would invert the dependency graph (Cranelift types, JIT/linker types, the integration-layer code carrier)
- Pipeline orchestration (int)
- Runtime intrinsics (intrinsics — §4b)
- Per-form transient typecheck-internal state

**What crosses the boundary.**
- Every type in this crate is a boundary type by definition. The crate IS its surface. The full enumeration is at `crates/cranelisp-types/public-api.txt` (auto-generated by `cargo public-api`); per-item rustdoc lives on the items themselves and can be browsed via `cargo doc -p cranelisp-types --no-deps`.

**Per-surface documentation.** Unlike the other crate-shaped surfaces, `cranelisp-types` has no separate `facades/types.md` document — the source-side rustdoc (crate-root `//!` narrative in `crates/cranelisp-types/src/lib.rs` plus per-item `///` comments) IS the facade. Decision retired the facade as a permanent record in S69 Submission 42 per Principle 7 (single source of truth) and lived-experience cost of dual-maintenance. The `public-api.txt` baseline gates the surface at PR time per the baseline-diff discipline (see `design/arch/CLAUDE.md` §"Baseline-diff discipline"); rustdoc-coverage is the source-side equivalent of the per-crate facade-compliance test for the other crates.

---

## Cross-references

- `principles.md` — architectural principles
- `facades/{crate}.md` — per-surface facade specs (as-designed public surface)
- `interfaces.md` — narrative companion to `crates/cranelisp-types/`
- `spec/` — language definition
