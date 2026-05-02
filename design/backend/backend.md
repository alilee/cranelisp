# Backend — Master Design

> **Owner**: `/design` (this file). Per-crate code conventions live in `crates/cranelisp-backend/CLAUDE.md` (`/dev`-narrow). Cross-crate facade is `design/arch/facades/backend.md` (`/arch`-owned). Bounded context is `design/arch/bounded-contexts.md` §3.
>
> **Scope of this doc**. Master design intent for `crates/cranelisp-backend/`: how the crate fulfills the bounded context against the as-designed facade — internal architecture, quality attributes, concurrency, cache + linker, decision register, pointers to subordinate topic docs. This doc does NOT re-derive the public surface (cite `facades/backend.md`) or the bounded-context full statement (cite `bounded-contexts.md` §3).
>
> **Status (refresh)**. Refreshed against the canonical contract — `bounded-contexts.md` §3 + `facades/backend.md` + Decisions 22–42. The facade is **target-stating**: it specifies the as-designed shape, not the as-built. Where the implementation in `crates/cranelisp-backend/src/` does not yet match the facade, this doc names the gap by section and points to the resolution path (an audit phase, an open FIXME, or a sprint-scope item). The audit `audits/backend-20260423.md` is read as the temporal snapshot of as-built state at that date — useful for understanding how the crate got here, **not** the target. The canonical contract (BC + facade + Decisions) wins where they disagree.

---

## 1. Bounded-context recap

Per `bounded-contexts.md` §3 — Backend's job is **typed AST → executable**. The crate translates symbol-table entries into Cranelift IR and produces compilation artefacts: in-memory machine code for direct execution, object files for linking, and the cache pair (metadata + object) for re-use across sessions. There is **one compilation entry point regardless of mode**; mode (in-memory vs object) is a property of the Cranelift `Module` instance the caller supplies, not a parameter on the entry point. The crate has **no cadence**; multiple compilations may run concurrently with disjoint inputs.

In-scope (per BC §3):

- IR emission for every spec-defined construct
- RC discipline at the call boundary (callee owns its heap parameters)
- In-memory artefact production with reclaim on drop
- Object-file production
- Cache read and write
- Per-module link binding for cross-module call indirection

Out of scope: type inference (typecheck), macro expansion (frontend), pipeline scheduling (int), runtime helpers (runtime — backend declares them as imports).

What crosses the boundary (per BC §3):

- **Inputs**: a symbol-table view; a Cranelift module to emit into.
- **Outputs**: a per-batch artefact carrying a retention root for the produced code plus per-symbol code addresses (for `int` to wrap in its concrete code carrier); for object mode, the object artefact and the cache pair.
- **Window types**: none.

Per Decision 41, the per-symbol code carrier (`Code`) is named in this crate as well as in `int`; the Principle 3 protection (no `cranelisp-types → cranelisp-backend` edge) survives intact because `Code` does **not** live in `cranelisp-types`.

---

## 2. Public surface

The facade `design/arch/facades/backend.md` is authoritative. **Do not restate signatures here** — cite §"Public surface" and §"Object file contract" of the facade for the Rust-level shape. This section names what the surface is *for* and which contract invariants this crate is responsible for upholding.

### 2.1 The three free functions (facade §"Public surface")

- `compile_to_module<M: Module>(scope, names, symbol_tables, introspection, module) -> Result<(), CompilationError>` — the **single CLIF emission entry**. Used by `int`'s priority workers (JIT path, per-symbol cardinality per Decision 41) and nice workers (object path, per-module cardinality). Mode is determined by the supplied `M` instance per Decision 23. Backend writes `Code::Jit { jit, ptr }` directly into each compiled symbol's entry via `SymbolTable::write_code(&self, sym, code)` (Decision 38; interior mutable). `Introspection { clif_ir, disasm, code_size, compile_duration }` is written iff `introspection.is_some()` — the `Option`'s presence IS the mode discriminator per Decision 38.

- `load_object(module, object, symbol_tables) -> Result<LinkerArtefact, CranelispError>` — the **JIT-mode cache-hit entry**. Reads a `.o` produced by an earlier `compile_to_object` call (or by `--link` mode), runs the cache linker to resolve each defined symbol's bare-name address (Decision 36), returns `LinkerArtefact { linker: Arc<Linker>, ptrs: HashMap<Symbol, *const u8> }` for `int` to wrap into `Code::Linker { linker, ptr }` per symbol (Decision 35). Per-module cardinality (one `Linker` holds many symbols) is unchanged by Decision 41 — the per-symbol direct-write pattern is for `compile_to_module` only.

- `compile_to_object(module, symbol_tables) -> Result<ObjectArtefact, CranelispError>` — the **nice-worker object-codegen entry**. Produces `ObjectArtefact { object: Vec<u8>, sidecar: SymbolTable<(), ()> }`. Backend writes nothing to disk; `int`'s `ObjectCache::write` performs the file IO and enforces the Decision-25 pairing invariant.

### 2.2 The retention newtypes

- `Jit` (facade §"Jit — the JIT retention newtype") — `Arc<Jit>` is the Decision-31 reclaim primitive. Custom `Drop` calls `unsafe { JITModule::free_memory() }`; the safety invariant is upheld by `int`'s GOT-swap discipline plus the language-level "fn values are heap closures, not raw code pointers" rule. Backend exposes only `new(builder) -> Self` and `module(&mut self) -> &mut JITModule` per facade — there is no public `compile_defn` or per-function entry point on `Jit`.

- `Linker` (facade §"Linker — the cache-load retention newtype") — opaque retention root for cache-hit code regions. `Arc<Linker>` is analogous to `Arc<Jit>` for cache-hit lifecycles. Public surface is `load_object(object: &[u8]) -> Result<Self, CranelispError>` (associated constructor) and `get_symbol(&self, name: &LinkerSymbol) -> Result<*const u8, LinkerError>` — the typed-result accessor per facade §2.6 (defensive resolution, Decision 37 — see §6.2 below).

### 2.3 The per-symbol code carrier

`Code` (facade §"Code — the per-symbol code carrier") lives **in this crate** per Decision 41. Two variants — `Jit { jit, ptr }` for fresh-build, `Linker { linker, ptr }` for cache-hit. `impl Code { pub fn ptr(&self) -> *const u8 }` is the variant-uniform code-address accessor consumed by `int` at GOT-write time. `Code` does NOT live in `cranelisp-types` — that would invert the dependency graph and breach Principle 3.

### 2.4 Errors

`CompilationError` (facade §"Errors") — typed error variants for codegen failures. `SymbolNotCompilable { module, symbol }` is the typed signal for the Decision 22 / Decision 37 contract-violation case. `CodegenFailed`, `ModuleError` carry source location and cause string. The pre-S58 ad-hoc `CranelispError::CodegenError { message: "..." }` string boundary is replaced by variant matching at the call site.

### 2.5 The seven bounded-context invariants (facade §"Bounded-context invariants")

These are the contract this design protects across sprints:

1. **Single compilation entry point per mode** (Decision 23) — `compile_to_module<M: Module>` is the sole CLIF emission path; mode is a property of the supplied `Module`, not a function parameter.
2. **Uniform consuming calling convention** (Decision 24) — every call site emits identically for RC management. No "borrowing" classification.
3. **Compiled code lives on `ModuleEntry::Def.code`** (Decisions 25, 41) — backend writes directly via `SymbolTable::write_code`; the field carries `Option<Code>`.
4. **`defined_symbols()` is the codegen-compilable predicate** (Decision 22) — backend trusts the contract; on miss returns `CompilationError::SymbolNotCompilable` rather than synthesising.
5. **Decision 31 reclaim safety** — custom `Drop for Jit` calls `unsafe JITModule::free_memory()`; safety is upheld externally by `int`'s GOT-swap discipline plus the closure-value rule. Backend does not enforce; backend relies.
6. **Two-GOT model, one CLIF** (Decision 23) — same data-symbol reference (`__cranelisp_got_{M}`) appears in every CLIF emission; resolution differs by `Module` impl at finalize.
7. **Bare names + `Linkage::Local` uniformly** (Decision 36) — every user function. The `--link` mode `_main` alias is `int::link_by_name`'s job, not backend's.

### 2.6 As-built deviations from §2.1–§2.5 (this is a refresh, not a status report)

The audit `audits/backend-20260423.md` records four substantive gaps between the facade target and as-built state at audit date. They remain open and are the major implementation work owed against this design intent:

| Facade target | As-built state at audit date | Resolution path |
|---|---|---|
| Single `compile_to_module<M>` entry; `Jit` exposes only `new`/`module` | `lib.rs::compile_to_module<M, C, L>` AND `jit.rs::Jit::compile_defn` are both public per-function entries; two parallel `CompileContext` builders; two `build_isa` (one in `cache/object.rs` parameterised, one in `jit.rs` hardcoded) | Audit Phase 1 — converge entry points + ISA + context builder. Cited under Simplicity §4.1 (Principle 11 — single pipeline) |
| `compile_to_module(...) -> Result<(), CompilationError>`; backend writes Code directly via `write_code` | `compile_to_module(...) -> Result<CompilationResult, CranelispError>` with a return tuple (`code_ptrs`, `artifacts`, `func_ids`, `entry_func_id`, etc.); int post-loop iterates and constructs `Code::Jit` (`worker.rs:2860-3018`); `SymbolTable::write_code` does not yet exist | Decision 41 follow-through — backend signature refactor + `SymbolTable::write_code` addition in `cranelisp-types` (FIXME `target: /arch` filed by `int`'s `/design` if not already; this refresh notes the dependency rather than re-files) |
| `Code` lives in `crates/cranelisp-backend/src/code.rs` | `Code` lives in `src/code.rs` (integration layer); `cranelisp-backend` does not yet name it | Same Decision 41 follow-through — co-ordinated `Code` move + `compile_to_module` signature refactor |
| `load_object` is a backend free function returning `LinkerArtefact { linker: Arc<Linker>, ptrs }` | `Linker::load_object(&mut self, _module_name, bytes) -> Result<(), CranelispError>` is a method on `Linker`; `Linker` itself is constructed elsewhere; no `LinkerArtefact` struct | Facade-driven refactor — wrap the existing relocator in the `load_object` free function shape; `LinkerArtefact` becomes a thin DTO over the existing internals. No semantic change, surface change only |

These deviations are observations *of the source*; they do not reflect a problem with the **contract**. The contract is implementable simply against the BC + facade — the implementation just hasn't caught up to the contract for several sprints. The simplicity check (§4.1 below) confirms this: the convergence is a *deletion + re-shape* exercise, not a *redesign* exercise. No FIXME `target: /arch` is filed for these — they are open implementation work on the existing canonical design.

---

## 3. Internal architecture

### 3.1 Module layout — current (per audit File Metrics)

| File | Lines | Responsibility |
|---|---:|---|
| `lib.rs` | 4655 | Crate root; `compile_to_module<M, C, L>`; `compile_defn_in_module`; `CodeFinalizer` impls for JIT + Object; ~3,932 lines of tests at the bottom |
| `compiler/mod.rs` | 1560 | `FnCompiler<M>`, `CompileContext`, scope/RC helpers, dispatch entry |
| `compiler/control_flow.rs` | 1948 | `let`, `if`, lambdas, par-bind continuation, closure + drop glue paths |
| `compiler/vec_codegen.rs` | 1315 | Vec literals, ops, COW fast/slow paths, element inc/dec helpers |
| `compiler/apply.rs` | 743 | Call lowering, ResolvedCall dispatch, closure invocation, bind lowering |
| `compiler/match_codegen.rs` | 581 | Pattern-match lowering |
| `compiler/literals.rs` | 465 | Literal lowering, constructor/operator-as-value |
| `compiler/trace_codegen.rs` | 396 | `trace` wrapper lowering |
| `operators.rs` | 531 | Inline primitive lowering, `(TraitName, Symbol, TypeName) → PrimitiveOp` map |
| `heap.rs` | 501 | Heap layout offsets, RC inc/dec emission, allocation helpers, last-use predicate |
| `jit.rs` | 1241 | `Jit` newtype + custom `Drop`, `build_isa()` (HARDCODED, parallel to `cache/object.rs`), intrinsic registration, **second** `compile_defn` and `build_compile_context` |
| `display.rs` | 831 | Value/type formatting (likely belongs in `int` per BC §6 ownership of REPL display, but historical) |
| `exe.rs` | 231 | Startup-object generation for `--link` mode |
| `cache/mod.rs` | 653 | Cache facade, paths, load helpers, **deprecated compatibility surface** |
| `cache/manifest.rs` | 419 | Manifest hashing, freshness checks |
| `cache/object.rs` | 707 | Object-module compilation, `build_isa(is_pic)` (the *intended* canonical helper) |
| `cache/serialize.rs` | 734 | Cache metadata serialisation |
| `cache/linker.rs` | 1009 | In-process object loader, relocations, GOT slot handling |
| `got.rs` | 9 | Compatibility re-export (deletion candidate per audit MED-1) |
| `codegen_types.rs` | 9 | Compatibility re-export (deletion candidate per audit MED-1) |

### 3.2 Module layout — target

The target is BC-shaped: `compile_to_module` is the only public per-symbol/per-module compile entry; everything else in this crate is implementation detail behind that entry, behind `compile_to_object`, or behind `load_object`. The audit's target diagram reduces to:

```
caller
  └─ compile_to_module(scope, names, &symbol_tables, introspection?, M) ─→ () + side-effects
        ├─ build_isa(M.is_pic())                              [single helper, in cache/object.rs]
        ├─ CompileContext::build(scope, names, symbol_tables, isa)   [one builder]
        ├─ for sym in names:
        │     compile_defn(plan, defn) ──→ FnCompiler<M>::compile_body
        ├─ M.finalize_definitions()                            [JIT path] / no-op [object path]
        ├─ for each compiled sym: write Code into symbol_tables[scope]
        └─ if introspection.is_some(): write Introspection per sym

caller (cache-hit)
  └─ load_object(scope, &bytes, &symbol_tables) ─→ LinkerArtefact { linker, ptrs }
        ├─ Linker::load_object(bytes) ──→ Linker
        └─ for each defined symbol: linker.get_symbol(bare_name)?   [Decision 37 defensive]

caller (object)
  └─ compile_to_object(scope, &symbol_tables) ─→ ObjectArtefact { object, sidecar }
        └─ same FnCompiler skeleton against ObjectModule + sidecar SymbolTable<(), ()> serialise

tests
  └─ FnCompiler / submodule narrow unit tests in their owning files
  └─ lib.rs reserved for crate-level orchestration tests
```

Three structural moves separate current from target (audit Phases 1–4):

1. **Single front door** (audit Phase 1). `Jit::compile_defn` and `jit.rs::build_compile_context` collapse — either deleted or made private behind `compile_to_module`. ISA construction goes through `cache::object::build_isa`. `CompileContext` is built once per batch.
2. **Hot-spot decomposition** (audit Phase 2). `control_flow.rs`, `vec_codegen.rs`, `compiler/mod.rs` carry ~7,008 lines and the four 100+-line monoliths (`compile_par_bind_continuation` 223, `build_adt_drop_glue_fn` 165, `compile_resolved_call` 153, `compile_lambda_body` 148). Split by protocol boundary, not arbitrary line count.
3. **Cache layer cleanup** (audit Phase 4 + Decision 41 follow-through). Deprecated re-exports (`got.rs`, `codegen_types.rs`, `CacheMetadata` envelope, "Wave 2b parallel migration" markers) delete; `cache/` carries one canonical SymbolTable-direct API. `Code` enum moves from `src/code.rs` here. Tests move from `lib.rs` to owning submodules.

These moves are not new design — they are decisions already taken (Decisions 23, 25, 32, 35, 36, 37, 41) finally landing in the file structure. Audit Phases 1–4 are the work plan; the canonical contract is what's already in BC + facade + Decisions.

### 3.3 Compilation flow (target shape, per facade + Decision 41)

```text
compile_to_module(scope, names, &symbol_tables, introspection?, &mut M):
    isa     = build_isa(M.is_pic())                           # cache/object.rs canonical helper
    plan    = CompileContext::build(scope, names, &symbol_tables, isa)
    declare functions    (bare names, Linkage::Local — Decision 36)
    declare GOT data     (__cranelisp_got_{scope}, mode-resolved at finalize — Decision 23)
    declare runtime imports
    for sym in names where defined_symbols() includes sym:
        compile_defn(plan, defn)                              # emits CLIF via FnCompiler<M>
    M.finalize_definitions()
    for each defined sym:
        ptr  = M.get_finalized_function(func_id)
        symbol_tables.get(scope)?.write_code(sym, Code::Jit { jit: jit_arc.clone(), ptr })
        if let Some(intro) = introspection:
            intro.insert(FQSymbol::new(scope, sym), Introspection { clif_ir, disasm, code_size, compile_duration })
    Ok(())
```

JIT cardinality is **per-symbol**: the caller invokes `compile_to_module` once per defined symbol, each invocation creating a fresh `Jit` (and thus a fresh `JITModule`). Object cardinality is **per-module**: one `compile_to_module` invocation processes the full module's defined symbols against an `ObjectModule`, then `compile_to_object` (which shares this skeleton) returns the bytes.

Decision 41 §1 explains the per-symbol JIT trade: per-redefinition reclaim becomes truly per-symbol (each `Code::Jit` clone in the table holds an independent `Arc<Jit>`; redefining one symbol drops one Arc to zero immediately). The cost is ~50 intrinsic registrations per `JITModule::new`. The integration-layer callsite is the one pattern in Decision 41 §1 — backend's body iterates `names: &[Symbol]` of length 1 in JIT mode, length N in object mode, but the body does not branch on cardinality.

Decision 22's `defined_symbols()` predicate is the *one* filter both the caller and the body trust: if a name in `names` resolves to an entry where `defined_symbols()` would not include it, the body returns `Err(CompilationError::SymbolNotCompilable { module, symbol })` immediately. Decision 37's "no swallowed failures" lands as a single `?` inside the body.

---

## 4. Quality attributes

### 4.1 Simplicity (Principle 6, Principle 11)

**Target**: one CLIF emission path; one ISA helper; one `CompileContext` builder; one cache API; bare-Local + GOT-indirect dispatch uniformly. The facade's "single compilation entry per mode" invariant is the witness.

**Audit findings against this target**:

- **HIGH-1** (overlapping entry points). Two public per-function compile entries (`lib.rs::compile_to_module` + `jit.rs::Jit::compile_defn`); two `CompileContext` builders; two `build_isa` (the crate root re-exports `cache::object::build_isa` as the intended authority but `jit.rs` has a hardcoded second one). Resolution: audit Phase 1 — the convergence step. The principle violated is **Principle 11 (single pipeline, mode parameters)** — every duplicate entrypoint is a divergence point.

- **MED-1** (cache layer migration residue). ~30 deprecated/back-compat markers in `cache/`; deprecated `CacheMetadata` envelope; `got.rs` and `codegen_types.rs` are 9-line compatibility re-exports. Resolution: audit Phase 4.

The two-front-door problem is the highest-leverage Simplicity item. Until it lands, the facade's "single compilation entry point per mode" invariant is aspirational. The convergence is a deletion exercise, not a redesign.

**Feasibility check (refresh)**: the facade target (one entry, one ISA, one context builder, signature `Result<(), CompilationError>`) is implementable simply against the BC. The only friction is the as-built state had two paths grown through earlier sprints; collapsing them is mechanical (audit Phase 1 + Decision 41 signature refactor). No contract-side ambiguity blocks the convergence — `/arch` does not need to redesign anything for this to land.

### 4.2 Maintainability (Principle 6)

**Target**: change-set blast radius bounded by file structure; `compiler/` is the boundary of compilation logic; functions stay near the project's ~100-line guidance from `src/CLAUDE.md` §"Code Structure".

**Audit findings against this target**:

- **HIGH-2** (mini-monoliths). `compiler/control_flow.rs` 1948 lines, `compiler/mod.rs` 1560, `compiler/vec_codegen.rs` 1315. Six functions over 100 lines each, the four worst offenders named above. Each encodes multiple protocols (builder setup + ownership + capture loading + branching + cleanup) in one function. Resolution: audit Phase 2 — split by protocol boundary, not arbitrary line count. Subordinate docs `ring2-rc.md` §3 (calling convention) and `compile-to-module.md` §7 (per-function compilation primitive) already specify the boundary cuts.

- **HIGH-3** (helper duplication families). `resolve_got_target` and `resolve_func_arity` walk import chains identically; `emit_extern_call_1..4` are arity-cloned; `compile_vec_set_cow` and `compile_vec_push_cow` clone the same COW skeleton. Resolution: audit Phase 3 — single symbol-table walker parameterised by what to read; one slice-based extern-call helper; one COW branch skeleton with fast/slow callbacks.

The mini-monolith condition is what makes feature work in `control_flow.rs` slow: review cost is dominated by re-establishing invariants of the surrounding 1948 lines, not by understanding the change.

**Feasibility check**: protocol-boundary splits are a refactor, not a redesign. The BC + facade do not constrain internal file structure; this is purely a `/dev` + `/review` cycle within the bounded context. No contract problem.

### 4.3 Observability

**Target**: when a codegen miscompile fires in production / a future debugging session, the right signal is visible — CLIF dumps, RC traces, last-use decisions, GOT-slot population events.

**Current state**:

- `CRANELISP_CODEGEN_DUMP=*|<module>|<module>::<symbol>` writes CLIF to stderr during `compile_to_module` (filter parser in `lib.rs:68`, dump writer at `lib.rs:83`). Cache-hit paths do NOT re-codegen, so use `/clif <name>` from the REPL for those (reads `Introspection.clif_ir`).
- `CRANELISP_CODEGEN_TRACE=1` populates `Introspection.clif_ir` + `Introspection.disasm` per Decision 38. The mode discriminator is `introspection.is_some()` per Decision 41; production batch carries zero per-symbol overhead.
- `CRANELISP_RC_TRACE=1` emits inc/dec events; `LIVE_ALLOCS` debug-asserts catch double-frees (per the runtime crate, but consumed from backend test paths).
- `io-trampoline-trace.md` documents the IO event log used during Wave 1 IO-scheduling debugging.
- `defects-456-reduction.md`, `defect-8-repro-notes.md`, `slice-4-21-hello-io-investigation.md` record specific incident debugging — observability that paid off (these are stale-as-live-design but kept as repro references; see §8).

**Gap**: backend has no first-class log of GOT-slot population. The pre-S58 silent-NULL pattern in `worker.rs:2810-2823` — where `linker.get_symbol(name) == None` was silently treated as "skip this slot" — is the historical defect category Decision 37 addresses. The current `Linker::get_symbol(&self, name: &str) -> Option<*const u8>` method is `Option`-returning; the *defensive* error must be raised at the call site (in `int`), not in backend's API. Backend's facade is correct (expose `Option`, let the caller decide what's fatal); the safety invariant lives in the caller's discipline.

The audit does not flag a positive log of "slot N for symbol s populated with ptr P" beyond `Introspection.code_size`. This is acceptable for now — the safety invariant (Decision 37) is the regression net — but a known gap for future incident response. **FIXME 0094 (filed below)** asks `/arch` to decide whether this is an `Introspection` extension or a separate trace flag; the surface impact is `int`'s, not backend's.

This sprint did not introduce new observability surfaces. The crate's observability story is documented enough in the existing CLIF dump filter + Introspection field set; future work expands rather than replaces.

### 4.4 Concurrency-safety (Principle 1, Principle 4)

**Target**: no shared mutable state across `compile_to_module` calls beyond what DashMap or Arc-of-immutable already provides. No global static-mut. No backend-internal locks taken during codegen.

**Current state**:

- Backend operates on `&DashMap<ModuleFullPath, SymbolTable<C, L>>` per Decision 38. Reads are shard-scoped; no exclusive borrow ever required.
- Within a single `compile_to_module` call, the `&mut M` (Cranelift module) is exclusive to that call. Cranelift's own internals are thread-local within the `JITBuilder` / `ObjectBuilder` boundary; backend respects this by never sharing the `&mut M` across threads.
- The GOT slot layout is pinned at typecheck time (Decision 37); codegen workers fill slot CONTENTS in any order, in parallel, with no inter-worker coordination. Each module's GOT is owned by `SymbolTable[M].got: Arc<GotTable>` — atomic-write per slot.
- `Jit::Drop` calls `unsafe free_memory()`; the safety invariant (Arc refcount 0 ⇒ no derived fn pointer reachable) is upheld externally, not by a backend-side lock. See §2.5 invariant #5.
- Per-symbol JIT cardinality (Decision 41) means each `compile_to_module` JIT call gets a fresh `JITModule`; there is no cross-symbol shared codegen state within a batch. Workers can run multiple `compile_to_module` calls concurrently against different symbols of the same module — the only contention point is the per-entry `SymbolTable::write_code` which is interior-mutable per Decision 38.

**Invariant** (restating facade #5): backend does not enforce Decision 31's reclaim invariant — it relies on `int`'s atomic GOT swap and the language-level "fn values are heap closures, not raw pointers" rule. If a future `--link` callback platform retains user fn pointers across calls, the platform-side rules in Decision 31's "Callback support" §4 must hold; backend's contract does not change.

This sprint did not touch backend concurrency. No subordinate concurrency doc exists yet under `design/backend/`; a future sprint that adds threaded codegen primitives (e.g., per-defn parallelism inside `compile_to_module`) would create one.

**Feasibility check**: the BC-mandated "no cadence; multiple compilations may run concurrently with disjoint inputs" is implementable cleanly because backend takes no internal locks. The interior-mutable `write_code` discipline (Decision 38) keeps the contract simple. No problem.

### 4.5 Performance (Principle 6 — not premature)

**Target**: codegen is not on a hot path of program execution; it sits between pipeline stages. Per-batch JIT setup, per-defn CLIF emission, finalize. The "pathological case" is large modules + REPL redefinition churn.

**Current state**:

- Per-symbol JIT cardinality (Decision 41) trades batch amortisation for per-redefinition reclaim immediacy. The cost is ~50 intrinsic registrations per `JITModule::new` invocation. Acceptable per the decision rationale (Principle 1 — decoupling — over Principle 6 marginal cost).
- Cache-hit path (`load_object`) skips codegen entirely; mmap the `.o`, resolve bare-name symbols, write to GOT slots. Decision 25's "cache stores both `.meta.json` AND `.o`" eliminates the previous "regenerated from `ast` on cache-hit load" wording — codegen only runs on fresh build.
- Object mode keeps per-module batching: one `ObjectModule` holds the whole module's defined symbols, written in a single `compile_to_object` call.

**Pathological cases identified**:

- REPL redefinition produces a single-defn JIT call per redefinition; Cranelift `JITModule::new` setup is dominant. Per Decision 41, this is the *correct* cost — per-redefinition immediacy is the design point. A future optimisation could share an isolation-bounded JIT-state across consecutive redefinitions of the same module, but is **not** scheduled and explicitly **rejected as premature** per `memory/feedback_no_premature_perf.md`.
- Large monomorphisation tables (multi-sig × constrained polymorphism × generic ADT impls) produce many per-symbol JIT calls; this is bounded by typecheck deciding what to materialise, not by backend scaling.

This sprint did not touch backend performance. No subordinate performance doc exists.

### 4.6 Testability (Principle 5)

**Target**: each compiler submodule (`compiler/control_flow.rs`, `vec_codegen.rs`, etc.) has narrow unit tests in its `#[cfg(test)] mod tests` block exercising the codegen primitive against a stub `Module`. `lib.rs` carries only crate-level orchestration tests.

**Audit finding against this target**:

- **MED-2** (test mis-location). `lib.rs` is 4655 lines, of which **3932 are tests** (test block starts at line 724, 64 tests). Meanwhile the seven compiler files in `compiler/` total 7008 lines with **zero local tests**. The structural foundation for narrow testing (`FnCompiler<M>` generic over `Module`) already exists. The blocker is just nobody has done the moves. Resolution: audit Phase 4.

The structural-testability claim is principled: backend's runtime imports are by symbol name (per facade §"Consumed surface" — `cranelisp_runtime::heap_alloc` etc. are referenced as strings during codegen), so a test-only `Module` can register stubs for those names. Backend can be unit-tested without a real `cranelisp-runtime` linkage. The audit does not flag this as a gap.

**Feasibility check**: test relocation is mechanical refactor. No contract problem.

---

## 5. Concurrency model

Backend's interaction with shared state is **read-only via SymbolTables, write-via interior-mutable `write_code`**:

1. The integration layer holds `shared.symbol_tables: DashMap<ModuleFullPath, SymbolTable<Code, ()>>` per Decision 38.
2. Workers pass `&shared.symbol_tables` (or a clone of the `Arc`) into `compile_to_module(_, _, symbol_tables, _, _)`. Backend treats this as a read-mostly view; per Decision 38, all SymbolTable access is `&SymbolTable` after Phase 0 (which is initiator-thread-only).
3. Per Decision 33, structural decls (`imports`, `exports`, `platforms`, `submodules`, `defn_order`) are fields on `SymbolTable` — read identically via shard locks. Backend reads `symbols[name].got_slot` via `.get(name)` (DashMap shard read).
4. The `&mut M: Module` is exclusive to the call. Backend never shares it.
5. Per Decision 41, backend constructs `Code::Jit { jit: Arc::clone(&jit_arc), ptr }` and calls `symbol_tables.get(scope)?.write_code(sym, code)` — a brief per-entry inner write lock through DashMap interior mutability.
6. The `Option<&DashMap<FQSymbol, Introspection>>` is similarly written through DashMap shard locks; `None` skips entirely.

Backend takes **no** locks itself. Cranelift's internals are exclusive to the `&mut M` borrow. Multiple `compile_to_module` calls may run concurrently against different `(scope, sym)` pairs; the only inter-call coordination point is the per-entry write_code shard.

The audit's silence on concurrency reflects the design's success here: there is nothing to flag because backend does not introduce shared mutable state. This is a Principle 1 + Principle 4 outcome.

---

## 6. Cache + linker architecture

Decisions 25, 31, 34, 35, 36, 37, 41 together specify the cache + linker shape. The relevant subordinate docs are `module-caching.md` and `compile-to-module.md` §16–17.

### 6.1 Cache writes — `compile_to_object`

`compile_to_object(scope, &symbol_tables) -> ObjectArtefact { object, sidecar }`:

- `object: Vec<u8>` — Mach-O / ELF / COFF emitted via `cranelift-object`. Per Decision 36, every user function is `Linkage::Local` with bare-name symbol. Per Decision 23, the `__cranelisp_got_{scope}` data symbol is `Linkage::Export` with relocation initialisers ordered by `SymbolTable[scope].symbols[name].got_slot`.
- `sidecar: SymbolTable<(), ()>` — the schema-versioned (Decision 34) serialised symbol table. Backend produces this; the integration layer's `ObjectCache::write` writes both files paired (Decision 25 pairing invariant; cache-load enforces `meta.json` ⇒ `.o` invariant).

Backend writes nothing to disk. File IO is `int`'s.

### 6.2 Cache reads — `load_object`

The cache-hit path is **not** a parallel codepath (Decision 37). It lives inside the integration layer's recursive `register_module` flow. Backend's role:

- `load_object(scope, &object_bytes, &symbol_tables) -> Result<LinkerArtefact, CranelispError>` — `Linker::load_object(bytes)` mmaps the bytes, runs relocations, indexes the symbol table.
- For each defined symbol `s` in `symbol_tables[scope]`, `linker.get_symbol(bare_name(s))` resolves the address. Bare-name lookup per Decision 36; `Linkage::Local` symbols are still indexable from the in-process linker (it filters only `.L*`-style debug symbols).
- Returns `LinkerArtefact { linker: Arc<Linker>, ptrs: HashMap<Symbol, *const u8> }` — `int` writes resolved ptrs into the SymbolTable GOT slots and constructs `Code::Linker { linker, ptr }` per symbol via `write_code`.

**No swallowed failures (Decision 37)**. The facade exposes `Linker::get_symbol(&self, name: &LinkerSymbol) -> Result<*const u8, LinkerError>` (a typed `Result`, not the source's current `Option`). At facade-level the contract is: **callers MUST treat resolution failure as `CacheLoadError`, not silently push NULL**. The pre-Sprint-58 `worker.rs:2810-2823` regression came from the `Option` → silent-skip pattern; Decision 37 plus the typed `Result` shape closes the door. **FIXME 0095 (filed below)** asks `/arch` to pin the typed `Result` shape into the facade explicitly so `int`-side reviewers see the safety contract.

### 6.3 Schema versioning (Decision 34)

`.meta.json` carries `schema_version: u32`. Mismatch invalidates the cache as if dependencies changed — not a cryptic deserialise error. Backend defines the constant `CACHE_SCHEMA_VERSION` in `cache/mod.rs`. Cache-write emits it; cache-load reads it first. The current value is `1` (Sprint 58 Step 5b).

### 6.4 In-process linker

`cache/linker.rs` (1009 lines) is backend's in-process object loader. It exists because JIT-mode cache-hit cannot use the system linker — it needs to mmap a `.o` and resolve relocations against in-memory addresses (runtime functions, GOT data symbols of other modules already loaded). The linker handles ELF / Mach-O variant uniformly per host platform. Subordinate docs: `executable-generation.md` for the dual `--link` system-linker path, `cache-repl-loads-triage.md` for the symptom history (now archive-candidate).

### 6.5 Object file contract — what crosses the boundary

Per facade §"Object file contract", the `.o` is **one file consumed by two readers**: in JIT mode by `Linker::load_object` (cache-hit path), in `--link` mode by the system linker. The two-GOT model in Decision 23 distinguishes which GOT is consulted at finalize, NOT where the `.o` lives. Backend emits identical CLIF for both modes; the `Module` impl supplied at finalize determines resolution. The `--link` mode `_main` alias is `int::link_by_name`'s job, not backend's.

---

## 7. Decision register

| Decision | Backend takeaway |
|---|---|
| **22** — `defined_symbols()` predicate | One filter; `compile_to_module` trusts the contract or returns `CompilationError::SymbolNotCompilable` |
| **23** — Uniform codegen, two-GOT model | One CLIF, two resolvers; mode is a property of the supplied `M`, not a parameter |
| **24** — Uniform consuming calling convention | Caller transfers ownership of heap params; callee owns. No "borrowing" classification. RC discipline is uniform across user fns, traits, builtins, externs, and constructors. |
| **25** — Code on `ModuleEntry::Def.code`; cache stores `.meta.json` + `.o` | Backend writes Code directly (per Decision 41 amend) into `ModuleEntry::Def.code`; cache-load reads both files paired |
| **26** — Platform fn ptrs on `ModuleEntry::Def.platform_fn_ptr`; `scheduling_class` in variant | Backend reads platform ptrs from symbol-table import chains, not a side registry |
| **31** — `Arc<Jit>` + custom `Drop` calls `unsafe free_memory()`; per-symbol JIT cardinality (per Decision 41 amend) | The `Jit` newtype; safety invariant relies on `int`'s GOT-swap discipline |
| **32** — `CodeStore` / `LinkerStore` empty markers + `Clone` super-bound | Backend signatures use `SymbolTable<Code, ()>` (per Decision 41 amend; previously `<C, L>`-blind) |
| **33** — Structural decls on `SymbolTable` | Backend reads imports/exports/etc. from symbol table directly |
| **34** — `schema_version: u32` cache envelope | Backend owns `CACHE_SCHEMA_VERSION` constant; cache-load checks first |
| **35** — `Code` enum (per Decision 41 amend, lives in `cranelisp-backend/src/code.rs`) | Backend constructs `Code` directly; integration layer also names it at session boundary; Principle 3 protected — `Code` does NOT enter `cranelisp-types` |
| **36** — Bare names + `Linkage::Local` uniformly | No `user`/`main` special case; `--link` `_main` alias is `int`'s job |
| **37** — Cache-hit lives inside `register_module`; codegen phase order-independent; defensive resolution | No `try_cache_hit_load` parallel path; `Linker::get_symbol` failure is `CacheLoadError`, never silent skip |
| **38** — `SharedState` is the formal worker-shareable subset; per-symbol mutability via `&SymbolTable` interior mutability (`write_code(&self, sym, code)`) | Backend operates on read-only symbol-table view + interior-mutable `write_code` |
| **39** — Per-defn source on `Introspection.source`; errors carry `ErrorLocation` | `CRANELISP_CODEGEN_TRACE=1` populates `clif_ir`/`disasm` on `Introspection`, not on `ModuleEntry::Def` |
| **40** — `trace.rs`/`io_trace.rs` relocate to int; runtime keeps `IoObserver` callback contract | Backend unchanged — backend's observability surfaces (CLIF dump, RC trace) are codegen-side; runtime's observation contract is orthogonal |
| **41** — `compile_to_module` per-symbol JIT cardinality; `Code` moves to `cranelisp-backend`; backend writes shared state directly; `Result<(), CompilationError>` | The single largest pending refactor against this design. Amends Decisions 31, 35. See §2.6 deviations table |
| **42** — `PlatformError` adopts `ErrorLocation` per variant | Backend's platform-related codegen paths surface `CranelispError::Platform` with `ErrorLocation`-carrying variants when relevant |

Decisions not listed (1–9 cross-crate framing, 10 base-pointer ABI in interface-types territory, 27 G8-before-G9 orchestration, 28 retracted, 29–30 form-by-form scheduler in int) are either consumed orthogonally or not backend-shaped.

---

## 8. Subordinate topic docs

The 21 existing docs under `design/backend/` (this `backend.md` is the master) elaborate specific subsystems. This master doc points; it does not reproduce. Live (cite-as-design-intent) vs stale (cite-as-historical-reference) is called out explicitly per the §1 framing — stale docs remain useful for repro context but should not be cited as authoritative.

| Topic | File | Status |
|---|---|---|
| Compilation function shape | `compile-to-module.md` | **Live**. Authoritative on §17 generics activation. Audit-current — describes Decision 25 + 32 + 35 outcome. Decision 41 update needed (signature `Result<(), CompilationError>`) |
| Ring 1 codegen | `ring1-codegen.md` | **Live**. Stable. Ring 0/1 primitives backbone |
| Ring 2 RC discipline | `ring2-rc.md` | **Live**. Authoritative on Decision 24 (uniform consuming convention). §10 addendum (string-literal RC residual through `print`) is current |
| Per-module GOT | `per-module-got.md` | **Live**. Authoritative on Decision 23's two-GOT runtime. Read alongside `compile-to-module.md` §5 |
| JIT/Object convergence | `jit-object-convergence.md` | **Live as design intent**; source is behind. Audit HIGH-1 directly relevant. The convergence is **not yet landed in the source** — Phase 1 of audit's plan is the convergence step |
| Module caching | `module-caching.md` | **Live**. Read alongside Decisions 25, 34, 37 |
| Executable generation | `executable-generation.md` | **Live**. `--link` mode; backend's `exe.rs` (231 lines) |
| HKT codegen | `hkt-codegen.md` | **Partial / stale**. Sprint 24 era; check against current monomorphisation pipeline before extending |
| IO trampoline | `io-trampoline.md` | **Live**. Backend's IO trampoline design |
| IO scheduling | `io-scheduling.md` | **Live**. Overlaps with §10.12 spec |
| IO trampoline trace | `io-trampoline-trace.md` | **Stale as live design**. Incident-debug residue. Reference only |
| Lenient eval | `lenient-eval.md` | **Live**. Spec §12.4.3 + §10.12 backend story |
| FQTypeName cache | `sprint51-fqtypename-cache.md` | **Partially stale**. Sprint 51 era; Decision 34's `schema_version` replaces the pre-S58 manifest hashing for shape changes |
| Sprint 19 panic boundary | `sprint19-panic-boundary.md` | **Live**. Catchable runtime panics. Check against current `runtime_panic` extern declared in facade §"Consumed surface" |
| AST-sourced codegen | `ast-sourced-codegen.md` | **Partially superseded** by Decision 25 (the `Def.ast` field). Cite cautiously |
| Auto-curry + run-tests | `auto-curry-and-run-tests.md` | **Live**. A2 + R1 codegen primitives |
| Cache REPL loads triage | `cache-repl-loads-triage.md` | **Stale**. Post-Decision-37 the "no swallowed failures" outcome lands in `module-caching.md`. Reference for history only |
| Defect 8 repro notes | `defect-8-repro-notes.md` | **Stale as live design**. Keep as cross-skill repro example |
| Defects 4/5/6 reduction | `defects-456-reduction.md` | **Stale as live design**. Sprint 59 W1 incident-debug residue |
| Slice 4 / 21-hello-io | `slice-4-21-hello-io-investigation.md` | **Stale as live design**. Sprint 61 era closure double-free reduction; keep for repro |

Six docs are flagged stale-as-design. They remain as references but should not be cited as authoritative design intent. **FIXME 0096 (filed below)** asks `/sprint` to schedule a 30-minute housekeeping pass that moves them to `design/backend/archive/` with a `README.md` indexing what each captured.

---

## 9. Open contract questions filed as FIXMEs

This refresh surfaced three contract questions where the facade is silent or where the as-built deviation suggests the facade should pin a contract more tightly. All three are filed below as new FIXMEs in `design/arch/fixmes/` per `triad-shared.md` §FIXME protocol.

The §2.6 deviations table is **not** filed as FIXME — those are open implementation work against the existing contract, not contract problems. The Decision-41 follow-through is already pending; this refresh confirms the contract is implementable simply once the implementation catches up.

### FIXME 0094 — Observability gap: GOT-slot population log

`target: /arch`. The integration layer populates GOT slots after each batch's `compile_to_module` returns. There is no first-class log entry per slot population — `Introspection.code_size` records per-defn size but does not record GOT slot index, address, or `Arc<Jit>` identity. Future incident response on a GOT-slot bug would benefit from a structured log. `/arch` decides surface — `Introspection` extension vs. separate trace flag — and whichever it is, this design doc gains a §4.3 elaboration. Backend gains no new surface either way (the log is `int`-side, fed by data backend already returns).

### FIXME 0095 — Pin `Linker::get_symbol` typed-Result shape in facade

`target: /arch`. Facade §"Linker — the cache-load retention newtype" says `pub fn get_symbol(&self, name: &LinkerSymbol) -> Result<*const u8, LinkerError>` (typed Result). The current source has `pub fn get_symbol(&self, name: &str) -> Option<*const u8>`. Decision 37's "no swallowed failures" rule lives at the call site (in `int`), not in backend's API — but the typed-Result shape makes the safety contract facade-visible. This is the closer of the door against the pre-S58 silent-NULL pattern. Confirm + define the `LinkerError` enum in `cranelisp-types` so callers can match.

### FIXME 0096 — Stale subordinate-doc archival pass

`target: /sprint`. Six subordinate docs (named in §8 above) are incident-debug or pivot residue that no longer reflects live design intent. They are still useful as repro references but pollute the "what is the current design?" answer when a contributor scans `design/backend/`. Schedule a 30-minute housekeeping pass that moves them to `design/backend/archive/` with an `archive/README.md` indexing what each captured. Live docs in §8's table stay.

---

## 10. Cross-references

- `design/arch/facades/backend.md` — public surface (authoritative)
- `design/arch/facades/types.md` — boundary types this crate consumes
- `design/arch/bounded-contexts.md` §3 — bounded-context full statement
- `design/arch/principles.md` and `design/arch/principles/NN-*.md` — principles cited above (1, 3, 4, 5, 6, 7, 11)
- `design/arch/CLAUDE.md` Decisions 22, 23, 24, 25, 26, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42 — backend-relevant decisions
- `audits/backend-20260423.md` — temporal snapshot of as-built state at audit date (NOT the target)
- `audits/backend-20260423-{current,target}-state.{mmd,svg}` — diagrams (target diagram aligns with §3.2 above; current diagram is the audit-date snapshot)
- `crates/cranelisp-backend/CLAUDE.md` — `/dev`-narrow code conventions
- `crates/cranelisp-backend/src/` — implementation surface
- 21 subordinate topic docs in `design/backend/` — see §8 above
