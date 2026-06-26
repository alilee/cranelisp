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

### 2.1 The three free functions (facade §"Public surface" — S75 D41-rotated)

The codegen boundary is **exactly three** free functions (facade §"Free functions"). **There is no separate object-compile entry** — the never-real `compile_to_object` free function is retracted (S75; facade tombstone); the object path is `compile_to_module::<ObjectModule>` + **caller** `finish().emit()` (the §2.5 caller-finalize contract in `compile-to-module.md`, symmetric to JIT mode where `int` holds the `JITModule` for `Arc<Jit>` reclaim).

- `compile_to_module<M: Module + CodeFinalizer>(scope, names, symbol_tables, module_aliases, module) -> Result<CompilationArtifacts, CompilationError>` — the **single CLIF emission entry**. Used by `int`'s priority workers (JIT path, per-symbol cardinality per Decision 41) and nice workers (object path, per-module cardinality). Mode is determined by the supplied `M` instance per Decision 23. Backend writes `Code::Jit(Arc<Jit>)` directly into each compiled symbol's entry via `SymbolTable::write_code(&self, sym, code)` (Decision 38; interior mutable) AND writes the resulting fn pointer to the entry's GOT slot via `got().store_slot(slot, ptr)` (D41 #1 + #2). It returns the always-created introspection artefact `CompilationArtifacts { clif_ir, code_size, compile_duration }` **by value** — the caller composes its `Introspection` (REPL/trace mode) or drops it (production batch). Backend never names `Introspection` (D41 #3 retracted, S70 Phase B). The `module_aliases` param feeds `compiler::resolve_func_arity` / `resolve_got_target` qualified-callee resolution.

- `produce_disasm(fq, symbol_tables) -> Result<String, CompilationError>` — the **on-demand disassembly entry**. Invoked lazily by `int` on a REPL `/disasm <fn>` request, NOT eagerly per-compile. Resolves the FQSymbol to its entry, reads the code ptr from `got().load_slot(slot)` + `code_size` from entry metadata, produces the disassembly string. Factored out of `CompilationArtifacts` because disassembly is much more expensive than CLIF-string capture and should not be paid unless asked.

- `load_object(module, object, symbol_tables, module_aliases) -> Result<LinkerArtefact, CranelispError>` — the **JIT-mode cache-hit entry**. Reads a `.o` produced by an earlier object-codegen pass (`compile_to_module::<ObjectModule>` + caller `finish().emit()`) or by `--link` mode, runs the cache linker to resolve each defined symbol's bare-name address (Decision 36), returns `LinkerArtefact { linker: Arc<Linker>, ptrs: HashMap<Symbol, *const u8> }` for `int` to write each ptr to the entry's GOT slot and store `Code::Linker(Arc<Linker>)` as the lifecycle owner (Decision 35). Per-module cardinality (one `Linker` holds many symbols) is unchanged by Decision 41 — the per-symbol direct-write pattern is for `compile_to_module` only. (`Linker::load_object` the method becomes `pub(crate)`; the free fn is the public entry.)

### 2.2 The retention newtypes

- `Jit` (facade §"Jit — the JIT retention newtype") — `Arc<Jit>` is the Decision-31 reclaim primitive. Custom `Drop` calls `unsafe { JITModule::free_memory() }`; the safety invariant is upheld by `int`'s GOT-swap discipline plus the language-level "fn values are heap closures, not raw code pointers" rule. Backend exposes only `new(builder) -> Self` and `module(&mut self) -> &mut JITModule` per facade — there is no public `compile_defn` or per-function entry point on `Jit`.

- `Linker` (facade §"Linker — the cache-load retention newtype") — opaque retention root for cache-hit code regions. `Arc<Linker>` is analogous to `Arc<Jit>` for cache-hit lifecycles. Public surface is `load_object(object: &[u8]) -> Result<Self, CranelispError>` (associated constructor) and `get_symbol(&self, name: &LinkerSymbol) -> Result<*const u8, LinkerError>` — the typed-result accessor per facade §2.6 (defensive resolution, Decision 37 — see §6.2 below).

### 2.3 The per-symbol lifecycle owner

`Code` (facade §"`Code` — the per-symbol lifecycle owner") lives **in this crate** per Decision 41. Post-S75 (FIXME 0244 backend half + the S66 variant slim) it carries **lifecycle ownership ONLY**, with exactly two variants — `Jit(Arc<Jit>)` for fresh-build, `Linker(Arc<Linker>)` for cache-hit. There is **no per-variant `ptr`** (the GOT is the single source of truth for callable addresses — read via `got().load_slot(slot)`) and **no `Code::Primitive`** (the marker is dropped; primitive-ness reads from `kind: DefKind::Primitive`, and primitives entries carry `code: None`). The variant-uniform `Code::ptr()` accessor is removed. `Code` does NOT live in `cranelisp-types` — that would invert the dependency graph and breach Principle 3.

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

### 2.6 As-built deviations from §2.1–§2.5 — CLOSED by S75 W2

The audit `audits/backend-20260423.md` recorded four substantive gaps between the facade target and as-built state. **S75 W2 (boundary rotation) closes all four.** They are no longer "owed future work" — they are the W2 step. Tracked here as the closure record:

| Facade target | Pre-S75 source state | S75 closure |
|---|---|---|
| Single `compile_to_module<M>` entry; no separate object-compile fn | `compile_to_module<M, C, L>` exists; the `lib.rs:821` `compile_to_object` stub (returns `unimplemented!()`, cites never-filed FIXME 0184) is a phantom third entry; `Jit::compile_defn` is an internal per-fn helper | W2 deletes the `compile_to_object` stub; object path is `compile_to_module::<ObjectModule>` + caller `finish().emit()`. `Jit::compile_defn` stays internal-but-exposed (facade Row 9). |
| `compile_to_module(...) -> Result<CompilationArtifacts, CompilationError>` + `module_aliases`; direct `write_code` + GOT-slot writes | `compile_to_module(...) -> Result<CompilationResult, CompilationError>` returning a tuple (`artifacts: HashMap<_, FunctionArtifacts>`, `code_ptrs`, `func_ids`, `entry_func_id`, `func_arities`, `warnings`); no `module_aliases` param | W2 rotates to the D41 signature (FIXME 0221): value-returned `CompilationArtifacts`, `module_aliases` param, `produce_disasm` authored, `CompilationResult` + `FunctionArtifacts` deleted. D41 #1/#2 direct-writes preserved; #3 retracted. |
| `Code` in `crates/cranelisp-backend/src/code.rs`, slimmed to `Jit(Arc<Jit>)`/`Linker(Arc<Linker>)`, no `Primitive` | `Code` already in `crates/cranelisp-backend/src/code.rs` (the D41 move landed) BUT still `{ jit, ptr }` / `{ linker, ptr }` + `Primitive` | W2 slims the variant payloads (drop `ptr`) AND deletes `Primitive` (FIXME 0244 backend half) — both together, no half-rotation (Rev 3). |
| `load_object` free fn returning `LinkerArtefact`; `Linker::load_object` `pub(crate)`; `Linker::get_symbol -> Result<_, LinkerError>` | free `load_object` already exists; `Linker::load_object` still `pub`; `Linker::get_symbol -> Option<*const u8>` | W2 narrows `Linker::load_object` to `pub(crate)`; rotates `get_symbol` to `Result<*const u8, LinkerError>` (D37). |

These were observations *of the source*, not a problem with the **contract** — the contract is implementable simply against the BC + facade, and S75 is the sprint where the implementation catches up. The simplicity check (§4.1) confirms it is a *deletion + re-shape* exercise, not a *redesign*. No FIXME `target: /arch` is owed — the rotation lands the existing canonical design (FIXMEs 0221 + 0244 are the tracking records, resolved in W2).

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
| `display.rs` | 831 | Value/type formatting (belongs in `int` per BC §6 ownership of REPL display; relocation tracked by FIXME 0108) |
| `exe.rs` | 231 | Startup-object generation for `--link` mode |
| `cache/mod.rs` | 653 | Cache facade, paths, load helpers, **deprecated compatibility surface** |
| `cache/manifest.rs` | 419 | Manifest hashing, freshness checks |
| `cache/object.rs` | 707 | Object-module compilation, `build_isa(is_pic)` (the *intended* canonical helper) |
| `cache/serialize.rs` | 734 | Cache metadata serialisation |
| `cache/linker.rs` | 1009 | In-process object loader, relocations, GOT slot handling |
| `got.rs` | 9 | Compatibility re-export (deletion candidate per audit MED-1) |
| `codegen_types.rs` | 9 | Compatibility re-export (deletion candidate per audit MED-1) |

### 3.2 Module layout — target

The target is BC-shaped: `compile_to_module` is the only public CLIF-emission entry; everything else in this crate is implementation detail behind it, behind `produce_disasm`, or behind `load_object`. The object path is `compile_to_module::<ObjectModule>` + caller `finish().emit()` — NOT a separate backend entry (S75 retraction). The target diagram reduces to:

```
caller
  └─ compile_to_module(scope, names, &symbol_tables, &module_aliases, M) ─→ CompilationArtifacts + side-effects
        ├─ build_isa(M.is_pic())                              [single helper, in cache/object.rs]
        ├─ CompileContext::build(scope, names, symbol_tables, module_aliases, isa)   [one builder]
        ├─ for sym in names:
        │     compile_defn(plan, defn) ──→ FnCompiler<M>::compile_body  (Expr::ConstrADT → compile_constr_adt)
        ├─ M.finalize_definitions()                            [JIT path] / no-op [object path]
        ├─ for each compiled sym: write_code(Code::Jit(Arc<Jit>)) + got().store_slot(slot, ptr)
        └─ return CompilationArtifacts { clif_ir, code_size, compile_duration }  [caller composes Introspection or drops]

caller (on-demand disasm)
  └─ produce_disasm(fq, &symbol_tables) ─→ String   [lazy; reads got().load_slot + code_size]

caller (cache-hit)
  └─ load_object(scope, &bytes, &symbol_tables, &module_aliases) ─→ LinkerArtefact { linker, ptrs }
        ├─ Linker::load_object(bytes) ──→ Linker   [Linker::load_object is pub(crate)]
        └─ for each defined symbol: linker.get_symbol(bare_name)?   [Decision 37 defensive → Result<_, LinkerError>]

caller (object)  — NO backend entry; the caller drives it:
  └─ compile_to_module::<ObjectModule>(scope, names, &symbol_tables, &module_aliases, obj) ─→ CompilationArtifacts
        └─ obj.finish().emit()?   [caller-side finalize; bytes + sidecar SymbolTable<(), ()> packaged into ObjectArtefact]

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
compile_to_module(scope, names, &symbol_tables, &module_aliases, &mut M) -> Result<CompilationArtifacts, CompilationError>:
    isa     = build_isa(M.is_pic())                           # cache/object.rs canonical helper
    plan    = CompileContext::build(scope, names, &symbol_tables, &module_aliases, isa)
    declare functions    (bare names, Linkage::Local — Decision 36)
    declare GOT data     (__cranelisp_got_{scope}, mode-resolved at finalize — Decision 23)
    declare runtime imports
    for sym in names where defined_symbols() includes sym:
        compile_defn(plan, defn)                              # emits CLIF via FnCompiler<M>; Expr::ConstrADT → compile_constr_adt
    M.finalize_definitions()
    for each defined sym:
        ptr  = M.get_finalized_function(func_id)
        symbol_tables.get(scope)?.write_code(sym, Code::Jit(jit_arc.clone()))   # lifecycle owner only — no ptr in Code
        symbol_tables.get(scope)?.got().store_slot(slot, ptr)                   # GOT is the single source of truth for the ptr
    return CompilationArtifacts { clif_ir, code_size, compile_duration }        # by value; caller composes Introspection or drops
```

(Object mode: same body against an `ObjectModule`; the caller then runs `obj.finish().emit()` — there is no `get_finalized_function`/`write_code` in object mode, so the per-symbol GOT/`Code` writes are gated by the `CodeFinalizer` capability, not a mode flag.)

JIT cardinality is **per-symbol**: the caller invokes `compile_to_module` once per defined symbol, each invocation creating a fresh `Jit` (and thus a fresh `JITModule`). Object cardinality is **per-module**: one `compile_to_module::<ObjectModule>` invocation processes the full module's defined symbols, then the **caller** runs `obj.finish().emit()` to obtain the bytes (the §2.5 caller-finalize contract — there is no `compile_to_object` backend entry).

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

- `CRANELISP_CODEGEN_DUMP=*|<module>|<module>::<symbol>` writes CLIF to stderr during `compile_to_module` (filter parser in `lib.rs:68`, dump writer at `lib.rs:83`). Cache-hit paths do NOT re-codegen, so use `/clif <name>` from the REPL for those (reads the introspection store).
- `CRANELISP_CODEGEN_TRACE=1` populates the int-side introspection store's `clif_ir` + `disasm` per Decision 38. **S80 D1b refinement (`d1-introspection-repl-only.md`):** the int-side introspection store is now `Option<DashMap>` — `None` outside the REPL — so the mode discriminator is "introspection store present" (REPL-only), not the old per-symbol `is_some()` on a value the backend always returned. Production `--run`/`--link` retains zero record. **The "no wasted generation" floor is the open follow-up (FIXME 0325, §9):** `compile_to_module` still runs `format!("{}", func.display())` unconditionally and returns the CLIF text in `CompilationArtifacts.clif_ir`; int drops it unread in batch. The design intent is a `capture_clif` codegen-input flag (set only when int's `RunMode` populates introspection — REPL) that short-circuits the `func.display()` formatting in `compile_defn_in_module` when false. The `CRANELISP_CODEGEN_DUMP` stderr-dump path is an independent, env-gated debugging aid and MUST stay live regardless of `capture_clif` (it is not introspection-store-bound) — so when `capture_clif` is false the dump path, if its filter matches, formats CLIF for that one defn locally rather than reading a skipped aggregate.
- `CRANELISP_RC_TRACE=1` emits inc/dec events; `LIVE_ALLOCS` debug-asserts catch double-frees (per the runtime crate, but consumed from backend test paths).
- `io-trampoline-trace.md` documents the IO event log used during Wave 1 IO-scheduling debugging.
- `defects-456-reduction.md`, `defect-8-repro-notes.md`, `slice-4-21-hello-io-investigation.md` record specific incident debugging — observability that paid off (these are stale-as-live-design but kept as repro references; see §8).

**Gap**: backend has no first-class log of GOT-slot population. The pre-S58 silent-NULL pattern in `worker.rs:2810-2823` — where `linker.get_symbol(name) == None` was silently treated as "skip this slot" — is the historical defect category Decision 37 addresses. The current `Linker::get_symbol(&self, name: &str) -> Option<*const u8>` method is `Option`-returning; the *defensive* error must be raised at the call site (in `int`), not in backend's API. Backend's facade is correct (expose `Option`, let the caller decide what's fatal); the safety invariant lives in the caller's discipline.

The audit does not flag a positive log of "slot N for symbol s populated with ptr P" beyond `Introspection.code_size`. This is acceptable for now — the safety invariant (Decision 37) is the regression net — but a known gap for future incident response. **FIXME 0099** (`*-gotobserver-implementation.md`) tracks the resolution: `/arch` chose option B (ring buffer + observer callback paralleling Decision 40's `IoObserver`) over an `Introspection` extension. Backend exposes the `GotObserver` contract (`got_observer.rs`); `int` implements the ring-buffer state.

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
- Object mode keeps per-module batching: one `ObjectModule` holds the whole module's defined symbols, written in a single `compile_to_module::<ObjectModule>` call; the caller then `finish().emit()`s (no `compile_to_object` entry).

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

### 6.1 Cache writes — the object path (`compile_to_module::<ObjectModule>` + caller `finish().emit()`)

There is **no `compile_to_object` backend free function** (S75 retraction). The nice worker drives the object path itself: it calls `compile_to_module::<ObjectModule>(scope, names, &symbol_tables, &module_aliases, &mut obj)`, then finalises the module caller-side via `obj.finish().emit()` to obtain the bytes, and packages bytes + sidecar into the `ObjectArtefact { object, sidecar }` it persists.

- `object: Vec<u8>` — Mach-O / ELF / COFF emitted via `cranelift-object` (from the caller's `finish().emit()`). Per Decision 36, every user function is `Linkage::Local` with bare-name symbol. Per Decision 23, the `__cranelisp_got_{scope}` data symbol is `Linkage::Export` with relocation initialisers ordered by `SymbolTable[scope].symbols[name].got_slot`.
- `sidecar: SymbolTable<(), ()>` — the schema-versioned (Decision 34) serialised symbol table. The integration layer's `ObjectCache::write` writes both files paired (Decision 25 pairing invariant; cache-load enforces `meta.json` ⇒ `.o` invariant).

`ObjectArtefact` is a backend-authored DTO (facade §"Return shapes"); backend writes nothing to disk. File IO is `int`'s.

### 6.2 Cache reads — `load_object`

The cache-hit path is **not** a parallel codepath (Decision 37). It lives inside the integration layer's recursive `register_module` flow. Backend's role:

- `load_object(scope, &object_bytes, &symbol_tables) -> Result<LinkerArtefact, CranelispError>` — `Linker::load_object(bytes)` mmaps the bytes, runs relocations, indexes the symbol table.
- For each defined symbol `s` in `symbol_tables[scope]`, `linker.get_symbol(bare_name(s))` resolves the address. Bare-name lookup per Decision 36; `Linkage::Local` symbols are still indexable from the in-process linker (it filters only `.L*`-style debug symbols).
- Returns `LinkerArtefact { linker: Arc<Linker>, ptrs: HashMap<Symbol, *const u8> }` — `int` writes resolved ptrs into the SymbolTable GOT slots and constructs `Code::Linker { linker, ptr }` per symbol via `write_code`.

**No swallowed failures (Decision 37)**. The facade exposes `Linker::get_symbol(&self, name: &LinkerSymbol) -> Result<*const u8, LinkerError>` (a typed `Result`, not the source's current `Option`). At facade-level the contract is: **callers MUST treat resolution failure as `CacheLoadError`, not silently push NULL**. The pre-Sprint-58 `worker.rs:2810-2823` regression came from the `Option` → silent-skip pattern; Decision 37 plus the typed `Result` shape closes the door. The typed-`Result` shape is now pinned in `facades/backend.md`; **FIXME 0100** (`*-relocate-single-consumer-types*`) Phase 2 covers placing `LinkerError` and the rest of backend's single-consumer types in `cranelisp-backend` per Principle 15.

### 6.3 Schema versioning (Decision 34)

`.meta.json` carries `schema_version: u32`. Mismatch invalidates the cache as if dependencies changed — not a cryptic deserialise error. Backend defines the constant `CACHE_SCHEMA_VERSION` in `cache/mod.rs`. Cache-write emits it; cache-load reads it first. The current value is `1` (Sprint 58 Step 5b).

### 6.4 In-process linker

`cache/linker.rs` (1009 lines) is backend's in-process object loader. It exists because JIT-mode cache-hit cannot use the system linker — it needs to mmap a `.o` and resolve relocations against in-memory addresses (runtime functions, GOT data symbols of other modules already loaded). The linker handles ELF / Mach-O variant uniformly per host platform. Subordinate docs: `executable-generation.md` for the dual `--link` system-linker path, `cache-repl-loads-triage.md` for the symptom history (now archive-candidate).

### 6.5 Object file contract — what crosses the boundary

Per facade §"Object file contract", the `.o` is **one file consumed by two readers**: in JIT mode by `Linker::load_object` (cache-hit path), in `--link` mode by the system linker. The two-GOT model in Decision 23 distinguishes which GOT is consulted at finalize, NOT where the `.o` lives. Backend emits identical CLIF for both modes; the `Module` impl supplied at finalize determines resolution. The `--link` mode `_main` alias is `int::link_by_name`'s job, not backend's.

---

## 7. Decision register

Per `design/arch/CLAUDE.md`'s active-vs-legacy split: active Decisions carry forward-handoff or pre-implementation work; legacy Decisions are fully embodied in the architecture and preserved for narrative continuity.

### Active

| Decision | Backend takeaway |
|---|---|
| **31** — `Arc<Jit>` + custom `Drop` calls `unsafe free_memory()`; per-symbol JIT cardinality (per Decision 41 amend) | The `Jit` newtype; safety invariant relies on `int`'s GOT-swap discipline (environmental — Cranelift `Memory::drop` evidence; amended S64) |
| **35** — `Code` enum (per Decision 41 amend, lives in `cranelisp-backend/src/code.rs`) | Backend constructs `Code` directly; integration layer also names it at session boundary; Principle 3 protected — `Code` does NOT enter `cranelisp-types` (operative) |
| **40** — `trace.rs`/`io_trace.rs` relocate to int; runtime keeps `IoObserver` callback contract | Backend unchanged — backend's observability surfaces (CLIF dump, RC trace) are codegen-side; runtime's observation contract is orthogonal (pre-implementation) |
| **41** — `compile_to_module` per-symbol JIT cardinality; `Code` moves to `cranelisp-backend`; backend writes shared state directly; `Result<(), CompilationError>` | The single largest pending refactor against this design. Amends Decisions 31, 35. See §2.6 deviations table (pre-implementation) |
| **42** — `PlatformError` adopts `ErrorLocation` per variant | Backend's platform-related codegen paths surface `CranelispError::Platform` with `ErrorLocation`-carrying variants when relevant (pre-implementation) |

### Legacy — embodied

| Decision | Backend takeaway |
|---|---|
| **22 (legacy — embodied)** — `defined_symbols()` predicate | One filter; `compile_to_module` trusts the contract or returns `CompilationError::SymbolNotCompilable` |
| **23 (legacy — embodied)** — Uniform codegen, two-GOT model | One CLIF, two resolvers; mode is a property of the supplied `M`, not a parameter |
| **24 (legacy — embodied)** — Uniform consuming calling convention | Caller transfers ownership of heap params; callee owns. No "borrowing" classification. RC discipline is uniform across user fns, traits, builtins, externs, and constructors. |
| **25 (legacy — embodied)** — Code on `ModuleEntry::Def.code`; cache stores `.meta.json` + `.o` | Backend writes Code directly (per Decision 41 amend) into `ModuleEntry::Def.code`; cache-load reads both files paired |
| **26 (legacy — embodied)** — Platform fn ptrs on `ModuleEntry::Def.platform_fn_ptr`; `scheduling_class` in variant | Backend reads platform ptrs from symbol-table import chains, not a side registry |
| **32 (legacy — embodied)** — `CodeStore` / `LinkerStore` empty markers + `Clone` super-bound | Backend signatures use `SymbolTable<Code, ()>` (per Decision 41 amend; previously `<C, L>`-blind) |
| **33 (legacy — embodied)** — Structural decls on `SymbolTable` | Backend reads imports/exports/etc. from symbol table directly |
| **34 (legacy — embodied)** — `schema_version: u32` cache envelope | Backend owns `CACHE_SCHEMA_VERSION` constant; cache-load checks first |
| **36 (legacy — embodied)** — Bare names + `Linkage::Local` uniformly | No `user`/`main` special case; `--link` `_main` alias is `int`'s job |
| **37 (legacy — embodied)** — Cache-hit lives inside `register_module`; codegen phase order-independent; defensive resolution | No `try_cache_hit_load` parallel path; `Linker::get_symbol` failure is `CacheLoadError`, never silent skip |
| **38 (legacy — embodied)** — `SharedState` is the formal worker-shareable subset; per-symbol mutability via `&SymbolTable` interior mutability (`write_code(&self, sym, code)`) | Backend operates on read-only symbol-table view + interior-mutable `write_code` |
| **39 (legacy — embodied)** — Per-defn source on `Introspection.source`; errors carry `ErrorLocation` | `CRANELISP_CODEGEN_TRACE=1` populates `clif_ir`/`disasm` on `Introspection`, not on `ModuleEntry::Def` |

Decisions not listed (1–9 cross-crate framing, 10 base-pointer ABI in interface-types territory, 27 G8-before-G9 orchestration, 28 retracted, 29–30 form-by-form scheduler in int) are either consumed orthogonally or not backend-shaped.

---

## 8. Subordinate topic docs

The existing docs under `design/backend/` (this `backend.md` is the master; 5 incident-debug docs moved to `archive/` in S75 W5 per FIXME 0096) elaborate specific subsystems. This master doc points; it does not reproduce. Live (cite-as-design-intent) vs stale (cite-as-historical-reference) is called out explicitly per the §1 framing — stale docs remain useful for repro context but should not be cited as authoritative.

| Topic | File | Status |
|---|---|---|
| Compilation function shape | `compile-to-module.md` | **Live**. Authoritative on §17 generics activation; describes Decision 25 + 32 + 35 outcome. **S75 banner at top of file** states the D41-rotated target (`Result<CompilationArtifacts, CompilationError>` + `module_aliases` param + `produce_disasm`; `compile_to_object` retracted; 3-entry boundary; `Code` slim + `Primitive` drop; `compile_constr_adt` §2.6). The body §8/§9.1 `CompilationResult` text is pre-rotation migration narrative superseded by the banner. |
| Minimal JIT-setup boundary (S76) | `jit-setup-boundary.md` | **Live**. Authoritative on the `Jit::new(symbol_tables)` constructor (the BC §3 minimal-JIT-setup boundary), `cranelisp_intrinsics::INTRINSICS_TABLE` consumption (construct + cache-hit), the `.meta.json` platform `schema_literal` round-trip (FIXME 0232), and the 0122 `--link` GOT-alignment re-test (fix already in `lib.rs:388`). Confirms the S76 W-Macro change is a backend NO-OP. |
| Ring 1 codegen | `ring1-codegen.md` | **Live**. Stable. Ring 0/1 primitives backbone. §"Bitwise Inline Primitives (FIXME 0416, S91)" is authoritative on the `bit-and/or/xor/not`·`shl`·`shr`·`popcount` 1:1 CLIF lowering, `add-i64`-mirrored registration, Cranelift-implicit shift masking, and zero public-API/`cranelisp-types` movement |
| Ring 2 RC discipline | `ring2-rc.md` | **Live**. Authoritative on Decision 24 (uniform consuming convention). §10 addendum (string-literal RC residual through `print`) is current. **§1.6 (S84 / FIXME 0375) — retire the unsound `<1024` RC guard from the `Type::Var` path** (gated on FIXME 0374 typecheck Tier-2): `classify(Type::Var)` becomes `unreachable!`; the guard is kept ONLY for the type-known mixed-ADT nullary-tag path (BC §3 invariant 9). §1.5 records the two historical sources of `Mixed` and why they are separable at `classify`, not at the 15 guarded-RC call sites |
| Per-module GOT | `per-module-got.md` | **Live**. Authoritative on Decision 23's two-GOT runtime. Read alongside `compile-to-module.md` §5 |
| JIT/Object convergence | `jit-object-convergence.md` | **Live as design intent**; source is behind. Audit HIGH-1 directly relevant. The convergence is **not yet landed in the source** — Phase 1 of audit's plan is the convergence step |
| Module caching | `module-caching.md` | **Live**. Read alongside Decisions 25, 34, 37 |
| Executable generation | `executable-generation.md` | **Live**. `--link` mode; backend's `exe.rs` (231 lines) |
| HKT codegen | `hkt-codegen.md` | **Partial / stale**. Sprint 24 era; check against current monomorphisation pipeline before extending |
| IO trampoline | `io-trampoline.md` | **Live**. Backend's IO trampoline design |
| IO scheduling | `io-scheduling.md` | **Live**. Overlaps with §10.12 spec |
| IO trampoline trace | `archive/io-trampoline-trace.md` | **Archived (S75 W5, FIXME 0096)**. Incident-debug residue. Reference only |
| Lenient eval | `lenient-eval.md` | **Live**. Spec §12.4.3 + §10.12 backend story |
| FQTypeName cache | `sprint51-fqtypename-cache.md` | **Partially stale**. Sprint 51 era; Decision 34's `schema_version` replaces the pre-S58 manifest hashing for shape changes |
| Sprint 19 panic boundary | `sprint19-panic-boundary.md` | **Live**. Catchable runtime panics. Check against current `runtime_panic` extern declared in facade §"Consumed surface" |
| AST-sourced codegen | `ast-sourced-codegen.md` | **Partially superseded** by Decision 25 (the `Def.ast` field). Cite cautiously |
| Auto-curry + run-tests | `auto-curry-and-run-tests.md` | **Live**. A2 + R1 codegen primitives |
| Cache REPL loads triage | `archive/cache-repl-loads-triage.md` | **Archived (S75 W5, FIXME 0096)**. Post-Decision-37 the "no swallowed failures" outcome lands in `module-caching.md`. Reference for history only |
| Defect 8 repro notes | `archive/defect-8-repro-notes.md` | **Archived (S75 W5, FIXME 0096)**. Keep as cross-skill repro example |
| Defects 4/5/6 reduction | `archive/defects-456-reduction.md` | **Archived (S75 W5, FIXME 0096)**. Sprint 59 W1 incident-debug residue |
| Slice 4 / 21-hello-io | `archive/slice-4-21-hello-io-investigation.md` | **Archived (S75 W5, FIXME 0096)**. Sprint 61 era closure double-free reduction; keep for repro |

**Archival done (S75 W5, FIXME 0096).** The five firmly-stale "Stale as live design" docs (`io-trampoline-trace.md`, `cache-repl-loads-triage.md`, `defect-8-repro-notes.md`, `defects-456-reduction.md`, `slice-4-21-hello-io-investigation.md`) moved to `design/backend/archive/` with an `archive/README.md` index. The two **partially**-stale docs (`hkt-codegen.md`, `sprint51-fqtypename-cache.md`, `ast-sourced-codegen.md`) retain residual live content and stay at the top level as cite-with-care references. FIXME 0096 may be `git rm`'d once `/sprint` confirms.

---

## 9. Tracked FIXMEs

The §2.6 deviations table is **not** filed as FIXME — those are open implementation work against the existing contract, not contract problems. The Decision-41 follow-through is already pending; this refresh confirms the contract is implementable simply once the implementation catches up.

The contract questions surfaced by earlier refreshes have all been resolved into existing FIXMEs:

### FIXME 0099 — GotObserver implementation (was: GOT-slot population log gap)

`target: /dev`. `/arch` chose option B (ring buffer + observer callback paralleling Decision 40's `IoObserver`) over an `Introspection` extension. Backend exposes the `GotObserver` contract (`crates/cranelisp-backend/src/got_observer.rs` — `GotEventTag`, `GotEvent`, `GotProvenance`, `GotObserver`, `register_got_observer`); `int` implements the ring-buffer state and env-var activation. See `design/arch/fixmes/0099-dev-backend-int-gotobserver-implementation.md`.

### FIXME 0100 — Relocate single-consumer types (was: pin `Linker::get_symbol` typed-Result shape)

`target: /dev`. The typed-`Result` shape for `Linker::get_symbol(&self, name: &LinkerSymbol) -> Result<*const u8, LinkerError>` is now pinned in `facades/backend.md`. FIXME 0100 Phase 2 covers placing `LinkerError`, `CompilationError`, and the GOT observer types in `cranelisp-backend` per Principle 15 (facade types live with their behavior). See `design/arch/fixmes/0100-dev-relocate-single-consumer-types-to-originating-crates.md`.

### FIXME 0096 — Stale subordinate-doc archival pass

`target: /sprint`. **DONE (S75 W5).** The five firmly-stale incident-debug docs moved to `design/backend/archive/` with an `archive/README.md` index; §8's table rows now point at `archive/`. The two partially-stale docs (`sprint51-fqtypename-cache.md`, `ast-sourced-codegen.md`) retain residual live content and stay top-level. FIXME 0096 is ready for `git rm` at `/sprint`'s confirmation. See `design/arch/fixmes/0096-design-backend-stale-subordinate-doc-archival.md`.

### FIXME 0108 — Relocate `display.rs` to `int`

`target: /dev`. `crates/cranelisp-backend/src/display.rs` (831 LOC) implements REPL value/type formatting; per BC §6 this belongs in `int`, not `cranelisp-backend`. Mechanical relocation; bundle naturally with FIXME 0099 or FIXME 0100 (both are `/dev`-narrow to backend + int). See `design/arch/fixmes/0108-dev-relocate-backend-display-rs-to-int.md`.

### FIXME 0325 — Skip CLIF-IR text generation in batch when introspection is off (S81 sub-wave 6a)

`target: /backend`. The data-flow completion of D1b's REPL-only-introspection ruling (`memory/introspection-repl-only-principle.md`). **Not a defect** — batch output is byte-identical; this is wasted `format!("{}", func.display())` allocation per compiled fn in `--run`/`--link`. **Design intent (§4.3):** a `capture_clif: bool` threaded into codegen; `compile_defn_in_module` skips the CLIF rendering when false; `code_size` (a cheap genuine byproduct read from `ctx.compiled_code()`) keeps flowing. The `CRANELISP_CODEGEN_DUMP` env-gated dump path stays live regardless (it is a debugging aid, not introspection-store-bound). **Threading shape — the design call:** the public entry `compile_to_module<M,C,L>(module_path, names, symbol_tables, module_aliases, &mut M)` is a 5-arg fn (`public-api.txt:579`). Adding `capture_clif` is a **public-surface change carrying a backend `public-api.txt` baseline regen** (called out in 0325 + SPRINT §6). Preferred: a single `bool` param (smaller diff than introducing a `CompileOptions` struct for one field; Principle 6 — complexity budget; a struct is the right move only if a second codegen-input flag is imminent, which it is not). The caller (int) passes `true` only when its `RunMode` populates the introspection store (REPL). See `design/arch/fixmes/0325-backend-skip-clif-when-introspection-off.md`.

### FIXME 0011 — `SchedulingClass` into the IO Effect node payload (S81 sub-wave 6a — likely DOC-CLOSE)

`target: /backend`. The Effect-node trampoline emit site (now `crates/cranelisp-intrinsics/src/io.rs:189`, **not** the FIXME's stale `cranelisp-runtime/src/io.rs:173` ref — the runtime crate was dissolved by D43) emits `scheduling_class: 0` as a placeholder because the class attaches to the platform symbol's manifest, not the runtime Effect node, and the trampoline has no symbol back-reference. The FIXME offered two resolutions: (a) thread the class into the Effect-node IR payload at codegen, or (b) document that the class is recovered via cross-trace correlation against int's scheduler trace (which carries it). **Disposition (design call):** the FIXME deferred "pending Slice 4 evidence"; no Slice-4 consumer demanding the class on the trampoline event has materialised, and `design/backend/io-scheduling.md:319` confirms backend does not interact with `SchedulingClass` (the independence-analysis decision is int's, pre-backend). Absent a concrete consumer, resolution (b) is the proportionate close — **no codegen change, no IR-payload extension, no baseline touch.** Record (b) in `io-scheduling.md` (the cross-trace-correlation recovery path) and close. Re-open with a node-payload extension only if a future scheduling-diagnostics consumer needs the class without correlation. See `design/arch/fixmes/0011-thread-scheduling-class-into-effect-payload.md`.

### FIXME 0258 — trace-defect tracker (S81 sub-wave 6a — STALE, all 3 defects already resolved)

`target: /qa` (tracker), resolvers `/dev backend` + `/dev intrinsics`. Held three named trace defects open as failing-not-ignored tests. **Verified against current source (2026-06-13): all three are RESOLVED and their tests are GREEN (suite 1231/0/1):** (1) **lexical-guard gap** — `crates/cranelisp-intrinsics/src/trace.rs:363` now also raises on the no-wrapper-yet lexical `(trace (trace e))` via the `already_swapped` branch (landed `548f0f6`, S77 W-Trace); `trace_nested_lexical_raises_runtime_error` passes. (2) **ADT-render overflow** — `bake_descriptor` now bounds depth at `MAX_DESCRIPTOR_DEPTH` and degrades interior repeats (`crates/cranelisp-backend/src/compiler/trace_codegen.rs:135,341`; landed `7ee37c2`, S76 W1.5); `trace_polymorphic_adt_result_renders` + `trace_adt_value_render_overflows_defect` pass. (3) **trait-prelude swap-all overflow** — same descriptor-depth bound resolves the `TestStandard`-prelude case; `trace_trait_heavy_prelude_overflows_defect` passes. **Disposition:** the /dev resolution work is complete; the tracker is stale. Close by (a) `/qa` flipping the three `[S77] FAILING` rows in `tests/plan/PLAN.md` (T2/T9/T10/T11) to GREEN with the resolving-commit cites, and (b) `git rm`-ing the FIXME. **Bonus reduction** — no backend code work. See `design/arch/fixmes/0258-qa-trace-nested-error-linked-binary-swap-all-tests.md`.

---

## 10. Cross-references

- `design/arch/facades/backend.md` — public surface (authoritative)
- `crates/cranelisp-types/src/lib.rs` `//!` rustdoc + per-item `///` — boundary types this crate consumes; `design/arch/bounded-contexts.md` §7 for cross-type narrative
- `design/arch/bounded-contexts.md` §3 — bounded-context full statement
- `design/arch/principles.md` and `design/arch/principles/NN-*.md` — principles cited above (1, 3, 4, 5, 6, 7, 11)
- `design/arch/CLAUDE.md` Decisions 31, 35, 40, 41, 42 (active) and 22, 23, 24, 25, 26, 32, 33, 34, 36, 37, 38, 39 (legacy — embodied) — backend-relevant decisions
- `audits/backend-20260423.md` — temporal snapshot of as-built state at audit date (NOT the target)
- `audits/backend-20260423-{current,target}-state.{mmd,svg}` — diagrams (target diagram aligns with §3.2 above; current diagram is the audit-date snapshot)
- `crates/cranelisp-backend/CLAUDE.md` — `/dev`-narrow code conventions
- `crates/cranelisp-backend/src/` — implementation surface
- subordinate topic docs in `design/backend/` (+ `design/backend/archive/` for the 5 incident-debug docs archived S75 W5 per FIXME 0096) — see §8 above
