# Phase 2 Codegen Convergence — Integration-Layer Design

**Sprint**: 56 (Phase 2 of `design/arch/pipeline-v4-roadmap.md`)
**Owner**: `/int`
**Scope**: Step 2b — delete `codegen_module_symbols` and route JIT through `compile_to_module`
**Status**: DRAFT

This document covers the integration-layer changes required for Step 2b of Phase 2 codegen convergence. It is the `/int` companion to `/backend`'s `design/backend/compile-to-module.md` (Wave 1 update) and `/typecheck`'s `design/typecheck/ast-annotation.md` (Wave 0 update).

## 1. Problem Statement

Today the compiler has **two** codegen entry points, each with its own GOT/JIT wiring logic:

| Path | Entry | File:line | What it compiles |
|------|-------|-----------|------------------|
| Object (.o via nice worker) | `cranelisp_backend::compile_to_module` | `src/session_v4.rs:3346` | Whole module at once |
| JIT (priority worker) | `crate::worker::codegen_module_symbols` | `src/worker.rs:2541` | Iterates `program`, calls `compile_and_register_defn_shared` per defn |

The object path is already "new-style": it hands a module path, a program-shaped input, and the shared symbol tables to `compile_to_module`, which reads GOT slots from `ModuleEntry::Def` and follows Import chains. After Phase 1 (Sprint 55), bodies and annotations live on `ModuleEntry::Def.ast` and on `Expr` nodes.

The JIT path is the holdout. It:

1. Allocates JITs **per-defn** internally via `compile_and_register_defn_shared` (`src/pipeline.rs:235`), creating one `JITModule` per `Defn`.
2. Builds a `SessionCompilationEnv` (`src/worker.rs:87`) that today's backend `CompilationEnv` trait consumes for GOT resolution. This duplicates the lookup logic already encoded against `symbol_tables` on the object path. Step 2b retires both the trait and the in-`src/` env (see `design/backend/compile-to-module.md` §12 for the uniform Module-resolved replacement).
3. Pre-allocates GOT slots for names the typechecker did not register (`pre_register_got_slots_in_tc` at `src/worker.rs:2593`). Wave 0 closes this gap: the typechecker now registers every compilable name with `ast: Some(_)` and its own `got_slot`.
4. Collects platform-function JIT symbols and GOT data defs via `SessionCompilationEnv::collect_jit_setup_for_module` (`src/worker.rs:308`). After Step 2b, cross-module GOT data defs are uniform `Linkage::Import` declarations emitted by `compile_to_module` (resolved via `JITBuilder::symbol_lookup_fn` on the JIT path and via linker relocations on the object path — see `design/backend/compile-to-module.md` §12). Platform function pointers are registered by the caller directly on the `JITBuilder` via `JITBuilder::symbol` before `JITModule::new`, as shown in the §5 pseudocode.
5. Calls `expand_multi_sig_defn` inside the backend on `DefnMulti` entries. Wave 0 pre-materialises mangled variants on the symbol table — this expansion becomes dead code.

The JIT and object paths have **diverged** on multi-sig handling: three deferred tests (`sketch_multi_sig_type_based_dispatch`, `sketch_multi_sig_different_arities`, `sketch_repl_multi_sig_different_arities`) fail today because the JIT path's multi-sig expansion in `collect_and_declare_defns` does not match the object path's expansion in `expand_multi_sig_defn`. Converging on one function removes the divergence; they pass as a direct byproduct of Step 2b.

Phase 2 collapses the two paths. After Step 2b, `compile_to_module` is the sole codegen entry point for both JIT and object compilation. The JIT path differs from the object path only in *which `cranelift_module::Module` implementation is supplied* (`JITModule` vs `ObjectModule`) and in *what the caller does with the finalised code pointers* (write into per-function `Code` + GOT store for JIT; emit `.o` bytes for object).

## 2. Target State

1. The priority worker claims a `Typecheck` or `JitCodegen` work item from the scheduler and, after form processing completes, calls `cranelisp_backend::compile_to_module(module_path, names, symbol_tables, &mut jit_module)` directly — **once per compilation unit**, with a freshly-created `JITModule`.
2. `names` is obtained via `SymbolTable::defined_symbols()` (Wave 0 deliverable) on the module's symbol table. This is a single shared filter used by both JIT and object callers; no caller re-enumerates the symbol table with its own predicate.
3. `compile_to_module` reads bodies from `ModuleEntry::Def.ast` and annotations from `Expr` nodes. Multi-sig variants, mono specializations, default method defns, trait-impl methods, and the REPL `__expr` synthetic are all uniform entries — the backend does no special expansion.
4. After `compile_to_module` returns, the priority worker calls `jit_module.finalize_definitions()?`, extracts each `FuncId` → code pointer via `jit_module.get_finalized_function(func_id)`, writes the pointer into the module's GOT slot (read from `ModuleEntry::Def.got_slot`), and stores a `Code { jit: jit_module, ptr }` keyed by symbol in the `CodegenProduct` DashMap — the *same* temporary home Step 2b leaves in place (see §4).
5. `codegen_module_symbols`, `compile_regular_defns`, `compile_and_register_defn_shared`, `pre_register_got_slots_in_tc`, and `SessionCompilationEnv` are deleted. `SessionCompilationEnv::collect_jit_setup_for_module` is deleted. The `finalize_module` REPL `__expr` special case, mono-inlining loop, default-method-inlining loop, and post-pass enrichment loop are deleted (Wave 0 makes each of these redundant).
6. One `JITModule` per compilation unit per priority-worker invocation — not per-defn and not per-session. This is the §9.4 "per-function JIT isolation" target in its Phase 2 form: "per-function" in the steady state because the scheduler hands priority workers one symbol at a time (`PriorityWork::JitCodegen(module, symbol)`), but the seam is `compile_to_module(..., names, ..., module)` so a caller that wants to compile several symbols into one JIT (e.g. a future batch path) is free to pass a larger `names` list.

## 3. SessionCompilationEnv Replacement Map

All `SessionCompilationEnv` methods are deleted in Step 2b. The backend's `compile_to_module` reads `symbol_tables` directly for all the data `SessionCompilationEnv` was serving. Mode-specific GOT resolution is handled outside the backend by the `Module` implementation (Object: relocations; JIT: `JITBuilder::symbol_lookup_fn`). See `design/arch/pipeline-v4.md` §9.3 and Principle 11 in `design/arch/CLAUDE.md`; the GOT reference emission mechanism is specified in `design/backend/compile-to-module.md` §12.

Authoritative table:

| `SessionCompilationEnv` method | Called from (today) | Disposition in Phase 2 |
|---|---|---|
| `resolve_got(&self, name: &Symbol) -> Option<(i64, usize)>` | Trait impl consumer during codegen | DELETED. Backend emits `global_value` against `Linkage::Import` data symbol `__cranelisp_got_{module}`; linker (object) or `JITBuilder::symbol_lookup_fn` (JIT) resolves it. |
| `resolve_got_module(&self, name) -> Option<(ModuleFullPath, usize)>` | Trait impl — consumed by cross-module call emission | DELETED. Cross-module resolution happens inside the backend reading `symbol_tables` directly. |
| `func_arity(&self, name) -> Option<usize>` | Trait impl — auto-curry and cross-module arity checks | DELETED. Derived inside the backend from `ModuleEntry::Def.param_names.len()` via Import-chain walk on `symbol_tables`. |
| `resolve_in_module(&self, module, name, depth)` *(private helper)* | Called by `resolve_got` | DELETED with its caller. |
| `resolve_module_slot(&self, module, name, depth)` *(private helper)* | Called by `resolve_got_module` | DELETED with its caller. |
| `arity_in_module(&self, module, name, depth)` *(private helper)* | Called by `func_arity` | DELETED with its caller. |
| `collect_jit_setup_for_module(platform_registry) -> (jit_symbols, got_data_defs)` | Called from `codegen_module_symbols` (worker.rs:2565) and `codegen_and_execute` (session_v4.rs:1473) | DELETED. Platform function pointers are registered on the `JITBuilder` by the caller via `JITBuilder::symbol` / `symbol_lookup_fn` before `JITModule::new`. GOT data defs are uniform `Linkage::Import` declarations emitted by `compile_to_module`; the JIT caller's `symbol_lookup_fn` maps `__cranelisp_got_{name}` to `symbol_tables[name].got.base_ptr()`. Platform-registry DLL lifetime management is unaffected — `LoadedPlatforms` still lives on `CompilerSession`. |

**Historical note.** Earlier Phase 3a iterations proposed JIT-specific env types and wrappers (`JitCompilationEnv`, `ObjectCompilationEnv`, `compile_to_module_jit`, `compile_to_module_object`, a crate-private `compile_to_module_core`, and a `CodegenTarget` enum); retracted in favour of the uniform Module-resolved strategy in `design/arch/pipeline-v4.md` §9.3 and Principle 11 in `design/arch/CLAUDE.md`. The `CompilationEnv` trait itself is also deleted — see `design/backend/compile-to-module.md` §12.

**Principle 7 check**: Single source of truth. The split between env impls was exactly the duplication Principle 7 warns against — two implementations of the same resolution logic, one for JIT and one for object. Step 2b collapses them to one: `compile_to_module` reading `symbol_tables`.

## 4. JITModule Lifetime (Phase 2→3 Bridge)

Per `/arch` review §6 condition 4, the per-function `JITModule` lifetime is explicitly scoped in Phase 2 so the Phase 3 G6 transition is a bounded refactor, not a rewrite. **`/arch` Phase 3a review §3 (Principle 8 Check) confirms** that wrapping the finalised module in `Arc<JITModule>` inside `Code` is NOT interim architecture — the `Arc` stays valid when `Code` moves onto `ModuleEntry::Def` in Phase 3 G6 (multiple entries sharing one finalised JIT module is a legitimate data sharing pattern, not a workaround).

**Phase 2 decision**: a `JITModule` is created per call to the priority worker's codegen step. At steady state, one call compiles one symbol (the scheduler hands priority workers one `PriorityWork::JitCodegen(module, symbol)` at a time), so there is one `JITModule` per compiled symbol — §9.4 target behaviour, met.

**Per-symbol lifetime**:

1. Priority worker creates `let mut jit_module = create_jit_module(extra_symbols)?;` where `extra_symbols` is the small set of runtime intrinsic pointers the backend also registers internally (see §5 pseudocode).
2. `compile_to_module(module_path, &names, &symbol_tables, &mut jit_module)` populates and defines functions. Internally it declares intrinsics on the module.
3. The worker calls `jit_module.finalize_definitions()?;` — this is the caller's responsibility because `compile_to_module` is generic over `M: Module` and `ObjectModule` does not have `finalize_definitions`. The `compile_to_module` docstring already notes this contract.
4. For each name in the result's `func_ids`, the worker calls `jit_module.get_finalized_function(func_id)` to get a `*const u8` code pointer, writes it to the symbol's pre-assigned GOT slot via `got.store_slot(slot, ptr)`, and stores a `Code { jit: jit_module_clone_or_rc?, ptr }` keyed by the symbol. Since `JITModule` is not `Clone`, storing several `Code` entries that share one `JITModule` requires wrapping the module in `Arc<JITModule>` or moving the module into a single `Code` entry (when `names.len() == 1`, the steady state, this is trivial).
5. The `Code` value is inserted into `CodegenProduct.code: DashMap<Symbol, Code>` (`src/session_v4.rs:420`). This keeps the JIT-owned executable memory alive for the process lifetime (or until REPL redefinition replaces the entry). **No change to `CodegenProduct`'s shape in Phase 2**.

**Explicit non-goal for Phase 2**: Do **not** move `Code` onto `ModuleEntry::Def.code`. That is Phase 3 G6. Step 2b keeps `CodegenProduct` as the temporary home. Reason: moving `code` onto `ModuleEntry::Def` requires either (a) the `SymbolTable<C, L>` generic parameterisation specified in `pipeline-v4.md §9.1`, or (b) a concrete `Option<Code>` field with `#[serde(skip)]` and cross-crate leakage of the `Code` type. Neither change is in Phase 2's scope. `CodegenProduct` is the correct bridge.

**Concurrency note**: multiple priority workers can execute `compile_to_module` concurrently on different modules. Each worker owns its own `JITModule` for the duration of the call. No shared JIT state exists between workers. See §9 risks for the intra-module case (two workers on the same module).

**Redefinition**: REPL eval replaces a defn → a new `JITModule` is created, a new `Code` is inserted into `codegen_products[module].code` replacing the prior entry (or the old entry is kept via explicit retention policy for in-flight calls). The GOT slot atomic-store swaps the pointer. The old `Code` drops when its entry is evicted, freeing the old executable memory. This is unchanged from today.

## 5. Priority Worker Loop

The existing priority worker (`src/worker.rs:2878 priority_worker_loop` and `src/worker.rs:3037 priority_worker_thread`) calls `codegen_module_symbols` inside the `ProcessResult::Complete` branch of `process_module_forms`. Step 2b inlines a direct `compile_to_module` call in its place. Per `design/arch/pipeline-v4.md` §9.3 and Principle 11 in `design/arch/CLAUDE.md`, the backend has a single entry point — `compile_to_module<M: Module>(module_path, names, symbol_tables, module) -> CompilationResult` — with no env parameter and no mode. GOT resolution is uniform: the backend emits `Linkage::Import` data symbols named `__cranelisp_got_{module}`; the JIT caller pre-registers a `JITBuilder::symbol_lookup_fn` that maps that name to the GOT's runtime base pointer (see `design/backend/compile-to-module.md` §12). `CompilationResult.artifacts: HashMap<Symbol, FunctionArtifacts>` is populated per-symbol.

```rust
Ok(ProcessResult::Complete { check_result, .. }) => {
    let table_ref = ctx.symbol_tables
        .get(&module)
        .ok_or_else(|| CranelispError::ModuleError {
            message: format!("symbol table missing for '{}'", module),
            file: None,
            span: Span::SYNTHETIC,
        })?;
    let names: Vec<Symbol> = table_ref.defined_symbols().collect();
    drop(table_ref); // release DashMap read guard before codegen

    if names.is_empty() {
        // No compilable defns (types-only module, imports-only module).
        // Still notify scheduler so lifecycle proceeds.
        let dummy = Symbol::from("__empty_module");
        ctx.scheduler.notify_inmem_codegen_complete(&module, &dummy, true);
    } else {
        // Build the JIT module. Register GOT resolver ONCE via
        // symbol_lookup_fn BEFORE constructing the JITModule — the backend
        // emits Linkage::Import data symbols named `__cranelisp_got_{module}`
        // and the JIT resolves them through this closure.
        //
        // extra_symbols also carries runtime intrinsic pointers (alloc,
        // dealloc, panic, etc.) and platform function pointers; those are
        // registered via JITBuilder::symbol before the JITModule is built.
        let extra_symbols = cranelisp_backend::jit::intrinsic_symbols();
        let platform_symbols = ctx.session.platform_registry().jit_symbols();
        let mut jit_builder = cranelisp_backend::jit::new_jit_builder()?;
        for (name, ptr) in extra_symbols.iter().chain(platform_symbols.iter()) {
            jit_builder.symbol(name.clone(), *ptr);
        }
        let st_ref = ctx.symbol_tables.clone();
        jit_builder.symbol_lookup_fn(Box::new(move |name| {
            name.strip_prefix("__cranelisp_got_")
                .and_then(|m| st_ref.get(&ModuleFullPath::from(m))
                    .map(|st| st.got.base_ptr() as *const u8))
        }));
        let mut jit_module = JITModule::new(jit_builder);

        // Single codegen call — the unified entry point per pipeline-v4
        // §9.3 and Principle 11. No env, no mode. The Module impl
        // (JITModule here, ObjectModule in nice workers) owns resolution.
        let result = cranelisp_backend::compile_to_module(
            module.clone(),
            &names,
            ctx.symbol_tables,
            &mut jit_module,
        )?;

        // Finalize — caller responsibility (JITModule-specific API; not on the
        // generic Module trait).
        jit_module.finalize_definitions()
            .map_err(|e| CranelispError::CodegenError {
                message: format!("JIT finalize failed for '{}': {e}", module),
                span: Span::SYNTHETIC,
            })?;

        // Register each finalized function into GOT + codegen_products.
        let jit_arc = std::sync::Arc::new(jit_module); // shared across Code entries
        let got = ctx.symbol_tables
            .get(&module)
            .expect("symbol table present")
            .got
            .clone();

        let codegen_entry = ctx.codegen_products
            .entry(module.clone())
            .or_default();

        for (name, func_id) in &result.func_ids {
            let ptr = jit_arc.get_finalized_function(*func_id);

            // Write to pre-assigned GOT slot.
            if let Some(slot) = lookup_got_slot(ctx.symbol_tables, &module, name) {
                got.store_slot(slot, ptr);
            }
            // (Names without a GOT slot — e.g. anonymous helpers — simply
            // don't participate in the GOT. This is unchanged from today.)

            codegen_entry.code.insert(
                name.clone(),
                crate::session_v4::Code {
                    jit: jit_arc.clone(),  // shared Arc<JITModule>
                    ptr,
                },
            );
        }

        // Populate introspection (REPL-only). Per /arch Finding 1,
        // CompilationResult.artifacts is HashMap<Symbol, FunctionArtifacts>
        // where FunctionArtifacts { clif_ir: String, disasm: Option<String>,
        // code_size: usize }. Loop over result.artifacts and key into the
        // session's DashMap<FQSymbol, Introspection>.
        if let Some(intr_map) = ctx.introspection {
            for (name, artifacts) in &result.artifacts {
                let fq = FQSymbol {
                    module: module.clone(),
                    symbol: name.clone(),
                };
                let mut entry = intr_map.entry(fq).or_default();
                entry.clif_ir = Some(artifacts.clif_ir.clone());
                entry.disasm = artifacts.disasm.clone();
                entry.code_size = artifacts.code_size;
            }
        }

        // Notify scheduler — one notification per compiled symbol.
        let total = names.len();
        for (i, name) in names.iter().enumerate() {
            let is_last = i + 1 == total;
            ctx.scheduler.notify_inmem_codegen_complete(&module, name, is_last);
        }
    }

    // Stash program for nice worker object codegen (unchanged).
    // Phase 3 removes this when nice workers enumerate names too.
    stash_codegen_program(ctx.shared_state, &module, program);
    ctx.scheduler.notify_typecheck_done(&module);
    module_sexps.remove(&module);
    suspend_states.remove(&module);
}
```

Notes on this pseudocode:

- `jit::new_jit_builder()` and `jit::intrinsic_symbols()` are tiny helpers in `crates/cranelisp-backend/src/jit/` that return a pre-configured `JITBuilder` and the runtime-intrinsic name→pointer pairs. They expose Cranelift's `JITBuilder` API to the caller so the caller can attach `symbol_lookup_fn` and extra `symbol` registrations before constructing the `JITModule`.
- The `symbol_lookup_fn` closure is the sole JIT-side GOT resolution mechanism. The backend emits every cross-module GOT reference as a `Linkage::Import` data symbol named `__cranelisp_got_{module}`; the closure strips that prefix and returns `symbol_tables[module].got.base_ptr()`. The object path uses linker relocations against the same symbol names and needs no `symbol_lookup_fn` — resolution is uniform at the emission site (see `design/backend/compile-to-module.md` §12) and forks only at `Module`-impl time.
- `lookup_got_slot` is a tiny helper that follows Import chains in the symbol table to find `ModuleEntry::Def.got_slot`. It may be a method on `SymbolTable` already; if not, it's a 10-line free function (or a `SymbolTable` method in `cranelisp-types` if shared). The nice worker also uses it (object path emits GOT data symbols that reference the same slots), so a shared method on `SymbolTable` is preferred.
- The `Arc<JITModule>` wrapping is cosmetic — in the steady state `names.len() == 1` and a plain `JITModule` in `Code` is sufficient. The pseudocode uses `Arc` to future-proof against a caller that passes >1 name per invocation. If `Code` is kept as `{ jit: JITModule, ptr }` (not `Arc`), the loop just moves the single `JITModule` into the single `Code` entry.
- `result.artifacts: HashMap<Symbol, FunctionArtifacts>` is the per-name introspection bundle (CLIF IR, disasm, code_size). `/arch` Phase 3a Finding 1 resolved the shape; `/backend` Wave 1 populates it. The artifact loop above is the concrete, implementable keying-by-`FQSymbol` pattern called for in `pipeline-v4.md` §9.6.
- Error handling uses `?` with `CranelispError` throughout, per `src/CLAUDE.md`.

The identical change applies to `priority_worker_thread` in `src/worker.rs:3037` (threaded worker), which mirrors `priority_worker_loop`. Both call `codegen_module_symbols` today; both get the same inline replacement.

## 6. REPL `__expr` Path

Today the REPL synthesises a `__expr` defn in `wrap_exprs_as_defns` at `src/worker.rs:2480` (approx; see `src/worker.rs:2500–2528` for the `DefnVariant` construction) — this already happens and is retained. The special case being removed is in `finalize_module` at `src/worker.rs:1229–1238`:

```rust
TopLevel::Expr(_) => {
    // Expressions are wrapped as synthetic __expr defns by the typechecker.
    // Retrieve the annotated body from the symbol table.
    if let Some(table) = ctx.symbol_tables.get(module) {
        if let Some(cranelisp_types::ModuleEntry::Def { ast: Some(annotated), .. }) = table.get("__expr") {
            return TopLevel::Expr(annotated.body().clone());
        }
    }
    tl.clone()
}
```

After Step 2a, callers no longer pass a `program` to `compile_to_module` — they pass `names`. After Wave 0, `__expr` is registered on the REPL module's symbol table as a `ModuleEntry::Def` with `ast: Some(annotated)` (the wrapped expression body). After Step 2b, the priority worker's `defined_symbols()` enumeration naturally includes `__expr` for REPL submissions (it is a defined symbol with `ast: Some(_)`), and `compile_to_module` compiles it like any other regular defn.

**End-to-end REPL expression eval**:

1. User types `(+ 1 2)`.
2. REPL (`src/session_v4.rs` eval path) calls `tc.check_form(Expr(...))` (existing).
3. Typecheck wraps the expression as `Defn { name: "__expr", variants: [DefnVariant { body: annotated, ... }] }` and registers it as a `ModuleEntry::Def` on the REPL module's symbol table with `ast: Some(...)` (Wave 0 deliverable already extends `register_def` to cover this path — called from `check_program`'s `wrap_exprs_as_defns`).
4. Priority worker (REPL thread or queued onto `BlockingJitCodegen`) picks up the module, enumerates `defined_symbols()` → `["__expr", ...other new defs...]`, calls `compile_to_module` once.
5. `compile_to_module` compiles `__expr` uniformly. Its body is a zero-arg function returning `i64` (the evaluated expression's bit-encoded result).
6. Worker finalises the JIT, extracts the pointer for `__expr`, stores in `Code`, updates the GOT slot.
7. REPL eval path reads the pointer from `codegen_products[repl_module].code["__expr"].ptr`, transmutes to `fn() -> i64`, calls it, displays the result.

**No special-case branch in `finalize_module`** — `__expr` is just a defn, and the worker treats it as such.

**Deletion**: `worker.rs:1229–1238` goes away entirely. The `TopLevel::Expr(_)` arm of the match inside `finalize_module` is replaced by passing the expression through unchanged — or, better, `finalize_module` itself ceases to post-process the program at all (see §7 Deletion List, items 6–9). Wave 0 made `program` post-processing redundant.

**Eval JIT persistence** (pipeline-v4 §6.2): the spec calls for a session-persistent eval JIT reused across REPL evals. That is gap G10 on the roadmap and is Phase 4 work. Step 2b continues the current pattern — one fresh `JITModule` per REPL submission — which is correct because `compile_to_module` creates JIT modules per codegen unit. The persistent-eval-JIT refactor (Phase 4) replaces the "create `JITModule` inside the worker" step with "re-use the session's eval JIT" for the REPL path only. It does **not** change the `compile_to_module` contract established here.

## 7. Deletion List

Exhaustive list of items deleted in Step 2b. Line numbers reflect the current HEAD and may drift as Wave 0 lands.

| # | Item | File:line | Notes |
|---|------|-----------|-------|
| 1 | `pub fn codegen_module_symbols(...)` | `src/worker.rs:2541` (definition) | The entire function. |
| 2 | Call site from `priority_worker_loop` | `src/worker.rs:2919` | Replaced by the inlined block in §5. |
| 3 | Call site from `priority_worker_thread` | `src/worker.rs:3135` | Same replacement as #2. |
| 4 | Call site from `codegen_and_execute` (session_v4) | `src/session_v4.rs:1457` | REPL eval also transitions to the inline pattern. |
| 5 | `fn compile_regular_defns(...)` | `src/worker.rs:2667` | Dead once `codegen_module_symbols` is deleted. |
| 6 | `fn pre_register_got_slots_in_tc(...)` | `src/worker.rs:2593` | Dead: Wave 0 makes the typechecker register every name with a `got_slot`. |
| 7 | `pub fn compile_and_register_defn_shared(...)` | `src/pipeline.rs:235` | Dead: `compile_to_module` handles the per-defn work internally. |
| 8 | `pub struct SessionCompilationEnv<'a>` + `impl CompilationEnv` | `src/worker.rs:87–214` | DELETED (no replacement env in `src/`). The backend has no env parameter — see §3 and `design/backend/compile-to-module.md` §12. |
| 9 | `impl SessionCompilationEnv<'_> { resolve_in_module, resolve_module_slot, arity_in_module, collect_jit_setup_for_module }` | `src/worker.rs:216–380` | DELETED with the struct. |
| 9a | `CompilationEnv` trait (backend-side) | `crates/cranelisp-backend/src/compiler/mod.rs` | DELETED by `/backend` in Wave 1. See `design/backend/compile-to-module.md` §12. Coordinated citation: `compile_to_module` no longer takes an env. |
| 10 | REPL `__expr` special case in `finalize_module` | `src/worker.rs:1229–1238` | See §6. |
| 11 | Mono-defn inlining loop in `finalize_module` | `src/worker.rs:1254–1258` | Wave 0 pre-materialises mono entries with `ast: Some(_)`; inlining is redundant. |
| 12 | Default-method inlining loop in `finalize_module` | `src/worker.rs:1245–1247` | Already on the symbol table per Phase 1; the push into `program` is redundant once callers read `names`. |
| 13 | Post-pass enrichment loop in `finalize_module` | `src/worker.rs:1260–1277` | `enrich_defn_from_side_maps` / `enrich_expr_from_side_maps` were the Phase 1 dual-write bridge. Wave 0 writes resolutions to AST nodes directly on `register_mono_entry`, so the enrichment is a no-op and the helpers become dead. |
| 14 | `program: Vec<TopLevel>` field on `ProcessResult::Complete` (and the program-building code at `src/worker.rs:1207–1241`) | `src/worker.rs:1207–1283` | Once `compile_to_module` takes `names` only and nice workers enumerate `defined_symbols()` themselves (Phase 3), the `program` output of `process_module_forms` is dead. **Step 2b may keep the `program` output alive for nice workers' `stash_codegen_program` call**, deferring full removal until Phase 3. This is called out as a deferred deletion — not Step 2b's burden. |
| 15 | `codegen_and_execute`'s `check: &CheckResult` parameter | `src/session_v4.rs:1444` | After Wave 0, the REPL path does not consume `constrained_fn_names` from `CheckResult` (it reads from the symbol table). The `CheckResult` parameter survives only for warnings and display — those stay. |
| 16 | The `traced_fns` + test-extern collection around line `src/session_v4.rs:1476–1519` | `src/session_v4.rs:1476–1519` | Retained. Trace display state and test runner state are orthogonal to codegen convergence — they wire extra JIT symbols into the REPL's `compile_to_module` call. Not a deletion; stays as caller-side extra-symbols input. |

Items 1–13 are the core Step 2b deletions. Items 14–16 are classifications — notes on what stays, what is deferred, and where `/int` should not over-reach.

**Cross-check**: these deletions reduce `src/worker.rs` by approximately 600–800 lines (out of 3195). The integration layer converges toward: `process_module_forms` (form-by-form typecheck + AST annotation) + an inline codegen block calling `compile_to_module` + scheduler notifications. The pipeline-convergence invariant in `/int`'s role — "single pipeline, batch and REPL share the same compilation logic" — is finally realised at the codegen entry point.

## 8. Migration Order

Step 2b is itself a sequence of sub-steps. Each sub-step builds and tests green (no new failures beyond the baseline 1590/22).

### Step 2b.1 — Introduce the priority worker codegen inline path

Because `/backend` Wave 1 lands the unified `compile_to_module<M: Module>(module_path, names, symbol_tables, module) -> CompilationResult` entry point (no env, no mode; `CompilationResult.artifacts` populated per-symbol), Step 2b.1 is predominantly a **call-site swap**: the body of `priority_worker_loop` / `priority_worker_thread` / `codegen_and_execute` switches from `codegen_module_symbols(...)` to the §5 inline block. The priority worker adds a `symbol_lookup_fn` and any `symbol` registrations (runtime intrinsics, platform fn pointers) to the `JITBuilder` before calling `JITModule::new`, then calls `compile_to_module` directly. No integration-layer env construction exists — the Module impl owns resolution.

Alongside the existing `codegen_module_symbols` call, add a **feature-gated or env-gated** version of the new inline block. Initially gated behind an env var (e.g., `CRANELISP_CODEGEN_V4=1`), so both paths exist and the new path can be exercised in CI selectively.

**Why gate?** It lets the Step 2b.4 and 2b.5 deletions happen as cleanup after the new path is proven, rather than in a single heroic commit. Also enables the 3 multi-sig JIT tests to be run against both paths side-by-side as a correctness check during implementation.

**Acceptance**: with the env var set, all tests pass (including the 3 flipping multi-sig tests). Without the env var, behaviour is unchanged.

### Step 2b.2 — Switch callers to the new path unconditionally

Remove the env gate. `priority_worker_loop`, `priority_worker_thread`, and `codegen_and_execute` all call the new inline block. `codegen_module_symbols` is no longer called.

**Acceptance**: all tests pass. The 3 multi-sig tests are green. `codegen_module_symbols` exists but is dead code.

### Step 2b.3 — Delete REPL `__expr` special case from `finalize_module`

Remove items 10, 11, 12, 13 from §7. `finalize_module`'s program-building loop becomes a simple clone pass. Wave 0 guarantees that all bodies and resolutions are already on symbol-table entries / AST nodes.

**Acceptance**: all tests pass. `finalize_module` is materially shorter (and in Phase 3 may disappear entirely).

### Step 2b.4 — Delete `codegen_module_symbols` and its helpers

Remove items 1, 5, 6, 7 from §7. `compile_regular_defns`, `pre_register_got_slots_in_tc`, `compile_and_register_defn_shared`.

**Acceptance**: all tests pass. `src/worker.rs` around line 2530–2700 is gone. `src/pipeline.rs:235` is gone.

### Step 2b.5 — Delete `SessionCompilationEnv`

Remove items 8, 9 from §7. `SessionCompilationEnv` struct + trait impl + private helpers. Coordinate with `/backend`: the `CompilationEnv` trait itself is deleted (item 9a); `compile_to_module` reads `symbol_tables` directly, and JIT GOT-base resolution is owned by the caller-registered `symbol_lookup_fn` on the `JITBuilder` (see §5 and `design/backend/compile-to-module.md` §12).

**Acceptance**: all tests pass. `src/worker.rs:82–380` is gone. No compilation-env code lives in `src/` and no `CompilationEnv` trait exists.

**Execution order**: 2b.1 → 2b.2 → 2b.3 → 2b.4 → 2b.5. Steps 2b.3, 2b.4, and 2b.5 can be interleaved (they touch disjoint code). The build must compile green after each.

## 9. Risks and Mitigations

### 9.1 Multi-worker coordination on the same module

**Risk**: Two priority workers concurrently claiming the same module's codegen. Today, `codegen_module_symbols` writes to GOT slots and inserts into `codegen_products`, but the scheduler is responsible for ensuring at most one worker per module at a time.

**Mitigation**: `CompileScheduler::take_priority_work` (`src/scheduler.rs:422`) already guarantees that `PriorityWork::Typecheck(module)` and `PriorityWork::JitCodegen(module, symbol)` for a given module do not issue to two workers simultaneously — module state is tracked in `ModulePool` (see `src/scheduler.rs:177`). Step 2b does not change this guarantee. **Finding**: confirmed no gap.

**Edge case**: the REPL eval path (`src/session_v4.rs:1418`) calls `codegen_and_execute` inline — it does not route through `take_priority_work`. For Step 2b, the inline REPL path holds the TypeChecker's per-module mutable access through `check_state`, so no other worker can process the same module concurrently. The `codegen_and_execute` codegen call thus has exclusive access to the module's symbol table and GOT. Document this invariant in the new inline block's comment.

### 9.2 GOT slot allocation race

**Risk**: Two paths allocating GOT slots for the same module without coordination. Today, `pre_register_got_slots_in_tc` (worker.rs:2593) ensures every compilable name has a slot before codegen begins — it's a catch-all for names the typechecker missed.

**Mitigation**: Wave 0's deliverable is that the typechecker assigns `got_slot: Some(_)` on `ModuleEntry::Def` for every defined symbol it registers (including mangled multi-sig variants and mono specializations). After Wave 0, `pre_register_got_slots_in_tc` is a no-op — there are no "missed" names. Step 2b deletes it (§7 item 6). The scheduler serialises typecheck on a module; after typecheck completes, codegen reads `got_slot` values that are already populated. No race.

**Verification**: a one-line assertion in the inline codegen block — for every `name` in `names`, assert `lookup_got_slot(symbol_tables, &module, name).is_some()` — catches any Wave 0 gap. Keep this as a `debug_assert!` in Step 2b.1, upgrade to a hard check before 2b.4 lands, then drop the check in Phase 3 when `SymbolTable::defined_symbols` provably filters to `got_slot.is_some()` entries.

### 9.3 Introspection continuity

**Risk**: `worker.rs` populates `Introspection { source, sexp, clif_ir, disasm, code_size, compile_duration }` on `codegen_products`' per-symbol entries via `compile_and_register_defn_shared` (src/pipeline.rs:295–304). After that function is deleted, introspection population must happen elsewhere.

**Mitigation**: Per `pipeline-v4.md §9.6`, introspection is a separate concern from compilation. `compile_to_module`'s return type includes `artifacts: HashMap<Symbol, FunctionArtifacts>` (CLIF IR, disasm, code_size) — the priority worker copies those into `introspection` keyed by `FQSymbol`, as shown in §5 pseudocode. Source text and sexp are populated earlier (during typecheck form processing) and are not affected by Step 2b. Compile duration is measurable with `std::time::Instant` around the `compile_to_module` call.

**Status**: **Resolved by /arch Phase 3a Finding 1**. `CompilationResult.artifacts: HashMap<Symbol, FunctionArtifacts>` where `FunctionArtifacts { clif_ir: String, disasm: Option<String>, code_size: usize }` is a Wave 1 `/backend` deliverable with a fixed shape. No outstanding coordination risk.

### 9.4 Platform function resolution

**Risk**: `SessionCompilationEnv::collect_jit_setup_for_module` registers platform function pointers as extra JIT symbols before `compile_to_module` runs. If it goes away before the caller registers them elsewhere, platform-dependent tests break.

**Mitigation**: The priority worker (§5 pseudocode) obtains `PlatformRegistry::jit_symbols()` and registers each pair directly on the `JITBuilder` via `JITBuilder::symbol(name, ptr)` before constructing the `JITModule`. Cranelift's linker then resolves platform calls through those registrations at `finalize_definitions` time. No env, no wrapper — the caller owns platform registration. `/platform` confirms `PlatformRegistry::jit_symbols()` exposes the name→pointer pairs the JIT needs. If the current `PlatformRegistry` API does not yet expose this shape, extending it is a Sprint 56 task for `/platform` and a blocker for Step 2b.5.

### 9.5 Introspection for mono specializations and multi-sig variants

**Risk**: Post-Wave-0, mono specializations and multi-sig variants are first-class symbol-table entries — they show up in `defined_symbols()` and get compiled. The REPL user typically doesn't want `/list` to show `add$Int+Int` alongside `add`. Introspection must stay consistent.

**Mitigation**: This is a REPL display concern, not a codegen concern. `SymbolInfo` / `describe_symbol` in the REPL decides what to surface for `/list`, `/info`, etc. Those paths already filter mangled names — no change required by Step 2b. Flagged as a cross-check: confirm during implementation that `/list` output is unchanged.

### 9.6 Arc<JITModule> vs move-into-Code

**Background**: When `names.len() > 1` (object path currently; JIT path only if a future caller batches), the single `JITModule` produced by `compile_to_module` cannot be moved into multiple `Code` entries. Either wrap in `Arc<JITModule>` (cheap) or refactor `Code` to hold `Option<JITModule>` with exactly one `Code` per module owning it (more invasive).

**Resolution**: **Accepted by /arch Phase 3a §3 (Principle 8 Check)**. Adopt `Arc<JITModule>` inside `Code` for Step 2b. Phase 3 G6 moves `Code` onto `ModuleEntry::Def`, at which point the `Arc` is still valid — multiple ModuleEntry entries sharing one finalised JIT module is a legitimate data-sharing pattern, not interim architecture. No later refactor is forced.

## 10. Test Plan

`/int` does not write tests (per `src/CLAUDE.md` and the sprint plan), but this section enumerates what `/qa` should cover and what counts as sprint acceptance.

### 10.1 Tests expected to flip green (deferred → passing)

- `tests/sketch_port/multi_sig.rs::sketch_multi_sig_type_based_dispatch`
- `tests/sketch_port/multi_sig.rs::sketch_multi_sig_different_arities`
- `tests/sketch_port/repl_multi_sig.rs::sketch_repl_multi_sig_different_arities`

These fail today because `collect_and_declare_defns` (JIT path) diverged from `expand_multi_sig_defn` (object path). After Step 2b, both paths go through the same `compile_to_module`, which reads pre-materialised mangled entries from the symbol table — there is no expansion at codegen time. Expected to pass after Step 2b.2 lands.

### 10.2 Regression protection — must remain green

- Full `cargo nextest run -p cranelisp` baseline: 1590 passed / 22 failed at sprint start. Any new failure is a regression.
- REPL smoke tests: `repl/demos/*.demo` playback (run via `/repl` skill's demo harness).
- `examples/*.cl` compile-and-run suite.
- `exemplar/` (Sudoku solver) compile-and-run.
- Stdlib compile-and-load.

### 10.3 New test coverage suggested

- `tests/v4_codegen/single_entry_point.rs` — assert that after a module is compiled, `codegen_products[module].code` has exactly the same symbol set as `symbol_tables[module].defined_symbols()`. Structural invariant.
- `tests/v4_repl_eval/repl_expr_via_symbol_table.rs` — drive the REPL with `(+ 1 2)`, assert the resulting `__expr` appears as a `ModuleEntry::Def` with `ast: Some(_)` and compiles identically to how a user-written `(defn my-expr [] (+ 1 2))` compiles (same CLIF IR for the body).
- `tests/v4_codegen/introspection_preserved.rs` — after compilation, `Introspection[fq]` has `clif_ir.is_some()`, `disasm.is_some()`, `code_size > 0` for every compiled name. Guards §9.3.

### 10.4 Sprint acceptance (from `sprints/SPRINT.md`)

- `codegen_module_symbols` deleted.
- `compile_regular_defns` deleted.
- One JIT codegen path exists.
- REPL eval works end-to-end through the unified path.
- Baseline of 1590/22 preserved or improved.
- 3 multi-sig JIT tests pass (net-green improvement: 1593/19 or better).

## 11. References

- `design/arch/pipeline-v4.md` §9.3 (`compile_to_module` signature), §9.4 (per-function JIT isolation), §9.6 (Introspection separate from compilation).
- `design/arch/pipeline-v4-roadmap.md` Phase 2 (G4, G5).
- `design/backend/compile-to-module.md` §2.1 (PRESCRIPTIVE signature), §2.3 (internal derivation table), §2.5 (caller usage).
- `design/typecheck/ast-annotation.md` (Wave 0 contract — which entries carry `ast: Some(_)`).
- `design/int/pipeline-convergence.md` (historical `/int` convergence analysis — this doc extends it to the codegen entry point).
- `sprints/SPRINT.md` Sprint 56 Architecture Review §2 (No Interim Architecture), §5.5 (REPL `__expr`), §6.4 (per-function JITModule lifetime).
- `/arch` review conditions #4 (Phase 2→3 bridge must keep `CodegenProduct` alive) and #5 (centralised `constrained_fn_names` / `defined_symbols` predicate on `SymbolTable`).

## 12. Next Skills

After this design doc is approved and Wave 0 (`/typecheck`) and Wave 1 (`/backend`'s signature change per Step 2a) are green:

- `/int` — execute Step 2b per the migration order in §8.
- `/qa` — add the tests in §10.3 and re-run the full baseline.
- `/platform` — confirm platform resolution per §9.4 before 2b.5 deletes `SessionCompilationEnv`.
- `/review` — review the Step 2b implementation, specifically the inlined codegen block in `priority_worker_loop`/`priority_worker_thread`/`codegen_and_execute` for coherence and the §9 invariants.
