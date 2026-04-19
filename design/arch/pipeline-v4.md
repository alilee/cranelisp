# Pipeline v4: Scheduler-Driven Concurrent Compilation

## 1. Overview

The compiler uses a central `CompileScheduler` to coordinate parallel typechecking and codegen across modules. There is no single `compile_unit` entry point — modules are registered with the scheduler, and worker threads pull work from a priority ladder.

```
CLI args → CompilerSession → register entry module → workers typecheck, discover deps, codegen
```

Two worker pools: **priority workers** handle typechecking and JIT codegen at normal OS priority. **Nice workers** handle object file codegen at low OS priority. The scheduler tracks module lifecycle and priority codegen for macro expansion. Symbol-level compilation state lives on the session's concurrent maps.

See `concurrent-pipeline.md` for the full scheduler design (module pools, priority queue, worker interfaces).

## 2. CLI and Main

### 2.1 Actions

```rust
enum Action { Run, Link, Release, Repl }
```

The positional argument is an entry module path (`foo.cl`) or a directory (resolved to `path/user.cl`). If omitted, defaults to `cwd/user.cl`. The action flag (`--run`, `--link`, `--release`) determines what happens after compilation. No flag means REPL.

### 2.2 Main Structure

```rust
fn main() {
    let (action, entry_module, project_root, settings) = parse_args();

    let s = CompilerSession::new(settings, project_root);

    if let Release = action {
        return s.build_release();
    }

    // Spawn workers. Priority workers handle typecheck + JIT.
    // Nice workers handle .o file writing.
    s.spawn_priority_workers(num_cpus());
    s.spawn_nice_workers(num_cpus());

    // Register the entry module. Workers discover dependencies
    // lazily during typechecking (imports trigger recursive loading).
    // session knows project root, and can search for the right source
    // file for this module full path.
    s.register_module(&entry_module);

    match action {
        Run => {
            s.scheduler.wait_inmem_complete()?;  // Err → print + exit
            s.trampoline(&entry_module);
            s.scheduler.wait_object_complete()?;
        }
        Link => {
            s.scheduler.wait_object_complete()?;
            s.link(&entry_module);
        }
        Repl => {
            loop {
                let src = read_line();
                match s.process_commands(&src) {
                    Nothing => {}
                    Final(sexp) => pretty_print(sexp),
                    Compile(src) => match s.eval(&src) {
                        Ok(Some(sexp)) => pretty_print(sexp),
                        Ok(None) => {}        // definition only, no result
                        Err(e) => print_error(e),  // TC rolled back
                    },
                }
            }
        }
        Release => {}
    }

    s.shutdown();
}
```

## 3. Module Processing

There is no `compile_unit` function. Modules are registered with the scheduler, and workers process them form-by-form.

### 3.0 Module Strategy

```rust
enum ModuleStrategy { Replace, Additive }
```

- **Replace**: the module's symbol table is cleared before processing. The new source is the complete definition of the module. Used for file loads, dependency compilation, and file watcher reloads.
- **Additive**: new forms are appended to the module's existing symbol table. Previous definitions persist. Used for REPL input, where each line adds to the accumulated module state.

### 3.1 Entry Point

The session registers the entry module with the scheduler:

```rust
s.register_module(&entry_module_name);
```

The session resolves the module path to a source file via `project_root` and `lib_dirs`, reads the source, parses it, and registers it with the scheduler (enters TypecheckFirst). Same resolution path as dependency discovery (§3.3).

All dependency discovery happens lazily during typechecking. When a worker encounters an import, qualified reference, or `mod` declaration, it loads and registers the dependency via the same `register_module` path. No upfront graph walk.

### 3.2 Form-by-Form Processing

When a priority worker claims a module for typechecking, it processes the module's forms in source order:

1. **Expand** the form. If the form is a macro call:
   - Look up the macro in the module table (`ModuleEntry::Macro`).
   - If the macro's function pointer and its call-graph dependencies are all compiled: call the expander, get the expanded sexp. Continue.
   - If not: walk the macro's `ModuleEntry.callees` to collect transitive uncompiled deps, then call `block_for_macro_codegen` on the scheduler. The worker releases this module and returns to the priority ladder for new work. When dependencies are compiled, the module unblocks and the worker resumes from this form.

   The call graph is TC-sourced: when each form is typechecked (step 3), method resolutions produce `call_graph_edges` on `FormCheckResult`, and `finalize_check_result()` writes each symbol's callee list to `ModuleEntry.callees` (a `Vec<FQSymbol>`) in the `SymbolTable`. When the macro is first used (this step), the worker reads the macro's `ModuleEntry::Macro.callees` and walks the transitive closure via `tc.symbol_table(module).get(name)` on each callee — each callee's own `ModuleEntry.callees` are already populated (it was typechecked before the macro, per spec §9.2.5). The result is the `needed: Vec<(ModuleFullPath, Symbol)>` passed to `block_for_macro_codegen`. See Decision 21 in `design/arch/CLAUDE.md`.
2. **Build AST** from the expanded sexp.
3. **Typecheck** the form. Typecheck writes results directly onto the AST nodes and into the symbol table (see §9 Data Model). Per-form results are immediately available — codegen workers don't wait for the whole module to finish typechecking. The worker enqueues newly-typechecked symbol names onto the JIT queue (or priority JIT queue for REPL eval).
4. **Notify** the scheduler via `notify_symbol_typechecked` — this may unblock other modules waiting on this symbol.
5. If the form is a **defmacro**: register the macro in the module table (`ModuleEntry::Macro` with clause info and AST). No compilation — that's deferred until first use (step 1).
6. After all forms: call `notify_typecheck_done` on the scheduler. The module enters TypecheckDone. The module path is enqueued onto the object queue.

### 3.3 Dependency Discovery During Typechecking

Dependencies are discovered lazily as a worker processes forms. When a worker encounters an unresolved import, `mod` declaration, or qualified reference:

1. **Resolve** the module path to a source file via `lib_dirs`.
2. **Check cache** — if a valid `.o` + `.meta.json` exists, restore the symbol table from `.meta.json` and register with the scheduler via `register_module_cached` (enters TypecheckDone). The symbol table from cache contains all type info, GOT slot assignments, and defn bodies needed for both codegen and introspection. The current module can continue immediately if the needed symbols are now available.
3. **Cache miss** — parse the source, register with the scheduler via `register_module` (enters TypecheckFirst, since the current module is waiting on it).
4. **Dependency edge** is implicit — the module's import specs in the symbol table record it.
5. If the needed symbol is not yet available (cache miss, or cache hit but symbol not yet typechecked): **block** the current module via `block_for_typecheck`. The worker returns to the priority ladder for new work.
6. When the needed symbol is typechecked, the original module unblocks and a worker resumes it.

Prelude discovery follows the same path: the first module that isn't the prelude triggers prelude loading when the worker injects `(import [prelude [*]])` during form processing.

### 3.4 Platform Loading

When form processing encounters a `(platform name)` form, the worker:

1. Resolves the DLL path relative to `project_root`.
2. Loads the DLL and reads function descriptors.
3. Registers platform function **type signatures** in the module's symbol table under the platform's module path (for typechecking IO chains). No code pointers — the typechecker only needs types.
4. Registers platform function **pointers and scheduling classes** in `session.platform` (for the IO trampoline at runtime).
5. Stores the DLL handle in `loaded_platforms` (keeps the DLL alive).

Any module can declare platforms. No prescan. Codegen for platform function calls emits IO effect node construction, not direct calls — the trampoline executes them at runtime using the platform registry.

### 3.5 Prelude

Prelude is just another dependency, discovered lazily. When a worker begins processing a non-prelude module, it injects `(import [prelude [*]])` which triggers prelude loading via §3.3. Cache hits are common for the prelude — the symbol table is restored from `.meta.json`, and in-memory code is loaded from `.o` via Linker on first demand (when a macro needs a prelude function).

## 4. Codegen

Codegen is driven by the scheduler via work queues. All codegen — JIT and object — goes through `compile_to_module`, the backend crate's sole compilation entry point (see §9.3).

### 4.1 Priority JIT Codegen (BlockingJitCodegen)

When a module's typecheck blocks on a macro that needs compiled functions, the scheduler's priority queue is populated (see `concurrent-pipeline.md` §4). Priority workers claim Ready entries and JIT-compile them:

1. Create a fresh JIT instance for this compile batch (per-batch isolation — see §9.4).
2. Call `compile_to_module` with the single symbol name. `compile_to_module` reads the symbol's AST body, resolved calls, and type info from the symbol table (see §9.1). It discovers platform symbols and cross-module GOT references internally from the symbol table.
3. Finalize the JIT, get the code pointer.
4. Write the code pointer to the symbol's pre-assigned GOT slot (atomic store).
5. Store the `Code { jit, ptr }` in codegen products (keeps JIT memory alive).
6. Notify the scheduler via `notify_priority_codegen_complete` (see `concurrent-pipeline.md` §4.3).

For cache-hit modules, the worker loads the `.o` via Linker instead of JIT-compiling. One Linker load resolves all symbols in the module. The worker notifies the scheduler for all loaded symbols.

### 4.2 JIT Codegen (JitCodegen)

After a module's typecheck is complete (TypecheckDone), its symbols need JIT compilation for execution (`InMemoryAndObject` mode). Priority workers at level 4 of the ladder claim un-codegenned symbols from the JIT queue:

1. The scheduler finds a typechecked symbol without a code pointer and not in `jit_reserved`.
2. The worker JIT-compiles it (same process as §4.1 — fresh JIT, `compile_to_module`, finalize, GOT write).
3. Notifies the scheduler. When all symbols are done, the scheduler sets `inmem_done`.

For `ObjectOnly` mode, this step doesn't run — the only JIT compilation is what the priority path demanded for macros.

### 4.3 Object Codegen

Nice workers compile entire modules to relocatable `.o` files:

1. Claim a TypecheckDone module from the object queue where `object_done` is false.
2. Collect all compilable symbol names from the module's symbol table.
3. Create one `ObjectModule` for the whole module.
4. Call `compile_to_module` with all symbol names. `compile_to_module` reads bodies, types, and resolved calls from the symbol table. Cross-module references become `Linkage::Import` declarations (the linker resolves them from other `.o` files).
5. Finalize, emit `.o` bytes.
6. Write `.meta.json` — serialized symbol table (includes bodies, types, GOT slot assignments — everything needed to restore the module from cache without re-typechecking).
7. Notify the scheduler which sets `object_done`.

Cache-hit modules have `object_done = true` from registration — nice workers skip them unless dirtied by additive changes.

At session shutdown (or before `--link`), nice workers are promoted to normal priority via `promote_object_codegen`. The session blocks until all modules reach Complete.

## 5. `CompilerSession`

### 5.1 Fields

```rust
pub struct CompilerSession {
    // --- Shared compilation state ---
    /// Per-module symbol tables. The single store for all per-module
    /// and per-symbol compilation state: types, GOT slots and tables,
    /// AST bodies, resolved calls, callees, structural declarations,
    /// platform function pointers, compiled code (JIT + Linker).
    /// See §9.1.
    pub symbol_tables: DashMap<ModuleFullPath, SymbolTable<Code, Linker>>,

    /// Loaded platform DLL handles. Must remain alive for process
    /// lifetime so function pointers stay valid. Platform function
    /// pointers live on symbol table entries; this just keeps the
    /// DLLs loaded.
    pub loaded_platforms: Mutex<Vec<LoadedPlatform>>,

    // --- Scheduler ---
    pub scheduler: CompileScheduler,

    // --- Session config (read-only after construction) ---
    pub settings: Settings,
    pub project_root: PathBuf,

    /// Shared ISA for codegen workers. Built once, cloned per worker.
    pub shared_isa: Arc<dyn TargetIsa>,
}
```

### 5.2 No Worker State on Session

Workers own their JIT instances thread-locally. There is no `InMemWorkerState` or `ObjectWorkerState` on the session. Each priority worker creates JIT instances as needed; each nice worker creates Cranelift object builders as needed. JIT instances are kept alive (they own executable memory) in codegen products (a concurrent map keyed by FQSymbol).

### 5.3 Concurrent Access Model

| Session field | Access pattern | Mechanism |
|---------------|---------------|-----------|
| `symbol_tables` | One writer per module, many readers; GOT slots written atomically by codegen workers | Concurrent map (DashMap); GOT atomic stores |
| `loaded_platforms` | Rare writes during loading, held for lifetime | Mutex |
| `scheduler` | Many readers/writers | Internal Mutex + condvars |
| `settings`, `project_root`, `shared_isa` | Read-only | No synchronization needed |

Everything lives on the symbol tables: type signatures, platform function pointers, dependency edges (import specs), GOT tables. File paths are deterministic from module path + project root + lib search path.

## 6. REPL

### 6.1 `process_commands`

```rust
enum CommandResult {
    Nothing,           // blank, comment, or side-effect-only command
    Final(Sexp),       // command that produces a displayable sexp
    Compile(String),   // raw source text — submit to scheduler
}

impl CompilerSession {
    fn process_commands(&self, input: &str) -> CommandResult;
}
```

Handles slash commands and blank/comment detection only. No parsing, expanding, or typechecking.

### 6.2 REPL Compilation

When the REPL receives source text:

1. `s.eval(&src)` submits the input to the current REPL module (set by `/mod`, starts in entry module). Definitions are registered with `Additive` strategy — appended to the module's accumulated forms.
2. A worker typechecks the forms under the current module's context (resolving names from its imports and local definitions). Typecheck writes results directly onto AST nodes and symbol table entries (§9.1).
3. If the input contains a trailing expression, that becomes a **temporary closure** — typechecked in the current module's scope but not registered in the GOT or the module's symbol table.
4. Eval walks the closure's call graph and submits any un-codegenned dependencies to the scheduler as `BlockingJitCodegen` entries, with a notification mechanism so eval knows when they're done. Eval blocks until notified.
5. Once dependencies are callable, eval JIT-compiles the closure itself on a **fresh `JITModule` created for this one eval**. That JIT is wrapped in our `Jit` newtype whose custom `Drop` calls `unsafe JITModule::free_memory()` (see Decision 31 and §9.4). The JIT is private to the eval path, outside the scheduler.
6. Eval calls the closure, gets the result, and lets the `Jit` wrapper drop — reclaiming the `__expr` function's executable memory. The eval JIT does not survive past the call.

The temporary closure is entirely outside the scheduler and GOT. Only its dependencies flow through the priority codegen path.

The REPL does **not** call `wait_all_complete`. It only waits for the closure's dependencies to be compiled (step 4). Background JIT of other definitions and object codegen continue while the result is displayed.

TC snapshot/restore wraps the compilation: on error, the typechecker rolls back to its pre-input state.

**Principle 11 note**: the eval closure's JIT compilation is a deliberate exception to "single pipeline" only in the narrow sense that it is synchronous on the eval path rather than routed through the scheduler's priority codegen queue. The closure is temporary (one-shot, not registered in the GOT or module table), has no caching requirement (no `.o`), and is always compiled by the eval path after its dependencies are ready. It uses the same `Jit`-wrapper-with-custom-`Drop` reclaim primitive as every other JIT batch (Decision 31) — there is no separate "eval JIT" subsystem. Routing the closure through the scheduler would require a one-shot work type with special cleanup; compiling inline is simpler and the parallelism benefit lives in the dependency path.

**Safety for `__expr`**: the custom `Drop → unsafe free_memory()` requires that no function pointer derived from the JIT is reachable when the `Jit` drops (Cranelift 0.116 `cranelift-jit/src/backend.rs:219` contract — see Decision 31). The `__expr` JIT satisfies this because (a) `__expr` is never written into a GOT slot, (b) the eval path consumes the result and returns to the caller in a single synchronous call before dropping the `Jit`, and (c) the language's `fn` values are heap closures that call through the GOT, not raw code pointers — so a returned value cannot smuggle out `__expr`'s address. A post-call assertion-only build may check that no `Arc<Jit>` clones exist before drop, but the language-level invariant is sufficient.

### 6.3 File Watcher

The file watcher runs on its own thread, watching `project_root` for `.cl` file changes:

1. On change: re-register the changed module with `Replace` strategy.
2. Workers typecheck the changed module. Existing dependencies that haven't changed are already compiled — only genuinely new imports trigger loading.
3. Dependents are NOT automatically re-registered. If the changed module's exported symbol types are unchanged, dependents remain valid (they call through the GOT, which is updated with new code pointers).

**Type-change limitation**: changing the type of an exported symbol is an error. Dependents compiled against the old type are stale, and we do not cascade recompilation through the call graph. The fix for the user is to introduce new names for changed signatures and update dependents to use the new names. Full incremental recompilation with type-change propagation is deferred.

GOT stability during evaluation: the scheduler pauses priority worker JIT codegen writes during REPL expression execution (between wait and result display). Typecheck can continue — only code pointer writes are paused.

### 6.4 Session Persistence

After a successful eval that contains definitions, `eval` regenerates the source of the current REPL module and saves it to `{project_root}/{module}.cl`. This happens after the closure call returns — eval already has all the context needed.

## 7. Run Mode

```rust
s.spawn_priority_workers(num_cpus());
s.spawn_nice_workers(num_cpus());
s.register_module(&entry_module_name);
s.scheduler.wait_inmem_complete()?;    // Err if any module failed
s.trampoline(&entry_module_name);      // execute main, handle IO
s.scheduler.wait_object_complete()?;   // promotes nice workers, waits for .o
```

`trampoline` verifies `main` exists in the entry module, calls it. If `main` returns `IO`, runs the IO trampoline to force the effect chain.

## 8. Link Mode

```rust
let s = CompilerSession::new_with_behaviour(settings, project_root, ObjectOnly);
s.spawn_priority_workers(num_cpus());
s.spawn_nice_workers(num_cpus());
s.register_module(&entry_module_name);
s.scheduler.wait_object_complete()?;   // Err if any module failed
s.link(&entry_module_name);            // invoke system linker
```

No background JIT for non-macro symbols. Priority workers only JIT symbols needed for macro expansion. Nice workers compile all modules to `.o`. `link` collects `.o` paths and invokes the system linker.

The startup stub calls the entry module's `main` function through the GOT — same indirect call mechanism as cross-module calls. The entry module name comes from the CLI; there is no special-casing for `"user"` or `"main"` in the backend.

## 9. Data Model

The symbol table is the **single per-module store** for all compilation state. There is no separate `CheckResult`, `TypecheckProduct`, or `program: Vec<TopLevel>` passed alongside the symbol table.

### 9.1 Symbol Table as Single Store

The symbol table holds all per-module state: symbol definitions, structural declarations, GOT, and compiled code. It spans the full pipeline — typecheck writes types and AST, codegen writes code pointers, cache serializes it. This is high cohesion, not a god object: every field relates to the same module's compilation state.

```rust
// In cranelisp-types. Trait bounds express the contract; defaults () for
// crates that don't handle compiled code (typecheck, backend).
pub struct SymbolTable<C: CodeStore = (), L: LinkerStore = ()> {
    pub symbols: HashMap<Symbol, ModuleEntry<C>>,

    // --- GOT (runtime memory for code pointers) ---
    pub got: GotTable,
    pub next_got_slot: usize,

    // --- Structural declarations (retained for .cl regeneration §6.4) ---
    pub imports: Vec<ImportDecl>,       // (import [module [names...]])
    pub exports: Vec<ExportDecl>,       // (export [names...])
    pub platforms: Vec<PlatformDecl>,   // (platform "name")
    pub submodules: Vec<ModuleName>,    // (mod child)

    // --- Cached object code (module-level .o loading) ---
    #[serde(skip)]
    pub linker: Option<L>,              // mapped .o code for cache-hit modules
}
```

`CodeStore` and `LinkerStore` are marker traits defined in `cranelisp-types`. `()` implements both trivially. The integration layer uses `SymbolTable<Code, Linker>` where `Code` (per-function entry holding an `Arc<Jit>` shared with its batch siblings — see §9.4) and `Linker` (per-module .o mapping) are defined in the backend or integration crate. Functions that only read types/AST/GOT take `SymbolTable` with the defaults — no generic parameters in their signatures.

The `symbols` map carries per-symbol entries. The structural declarations are module-level — they record the original `(import ...)`, `(export ...)`, `(platform ...)`, `(mod ...)` forms for `.cl` regeneration after REPL changes (§6.4). The per-symbol `ModuleEntry::Import` entries are the *resolved effects* of import declarations; the `imports: Vec<ImportDecl>` is the *original specification*.

Module path is not stored — it is deterministic from the DashMap key. File paths are deterministic from module path + project root + lib search path.

The generic parameters `C` (per-function code) and `L` (per-module linker) default to `()` for crates that don't handle compiled code. The typecheck and backend crates work with `SymbolTable` (defaults). The integration layer works with `SymbolTable<Code, Linker>`. Functions that only read types/AST/GOT take `SymbolTable` — no generic parameters needed. `C` and `L` fields are `#[serde(skip)]` — cache serialization writes types, AST, GOT slots, and structural declarations; code is regenerated from the AST on cache hit.

Each `ModuleEntry::Def` carries everything typecheck produced and codegen needs:

```rust
ModuleEntry::Def {
    // --- Type info (written by typecheck) ---
    scheme: Scheme,
    param_names: Vec<Symbol>,
    kind: Box<DefKind>,
    callees: Vec<FQSymbol>,
    trait_origin: Option<FQSymbol>,
    visibility: Visibility,
    docstring: Option<String>,

    // --- AST body (written by typecheck, read by codegen) ---
    ast: Option<DefnVariant>,       // params + body + annotations

    // --- GOT (slot assigned by typecheck, pointer written by codegen) ---
    got_slot: Option<usize>,

    // --- Compiled code (written by codegen, keeps JIT memory alive) ---
    #[serde(skip)]
    code: Option<C>,                // per-function code pointer + shared Arc<Jit> (see §9.4)
}
```

The `ast` field stores the typechecked function body. Typecheck writes resolved calls and expression types **directly onto AST nodes** during type inference — not into side maps keyed by Span. An `Expr::Apply` carries its `ResolvedCall`; every `Expr` node carries its inferred `Type`. Spans are retained for error messages only, not as keys into side tables.

Platform functions live in their platform submodule's symbol table as `ModuleEntry::Def` entries with `PrimitiveKind::PlatformEffect` and the DLL function pointer. No separate `session.platform` registry — the IO trampoline resolves platform functions by looking them up in the symbol table, same as any other symbol.

Multi-sig functions: the typechecker expands `DefnMulti` into mangled variant entries (`add$Int+Int`, etc.), each as a separate `ModuleEntry::Def` with its own `ast`, `got_slot`, and `scheme`. The base name gets `DefKind::Overloaded { variants }` with `got_slot: None`. `compile_to_module` looks up entries in the symbol table — if it finds `Overloaded`, it compiles the variant entries instead. No special-case expansion in codegen.

Constrained polymorphic functions: the template entry has `DefKind::UserFn { constrained_fn: Some(_) }`. Monomorphised specializations are separate entries with their own `ast` and `got_slot`, same as multi-sig variants.

Default trait method implementations: separate `ModuleEntry::Def` entries, same pattern.

This means `CheckResult` is eliminated as a boundary type. Typecheck writes directly to the symbol table. The only transient outputs from typecheck are: warnings (consumed immediately) and display info (for REPL output formatting).

### 9.2 GOT

The `GotTable` — the runtime memory region where code pointers are written — lives on the `SymbolTable`. It is created when the module is first registered (before typecheck begins) so that its base address is stable for the process lifetime. Slot indices are assigned during typecheck as symbols are registered. Code pointers are written during codegen (atomic store to pre-assigned slot).

Cross-module GOT resolution: when `compile_to_module` compiles a function that calls into another module, it follows the Import chain in the symbol table to find the target module and GOT slot, then reads the target module's `symbol_tables[target].got.base_ptr()` for the GOT base address. In JIT mode, this base address is embedded as a literal pool entry in the JIT module. In object mode, it becomes a data symbol with `Linkage::Import` that the linker resolves.

### 9.3 `compile_to_module` — Sole Compilation Entry Point

```rust
pub fn compile_to_module<M: Module>(
    module_path: ModuleFullPath,
    names: &[Symbol],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable>,
    module: &mut M,
) -> Result<CompilationResult, CranelispError>
```

This is the **only** function that compiles Cranelisp functions into Cranelift IR. Both JIT and object paths call it. It is fully self-sufficient — given the symbol tables and a Cranelift Module, it discovers everything it needs:

- **What to compile**: `names` lists the symbols. For each name, reads the `ast` (body), `scheme` (types), and resolved calls from `symbol_tables[module_path]`. For `Overloaded` entries, compiles each variant instead.
- **Intrinsics**: declared on the module internally.
- **Cross-module references**: discovered by following Import chains in the symbol table. Declared as `Linkage::Import` on the module. GOT base addresses read from `symbol_tables[target_module].got`.
- **Platform symbols**: discovered from Import chains that resolve to `PrimitiveKind::PlatformEffect` entries carrying DLL function pointers.

The caller controls granularity:
- **JIT workers**: pass N symbol names, one fresh `JITModule` → per-batch isolation (§9.4)
- **Object workers**: pass all symbol names, one `ObjectModule` → per-module `.o` file

### 9.4 Per-Batch JIT Isolation

JIT codegen creates one `JITModule` per `compile_to_module` call (per compile batch). This is by design:

- **REPL replacement**: redefining a function produces a new JIT module for the new batch. The old batch's JIT stays alive (keeping old code valid for any in-flight calls) until every `Code` entry referencing it drops — at which point the `Arc<Jit>` refcount hits zero and the custom `Drop` fires.
- **Parallel codegen**: workers compile batches independently without synchronizing on a shared JIT module.
- **Memory management**: a custom `Drop` on our `Jit` wrapper calls `unsafe JITModule::free_memory()`, which frees all executable memory allocated by that JIT. This is the ONLY way to reclaim JIT pages in Cranelift 0.116 — see below. (Decision 31.)

**Cranelift 0.116 behaviour we must work around.** The default `JITModule` drop path does NOT free executable memory:

```rust
// cranelift-jit-0.116.1/src/memory.rs:269-276
impl Drop for Memory {
    fn drop(&mut self) {
        // leak memory to guarantee validity of function pointers
        mem::replace(&mut self.allocations, Vec::new())
            .into_iter()
            .for_each(mem::forget);
    }
}
```

Cranelift leaks-on-drop by design so that dangling fn pointers can never dereference freed memory. To reclaim, callers must explicitly invoke `JITModule::free_memory(self)` (marked `unsafe` — `cranelift-jit-0.116.1/src/backend.rs:219`) once they know no fn pointer derived from that JIT is reachable. `prepare_for_function_redefine` does NOT reclaim (`cranelift-jit-0.116.1/src/backend.rs:575-596`, with a `FIXME` from Cranelift's own author flagging the missing dealloc).

So the `Jit` wrapper in our backend implements a custom `Drop`:

```rust
pub struct Jit {
    module: ManuallyDrop<JITModule>,
}

impl Drop for Jit {
    fn drop(&mut self) {
        // SAFETY: the Arc<Jit> refcount reaching zero is our proof that
        // no ModuleEntry::Def.code entry retains a code pointer into this
        // JIT. Combined with the language-level invariant that user-returned
        // fn values are heap closures calling through the GOT (not raw code
        // pointers), no fn pointer into this JIT is reachable.
        let module = unsafe { ManuallyDrop::take(&mut self.module) };
        unsafe { module.free_memory() };
    }
}
```

The `Code` type (the generic parameter `C` on `SymbolTable<C, L>` and `ModuleEntry<C>`) holds an `Arc<Jit>` so that N compiled functions produced by one `compile_to_module` call share one underlying `Jit`:

```rust
pub struct Code {
    pub jit: Arc<Jit>,   // owns executable memory; shared across sibling entries
    pub ptr: *const u8,  // code pointer (into jit's memory)
}
```

Each function's `Code` lives on its `ModuleEntry::Def.code` field — no separate codegen products map. When a REPL eval redefines a function, the new `Code` (with a new `Arc<Jit>`) replaces the old one on the entry; when every sibling `Code` from the old batch has been replaced or evicted, the last `Arc<Jit>` drops and the `unsafe free_memory()` call reclaims the old batch's pages. When a cached `.o` is loaded, the `Linker` lives on `SymbolTable.linker` (the `L` parameter) and keeps the mapped code alive for all functions in that module.

**Safety invariant for `unsafe free_memory()`** (maintained by symbol-table + GOT discipline):

- Every derivative code pointer lives on a `ModuleEntry::Def.code` (which holds an `Arc<Jit>` — refcount > 0 while any such pointer is reachable), OR is ephemeral (stack-local during compile/call, drops before function return), OR is a GOT slot.
- GOT slots pointing into batch X are updated to point at new code (atomic swap) *before* the old `Arc<Jit>` can drop (the new batch's `Code` write + GOT atomic store happen before the old `Code` is overwritten).
- Language-level invariant: user-returned `fn` values are heap closures that call into the GOT, not raw code pointers. Eval cannot leak a code address from an `__expr` JIT into a returned value.

Each function finds callees via GOT-indirect calls — there are no direct intra-module FuncId calls in JIT mode. This is the cost of batch isolation: one extra indirection per call. It is acceptable because GOT loads are L1-cached in practice.

### 9.5 Cache Serialization

The `.meta.json` file is a serialized `SymbolTable`. Since the symbol table contains everything (types, GOT slots, AST bodies, resolved calls), a cache hit restores the full compilation state without re-typechecking. The `.o` file is the object code. Together they are sufficient to:

- Restore the module into the session (cache hit — no re-typecheck, no re-codegen)
- Load code from `.o` via Linker (JIT demand — macro expansion needs a prelude function)
- Regenerate the `.o` from the symbol table alone (REPL defn change — re-codegen without re-typecheck)

File paths are deterministic from module path + project root + lib search path. No path storage needed in the cache metadata.

### 9.6 Introspection

Introspection data (CLIF IR, disassembly, source text, sexp, compilation timing) is populated as the pipeline progresses and stored in a separate concurrent map:

```rust
pub introspection: DashMap<FQSymbol, Introspection>,
```

This is display-only data for slash commands (`/clif`, `/disasm`, `/source`, `/sexp`, `/time`). It is not needed for compilation or caching. Source text for `/source` is extracted from the AST body stored on the symbol table entry — no separate `source_text` field needed.

## 10. Display

`eval` and slash commands return `Sexp` values (possibly with comment annotations). `pretty_print` renders them. Constructing a displayable sexp from an eval result (formatting a value with its type annotation) is `eval`'s responsibility.

## 11. Settings

```rust
struct Settings {
    lib_dirs: Vec<PathBuf>,     // --lib_search and/or cranelisp.toml
    no_color: bool,             // --no-color or NO_COLOR env
}
```

Read from `cranelisp.toml` in `project_root` (if it exists), overridden by CLI flags.

## 12. Invariants

1. **No `compile_unit`.** All compilation is driven by the scheduler and workers. There is no function that takes source text and returns a result.
2. **Form-by-form processing.** Within a module, forms are processed sequentially in source order (spec §9.12). Parallelism is inter-module only.
3. **No codegen in typecheck.** Typechecking produces type info. Codegen is a separate activity driven by the scheduler. Exception: macro expansion requires JIT codegen of the macro function (and its dependencies) before typechecking can continue.
4. **Workers own their JIT state.** No `InMemWorkerState` on the session. JIT instances are thread-local until stored in codegen products.
5. **Session maps are concurrent.** Symbol tables use concurrent maps. The scheduler's Mutex covers coordination state only.
6. **`process_commands` is thin.** Slash commands and blank detection only. All compilation goes through the scheduler.
7. **Dependency discovery is lazy.** Modules are discovered and registered during form processing when imports, `mod` declarations, or qualified references are encountered. There is no upfront graph walk. Dependency edges are implicit in the symbol table's import specs.
8. **File watcher re-registers modules.** Notifications trigger re-registration + cascade, not direct compilation. Workers handle the rest.
9. **Module locks are implicit.** The scheduler ensures no two workers typecheck the same module. No explicit per-module lock needed for typecheck exclusivity.
10. **Cache hits enter TypecheckDone.** Cached modules skip typecheck entirely. Symbol table restored from `.meta.json`, code loaded from `.o` on demand.
11. **Object codegen is per-module.** One `.o` per module. Nice workers claim whole modules.
12. **Priority ladder prevents starvation.** TypecheckFirst before priority codegen before TypecheckNext before JIT codegen. Urgent work always runs first.
13. **Errors cascade through dependencies.** A Failed module causes all modules waiting on its symbols to also fail. Wait methods return the first error. The REPL rolls back TC state on failure; batch mode exits.
14. **Symbol table is the single store.** All per-symbol compilation state lives on `ModuleEntry`. No parallel data structures (CheckResult, TypecheckProduct, program) are passed alongside the symbol table. Typecheck writes to it; codegen reads from it; cache serializes it.
15. **One compilation entry point.** All codegen — JIT and object — goes through `compile_to_module`. No parallel codegen paths.
16. **No `"user"` special-casing in the backend.** The backend treats all module names uniformly. `"user"` is only special in CLI argument parsing (default module name when no file is specified).
