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
    let (action, entry_module_path, settings) = parse_args();

    let entry_module_path = slug(entry_module_path);
    let project_root = base_dir(entry_module_path);

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
    s.register_module(&entry_module_name);

    match action {
        Run => {
            s.scheduler.wait_inmem_complete()?;  // Err → print + exit
            s.trampoline(&entry_module_name);
            s.scheduler.wait_object_complete()?;
        }
        Link => {
            s.scheduler.wait_object_complete()?;
            s.link(&entry_module_name);
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
3. **Typecheck** the form via `tc.check_form()`. This produces per-form typecheck output (method resolutions, expr_types, constraints for this form's symbols) and registers it in the session's concurrent module table. Per-form results accumulate into the module's full `CheckResult`, but each symbol's data is available for codegen immediately — codegen workers don't wait for the whole module to finish typechecking.
4. **Notify** the scheduler via `notify_symbol_typechecked` — this may unblock other modules waiting on this symbol.
5. If the form is a **defmacro**: register the macro in the module table (`ModuleEntry::Macro` with clause info and AST). No compilation — that's deferred until first use (step 1).
6. After all forms: call `notify_typecheck_done` on the scheduler. The module enters TypecheckDone.

### 3.3 Dependency Discovery During Typechecking

Dependencies are discovered lazily as a worker processes forms. When a worker encounters an unresolved import, `mod` declaration, or qualified reference:

1. **Resolve** the module path to a source file via `lib_dirs`.
2. **Check cache** — if a valid `.o` + `.meta.json` exists, restore type info into the TypeChecker and register with the scheduler via `register_module_cached` (enters TypecheckDone). The current module can continue immediately if the needed symbols are now available.
3. **Cache miss** — parse the source, register with the scheduler via `register_module` (enters TypecheckFirst, since the current module is waiting on it).
4. **Dependency edge** is implicit — the module's import specs in the TypeChecker record it.
5. If the needed symbol is not yet available (cache miss, or cache hit but symbol not yet typechecked): **block** the current module via `block_for_typecheck`. The worker returns to the priority ladder for new work.
6. When the needed symbol is typechecked, the original module unblocks and a worker resumes it.

Prelude discovery follows the same path: the first module that isn't the prelude triggers prelude loading when the worker injects `(import [prelude [*]])` during form processing.

### 3.4 Platform Loading

When form processing encounters a `(platform name)` form, the worker:

1. Resolves the DLL path relative to `project_root`.
2. Loads the DLL and reads function descriptors.
3. Registers platform function **type signatures** in the TypeChecker's module table under the platform's module path (for typechecking IO chains). No code pointers — the typechecker only needs types.
4. Registers platform function **pointers and scheduling classes** in `session.platform` (for the IO trampoline at runtime).
5. Stores the DLL handle in `loaded_platforms` (keeps the DLL alive).

Any module can declare platforms. No prescan. Codegen for platform function calls emits IO effect node construction, not direct calls — the trampoline executes them at runtime using the platform registry.

### 3.5 Prelude

Prelude is just another dependency, discovered lazily. When a worker begins processing a non-prelude module, it injects `(import [prelude [*]])` which triggers prelude loading via §3.3. Cache hits are common for the prelude — type info is restored from `.meta.json`, and in-memory code is loaded from `.o` via Linker on first demand (when a macro needs a prelude function).

## 4. Codegen

Codegen is driven by the scheduler, not by a caller invoking a codegen function.

### 4.1 Priority JIT Codegen (BlockingJitCodegen)

When a module's typecheck blocks on a macro that needs compiled functions, the scheduler's priority queue is populated (see `concurrent-pipeline.md` §4). Priority workers claim Ready entries and JIT-compile them:

1. Create a JIT instance (using the session's shared ISA).
2. Read the symbol's typechecked AST and CheckResult from the session.
3. Compile to machine code.
4. Register the code pointer in the session's GOT (atomic store to pre-assigned slot).
5. Notify the scheduler via `notify_priority_codegen_complete` (see `concurrent-pipeline.md` §4.3).

For cache-hit modules, the worker loads the `.o` via Linker instead of JIT-compiling. One Linker load resolves all symbols in the module. The worker notifies the scheduler for all loaded symbols.

### 4.2 JIT Codegen (JitCodegen)

After a module's typecheck is complete (TypecheckDone), its symbols need JIT compilation for execution (`InMemoryAndObject` mode). Priority workers at level 4 of the ladder claim un-codegenned symbols:

1. The scheduler finds a typechecked symbol without a code pointer and not in `jit_reserved`.
2. The worker JIT-compiles it (same process as §4.1).
3. Notifies the scheduler. When all symbols are done, the scheduler sets `inmem_done`.

For `ObjectOnly` mode, this step doesn't run — the only JIT compilation is what the priority path demanded for macros.

### 4.3 Object Codegen

Nice workers compile entire modules to relocatable `.o` files:

1. Claim a TypecheckDone module where `object_done` is false.
2. Compile all the module's symbols to a single `.o` file using Cranelift's object backend.
3. Write `.meta.json` cache metadata (symbol table, module structure, source hash).
4. Notify the scheduler which sets `object_done`.

Cache-hit modules have `object_done = true` from registration — nice workers skip them unless dirtied by additive changes.

At session shutdown (or before `--link`), nice workers are promoted to normal priority via `promote_object_codegen`. The session blocks until all modules reach Complete.

## 5. `CompilerSession`

### 5.1 Fields

```rust
pub struct CompilerSession {
    // --- Shared compilation state (concurrent maps) ---
    /// Type checker. Per-module symbol tables are concurrent maps.
    /// Multiple workers read/write concurrently (one writer per module,
    /// many cross-module readers).
    pub tc: TypeChecker,

    /// GOT for code pointer registration. Pre-assigned slots,
    /// atomic stores. Multiple workers write concurrently.
    pub got: GotTable,

    /// Platform registry — function pointers and scheduling classes
    /// for the IO trampoline. Keyed by fully qualified symbol
    /// (e.g., `db/query`, `net/fetch`) since two platforms may
    /// export the same bare name. Populated during platform loading,
    /// read-only after compilation completes.
    pub platform: Mutex<HashMap<FQSymbol, PlatformFunction>>,

    /// Loaded platform DLL handles. Must remain alive for process
    /// lifetime so function pointers stay valid.
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

Workers own their JIT instances thread-locally. There is no `InMemWorkerState` or `ObjectWorkerState` on the session. Each priority worker creates JIT instances as needed; each nice worker creates Cranelift object builders as needed. JIT instances are kept alive (they own executable memory) in a thread-local or worker-scoped collection.

### 5.3 Concurrent Access Model

| Session field | Access pattern | Mechanism |
|---------------|---------------|-----------|
| `tc` module tables | One writer per module, many readers | Concurrent map (DashMap) |
| `got` | Many writers (pre-assigned slots) | Atomic stores |
| `platform` | Rare writes during loading, read-only at runtime | Mutex |
| `scheduler` | Many readers/writers | Internal Mutex + condvars |
| `settings`, `project_root`, `shared_isa` | Read-only | No synchronization needed |

Platform function type signatures are in the TypeChecker's module tables (for typechecking). Platform function pointers and scheduling classes are in `session.platform` (for the IO trampoline). Dependency edges are derivable from the TypeChecker's module import specs; the file→module mapping is stored on each module entry.

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
2. A worker typechecks the forms under the current module's context (resolving names from its imports and local definitions).
3. If the input contains a trailing expression, that becomes a **temporary closure** — typechecked in the current module's scope but not registered in the GOT or the module's symbol table.
4. Eval walks the closure's call graph and submits any un-codegenned dependencies to the scheduler as `BlockingJitCodegen` entries, with a notification mechanism so eval knows when they're done. Eval blocks until notified.
5. Once dependencies are callable, eval JIT-compiles the closure itself using a **persistent eval JIT** — a long-lived JIT instance retained across the session. The closure code from previous evals can be discarded or memoised at eval's discretion. The eval JIT is private to the eval path, outside the scheduler.
6. Eval calls the closure, gets the result, returns it.

The temporary closure is entirely outside the scheduler and GOT. Only its dependencies flow through the priority codegen path. The eval JIT instance is reused across evals — no allocation/teardown per expression.

The REPL does **not** call `wait_all_complete`. It only waits for the closure's dependencies to be compiled (step 4). Background JIT of other definitions and object codegen continue while the result is displayed.

TC snapshot/restore wraps the compilation: on error, the typechecker rolls back to its pre-input state.

**Principle 11 note**: the eval closure's JIT compilation is a deliberate exception to "single pipeline." The closure is temporary (one-shot, not registered in the GOT or module table), has no caching requirement (no `.o`), and has different lifetime semantics (persistent eval JIT reused across evals, not worker-scoped). Routing it through the scheduler would require adding a one-shot work type with special cleanup — complexity that buys nothing since the closure is always compiled synchronously by the eval path after its dependencies are ready. Only the dependencies flow through the scheduler, which is where the parallelism benefit lives.

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

## 9. Display

`eval` and slash commands return `Sexp` values (possibly with comment annotations). `pretty_print` renders them. Constructing a displayable sexp from an eval result (formatting a value with its type annotation) is `eval`'s responsibility.

## 10. Settings

```rust
struct Settings {
    lib_dirs: Vec<PathBuf>,     // --lib_search and/or cranelisp.toml
    no_color: bool,             // --no-color or NO_COLOR env
}
```

Read from `cranelisp.toml` in `project_root` (if it exists), overridden by CLI flags.

## 11. Invariants

1. **No `compile_unit`.** All compilation is driven by the scheduler and workers. There is no function that takes source text and returns a result.
2. **Form-by-form processing.** Within a module, forms are processed sequentially in source order (spec §9.12). Parallelism is inter-module only.
3. **No codegen in typecheck.** Typechecking produces type info. Codegen is a separate activity driven by the scheduler. Exception: macro expansion requires JIT codegen of the macro function (and its dependencies) before typechecking can continue.
4. **Workers own their JIT state.** No `InMemWorkerState` on the session. JIT instances are thread-local.
5. **Session maps are concurrent.** TypeChecker module tables and macro registry use concurrent maps. The scheduler's Mutex covers coordination state only.
6. **`process_commands` is thin.** Slash commands and blank detection only. All compilation goes through the scheduler.
7. **Dependency discovery is lazy.** Modules are discovered and registered during form processing when imports, `mod` declarations, or qualified references are encountered. There is no upfront graph walk. Dependency edges are implicit in the TypeChecker's import specs.
8. **File watcher re-registers modules.** Notifications trigger re-registration + cascade, not direct compilation. Workers handle the rest.
9. **Module locks are implicit.** The scheduler ensures no two workers typecheck the same module. No explicit per-module lock needed for typecheck exclusivity.
10. **Cache hits enter TypecheckDone.** Cached modules skip typecheck entirely. In-memory code is loaded from `.o` on demand.
11. **Object codegen is per-module.** One `.o` per module. Nice workers claim whole modules.
12. **Priority ladder prevents starvation.** TypecheckFirst before priority codegen before TypecheckNext before JIT codegen. Urgent work always runs first.
13. **Errors cascade through dependencies.** A Failed module causes all modules waiting on its symbols to also fail. Wait methods return the first error. The REPL rolls back TC state on failure; batch mode exits.
