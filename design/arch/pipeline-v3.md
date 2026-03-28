# Pipeline v3: Unified Compilation with Queued Codegen

## 1. Overview

The compiler has one pipeline entry point (`compile_unit`), one session (`CompilerSession`), and two codegen queues (in-memory and object). Modes differ only in which queues they drain and when.

```
CLI args → CompilerSession → compile_unit (stages 1-5) → codegen queues → drain
```

There is no separate batch pipeline, REPL pipeline, or module-loading pipeline. There is no orchestration wrapper around `compile_unit`. Prelude loading, platform DLL loading, and recursive dependency resolution all happen inside `compile_unit`.

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

    let entry_module_name = slug(entry_module_path);
    let project_root = base_dir(entry_module_path);

    let mut s = CompilerSession::new(settings, project_root);

    let src = read_file(entry_module_path);
    let codegen = match action {
        Link => ObjectOnly,
        _ => InMemoryAndObject,
    };
    let ctx = CompileContext::new(entry_module_name, codegen);

    if let Release = action {
        return s.build_release(&ctx);
    }

    s.compile_unit(&src, &ctx, Replace);

    match action {
        Run | Repl => s.spawn_hot_inmem_codegen(),
        _ => {}
    }
    s.spawn_nice_object_codegen();

    match action {
        Repl => {
            s.spawn_file_watcher();
            loop {
                let src = read_line();
                s.pause_watcher_codegen();
                s.hot_flush_in_mem_queue();
                if let Some(form) = match s.process_commands(&src) {
                    Nothing => None,
                    Final(form) => Some(form),
                    Compile(src) => Some(s.compile_unit(&src, &ctx, Additive)),
                } {
                    pretty_print_form(form);
                }
                s.resume_watcher_codegen();
            }
            s.hot_flush_object_queue();
        }
        Run => {
            s.hot_flush_in_mem_queue();
            s.trampoline(&ctx);
            s.hot_flush_object_queue();
        }
        Link => {
            s.hot_flush_object_queue();
            s.link(&ctx);
        }
        Release => {}
    }
}
```

## 3. `compile_unit`

### 3.1 Signature

```rust
impl CompilerSession {
    pub fn compile_unit(
        &mut self,
        source: &str,
        ctx: &CompileContext,
        strategy: ModuleStrategy,
    ) -> CompileUnitResult;
}
```

One entry point. Takes source text. Returns a form suitable for display. No codegen, no execution.

### 3.2 Stages

```
Stage 1: Parse          source → Vec<Sexp>
Stage 2: Extract        Vec<Sexp> → (ModuleStructure, Vec<Sexp>)
  2a: Platform loading   (platform ...) forms → load DLL, register symbols
  2b: Dependency graph    register import edges in module_deps (even if later stages fail)
  2c: Dependency loading  unresolved imports → recursive compile_unit calls (see §3.4)
  2d: Import/export       register in typechecker
  2e: Prelude injection   if prelude is loaded and this isn't prelude
Stage 3: Expand          defmacro interception, macro expansion, begin-flatten
Stage 4: Build AST       Vec<Sexp> → Vec<TopLevel>
  4b: Bind chain analysis (auto IO scheduling)
Stage 5: Typecheck       Vec<TopLevel> → CheckResult (unified multi-pass)
Enqueue: push CodegenItem to in-mem and/or object queue per CodegenBehaviour
```

`compile_unit` runs entirely on the calling thread. It does not JIT, does not execute, does not write `.o` files. It pushes work to queues and returns.

### 3.3 Platform Loading (Stage 2a)

When `compile_unit` encounters a `(platform name)` form during extraction, it:
1. Resolves the DLL path relative to `project_root`
2. Loads the DLL and reads function descriptors
3. Registers platform types in the typechecker
4. Registers platform symbols in `platform_symbols` (for later JIT use)
5. Registers scheduling classes in `scheduling_registry`

No prescan. No caller-side setup. Any module — entry file, dependency, REPL input — can declare platforms.

### 3.4 Dependency Loading (Stage 2b)

For each unresolved import, `compile_unit` checks whether the dependency is already available (compiled in this session or cached on disk) before resorting to source compilation.

#### 3.4.1 Resolution Order

For each unresolved import module:

1. **Already loaded.** The typechecker already has the module's symbol table (from an earlier `compile_unit` call in this session). Nothing to do.

2. **Cache hit.** A valid `.o` + `.meta.json` exists on disk and the source hasn't changed (hash match). Load from cache:
   - Read `.meta.json` → restore `SymbolTable`, `ModuleStructure`, and type registrations into the typechecker. This gives stage 5 everything it needs to resolve imports from this dependency. Register dependency edges in `module_deps`.
   - Enqueue a `FromCache` codegen item carrying the `.o` path to the codegen queue. The worker pool loads the `.o` and JITs it (or collects the path for the system linker). Cache-hit loading does NOT JIT inside `compile_unit` — like source compilation, it enqueues and returns.
   - No `compile_unit` call. The dependency's symbols are fully available for typechecking; its code is loaded asynchronously by workers.

3. **Cache miss.** No cache, or source has changed. Compile from source:
   - Resolve the module source file via `lib_dirs`.
   - Read the source and call `compile_unit` recursively. This runs stages 1-5 for the dependency and enqueues its codegen items to the queues.
   - Cycle detection via `compile_stack`.
   - Independent dependencies are compiled in parallel (see §3.4.3).

Prelude loads through this same mechanism when any module imports from it. There is no special prelude pre-loading step.

#### 3.4.3 Parallel Dependency Typechecking

When a module imports multiple dependencies that are independent of each other (no imports between them), their `compile_unit` calls run in parallel.

The dependency graph is a DAG. At stage 2b, the set of unresolved imports forms a level of this DAG. Dependencies within the same level have no edges between them — they can be typechecked concurrently.

**How it works:**

1. Stage 2 extracts all imports. Partition into: already loaded, cache hits (restored synchronously), and cache misses.
2. For cache misses, resolve source files and read them.
3. Fork: launch parallel `compile_unit` calls for independent dependencies. Each receives a read-only view of the existing typechecker state (modules already loaded) and writes to its own module namespace.
4. Join: merge the resulting module symbol tables into the typechecker. Each module writes to a distinct `ModuleFullPath` — no overlap, no conflicts.
5. Continue with stage 2c (import registration) on the calling module.

**Module locking model:**

Each module symbol table has a lock. `compile_unit` acquires an exclusive lock on its target module at entry and holds it through stages 1-5. If the lock is already held (another `compile_unit` is building the same module concurrently), the call fails immediately with an error — no blocking, no waiting.

```rust
// Pseudocode
fn compile_unit(&mut self, source: &str, ctx: &CompileContext, strategy: ModuleStrategy) -> Result<...> {
    let lock = self.tc.try_lock_module(&ctx.module)?;  // error if already locked
    // ... stages 1-5 ...
    // lock released on return (RAII)
}
```

This gives three guarantees:

1. **No concurrent writes to the same module.** Two `compile_unit` calls targeting the same `ModuleFullPath` cannot overlap. The second one errors immediately.
2. **Reads of other modules are always consistent.** A locked module is being built — readers of *other* modules see only completed symbol tables. Parallel dependencies are independent by definition, so they never read each other's in-progress state.
3. **Deadlock-free.** `try_lock` is non-blocking. If a cycle somehow bypasses `compile_stack` detection, the lock fails rather than deadlocking.

The lock also serves as the concurrency check for the file watcher: if the watcher tries to recompile a module that's currently being compiled (e.g., the user is typing a REPL expression that triggered the same module load), the watcher's `compile_unit` call fails and can retry later.

**Shared mutable state** beyond the per-module locks is limited to:
- The type variable counter (`TypeId` allocation) — a single atomic counter.
- The codegen queues — concurrent push from multiple producers.

**Composition with codegen queues:** Each parallel `compile_unit` pushes its own `CodegenItem`s to the shared codegen queues. The queues are designed for concurrent producers (multiple parallel typechecks) and concurrent consumers (worker thread pool). The full DAG fans out at every level — parallel typechecks feed parallel codegen.

#### 3.4.2 Cache Validity

A cached module is valid when:
- The `.o` and `.meta.json` files both exist.
- The stored source hash matches the current source file's hash.
- All transitive dependency hashes match (a dependency that was recompiled invalidates its dependents).

When validity cannot be confirmed, fall through to cache miss (recompile from source).

### 3.5 Return Value

```rust
pub struct CompileUnitResult {
    pub check_result: CheckResult,
    pub program: Vec<TopLevel>,
    pub module_structure: ModuleStructure,
    pub warnings: Vec<Warning>,
    pub display: Option<DisplayInfo>,
}
```

No `value`, no `result_type`. Those are produced when the in-mem queue is drained and code is executed. The `display` field carries type information for the REPL's pretty-printer.

## 4. `CompileContext`

```rust
pub struct CompileContext {
    pub module: ModuleFullPath,
    pub codegen: CodegenBehaviour,
}

pub enum CodegenBehaviour {
    InMemoryAndObject,  // enqueue to both queues
    ObjectOnly,         // enqueue to object queue only
}

pub enum ModuleStrategy {
    Additive,   // REPL: definitions accumulate
    Replace,    // file load: module = exactly these forms
}
```

No `CompileMode`. The distinction between GOT-indirect and direct calls is an implementation detail of the in-mem codegen worker, not a pipeline concern. No `CodegenTarget` — replaced by `CodegenBehaviour` which describes *which queues* receive work.

`ModuleStrategy` is a parameter on `compile_unit`, not a field on `CompileContext`, because the same context (same module, same codegen behaviour) may be used with different strategies (Replace for file load, Additive for REPL input within the same module).

## 5. `CompilerSession`

### 5.1 Fields

```rust
pub struct CompilerSession {
    // --- Pipeline core (stages 1-5) ---
    // compile_unit reads/writes only these fields
    tc: TypeChecker,
    expander: CraneliftExpander,
    compile_stack: Vec<ModuleFullPath>,
    lib_dirs: Vec<PathBuf>,
    scheduling_registry: SchedulingRegistry,
    platform_symbols: Vec<(String, *const u8)>,
    module_deps: ModuleDependencyGraph,

    // --- Codegen queues ---
    // compile_unit pushes; workers drain
    inmem_queue: CodegenQueue,
    object_queue: CodegenQueue,

    // --- Worker state ---
    // owned by drain/flush methods, never touched by compile_unit
    inmem_worker: InMemWorkerState,
    object_worker: ObjectWorkerState,

    // --- Session config ---
    settings: Settings,
    project_root: PathBuf,
}
```

`compile_unit` touches only the pipeline core fields and the queues. It never reads or writes worker state. Workers own their state privately.

### 5.2 `InMemWorkerState`

```rust
struct InMemWorkerState {
    got_state: ModuleCodegenState,
    jit_modules: Vec<Jit>,
    traced_fns: Vec<TracedFnInfo>,
    trace_extra_symbols: Vec<(String, *const u8)>,
}
```

### 5.3 `ObjectWorkerState`

```rust
struct ObjectWorkerState {
    cache_dir: Option<PathBuf>,
    compiled_o_paths: Vec<PathBuf>,
    compiled_module_structures: Vec<(ModuleFullPath, ModuleStructure)>,
    cross_module_func_sigs: Vec<(Symbol, usize)>,
}
```

## 6. Codegen Queues

### 6.1 `CodegenItem`

```rust
pub enum CodegenItem {
    FromSource {
        module: ModuleFullPath,
        program: Vec<TopLevel>,
        check_result: CheckResult,
        module_structure: ModuleStructure,
        source: String,
    },
    FromCache {
        module: ModuleFullPath,
        object_path: PathBuf,
        got_slot_map: HashMap<Symbol, usize>,
    },
}
```

Owns all data. No borrows from the call stack. `compile_unit` builds `FromSource` after stage 5 and pushes to one or both queues based on `CodegenBehaviour`. Cache hits (§3.4.1) push `FromCache` with the `.o` path. Workers handle both: `FromSource` JIT-compiles from IR; `FromCache` loads the cached object via `Linker`.

### 6.2 Queue Operations

```rust
impl CompilerSession {
    /// Spawn worker threads that drain the in-mem queue at full priority.
    /// Workers JIT-compile each CodegenItem, register code pointers in the GOT.
    /// Multiple workers run concurrently — one per core.
    fn spawn_hot_inmem_codegen(&mut self);

    /// Spawn worker threads that drain the object queue at nice (low) priority.
    /// Workers compile each CodegenItem to a relocatable .o file.
    /// Nice priority: must not compete with typecheck on the main thread.
    fn spawn_nice_object_codegen(&mut self);

    /// Block until all in-mem queue items are JIT-compiled.
    /// Called before execution (trampoline, REPL eval).
    fn hot_flush_in_mem_queue(&mut self);

    /// Block until all object queue items are written to .o files.
    /// Promotes remaining work from nice to full priority —
    /// the work has joined the critical path to program exit.
    fn hot_flush_object_queue(&mut self);
}
```

### 6.3 Priority Model

| Thread | Priority | Rationale |
|--------|----------|-----------|
| Main thread (stages 1-5) | Highest | Finding type errors fast matters most |
| In-mem codegen workers | Full | Execution is blocked until JIT completes |
| User program threads (sparks) | Full | Lenient evaluation / parallel bind — user-visible latency |
| Object codegen workers | Nice | Background work; must not contend with any of the above |
| Object workers after `hot_flush` | Full | Now on critical path to exit |

The nice priority on object workers protects three things: typecheck throughput on the main thread, JIT compilation speed on the in-mem workers, and user program execution speed (lenient evaluation sparks, parallel bind chains). Object codegen is strictly background — it must never steal cores from any work the user is waiting on. `hot_flush_object_queue` promotes remaining object work to full priority because at that point the programme is trying to exit and the object work has joined the critical path.

### 6.4 Concurrency Model

`compile_unit` runs single-threaded on the main thread. It pushes `CodegenItem`s to queues. Queue workers are a thread pool — each item is JIT-compiled (or `.o`-compiled) independently on its own core.

This works because:

- **Codegen items are independent.** Each owns its `Program` + `CheckResult`. JIT compilation of module A does not need the JIT output of module B. It needs the *typecheck* output (GOT slot assignments, method resolutions), which was resolved during stage 5 on the main thread.
- **GOT registration is the serialisation point.** After a worker JITs a function, it writes the code pointer to a GOT slot via a single atomic store. The slot index was assigned during typecheck.
- **`hot_flush` is a barrier.** It blocks until all in-flight workers complete.
- **In-mem and object queues run in parallel.** Both are being drained concurrently — in-mem at full priority, object at nice.

### 6.5 Producer-Consumer Clarification

The codegen system is a classic **producer-consumer** pattern with a shared concurrent queue — not a coordinator pattern, not request-response, not message passing between named threads.

`compile_unit` is a **producer**: it pushes `CodegenItem`s to the shared queues and returns immediately. It does not wait for codegen, does not know how many workers exist, and does not care whether any worker has started. The in-mem and object worker pools are **consumers**: N threads, spawned once, continuously draining their respective queues. Workers are always running once spawned — they loop on try-pop, compile whatever they find, and park (condvar wait) when the queue is empty. There is no coordinator thread, no batch accumulation, no dispatch step. The queue IS the communication mechanism. `hot_flush` is a **barrier**, not a dispatcher: it signals "no more items coming" and blocks until the queue is empty and all in-flight compilations complete. It does not assign work to threads — workers are already draining. When parallel `compile_unit` calls run (from `load_dependencies`), each producer thread pushes to the same shared queue. Workers drain items regardless of which producer enqueued them.

## 7. REPL

### 7.1 `process_commands`

```rust
enum CommandResult {
    Nothing,           // blank, comment, or side-effect-only command (/help, /list)
    Final(Form),       // command that produces a form to display (/source, /expand)
    Compile(String),   // raw source text — pass to compile_unit
}

impl CompilerSession {
    fn process_commands(&mut self, input: &str) -> CommandResult;
}
```

`process_commands` handles only slash commands and blank/comment detection. It does **not** parse, expand, intercept defmacros, or handle imports. All of those are pipeline concerns handled inside `compile_unit`.

If the input starts with `/`, dispatch to the appropriate command handler. Otherwise return `Compile(input.to_string())`.

### 7.2 REPL Loop

```rust
loop {
    let src = read_line();
    s.hot_flush_in_mem_queue();
    if let Some(form) = match s.process_commands(&src) {
        Nothing => None,
        Final(form) => Some(form),
        Compile(src) => Some(s.compile_unit(&src, &ctx, Additive)),
    } {
        pretty_print_form(form);
    }
}
```

Eight lines. One pretty-printer. `compile_unit` returns a form. `/source` returns a form. Both go through `pretty_print_form`.

### 7.3 Error Recovery

TC snapshot/restore wraps the `Compile` path. On error, the typechecker rolls back to its pre-input state. This happens in the REPL loop (or inside `compile_unit` with a flag), not in `process_commands`.

### 7.4 File Watcher

The file watcher recompiles changed modules immediately — it does not defer work to the REPL prompt. The user may be editing in their IDE without touching the REPL; compilation should happen in the background as files are saved.

```rust
s.spawn_file_watcher();
```

`spawn_file_watcher` starts a background thread that watches `project_root` for `.cl` file changes. On each change notification, it calls `s.recompile_module_and_dependents(module, src)` (see §7.4.1). The watcher thread uses `compile_unit` (which is `&self`) and enqueues codegen to the shared queue — workers JIT the recompiled modules in the background.

#### 7.4.1 Recompilation with Cascade

When a file change notification arrives, the watcher:

1. **Recompile the changed module.** `compile_unit(&src, &ctx, Replace)`. Takes the module lock. Stages 1-5 run, codegen is enqueued. Stage 2 registers the module's import edges in `module_deps` (even if later stages fail).

2. **Cascade to dependents.** Look up the module's transitive dependents in `module_deps`, topologically sort them, recompile each in order. Each dependent is recompiled from its source file (re-read from disk) via `compile_unit`.

3. **Lock contention.** If `try_lock` fails for any module (already being compiled — e.g., another notification or the REPL is compiling it), add it to a retry set and attempt again after the current batch completes.

4. **Failed compilations.** If a module fails to compile (type error, etc.), it enters the error set. Its dependency edges from stage 2 survive in `module_deps` — so when a later notification fixes the upstream dependency, the failed module is included in the cascade and retried.

#### 7.4.2 Module Dependency Graph

```rust
struct ModuleDependencyGraph {
    /// Forward edges: module → modules it imports.
    imports: HashMap<ModuleFullPath, Vec<ModuleFullPath>>,
    /// Reverse edges: module → modules that import it.
    dependents: HashMap<ModuleFullPath, Vec<ModuleFullPath>>,
    /// Maps canonical file paths to module paths.
    file_to_module: HashMap<PathBuf, ModuleFullPath>,
}
```

Populated during stage 2 (extract) of every `compile_unit` call. The forward edges come from `import` declarations in the source — not from the symbol table. This means dependency edges are registered even when compilation fails, which is essential for cascade recompilation after a fix.

#### 7.4.3 Interaction with REPL

The file watcher runs on its own thread. Recompilation and codegen enqueuing happen concurrently with the user typing at the REPL. The in-mem codegen workers JIT the recompiled modules in the background.

When the user presses enter, `hot_flush_in_mem_queue` is a barrier — it waits for any in-flight recompilations and JIT work to complete before evaluating the user's expression. If the file watcher finished before the user pressed enter, the flush is instant. The user only waits if recompilation is still in flight.

**GOT stability during evaluation.** During REPL expression evaluation (from `hot_flush_in_mem_queue` through execution to result display), watcher-triggered codegen must not write to the GOT. The pattern: `pause_watcher_enqueue` before `hot_flush`, `resume_watcher_enqueue` after evaluation completes. This ensures the GOT is stable during execution — a function mid-execution always sees consistent code pointers for its callees. Watcher `compile_unit` calls (stages 1-5) can continue during this window — only codegen enqueuing is paused. This keeps typecheck latency low while protecting execution consistency.

#### 7.4.4 Coalescing

If multiple notifications arrive in quick succession (e.g., IDE save-all), natural coalescing occurs:

- A module that appears in multiple cascades is recompiled once — the second `compile_unit` attempt hits `try_lock`, fails, and is retried. By retry time, the first compilation has completed and the module is up-to-date.
- A module whose own file changed AND is a dependent of another changed module: the direct notification and the cascade both target the same module. The lock ensures only one compilation runs; the other becomes a no-op on retry (source hash unchanged after the first compilation).

### 7.5 Session Persistence

After a successful `compile_unit` call with `Additive` strategy that contains definitions (defn, deftype, deftrait, impl), `compile_unit` saves the accumulated module to `{project_root}/{module}.cl`. This is a side effect inside `compile_unit` — the caller does not need to check or trigger the save. Pure expressions (no definitions) do not trigger a save.

## 8. Run Mode

```rust
s.compile_unit(&src, &ctx, Replace);   // stages 1-5, enqueue codegen
s.spawn_hot_inmem_codegen();            // start JIT workers
s.spawn_nice_object_codegen();          // start .o workers (background)
s.hot_flush_in_mem_queue();             // wait for JIT to finish
s.trampoline(&ctx);                     // execute main, handle IO
s.hot_flush_object_queue();             // wait for .o (promote to hot)
```

`trampoline` verifies `main` exists, calls it. If `main` returns `IO`, runs the IO trampoline to force the effect chain.

## 9. Link Mode

```rust
let ctx = CompileContext::new(entry_module_name, ObjectOnly);
s.compile_unit(&src, &ctx, Replace);    // stages 1-5, enqueue to object queue only
s.spawn_nice_object_codegen();           // start .o workers
s.hot_flush_object_queue();              // wait (promoted to hot)
s.link(&ctx);                            // invoke system linker
```

No in-mem queue, no JIT, no execution. `compile_unit` pushes to the object queue only. `link` collects `.o` paths from the object worker state, generates the startup object, and invokes the system linker.

## 10. Form and Display

### 10.1 Form Type

`compile_unit`, `/source`, `/expand`, and other commands all return a `Form` — a uniform representation of something to display. The exact structure of `Form` is owned by the display layer, not the pipeline.

A `Form` carries enough information for `pretty_print_form` to render it: a value (if execution occurred), a type, display metadata, and optionally the source sexp.

### 10.2 `pretty_print_form`

One function. Handles all REPL output: evaluated expressions, definition confirmations, slash command results, errors. Uses the universal output format from `repl/spec.md`:

```
:Type value ; classification — docstring
```

## 11. Settings

```rust
struct Settings {
    lib_dirs: Vec<PathBuf>,     // --lib_search and/or cranelisp.toml
    no_color: bool,             // --no-color or NO_COLOR env
}
```

Read from `cranelisp.toml` in `project_root` (if it exists), overridden by CLI flags. `CRANELISP_LIB` environment variable is an alternative to the TOML file for lib search paths.

## 12. Invariants

1. **One entry point.** All compilation — entry module, dependencies, prelude, REPL input, file watcher reloads — goes through `compile_unit`.
2. **No codegen in `compile_unit`.** Stages 1-5 only. Codegen is enqueued, not executed.
3. **No execution in `compile_unit`.** Values are produced when queues are drained, not during compilation.
4. **Queues own their data.** `CodegenItem` owns `Program`, `CheckResult`, etc. No borrows from the call stack.
5. **Workers own their state.** GOT state, JIT modules, cache state — all private to workers. `compile_unit` never touches them.
6. **Main thread is sacred.** Nice-priority background work must not slow typecheck on the main thread.
7. **`hot_flush` is a barrier.** Blocks until all in-flight queue items are processed.
8. **`hot_flush_object_queue` promotes to full priority.** Remaining object work joins the critical path.
9. **Platform and prelude are not special.** They are handled inside `compile_unit` like any other module-level form. No prescan, no pre-loading, no caller-side setup.
10. **`process_commands` is thin.** Slash commands and blank detection only. All compilation logic is in `compile_unit`.
11. **Dependency graph is populated at stage 2, not stage 5.** Import edges are registered from source declarations before typechecking. A failed `compile_unit` still records its dependencies — this is essential for cascade recompilation after a fix.
12. **File watcher recompiles immediately.** Notifications trigger `compile_unit` + cascade on the watcher thread, not deferred to the REPL prompt. `hot_flush_in_mem_queue` at the prompt is just a barrier for any in-flight work.
13. **Module locks are non-blocking.** `try_lock` fails immediately if the module is already being compiled. The caller retries later. No deadlocks.
