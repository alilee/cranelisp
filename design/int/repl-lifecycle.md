# REPL Lifecycle Design

Sprint 23 design document for file watching, `/reset`, shell escape, REPL cache integration, `--link` CLI wiring, and project_root resolution. Written by `/int`.

## 1. File Watching

### 1.1 Crate and Architecture

Use the `notify` crate with `RecommendedWatcher` (FSEvents on macOS, inotify on Linux). The watcher runs in its own OS thread (managed by `notify`) and delivers events via an `mpsc::channel`.

The `FileWatcher` struct lives in a new `src/repl/watch.rs` module:

```rust
pub struct FileWatcher {
    watcher: RecommendedWatcher,
    rx: mpsc::Receiver<notify::Result<Event>>,
    watched_dirs: HashSet<PathBuf>,
}
```

### 1.2 What Directories to Watch

Watch the **parent directory** of each loaded `.cl` file, not the file itself. This is critical for reliable editor detection — many editors (vim, emacs, VSCode) save via atomic rename: write to `foo.cl.tmp`, then `rename(foo.cl.tmp, foo.cl)`. Watching the file directly would lose the watch after the rename. Watching the parent directory catches the rename event.

Directories are added to the watch set:
- After prelude loading (all stdlib module directories).
- After each `(import ...)` or `/mod` that loads a new file.
- After a cascade reload loads modules from new directories.

Use `RecursiveMode::NonRecursive` — we only watch directories we know contain loaded files. This avoids watching the entire project tree (which could include build artifacts, `.git`, etc.).

### 1.3 Change Detection and Poll Timing

**Poll point**: Before each REPL prompt, when the input buffer is empty (not mid-multiline-input). This is a non-blocking `try_recv` drain loop — all queued events are consumed in one pass.

**Event filtering**:
- Only `EventKind::Create` and `EventKind::Modify` events.
- Only `.cl` files (check extension). Skip `.cl.tmp` to avoid spurious events during atomic saves.
- Canonicalize paths for consistent comparison with loaded module paths.

**Content hash verification**: After detecting a file change event, read the file and compute its SHA-256 hash. Compare against the hash stored in the `CompiledModule`. If the hash is unchanged (e.g., editor saved without modifications, or the event was a metadata-only change), skip reloading. This prevents unnecessary recompilation.

### 1.4 Cascade Invalidation

When a file changes:

1. Map the changed file path to its `ModuleFullPath` via `file_path_to_module()` — scan `tc.modules` for matching `file_path`.
2. Reload the changed module via `reload_module()` — full pipeline: read file, parse, expand, typecheck, compile, update GOT entries.
3. Find transitive dependents via BFS over the module dependency graph (scan `import_specs` and `mod_decls` in all `CompiledModule`s).
4. Reload each dependent in BFS order (direct dependents first).

**GOT atomicity**: All reloads complete synchronously before returning to the prompt. After `reload_module()` updates GOT entries for the changed module, dependent modules are reloaded in the same synchronous pass. No user code runs between partial GOT updates.

**Macro invalidation**: If the changed module defines macros, dependent modules must be re-expanded (not just recompiled). Since `reload_module()` runs the full pipeline (parse -> expand -> typecheck -> compile), this is handled implicitly. The cost is proportional to the number of dependents, but correctness requires it.

### 1.5 Error Recovery: Last-Known-Good

If `reload_module()` fails (parse error, type error, etc.):

1. Restore the previous `CompiledModule` (saved before the reload attempt).
2. Restore GOT entries to their previous values.
3. Remove macros from `MacroEnv` that were part of the old module (they were cleared before the reload attempt), then re-register them from the restored module.
4. Mark the module as "locked" in `locked_modules: HashSet<ModuleFullPath>`.
5. Report the error to the user.

Locked modules block new definitions (defn, deftype, etc.) but allow expression evaluation. When the file changes again, the lock is cleared and reload is retried.

### 1.6 Interaction with Cache

When a watched file changes:
- The corresponding cache entry is implicitly invalidated because the content hash no longer matches.
- After successful reload, a new cache packet is submitted to the `CacheWriter` background thread.
- Dependent modules are also recompiled, generating new cache entries.
- Unchanged modules retain their cached `.o` files.

### 1.7 User Notification

Per the spec (§14.3), display `[changed: file1.cl, file2.cl]` before the next prompt. File paths are relative to the project root. If more than 5 files changed, truncate the list.

## 2. `/reset` Command

### 2.1 State to Clear

A complete `/reset` must clear the following state, in order:

| # | State | Location | Action |
|---|-------|----------|--------|
| 1 | User-defined GOT entries | `ModuleCodegenState` / GOT table | Clear all non-primitive function pointers |
| 2 | Module tables | `TypeChecker.modules` | Remove all modules except `primitives` (compiler-seeded) |
| 3 | Loaded modules tracking | `loaded_modules: HashMap` | Clear entirely |
| 4 | Type environments | `TypeChecker` fields: `type_defs`, `constructor_to_type`, `trait_registry`, `overloads`, `resolved_overloads`, `constrained_fns` | Clear user-defined entries; retain primitive type registrations |
| 5 | Macro environment | `MacroEnv` | Clear all macros (prelude macros will be re-registered during prelude reload) |
| 6 | JIT compiled code | `Vec<Jit>` (stored JIT modules) | Drop references. See §2.2 for memory leak limitation. |
| 7 | Definition history | `DefEntry` storage | Clear all entries |
| 8 | Current module | `current_module` | Reset to `user` (default) or project root module |
| 9 | Locked modules | `locked_modules: HashSet` | Clear entirely |
| 10 | Linker state | `linker: Option<Linker>` | Drop and re-create on next cache load |
| 11 | Cache writer | `cache_writer: Option<CacheWriter>` | Keep running — no need to restart |

**Not cleared:**
- File watcher — continues running across reset (per spec §12.4).
- Object cache on disk — preserved (per spec §12.5). This is the key to fast reset.
- Terminal history — preserved by the line editor (rustyline/reedline).

### 2.2 JIT Memory Leak Limitation

Cranelift's `JITModule` does not support freeing individual compiled functions or selective deallocation of code memory. When `/reset` drops the stored `Jit` modules, the Rust `Drop` impl runs, but depending on the JIT backend implementation, the underlying code memory may not be fully reclaimed.

Repeated `/reset` cycles will leak JIT memory. For the showcase use-case (simulate fresh start with warm cache), this is acceptable — the process does not run long enough for it to matter.

If this becomes a problem, the nuclear option is to re-create the `JITModule` entirely, re-registering all extern symbols (`runtime/*`, primitives, platform functions). This is expensive but achievable since the symbol table is reconstructible.

Document this limitation in the REPL's `/help reset` output or startup banner.

### 2.3 Prelude Reload After Reset

After clearing state:

1. Re-register primitive types and functions in the fresh `TypeChecker`.
2. Call `load_prelude()` — this goes through the cache path. If cached `.o` files exist for all prelude modules, the prelude loads from cache without recompilation. This makes `/reset` near-instant with a warm cache.
3. Inject implicit `(import [prelude [*]])` into the user module.
4. Update watched paths (the file watcher now knows about prelude module directories).

### 2.4 Implementation Outline

```rust
fn cmd_reset(&mut self) {
    // 1. Clear all session state
    self.clear_session_state();

    // 2. Re-initialize TypeChecker with primitives
    self.tc = TypeChecker::new();
    self.tc.register_primitives();

    // 3. Reload prelude (from cache if available)
    match self.load_prelude() {
        Ok(()) => {
            println!("Session reset.");
        }
        Err(e) => {
            eprintln!("Error: Failed to load prelude: {}", e);
            println!("Session reset (no prelude).");
        }
    }

    // 4. Reset current module
    self.current_module = ModuleFullPath::from("user");
    self.tc.register_module_prefix("user");

    // 5. Update watcher for newly loaded modules
    self.update_watched_paths();

    // 6. Reset timing
    self.last_compile_ms = Some(0);
    self.last_eval_ms = Some(0);
}
```

## 3. Shell Escape `;#!`

### 3.1 Input Interception

The shell escape is intercepted **before the input reaches the parser**. In the REPL loop, after reading a complete line (before calling `eval()`):

```rust
let trimmed = input.trim();
if trimmed.starts_with(";#!") {
    let cmd = trimmed[3..].trim();
    self.run_shell_command(cmd);
    continue; // skip normal eval
}
```

This check happens after paren-balancing logic (so multi-line input accumulation is not affected) but before the reader parses the line. Since `;` starts a Cranelisp comment, even if the line somehow reached the parser, it would be ignored.

### 3.2 Command Execution

```rust
fn run_shell_command(&self, cmd: &str) {
    if cmd.is_empty() {
        return; // silently re-prompt per spec §13.6
    }

    let status = std::process::Command::new("/bin/sh")
        .arg("-c")
        .arg(cmd)
        .stdin(std::process::Stdio::inherit())
        .stdout(std::process::Stdio::inherit())
        .stderr(std::process::Stdio::inherit())
        .status();

    match status {
        Ok(exit_status) => {
            if !exit_status.success() {
                if let Some(code) = exit_status.code() {
                    println!("exit status: {}", code);
                } else {
                    // Terminated by signal (Unix)
                    #[cfg(unix)]
                    {
                        use std::os::unix::process::ExitStatusExt;
                        if let Some(sig) = exit_status.signal() {
                            println!("killed by signal: {}", sig);
                        }
                    }
                }
            }
        }
        Err(e) => {
            eprintln!("failed to execute command: {}", e);
        }
    }
}
```

Key design choices:
- **`/bin/sh -c`**: Standard POSIX shell interpretation. No attempt to parse or split the command ourselves.
- **Inherited stdio**: stdout and stderr pass through directly. The user sees output in real time, including interactive programs.
- **Synchronous**: The REPL blocks until the command completes. No background execution.
- **No state interaction**: The command runs in a child process. Environment variable changes, working directory changes, etc. do not propagate back.
- **Timing reset**: The prompt after a shell escape shows `0+0ms` — shell commands are not Cranelisp evaluations.

## 4. REPL Cache Integration

### 4.1 Cache Write After Module Compilation

When the REPL compiles a module (during prelude load, `(import ...)`, or file watching reload), it should write a cache packet:

1. After successful compilation of a module, call `build_cache_packet()` to create a `CacheWritePacket`.
2. Submit the packet to the `CacheWriter` background thread via `writer.submit(packet)`.
3. The `CacheWriter` processes the packet asynchronously — compiles the Cranelift `ObjectModule` to `.o`, writes the metadata JSON, and accumulates manifest entries.
4. On REPL shutdown (`Drop` impl), the `CacheWriter` flushes remaining writes and updates manifests.

### 4.2 Cache Load on Startup/Reset

During `load_prelude()` and `compile_module_graph()`:

1. For each module in topological order, check the cache manifest for a matching entry (module path + source hash).
2. If a cache hit: load the `.o` file via the `Linker`, reconstruct the `CompiledModule` from the metadata JSON, and install the module scope.
3. If a cache miss: compile from source, then submit a cache write packet.

### 4.3 CacheWriter Background Thread Pattern

Follow the sketch's pattern exactly — it is clean and well-proven:

```
CacheWriter {
    tx: mpsc::Sender<CacheWriteMsg>,
    handle: Option<JoinHandle<()>>,
}

enum CacheWriteMsg {
    Write(CacheWritePacket),
    Shutdown,
}
```

- **Lazy initialization**: Created on first cache write (`get_or_insert_with`), not at REPL startup.
- **Non-blocking submits**: `tx.send()` is non-blocking from the REPL's perspective.
- **Ordered shutdown**: `Drop` sends `Shutdown`, then `join()`s the thread. This ensures all pending writes complete and manifests are written before the process exits.
- **Manifest accumulation**: The background thread accumulates `(cache_dir, module_path, source_hash)` tuples and writes manifests in bulk on shutdown, avoiding repeated manifest reads/writes.

### 4.4 `/reset` and Cache Writer

On `/reset`, the `CacheWriter` continues running. It does not need to be restarted because:
- Pending cache writes from before the reset are still valid (they reflect correctly compiled modules).
- After reset, new cache writes will be submitted for freshly compiled modules (if any).
- The cache writer is stateless with respect to session state — it just processes packets.

## 5. `--link` CLI Wiring

### 5.1 CLI Flag

Add `--link <file.cl>` as a new `RunMode` variant:

```rust
enum RunMode {
    Repl,
    RunFile { path: String, no_cache: bool },
    Link { path: String },           // new
    Error(String),
}
```

### 5.2 Execution Flow

```
parse_args() -> RunMode::Link { path }
    -> compile_module_graph_cached(path, ...) // same as --run
    -> verify main symbol exists
    -> collect all .o files from cache
    -> generate startup stub .o
    -> invoke system linker (ld)
    -> produce native executable
```

The compilation step is identical to `--run` — it produces cached `.o` files. The linking step is new and is provided by `/backend` (in the `Linker` module or a new `exe.rs`). `/int` wires the CLI flag to the backend's linking function.

### 5.3 Output Path Derivation

If `--link examples/hello.cl` is given without an explicit output path, derive the output name from the entry file stem: `hello` (no extension). If an output path is provided (`--link hello.cl -o myapp`), use it directly.

### 5.4 Error Cases

- Entry file not found: print error, exit 1.
- No `main` function in entry module: print clear error before invoking linker, exit 1.
- Linker failure: print linker error output, exit 1.
- Missing bundle library: print diagnostic explaining how to build it, exit 1.

## 6. Project Root Resolution

### 6.1 The Problem

The current `src/main.rs` derives `project_root` from the entry file's parent directory:

```rust
let project_root = file_path.parent().unwrap_or(Path::new("."));
```

This is wrong for files in subdirectories. Running `cranelisp --run exemplar/solver.cl` from the project root sets `project_root` to `exemplar/`, which lacks `stdlib/`. Module resolution for prelude and stdlib then fails.

The sketch has the same bug in `batch.rs` (uses `entry_path.parent()`), but works in practice because the sketch's `--cwd` flag is used to set the working directory before batch runs. The sketch's REPL uses `std::env::current_dir()` and works correctly.

### 6.2 The Fix

Use `std::env::current_dir()` as `project_root` for all modes (batch, REPL, and `--link`):

```rust
let project_root = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
```

Rationale:
- The project root is the directory from which the user invokes the compiler. This is the natural location for `stdlib/`, `.cranelisp-cache/`, and project configuration files.
- The entry file may live in any subdirectory (`src/`, `exemplar/`, `examples/`). Its parent directory is not the project root.
- The REPL already uses `cwd` and works correctly. Batch should match.
- The sketch provides `--cwd` to override the working directory before batch runs, which is equivalent to `cd dir && cranelisp --run file.cl`. The reimplementation does not need `--cwd` because `project_root = cwd` is the default.

### 6.3 Module Resolution with cwd-Based Project Root

With `project_root = cwd`:
- `stdlib/` is found at `{project_root}/stdlib/` (the project's standard library).
- `.cranelisp-cache/` is at `{project_root}/.cranelisp-cache/`.
- Entry file is resolved relative to cwd (as it already is — `Path::new(path)` is a relative path).
- Submodules are resolved relative to their parent module's file location (this is unchanged — submodule resolution uses the parent file's directory, not the project root).

## 7. Sketch Comparison

### 7.1 File Watching

The sketch's `watch.rs` implementation is compact (~80 lines) and well-designed. The reimplementation follows the same approach:
- `notify` crate with `RecommendedWatcher`.
- Watch parent directories, not individual files.
- Non-blocking `try_recv` poll before each prompt.
- Filter for `.cl` files, skip `.cl.tmp`.
- Content hash comparison to avoid unnecessary reloads.

**Divergence**: The spec adds user notification (`[changed: ...]` message before the prompt). The sketch prints `; Reloaded <module>` after each reload, which is less informative. The reimplementation will display both: the change notification and reload results.

**Divergence**: The spec specifies lazy recompilation (mark stale, recompile on next access). The sketch recompiles eagerly on detect. The reimplementation follows the sketch's eager approach — the spec's "lazy" wording is about not recompiling in a background thread, not about deferring to the next access. Eager recompilation before the prompt ensures GOT consistency and avoids surprising delays during evaluation.

### 7.2 `/reset`

The sketch does **not** have a `/reset` command. This is new functionality.

The sketch's `/reload` command handles per-module reload (retrying locked modules). The reimplementation's `/reset` is fundamentally different — it clears all session state and starts fresh, rather than reloading individual modules.

**Design insight from sketch**: The sketch's `ReplSession::new()` + `load_prelude()` sequence shows the full initialization path. `/reset` essentially replays this sequence without recreating the file watcher or line editor.

### 7.3 Shell Escape

The sketch does **not** have a shell escape. This is new functionality.

The `;#!` prefix is a clean design choice — it avoids any parser interaction because `;` starts a comment. The implementation is trivially simple (`std::process::Command`).

### 7.4 REPL Cache Integration

The sketch's `CacheWriter` pattern (mpsc channel + background thread + manifest accumulation on shutdown) is clean and the reimplementation copies it directly. Key sketch patterns preserved:
- Lazy `CacheWriter` initialization (`get_or_insert_with`).
- `CacheWriteMsg::Shutdown` for ordered shutdown.
- Manifest accumulation by cache directory, bulk-written on shutdown.
- `Drop` impl that calls `shutdown()` if not already done.

### 7.5 `--link` / `--exe`

The sketch implements this as `--exe` with an `exe.rs` module and `build_executable()` function in `batch.rs`. The approach is sound: compile via the normal pipeline (producing cached `.o` files), then link them with a startup stub and runtime bundle.

**Naming divergence**: The reimplementation uses `--link` (more descriptive of the action — linking cached objects into an executable). The sketch uses `--exe` (more descriptive of the output). `/arch`'s review approves either name.

### 7.6 Project Root

The sketch has the same bug in `batch.rs` (entry file parent as project root) but works around it with `--cwd`. The sketch's REPL uses `cwd` correctly. The reimplementation fixes batch mode to use `cwd` consistently, eliminating the need for a `--cwd` flag.
