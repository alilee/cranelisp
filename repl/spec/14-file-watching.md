> [REPL specification index](index.md)

## 14. File Watching [R4 S23]

The REPL automatically detects when source files change on disk, eagerly recompiles the affected modules, and notifies the user of the result. The developer edits files in their editor, saves, and the REPL immediately recompiles — no manual reload command needed.

### 14.1 Watch Scope [Tested tests/repl_watch::watch_emits_notification_when_loaded_module_source_changes]

The file watcher MUST monitor directories that contain source files actually loaded during the current session. This includes:
- The project root directory (if one was determined at startup).
- Directories of modules loaded via `(import ...)` or `/mod`, and their transitive dependencies.

The watcher SHOULD use OS-level filesystem notification (e.g., `FSEvents` on macOS, `inotify` on Linux) rather than polling. This provides near-instant detection without CPU overhead.

New files in watched directories SHOULD be detected, but they do not trigger any action until they are referenced by an import or module load.

The watcher MUST NOT watch directories that have not been imported. Stdlib directories are watched only if the prelude or a user module actually imported from them.

### 14.2 Eager Recompilation [Tested+Neg tests/repl_watch::watch_does_not_notify_on_metadata_only_change]

When a `.cl` source file is modified (content change, not just metadata/timestamp), the watcher MUST:

1. **Identify the module.** Map the changed file path to its module identity in the module graph.
2. **Clear old module state.** Remove the module's previous definitions from the typechecker, trait registry, and symbol tables so that recompilation does not conflict with existing definitions.
3. **Recompile immediately.** Re-read, re-parse, re-typecheck, and re-compile the module. Update GOT entries so callers get the new code.
4. **Cascade to dependents.** Dependents of the changed module MUST also be recompiled in topological order.
5. **Notify the user of the result.** Display `[updated: <file>]` on success or `[errors: <file>]` on failure (see §14.3).

Recompilation is **eager** — it happens as soon as the change is detected (at the next poll opportunity, before the next prompt), not deferred until the module is accessed.

Content hash comparison MUST be used to skip metadata-only changes (e.g., `touch foo.cl`). The watcher records the content hash of each source file when it is first loaded and compares against it on each filesystem event. Only true content changes trigger recompilation.

### 14.3 Notification Format [Tested tests/repl_watch::watch_notification_uses_bracketed_file_format]

The recompilation result IS the notification. There is no separate `[changed: ...]` message.

**On success:**

```
0+0ms; user> (+ 1 2)
:primitives/Int 3
[updated: math.cl]
0+0ms; user>
```

The format is `[updated: <file>]` where `<file>` is the path relative to the project root. If multiple modules were recompiled, each gets its own notification line.

**On failure:**

```
0+0ms; user> (+ 1 2)
:primitives/Int 3
[errors: math.cl]
  math.cl:5:3 — type error: expected Int, got String
0+0ms; user>
```

The format is `[errors: <file>]` followed by the error details on indented lines. The error details use the standard error format (§5.1).

**Input preservation (nice-to-have):** If the user is mid-input when a notification arrives, the notification SHOULD print on a new line, then reinstate the partial input line so typing is uninterrupted. Implementation SHOULD use rustyline's `ExternalPrinter` API for this — with the S106 line editor (§10.8) now a normative default-build dependency, `ExternalPrinter` is the wired-in home for this behaviour on the interactive branch. As an interim approach, notifications MAY be deferred until the next prompt boundary (before the prompt is printed). Notifications MUST NOT corrupt the user's input.

### 14.4 Error Blocking [Tested tests/repl_watch::watch_errors_block_evaluation_no_last_known_good]

When a module fails to recompile, the REPL MUST block further evaluation until the error is resolved:

1. The module is added to the session's error set.
2. Before evaluating any expression, the REPL checks the error set. If non-empty, it refuses evaluation with a message: `Cannot evaluate: module '<name>' has errors. Fix the source file and save.`
3. Slash commands (`/help`, `/quit`, etc.) remain available during error blocking — only expression evaluation is blocked.
4. When the source file is modified again (presumably with a fix), the watcher triggers another recompilation attempt. If recompilation succeeds, the module is removed from the error set, and evaluation resumes normally. If it fails again, the error set is updated with the new error.

There is **no last-known-good fallback**. Source code diverging from runtime behavior is dangerous — the user must see the error and fix it. The error blocking ensures they cannot accidentally evaluate code that depends on a broken module.

```
[errors: math.cl]
  math.cl:5:3 — type error: expected Int, got String
0+0ms; user> (+ 1 2)
Cannot evaluate: module 'math' has errors. Fix the source file and save.
0+0ms; user>
;; User fixes math.cl and saves...
[updated: math.cl]
0+0ms; user> (+ 1 2)
:primitives/Int 3
```

### 14.5 Module State on Error [R4 S23]

When a module fails to recompile:

1. The old module state has already been cleared (§14.2 step 2).
2. The module is in an error state — its definitions are unavailable.
3. The error set prevents evaluation from proceeding (§14.4).
4. The module remains watched. The next file modification triggers another recompilation attempt.

This "errors block" approach is preferable to "last-known-good" because it prevents the dangerous situation where the source file says one thing but the runtime does another. The user is forced to address the error before continuing.

### 14.6 Clearing Errors [R4 S23]

Error-locked modules (§14.4) are cleared when the offending file is fixed and saved — the watcher detects the change, recompiles successfully, and removes the module from the error set. The user can also restart the REPL (`/quit`) to clear all state.

### 14.7 Interaction with Object Cache [Tested tests/repl_watch::watch_change_triggers_cache_directory_creation]

File watching and the object cache work together:
- Recompilation invalidates and replaces cache entries for changed modules.
- Unchanged modules continue to use their cached `.o` files. [Tested tests/cache::cache_repl_import_of_restored_module_reaching_callee_only_module_evaluates, tests/cache::cache_repl_import_of_callee_module_then_restored_caller_evaluates]
- Failed recompilations do NOT update the cache — the stale cache entry remains until a successful recompilation replaces it.

This means that after editing one file, only that file and its dependents are recompiled — unchanged modules load instantly from cache.
