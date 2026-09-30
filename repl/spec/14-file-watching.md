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

### 14.2 Eager Recompilation [Tested+Neg tests/repl_watch::watch_does_not_notify_on_metadata_only_change] [Tested tests/repl_persist::persist_definition_removed_by_save_is_not_callable_or_rewritten, tests/repl_persist::watch_definition_removed_from_imported_file_fails_its_importer — step 2 for a concrete ordinary function omitted by a save, in the file and through an importer; the retained `g` is the control] [Tested tests/repl_persist::persist_generic_definition_removed_by_save_is_not_callable_or_rewritten, tests/repl_persist::persist_save_omitting_generic_caller_and_its_callee_reloads_unlocked, tests/repl_persist::watch_generic_removed_from_imported_file_fails_importer_until_its_save — step 2 for a generic function omitted by a save, in the file and through an importer that fails, then is released by its own compiling save; a generic caller omitted with its callee does not refuse the save] [Tested+Neg tests/repl_persist::persist_import_omitted_by_save_is_not_in_scope_or_rewritten, tests/repl_persist::persist_import_kept_by_save_stays_in_scope_and_is_written_once_control — step 2 for an `import` the save omits: out of `/imports` and bare scope, and not written back; a kept import stays and is written once] [Tested src/session_v4/persistence_tests.rs::rebuild_prologue_establishes_exactly_what_the_saved_source_keeps — unit; step 2 for the other declaration kinds a save omits (type, trait, impl, macro, submodule, import alias): only what the saved source keeps remains, and the module's state outside its table is reset; no e2e cell for these kinds] [Tested tests/repl_persist::watch_qualified_caller_fails_on_removed_callee_until_it_is_restored, tests/repl_persist::watch_qualified_type_dependent_locked_until_its_module_compiles — step 4 for a dependent reached only by a qualified function call or type reference: it recompiles, fails and locks, and its dependency's fix releases it] [Tested src/session_v4/lifecycle.rs::reload_plan_orders_qualified_dependent_after_its_dependency, src/session_v4/persistence_tests.rs::order_check_rebuilds_a_new_qualified_caller_after_its_callee — unit; step 4 order for a qualified dependent, including a reference first introduced in the same reload] [Tested tests/repl_persist::watch_fix_of_dependency_failed_at_startup_recompiles_its_dependents, tests/repl_persist::watch_fix_of_dependency_failed_in_session_recompiles_its_dependents_control — step 4 after a startup failure: fixing the dependency recompiles, in order, the dependents that failed through it, as it does after an in-session failure] [Tested tests/repl_persist::watch_fix_of_module_newly_imported_by_failing_save_recompiles_importer — step 4: fixing a module that a failing save newly imported recompiles the importer] [Tested tests/repl_persist::watch_dependency_save_recompiles_importer_failed_at_startup_in_own_source, tests/repl_persist::watch_dependency_save_recompiles_qualified_caller_failed_at_startup_in_own_source, tests/repl_persist::watch_dependency_save_recompiles_importer_failed_at_startup_resolving_import — step 4 after a module failed at startup in its own source against its dependency, through an `import` or a qualified reference at the type pass and through an unresolved imported name in Pass 0: the dependency's save recompiles it and then its importer] [Tested src/session_v4/persistence_tests.rs::own_source_failure_at_every_stage_records_the_dependency_it_failed_against — unit; every stage, including Pass-1 expansion, a macro-written reference and a macro checkpoint, records the dependency]

When a `.cl` source file is modified (content change, not just metadata/timestamp), the watcher MUST:

1. **Identify the module.** Map the changed file path to its module identity in the module graph.
2. **Clear old module state.** Remove the module's previous definitions from the typechecker, trait registry, and symbol tables so that recompilation does not conflict with existing definitions.
3. **Recompile immediately.** Re-read, re-parse, re-typecheck, and re-compile the module. Update GOT entries so callers get the new code.
4. **Cascade to dependents.** Dependents of the changed module MUST also be recompiled in topological order. Dependents include modules that import the changed module and modules that refer to its functions or types through a fully-qualified reference; a qualified reference makes a module a dependent without an `import` declaration, so the relation is wider than the declaration graph that orders compilation (language spec [`spec/08-modules.md §8.10.1`](../../spec/08-modules.md)). A dependent that fails to recompile follows §14.4–§14.6.
5. **Notify the user of the result.** Display `[updated: <file>]` on success or `[errors: <file>]` on failure (see §14.3).

A reload that would change the structure of a live nominal type fails instead
(§14.8).

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

### 14.4 Error Blocking [Tested tests/repl_watch::watch_errors_block_evaluation_no_last_known_good] [Tested tests/repl_watch::watch_type_error_reload_of_imported_module_blocks_without_hanging — items 2–3 after an imported module fails typecheck, five sessions per run, 15 consecutive stress runs]

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

### 14.5 Module State on Error [Tested+Neg tests/repl_persist::persist_type_error_reload_locks_file_until_a_save_compiles, tests/repl_persist::persist_parse_error_reload_lock_survives_restart_until_a_save_compiles, tests/repl_persist::watch_cascade_failed_importer_locked_until_import_is_fixed, tests/repl_persist::watch_qualified_caller_fails_on_removed_callee_until_it_is_restored, tests/repl_persist::watch_qualified_type_dependent_locked_until_its_module_compiles, tests/repl_persist::persist_structural_reload_failure_keeps_saved_edit_until_restart, tests/repl_persist::persist_compatible_save_after_structural_reload_failure_releases_the_file — item 5 for type-error, parse-error, cascade-dependent, qualified-reference-dependent and §14.8 causes: the rejected turn leaves the session and file unchanged, a second failure keeps the lock, and a compiling save releases it] [Tested tests/repl_watch::watch_errors_block_evaluation_no_last_known_good — items 3–4] [Tested src/session_v4/persistence_tests.rs::reload_replaces_declaration_records_and_failed_reload_clears_them — unit; item 2: a failed reload leaves no record of the module's displaced declarations, so introspection does not show them; no e2e cell]

A module fails to recompile when §14.2 step 3 does not complete, including
when its file does not parse or typecheck and when §14.8 refuses the reload.
When a module fails to recompile:

1. The old module state has already been cleared (§14.2 step 2).
2. The module is in an error state — its definitions are unavailable.
3. The error set prevents evaluation from proceeding (§14.4).
4. The module remains watched. The next file modification triggers another recompilation attempt.
5. The module is locked: the REPL MUST NOT overwrite its file, so the saved
   content remains on disk. A REPL turn whose success would regenerate that
   file (§15.1) is rejected and leaves the session and the file unchanged. The
   lock releases when a later save of the file recompiles successfully
   (§14.4 item 4).

This "errors block" approach is preferable to "last-known-good" because it prevents the dangerous situation where the source file says one thing but the runtime does another. The user is forced to address the error before continuing.

### 14.6 Clearing Errors [Tested tests/repl_watch::watch_clears_error_state_when_subsequent_edit_fixes_source, tests/repl_persist::watch_cascade_failed_importer_locked_until_import_is_fixed, tests/repl_persist::watch_qualified_caller_fails_on_removed_callee_until_it_is_restored, tests/repl_persist::watch_qualified_type_dependent_locked_until_its_module_compiles, tests/repl_persist::persist_parse_error_reload_lock_survives_restart_until_a_save_compiles, tests/repl_persist::persist_structural_reload_failure_keeps_saved_edit_until_restart, tests/repl_persist::persist_mod_definition_keeps_dependency_source_failed_at_startup — a compiling save clears the error, a cascade-failed dependent, including one reached only by a qualified reference, is released by its dependency's fix, an entry file still failing at restart stays locked, a dependency still failing at restart keeps its file against a `/mod` definition (in-session control), and a restart establishes a changed type structure] [Tested tests/repl_persist::watch_fix_of_dependency_failed_at_startup_recompiles_its_dependents — after a startup failure, fixing the dependency clears its dependents' errors, and a later definition is accepted and written once] [Tested tests/repl_persist::watch_fix_of_module_newly_imported_by_failing_save_recompiles_importer — after a failing save that added an import of a failing module, fixing that module clears the importer's error, and a later definition is accepted] [Tested tests/repl_persist::watch_dependency_save_recompiles_importer_failed_at_startup_in_own_source, tests/repl_persist::watch_dependency_save_recompiles_qualified_caller_failed_at_startup_in_own_source, tests/repl_persist::watch_dependency_save_recompiles_importer_failed_at_startup_resolving_import — after a startup failure in a dependent's own source, the dependency's save clears the errors of the dependent and its importer, and calls through both evaluate]

Error-locked modules (§14.4, §14.5) are cleared when the offending file is fixed and saved — the watcher detects the change, recompiles successfully, and removes the module from the error set.

Restarting the REPL does not bypass a failure. The restarted session compiles
the saved source (§15.2): source that compiles is established, including a
changed type structure (§14.8); source that still fails is not established,
and a failing backing file follows §15.2.3.

### 14.7 Interaction with Object Cache [Tested tests/repl_watch::watch_change_triggers_cache_directory_creation]

File watching and the object cache work together:
- Recompilation invalidates and replaces cache entries for changed modules.
- Unchanged modules continue to use their cached `.o` files. [Tested tests/cache::cache_repl_import_of_restored_module_reaching_callee_only_module_evaluates, tests/cache::cache_repl_import_of_callee_module_then_restored_caller_evaluates]
- Failed recompilations do NOT update the cache — the stale cache entry remains until a successful recompilation replaces it.

This means that after editing one file, only that file and its dependents are recompiled — unchanged modules load instantly from cache.

### 14.8 Structural Type Changes Require Restart [Tested+Neg tests/repl_persist::persist_external_edit_changing_field_type_fails_requiring_restart, tests/repl_persist::persist_structural_reload_failure_keeps_saved_edit_until_restart, tests/repl_persist::persist_compatible_save_after_structural_reload_failure_releases_the_file, tests/repl_persist::persist_reloaded_docstring_edit_of_repl_entered_type_survives_regeneration, tests/repl_persist::persist_reloaded_docstring_edit_of_file_loaded_type_survives_regeneration, tests/repl_persist::persist_external_edit_changing_defn_body_reloads_control, tests/repl_persist::watch_imported_type_field_reorder_fails_requiring_restart — entry-module field-type and field-count reloads fail with the type and restart named; a repeated structural save fails again; restart establishes the edit; docstring-only and body-only edits reload; an imported module's field reorder fails with the type and restart named, its dependent runs neither layout and `/quit` is read, 15 consecutive stress runs. The lock and release legs of these cells evidence §14.5 item 5 for this cause. Payload-label, type-parameter and visibility facets, and a structural reload beside another module standing failed, are unit-evidenced only]

A watcher reload MUST NOT change the structure of a live nominal type. When a
changed file redeclares a `deftype` whose canonical name is live in the
session, and the redeclaration is not structurally identical to the live
declaration under
[§18.5](18-redefinition.md#185-type-declaration-re-establishment), the reload
of that file fails:

- The `[errors: <file>]` notification (§14.3) identifies the type and states
  that a restart is required to establish its changed structure. This
  information is normative; wording and layout are implementation-defined.
- Error blocking, the module lock and clearing follow §14.4–§14.6.

A structurally identical redeclaration, such as one that changes only
docstrings or positional sum-payload labels, does not fail under this section.

A restart compiles the saved source with no prior live declaration (§15.2), so
saved source that otherwise compiles establishes the changed type.
