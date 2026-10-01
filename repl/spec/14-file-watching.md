> [REPL specification index](index.md)

## 14. File Watching [R4 S23]

The REPL automatically detects when source files change on disk, eagerly recompiles the affected modules, and notifies the user of the result. The developer edits files in their editor, saves, and the REPL immediately recompiles — no manual reload command needed.

### 14.1 Watch Scope [Uncovered S122 — partial: the watched-directory MUST is tested; its MUST NOT has no cell]

The file watcher MUST monitor directories that contain source files actually loaded during the current session. This includes:
- The project root directory (if one was determined at startup).
- Directories of modules loaded via `(import ...)` or `/mod`, and their transitive dependencies. [Tested tests/repl_watch::watch_emits_notification_when_loaded_module_source_changes — a project-root module loaded through an `import` is watched]

The watcher SHOULD use OS-level filesystem notification (e.g., `FSEvents` on macOS, `inotify` on Linux) rather than polling. This provides near-instant detection without CPU overhead.

New files in watched directories SHOULD be detected, but they do not trigger any action until they are referenced by an import or module load.

The watcher MUST NOT watch directories that contain no source file loaded during the current session. Stdlib directories are watched only if the session loaded a module from them. [Uncovered S122 — no cell: an unloaded directory's changes produce no notification whether or not it is watched, so the rule is not observable end to end, and no unit cell observes the watched-directory set]

### 14.2 Eager Recompilation [Uncovered S122 — partial: steps 2–4, eagerness, quiescence and the content-hash filter are evidenced on their rows; an omitted export and a save during an evaluation have no cell]

When a `.cl` source file is modified (content change, not just metadata/timestamp), the watcher MUST:

1. **Identify the module.** Map the changed file path to its module identity in the module graph.
2. **Start from an empty namespace.** The module is rebuilt from its saved source alone; nothing its previous state held carries into the rebuild. [Tested — observed through step 3's omission cells]
3. **Recompile immediately.** Re-read, re-parse, re-typecheck and re-compile the module from that source. When the rebuild succeeds, the module's definitions and declarations of every kind, its imports and aliases, its submodule declarations and its exports are exactly those its saved source establishes. Anything the saved source omits is no longer in scope, is not shown by introspection and is not written by regeneration (§15.1). Callers get the rebuilt definitions. [Tested tests/repl_persist::persist_definition_removed_by_save_is_not_callable_or_rewritten, tests/repl_persist::watch_definition_removed_from_imported_file_fails_its_importer — steps 2–3 for a concrete ordinary function the save omits: not callable, not shown by `/sig`, not written back, and an importer that uses it fails; the retained `g` is the control] [Tested tests/repl_persist::persist_generic_definition_removed_by_save_is_not_callable_or_rewritten, tests/repl_persist::persist_save_omitting_generic_caller_and_its_callee_reloads_unlocked, tests/repl_persist::watch_generic_removed_from_imported_file_fails_importer_until_its_save — steps 2–3 for a generic function the save omits, in the file and through an importer that fails, then is released by its own compiling save; a generic caller omitted with its callee does not refuse the save] [Tested+Neg tests/repl_persist::persist_import_omitted_by_save_is_not_in_scope_or_rewritten, tests/repl_persist::persist_import_kept_by_save_stays_in_scope_and_is_written_once_control — steps 2–3 for an `import` the save omits: out of `/imports` and bare scope, and not written back; a kept import stays and is written once] [Tested src/session_v4/persistence_tests.rs::rebuild_prologue_establishes_exactly_what_the_saved_source_keeps — unit; steps 2–3 for the other declaration kinds a save omits (type, trait, impl, macro, submodule, import alias): only what the saved source keeps remains, and the module's state outside its table is reset; no e2e cell for these kinds, and no cell for an omitted export]
4. **Cascade to dependents.** Once the changed module compiles, its dependents MUST also be recompiled in topological order. Dependents include modules that import the changed module and modules that refer to its functions or types through a fully-qualified reference; a qualified reference makes a module a dependent without an `import` declaration, so the relation is wider than the declaration graph that orders compilation (language spec [`spec/08-modules.md §8.10.1`](../../spec/08-modules.md)). A dependent that fails to recompile locks the session (§14.5); a dependent with any dependency standing failed is not recompiled until every such dependency compiles (§14.5). [S122] [Tested tests/repl_persist::watch_qualified_caller_fails_on_removed_callee_until_it_is_restored, tests/repl_persist::watch_qualified_type_dependent_locked_until_its_module_compiles — step 4 for a dependent reached only by a qualified function call or type reference: a removed callee fails it and locks the session, and a failing dependency locks the session; the dependency's fix releases it] [Tested+Neg tests/repl_persist::watch_parse_failed_dependency_locks_session_without_recompiling_dependents, tests/repl_persist::watch_cascade_failed_importer_locked_until_import_is_fixed, tests/repl_persist::watch_qualified_type_dependent_locked_until_its_module_compiles, tests/repl_persist::watch_fix_of_dependency_failed_in_session_recompiles_its_dependents_control, tests/repl_persist::session_lock_stands_until_no_module_fails_and_names_each_failing_file — a dependent of a module that fails to parse or typecheck, through an `import`, a qualified type reference or transitively, is neither recompiled nor reported until the fixing save, then is rebuilt; a dependent with a second dependency still failing goes on waiting] [Tested src/session_v4/lifecycle.rs::reload_plan_orders_qualified_dependent_after_its_dependency, src/session_v4/persistence_tests.rs::order_check_rebuilds_a_new_qualified_caller_after_its_callee — unit; step 4 order for a qualified dependent, including a reference first introduced in the same reload] [Tested tests/repl_persist::watch_fix_of_dependency_failed_at_startup_recompiles_its_dependents, tests/repl_persist::watch_fix_of_dependency_failed_in_session_recompiles_its_dependents_control — step 4 after a startup failure: fixing the dependency recompiles, in order, the dependents that failed through it, as it does after an in-session failure] [Tested tests/repl_persist::watch_fix_of_module_newly_imported_by_failing_save_recompiles_importer — step 4: fixing a module that a failing save newly imported recompiles the importer] [Tested tests/repl_persist::watch_dependency_save_recompiles_importer_failed_at_startup_in_own_source, tests/repl_persist::watch_dependency_save_recompiles_qualified_caller_failed_at_startup_in_own_source, tests/repl_persist::watch_dependency_save_recompiles_importer_failed_at_startup_resolving_import — step 4 after a module failed at startup in its own source against its dependency, through an `import` or a qualified reference at the type pass and through an unresolved imported name in Pass 0: the dependency's save recompiles it and then its importer] [Tested src/session_v4/persistence_tests.rs::own_source_failure_at_every_stage_records_the_dependency_it_failed_against — unit; every stage, including Pass-1 expansion, a macro-written reference and a macro checkpoint, records the dependency]
5. **Notify the user of the result.** Display `[updated: <file>]` on success or `[errors: <file>]` on failure (see §14.3).

A reload that would change the structure of a live nominal type fails instead
(§14.8).

An incremental REPL turn does not rebuild its module: it adds to, or replaces
within, the module's current namespace (§15.6, §18).

Recompilation is **eager** — it happens as soon as the change is detected, not deferred until the module is accessed. [Tested tests/repl_watch::watch_recompiles_changed_module_eagerly — `[updated:]` appears although no turn uses the module] A reload never starts while a turn's evaluation, including any IO it executes, is in progress; it runs between turns, before the next prompt. [Tested tests/repl_watch::watch_notification_appears_at_prompt_boundary_not_mid_result — a save made by a `/sh` turn is reloaded at that turn's prompt, before the next evaluation, which observes the rebuilt definition; no cell saves a file while an evaluation or its IO is in progress] [Tested+Neg tests/repl_persist::watch_idle_readable_save_survives_the_next_definition, tests/repl_persist::watch_idle_unreadable_save_locks_before_the_next_definition_overwrites_it — a save made while the REPL is idle at the prompt is reloaded by the next turn, and the turn's definition does not overwrite it; an unreadable save locks and keeps its bytes; their controls are `watch_idle_readable_save_before_failing_definition_is_reloaded_control` and `watch_idle_unreadable_save_before_expression_locks_control`] [Tested src/session_v4/persistence_tests.rs::the_pre_turn_poll_reloads_an_idle_save_before_the_turn — unit; the turn after an idle save observes the rebuilt module] [Tested tests/repl_persist::watch_startup_save_is_loaded_and_later_definitions_reach_the_file, tests/repl_persist::watch_save_after_first_prompt_is_loaded_and_later_definitions_reach_the_file_control — a save made after the session reads the entry and before the watcher first sees it is reloaded, and later definitions reach the file; the control saves at the first prompt] [Tested src/session_v4/persistence_tests.rs::a_save_before_the_watchers_first_sight_is_reloaded, src/session_v4/persistence_tests.rs::a_cache_hit_restore_records_the_state_it_validated — unit; the same window for the entry and for a dependency loaded by `register_dep`, and the state a cache-hit restore validated is the state compared]

Content hash comparison MUST be used to skip metadata-only changes (e.g., `touch foo.cl`). The watcher records the content hash of each source file when it is first loaded and compares against it on each filesystem event. Only true content changes trigger recompilation. [Tested+Neg tests/repl_watch::watch_recompiles_changed_module_eagerly, tests/repl_watch::watch_does_not_notify_on_metadata_only_change — a content change reloads; a `touch` does not] [Tested src/watch.rs::harvest_content_hash_skips_identical_rewrite_reports_real_change — unit; an identical rewrite is skipped and a changed one reported]

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

A save that newly loads a module whose file fails to compile reports `[errors: <file>]` for that module's file. [Tested tests/repl_persist::watch_save_newly_loading_failing_module_names_it_until_its_own_save_compiles, tests/repl_persist::watch_save_newly_loading_unparseable_module_names_it_not_the_importer — a save that newly imports `n.cl` prints `[errors: n.cl]` carrying `n`'s own type error, and its own parse error]

**Input preservation (nice-to-have):** If the user is mid-input when a notification arrives, the notification SHOULD print on a new line, then reinstate the partial input line so typing is uninterrupted. Implementation SHOULD use rustyline's `ExternalPrinter` API for this — with the S106 line editor (§10.8) now a normative default-build dependency, `ExternalPrinter` is the wired-in home for this behaviour on the interactive branch. As an interim approach, notifications MAY be deferred until the next prompt boundary (before the prompt is printed). Notifications MUST NOT corrupt the user's input.

### 14.4 Error Blocking [Tested tests/repl_watch::watch_errors_block_evaluation_no_last_known_good] [Tested tests/repl_watch::watch_type_error_reload_of_imported_module_blocks_without_hanging — items 2–3 after an imported module fails typecheck, five sessions per run, 15 consecutive stress runs]

When a module fails to recompile, it stands **failed** and the session is locked (§14.5):

1. The module is added to the session's error set.
2. Expressions and definitions are refused while the session is locked; §14.5 states what the refusal reports.
3. Slash commands remain available (§14.5).
4. When the source file is modified again (presumably with a fix), the watcher triggers another recompilation attempt. If recompilation succeeds, the module is removed from the error set. If it fails again, the error set is updated with the new error.

There is **no last-known-good fallback**. Source code diverging from runtime behavior is dangerous — the user must see the error and fix it. The error blocking ensures they cannot accidentally evaluate code that depends on a broken module.

The refusal's wording in this transcript is illustrative (§14.5):

```
[errors: math.cl]
  math.cl:5:3 — type error: expected Int, got String
0+0ms; user> (+ 1 2)
Cannot evaluate: math.cl has errors. Fix it and save.
0+0ms; user>
;; User fixes math.cl and saves...
[updated: math.cl]
0+0ms; user> (+ 1 2)
:primitives/Int 3
```

### 14.5 Module State on Error [Tested — items 1–2 for a type, parse or read failure by unit, the parse failure also e2e; the session lock on its rows]

A module fails to recompile when §14.2 step 3 does not complete, including
when its file does not parse or typecheck and when §14.8 refuses the reload,
and when it fails as a dependent recompiled under §14.2 step 4.
When a module fails to recompile:

1. The old module state has already been cleared (§14.2 step 2).
2. The module is in an error state — its definitions are unavailable. [Tested src/session_v4/persistence_tests.rs::reload_replaces_declaration_records_and_failed_reload_clears_them — unit; a reload that fails at type check leaves no record of the module's displaced declarations, so introspection does not show them] [Tested+Neg src/session_v4/persistence_tests.rs::reload_that_cannot_parse_or_read_keeps_nothing_of_the_module, tests/repl_persist::watch_parse_failed_dependency_locks_session_without_recompiling_dependents — a reload whose source does not parse, or cannot be read, keeps nothing of the module (unit); e2e, after a parse-failing save `/sig math/sq` reports an unknown symbol and the dependent is not recompiled against the previous namespace]
3. The session is locked (below). [Tested tests/repl_watch::watch_errors_block_evaluation_no_last_known_good]
4. The module remains watched. The next file modification triggers another recompilation attempt. [Tested tests/repl_watch::watch_clears_error_state_when_subsequent_edit_fixes_source — a save after the failure is recompiled]

**Session lock.** The session is **locked** while any module stands failed. A
module comes to stand failed when:

- a save leaves the loaded program uncompilable: the saved file does not parse
  or typecheck, §14.8 refuses it, or a dependent recompiled under §14.2 step 4
  fails against it;
- it fails to compile at startup (§15.2.3), including an entry file that
  cannot be read (§0.5.5 rule 4) [Tested tests/cli_missing_entry.rs::repl_unreadable_entry_file_locks_session_and_keeps_its_bytes]; or
- it fails to compile when `/mod` loads it (§3.9).

While the session is locked:

- every code turn is refused: a definition, an expression, or a slash command
  that evaluates code, such as `/mem EXPR`, `/time` or `/run-tests` [Tested+Neg tests/repl_persist::session_lock_refuses_every_code_turn_outside_the_failed_module, src/repl/mod.rs::locked_session_refuses_every_code_turn_in_any_module, src/repl/mod.rs::locked_session_refuses_exactly_the_commands_that_run_program_code — e2e: a definition, a `deftype`, an expression, `/mem EXPR` and `/time EXPR` in a module other than the failed one are refused, and `/sig h`, `/info U` and a snapshot show the session and `user.cl` unchanged; unit: every code-turn kind, and each evaluating command, is refused while locked and admitted unlocked]. A refused
  turn leaves the session and every file unchanged. No backing file is
  regenerated or overwritten (§15.1), so each saved file stays on disk as
  saved;
- the refusal names the failing file or files and the remedy; its wording is
  implementation-defined;
- other slash commands remain available: the introspection commands; the
  compile-only diagnostics `/type`, `/expand`, `/sexp`, `/ast`, `/clif` and
  `/disasm`, which compile or expand without running program code; `/sh`
  (§13); `/mod` (§3.9); and `/quit` (§0.1) [Tested src/repl/mod.rs::locked_session_refuses_exactly_the_commands_that_run_program_code, tests/repl_persist::session_lock_refuses_every_code_turn_outside_the_failed_module, tests/repl_persist::mod_load_failure_locks_session_until_its_save_compiles, tests/repl_persist::quit_while_locked_exits_zero_without_reprinting_errors — unit: introspection, the compile-only diagnostics, `/sh`, `/mod` and `/quit` are admitted while locked; e2e: `/sig`, `/help`, `/sh`, `/mod` and `/quit` answer while locked];
- an incomplete form pending at EOF is dropped unevaluated, and the process
  exits as §0.1 states [Tested+Neg tests/repl_persist::eof_while_locked_drops_pending_form_unevaluated, tests/repl_negative::parse_error_unclosed_paren_neg — while locked, no value and no diagnostic follow the last prompt; the unlocked twin reports the unclosed form];
- saves are still recompiled (§14.2). A module with any dependency standing
  failed waits: its definitions are unavailable, and it is not recompiled,
  reported or locked until every such dependency compiles, and it is then rebuilt (§14.2 step 4). A save of a
  module's own file is always attempted, because its saved source decides its
  dependencies; it waits only if one of those stands failed [Tested+Neg tests/repl_persist::session_lock_refuses_every_code_turn_outside_the_failed_module, tests/repl_persist::session_lock_stands_until_no_module_fails_and_names_each_failing_file, src/session_v4/persistence_tests.rs::dependents_of_a_failed_module_wait_unattempted_until_it_compiles, src/session_v4/persistence_tests.rs::saved_root_still_importing_a_failed_module_waits_and_dropping_the_import_rebuilds — a save of an unrelated `user.cl` while locked is recompiled; a dependent with a second failing dependency is not recompiled or reported after the first is fixed; unit: waiting dependents are not attempted and have no notification, and a saved root still importing the failed module waits while one dropping the import rebuilds]; and
- the dependents of a module that failed at startup likewise wait: they are
  pending, not failed, and build when the fix compiles [Tested+Neg tests/repl_persist::startup_with_ill_typed_project_prelude_names_only_the_prelude, tests/repl_persist::startup_with_unparseable_project_prelude_names_only_the_prelude, tests/repl_persist::persist_mod_definition_keeps_dependency_source_failed_at_startup, src/session_v4/persistence_tests.rs::startup_failing_dependency_stands_failed_and_the_entry_waits — a prelude failing to typecheck or parse at startup is the only module reported and named, `user.cl` is unchanged, and the fixing save builds `user`; a dependency failing at startup locks a definition in `user`, naming the dependency].

The lock releases when a save leaves no module standing failed. A restart
releases it only if the saved source then compiles (§14.6). [S122] [Tested tests/repl_persist::persist_type_error_reload_locks_file_until_a_save_compiles, tests/repl_persist::persist_parse_error_reload_lock_survives_restart_until_a_save_compiles, tests/repl_persist::watch_cascade_failed_importer_locked_until_import_is_fixed, tests/repl_persist::watch_qualified_caller_fails_on_removed_callee_until_it_is_restored, tests/repl_persist::watch_qualified_type_dependent_locked_until_its_module_compiles, tests/repl_persist::persist_structural_reload_failure_keeps_saved_edit_until_restart, tests/repl_persist::persist_compatible_save_after_structural_reload_failure_releases_the_file, tests/repl_persist::persist_dependency_change_locks_startup_degraded_entry_until_its_save_compiles — the parse, typecheck, §14.8, dependency and dependent-failure triggers, and an entry failing at startup: a definition in the entry is refused and its file stays as saved, a second failure keeps the lock, and a compiling save releases it] [Tested+Neg tests/repl_persist::session_lock_refuses_every_code_turn_outside_the_failed_module, tests/repl_persist::watch_parse_failed_dependency_locks_session_without_recompiling_dependents, tests/repl_persist::session_lock_stands_until_no_module_fails_and_names_each_failing_file, tests/repl_persist::mod_load_failure_locks_session_until_its_save_compiles, tests/repl_persist::persist_startup_load_failure_locks_session_until_a_save_compiles, tests/repl_persist::persist_reset_does_not_release_startup_lock, tests/repl_persist::watch_unreadable_save_locks_session_and_keeps_its_bytes_until_a_readable_save, tests/repl_persist::watch_one_save_repairing_a_module_and_importing_it_releases_the_lock, tests/repl_persist::watch_save_newly_loading_failing_module_names_it_until_its_own_save_compiles, tests/repl_persist::watch_project_prelude_parse_failure_names_only_the_prelude, tests/repl_persist::watch_qualified_caller_fails_on_removed_callee_until_it_is_restored — the lock outside the failed module and against a structural turn; a dependency that fails to parse; release only when no module stands failed, with each failing file named; the `/mod`, startup and unreadable-save triggers; `/reset` not releasing; one save that repairs a module and makes another import it releases the lock; a newly loaded failing module, not its importer, is named until its own save compiles; a failing prelude, not its dependent, is named; each refusal names the failing file or files and the save remedy, and the file the failure is in when a dependent fails]

This "errors block" approach is preferable to "last-known-good" because it prevents the dangerous situation where the source file says one thing but the runtime does another. The user is forced to address the error before continuing.

### 14.6 Clearing Errors [Tested — the session-lock release is evidenced under §14.5]

A failed module is cleared when it next recompiles successfully, after a save of its own file or as a dependent rebuilt after its dependency compiles (§14.2 step 4), and is removed from the error set. The session lock releases as §14.5 states. [Tested tests/repl_watch::watch_clears_error_state_when_subsequent_edit_fixes_source, tests/repl_persist::persist_type_error_reload_locks_file_until_a_save_compiles, tests/repl_persist::watch_qualified_caller_fails_on_removed_callee_until_it_is_restored — a compiling save of its own file clears a failed module, and a dependent that failed against a removed callee is cleared when the callee's module compiles again] [Tested tests/repl_persist::watch_fix_of_dependency_failed_at_startup_recompiles_its_dependents — after a startup failure, fixing the dependency clears its dependents' errors, and a later definition is accepted and written once] [Tested tests/repl_persist::watch_fix_of_module_newly_imported_by_failing_save_recompiles_importer — after a failing save that added an import of a failing module, fixing that module clears the importer's error, and a later definition is accepted] [Tested tests/repl_persist::watch_dependency_save_recompiles_importer_failed_at_startup_in_own_source, tests/repl_persist::watch_dependency_save_recompiles_qualified_caller_failed_at_startup_in_own_source, tests/repl_persist::watch_dependency_save_recompiles_importer_failed_at_startup_resolving_import — after a startup failure in a dependent's own source, the dependency's save clears the errors of the dependent and its importer, and calls through both evaluate]

Restarting the REPL does not bypass a failure. The restarted session compiles
the saved source (§15.2): source that compiles is established, including a
changed type structure (§14.8); source that still fails is not established,
and a failing backing file follows §15.2.3. [Tested tests/repl_persist::persist_parse_error_reload_lock_survives_restart_until_a_save_compiles, tests/repl_persist::persist_mod_definition_keeps_dependency_source_failed_at_startup, tests/repl_persist::persist_structural_reload_failure_keeps_saved_edit_until_restart — an entry file still failing at restart stays locked, a dependency still failing at restart keeps its file against a `/mod` definition (in-session control), and a restart establishes a changed type structure]

### 14.7 Interaction with Object Cache [Tested tests/repl_watch::watch_change_triggers_cache_directory_creation]

File watching and the object cache work together:
- Recompilation invalidates and replaces cache entries for changed modules.
- Unchanged modules continue to use their cached `.o` files. [Tested tests/cache::cache_repl_import_of_restored_module_reaching_callee_only_module_evaluates, tests/cache::cache_repl_import_of_callee_module_then_restored_caller_evaluates]
- Failed recompilations do NOT update the cache — the stale cache entry remains until a successful recompilation replaces it.

This means that after editing one file, only that file and its dependents are recompiled — unchanged modules load instantly from cache.

### 14.8 Structural Type Changes Require Restart [Tested+Neg]

A watcher reload MUST NOT change the structure of a live nominal type. When a
changed file redeclares a `deftype` whose canonical name is live in the
session, and the redeclaration is not structurally identical to the live
declaration under
[§18.5](18-redefinition.md#185-type-declaration-re-establishment), the reload
of that file fails: [Tested tests/repl_persist::persist_external_edit_changing_field_type_fails_requiring_restart, tests/repl_persist::persist_structural_reload_failure_keeps_saved_edit_until_restart, tests/repl_persist::watch_imported_type_field_reorder_fails_requiring_restart — entry-module field-type and field-count reloads fail; a repeated structural save fails again; an imported module's field reorder fails, its dependent runs neither layout and `/quit` is read, 15 consecutive stress runs. Type-parameter and visibility facets, and a structural reload beside another module standing failed, are unit-evidenced only]

- The `[errors: <file>]` notification (§14.3) identifies the type and states
  that a restart is required to establish its changed structure. This
  information is normative; wording and layout are implementation-defined. [Tested tests/repl_persist::persist_external_edit_changing_field_type_fails_requiring_restart, tests/repl_persist::watch_imported_type_field_reorder_fails_requiring_restart — the type and the restart are named]
- The session locks (§14.5), and clearing follows §14.6. [Tested tests/repl_persist::persist_structural_reload_failure_keeps_saved_edit_until_restart, tests/repl_persist::persist_compatible_save_after_structural_reload_failure_releases_the_file — a definition is refused and the file stays as saved, evaluation is refused, and a structurally identical save releases the lock]

A structurally identical redeclaration, such as one that changes only
docstrings or positional sum-payload labels, does not fail under this section. [Tested+Neg tests/repl_persist::persist_reloaded_docstring_edit_of_repl_entered_type_survives_regeneration, tests/repl_persist::persist_reloaded_docstring_edit_of_file_loaded_type_survives_regeneration, tests/repl_persist::persist_external_edit_changing_defn_body_reloads_control — docstring-only and body-only edits reload; the payload-label facet is unit-evidenced only]

A restart compiles the saved source with no prior live declaration (§15.2), so
saved source that otherwise compiles establishes the changed type. [Tested tests/repl_persist::persist_structural_reload_failure_keeps_saved_edit_until_restart — restart establishes the edit]
