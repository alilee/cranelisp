> [REPL specification index](index.md)

## 15. REPL Session Persistence [R4 S52]

### 15.1 Source Regeneration [S122 — partial: a never-recorded backing file is overwritten (ACT-1047); the other rows are Tested] [Tested tests/repl_persist::persist_user_cl_is_created_with_definition_after_session] [Tested+Neg tests/repl_persist::persist_import_omitted_by_save_is_not_in_scope_or_rewritten, tests/repl_persist::persist_import_kept_by_save_stays_in_scope_and_is_written_once_control — after a reload whose saved source omits an `import`, regeneration does not write it back; a kept import is written once]

The REPL MUST persist interactive definitions to disk by maintaining a backing `.cl` file for the entry module (e.g. `user.cl`). When the user enters a definition that compiles successfully:

1. The definition MUST be compiled and installed in the session. [R4 S52]
2. The entry module's backing `.cl` file MUST be **regenerated** atomically from the module's current state. The regeneration is performed by the REPL after eval — it is not part of the compilation or `.o` caching pipeline. [R4 S52] [Tested tests/repl_persist::watch_idle_readable_save_survives_the_next_definition, tests/repl_persist::watch_startup_save_is_loaded_and_later_definitions_reach_the_file, src/session_v4/persistence_tests.rs::regeneration_keeps_an_unseen_save — the module's current state includes a save the session has not yet loaded: a save at an idle prompt or during startup is reloaded before the definition is written, and regeneration refuses to write over a recorded file whose state on disk differs] [S122 — a backing file that exists but was never recorded, such as a `user.cl` created after a session started without one, is overwritten by the next definition (ACT-1047; RED allocated)]

The regenerated source file MUST be valid, parseable Cranelisp source — loading it through the normal module graph pipeline MUST reproduce the same session state. [R4 S52]

While the session is locked, no backing file is regenerated; §14.5 governs it. [Tested tests/repl_persist::persist_structural_reload_failure_keeps_saved_edit_until_restart, tests/repl_persist::persist_compatible_save_after_structural_reload_failure_releases_the_file, tests/repl_persist::persist_type_error_reload_locks_file_until_a_save_compiles, tests/repl_persist::persist_parse_error_reload_lock_survives_restart_until_a_save_compiles, tests/repl_persist::watch_cascade_failed_importer_locked_until_import_is_fixed, tests/repl_persist::watch_qualified_caller_fails_on_removed_callee_until_it_is_restored, tests/repl_persist::watch_qualified_type_dependent_locked_until_its_module_compiles, tests/repl_persist::persist_mod_definition_keeps_dependency_source_failed_at_startup — §14.8, type-error, parse-error, dependency and dependent-failure causes, and a dependency still failing at restart: the failed module's file, or the entry's, stays as saved after a refused definition] [Tested tests/repl_persist::session_lock_refuses_every_code_turn_outside_the_failed_module, tests/repl_persist::persist_startup_load_failure_locks_session_until_a_save_compiles, tests/repl_persist::watch_unreadable_save_locks_session_and_keeps_its_bytes_until_a_readable_save, tests/repl_persist::watch_idle_unreadable_save_locks_before_the_next_definition_overwrites_it, tests/cli_missing_entry.rs::repl_unreadable_entry_file_locks_session_and_keeps_its_bytes — `user.cl` stays byte-identical while a module it does not depend on fails, while the entry fails at startup, and while it holds unreadable bytes saved mid-session, saved at an idle prompt or present at startup]

A definition entered in the session that fails to compile MUST NOT trigger regeneration and is never written. The backing file reflects the last successfully compiled state. [Tested+Neg tests/repl_persist::persist_typecheck_rejected_redefinition_not_written_by_later_regeneration, tests/repl_persist::persist_commit_gate_rejected_redefinition_not_written_by_later_regeneration, tests/repl_persist::persist_failed_import_not_written_to_backing_neg, tests/repl_persist::persist_expression_only_session_leaves_hand_authored_user_cl_untouched — a definition rejected at typecheck or at the commit gate and a failed `import` are not written by a later regeneration, which keeps the prior definition; an expression-only session leaves the file untouched]

### 15.2 Session Restore [Tested tests/repl_persist::persist_defn_survives_restart_via_user_cl]

On REPL startup, the entry module's backing `.cl` file MUST be loaded through the normal module graph pipeline (with cache hit for fast restore). Definitions from the previous session MUST survive restart — the user resumes where they left off. [R4 S52]

If the backing file does not exist (first session, or user deleted it), the REPL MUST start with an empty module. [R4 S52]

#### 15.2.1 Persistence Authority — Restoration Governs, Redefinition Wins [S113]

The backing `.cl` file is **authoritative for restoration only** — it establishes the definitions the session *starts with*, never overriding what the user enters next. The authority model is precise: [S113]

1. **Restoration.** On startup the backing file's definitions are loaded and become the session's initial state (§15.2). A directory holding a persisted `user.cl` (+ `.cranelisp-cache`) therefore **resumes the prior session**, not a fresh program. [S113]
2. **Redefinition wins.** Any definition entered in the session **replaces** a restored definition of the same name (§15.6) — just-entered source always governs. On-disk authority never overrides live input. [S113]
3. **Input is session input, not a fresh program.** Both interactive typing and **piped stdin** (`cranelisp < script.cl` run in a directory with a persisted `user.cl`) are evaluated **against the restored definitions**. A script that references a name it does not itself (re)define resolves that name to the **previous session's** binding — the input augments a resumed session, it does not start a clean one. This is the correct behaviour, but it is a **sharp edge** for anyone applying the `--run` mental model (a self-contained program) to a piped REPL session: the same script piped into an empty directory versus a directory carrying prior state can produce different results. Fresh-program semantics are `cranelisp --run script.cl` (§0.2) or a REPL launched in an **empty** working directory. [S113]

#### 15.2.2 Startup Restore Notice [S113]

Because a resumed session is not visually distinct from a fresh one, the self-documenting-REPL principle requires the session to **say** it resumed prior state. When startup restores a **non-empty** backing file, the REPL SHOULD emit a single R6-metadata line before the first prompt, naming how much state was restored and from where: [S113]

```
; resumed 7 definitions from user.cl
user>
```

- The count is the number of restored **definitions** (the §15.7 persisted forms), not transient expressions. The count MUST be **singular-aware** — `1 definition`, `N definitions`. [S113]
- The notice MUST be **suppressed when the backing file is absent or empty** — a first session in an empty directory MUST reach the prompt with no extra output, preserving the first-session experience (§6.2) and keeping fresh-directory session transcripts byte-identical. [S113]
- When the entry module fails to compile at startup (§15.2.3), nothing is restored and the notice is not printed. [Tested+Neg src/session_v4/persistence_tests.rs::startup_restore_notice_is_emitted_only_when_the_entry_compiled — unit; an entry failing at startup yields no notice, and a compiling control counts its two definitions. The notice is TTY-only (below), so the piped e2e harness cannot observe it]
- The notice is startup-only chrome (§10.3 metadata role), never persisted and never part of a value/definition response. [S113]

**Rendering.** The restore notice is an R6 dim-metadata line (§10.3), grouped
with the other startup notices, such as the search-index notice and the
`Cranelisp.toml` create notice (§0.5.7). It is **not** part of the startup
banner (§6.2), so the banner stays byte-stable across fresh and resumed
sessions. [S114]

**TTY gate.** The restore notice is interactive chrome for a human at the
prompt, like terminal styling (§10.1) and the line editor (§10.8). It is
emitted **only when stdout/stdin is a TTY**; a **non-TTY session (piped stdin,
harness, batch) MUST NOT emit it**, so restore-mode and fresh-mode
non-interactive transcripts stay byte-identical (§10.5). [S114]

**Count.** The count MUST be the number of definitions that actually restored:
a definition that failed to restore at startup (§15.2.3) is not counted, even
though its source remains in the backing file. [S113/S114]

#### 15.2.3 Startup Load Failure [Tested+Neg]

If a module's saved source fails to compile at startup, whether the entry
module's backing `.cl` file (§15.1) or a file the session loads, the REPL MUST
report the load error and still reach a prompt. The module then stands failed,
and the session is locked (§14.5) until a save leaves no module standing
failed. There is no repair at the prompt: definitions are refused like every
other code turn, the failing file stays on disk as saved, and the remedy is to
save a version that compiles. [Tested+Neg tests/repl_persist::persist_startup_load_failure_locks_session_until_a_save_compiles, tests/repl_persist::persist_reset_does_not_release_startup_lock, tests/repl_persist::persist_mod_definition_keeps_dependency_source_failed_at_startup, tests/repl_persist::startup_with_ill_typed_project_prelude_names_only_the_prelude — an entry failing at startup reaches a prompt and refuses a call, a same-name definition and an other-name definition, naming `user.cl` and the save remedy, with the file unchanged, until a compiling save; `/reset` does not release the lock; a dependency or prelude failing at startup locks the entry, and its file stays as saved] [Tested tests/repl_persist::persist_parse_error_reload_lock_survives_restart_until_a_save_compiles — a parse-failing entry at restart: the error is reported, `(g)` is refused, a definition is rejected, the file is unchanged, and a compiling save releases the lock] [Tested tests/repl_persist::persist_dependency_change_locks_startup_degraded_entry_until_its_save_compiles — an entry failing at startup stays locked when its dependency's save rebuilds it and it fails again: a definition is refused, the file is unchanged, and a compiling save of the entry releases it]

A failure caused by a watched file changing during a session is specified in §14.4–§14.6.

### 15.3 Unified Development Model [Tested tests/repl_persist::persist_external_edit_changing_defn_body_reloads_control] [Tested tests/repl_persist::persist_structural_reload_failure_keeps_saved_edit_until_restart — a structural edit takes effect at restart]

This design unifies interactive and file-based development:
- Interactive definitions are source files that happen to be managed by the REPL.
- File watching (§14) applies uniformly — external edits to the backing file MUST be picked up by the watcher and recompiled. An edit that changes the structure of a live nominal type takes effect at restart, not by reload (§14.8).
- The object cache (§14.7) accelerates both imported modules and the user's own work.

### 15.4 Regeneration Integrity [Uncovered S122 — partial: rule 1 is tested, rule 6 only for rule 1, and rules 2–4 have no cell; rules 2 and 4 are a known nonconformance (ACT-1005); see the rows]

The regenerated source file MUST satisfy the following invariants:

1. **Round-trip correctness:** Loading the regenerated file through the compiler MUST produce the same types, values, and module exports as the interactive session. [Tested tests/repl_persist::persist_bug0220_cache_restored_userfns_survive_repl_edit_regen, tests/repl_persist::persist_cache_restored_declarations_survive_repl_edit_regen, tests/repl_persist::persist_file_loaded_declarations_survive_repl_edit_regen] [Tested tests/repl_persist::persist_reloaded_docstring_edit_of_repl_entered_type_survives_regeneration, tests/repl_persist::persist_reloaded_docstring_edit_of_file_loaded_type_survives_regeneration — after a docstring-only declaration reload]
2. **Authorship ordering:** Definitions MUST appear in the order they were registered with the session — file-loaded modules in source declaration order; REPL-introduced symbols appended in the order they were entered. Redefinition MUST NOT reorder; a redefined symbol keeps its original position. Cranelisp's cluster-atomic typecheck handles forward references natively, so dependency ordering is not a correctness requirement — the regenerated file reflects authorship intent. [Uncovered S122 — no cell observes order; tests/repl_persist::persist_user_cl_is_valid_source_with_topological_ordering asserts presence and reload only. Known nonconformance carried to S123/S124: the regenerator groups by kind and sorts by callee dependency (ACT-1005)]
3. **Symbol qualification preservation:** The regenerated source MUST preserve the user's original qualification style. If the user wrote a fully-qualified reference (`core.option/Some`), it MUST remain fully-qualified. If the user wrote a bare name (`Some`) that was resolved via an import, it MUST remain bare. The regenerator MUST NOT rewrite bare names to qualified or vice versa. [Uncovered S122 — no cell]
4. **Structural sections at top in fixed order:** Structural sections MUST appear at the top of the regenerated file in this fixed order: (a) platforms — `(declare-platform ...)` forms; (b) submodules — `(mod ...)` declarations; (c) exports — `(export ...)` forms; (d) imports — `(import ...)` forms. Within each section, items appear in authorship order (file parse order + REPL append). Definitions follow the four structural sections. [Uncovered S122 — no cell; known nonconformance carried to S123/S124 (ACT-1005)]
5. **Comments:** The behaviour of comments in regenerated source is unspecified. The implementation MAY strip comments, preserve them, or handle them in any other way. [R4 S52]
6. **Cache independence:** Rules 1–4 MUST hold whether the module's current definitions were compiled from source or restored from the object cache (§14.7). [Uncovered S122 — partial: rule 1 holds on both legs, restored by tests/repl_persist::persist_bug0220_cache_restored_userfns_survive_repl_edit_regen and tests/repl_persist::persist_cache_restored_declarations_survive_repl_edit_regen, compiled from source by tests/repl_persist::persist_file_loaded_declarations_survive_repl_edit_regen; no test observes rules 2–4 on either leg; rule 1 for a `/mod` turn in a cache-restored module holding a top-level macro call: tests/repl_persist::persist_mod_turn_on_cache_restored_macro_expanded_module, fresh control tests/repl_persist::persist_mod_turn_on_fresh_macro_expanded_module_control]

Rules 2 and 4 and in-place redefinition share one intent: the regenerated file is a faithful record of what the user typed and when, not a form derived from compilation properties. The compiler already handles forward references and dependency resolution, so regeneration does not reorder for correctness. [Tested tests/repl_persist::persist_repl_begin_spanning_sections_written_once, tests/repl_persist::persist_file_loaded_begin_spanning_sections_written_once — a `begin` spanning sections is written once, as authored ([design §1.4](../../design/int/session-persistence.md#14-dependency-ordering)); the note's other clauses are rules 2 and 4]

**Template qualification to round-trip correctness. [S121]** Rule 1 reproduces
the current authored source, types, exports, and ordinary values. It does not
preserve historical generated code that is absent from that source:

- persisted authored macro calls are re-expanded using the macro definition
  current at reload or restart; and
- an authored `impl` that omits a default method re-materializes that method
  using the trait default body current at reload or restart.

Accordingly, an already-compiled expansion or generated default realization
may retain its earlier body in the live session after a future-only template
redefinition, then acquire the latest body when source is recompiled. This is
the only qualification introduced here; it does not permit rewriting authored
source or changing an existing live realization without its specified
typecheck/re-`impl` boundary (§18.4, §18.6).

### 15.5 File Watching Integration [R4 S52]

The file watcher (§14) MUST ignore writes triggered by the REPL's own source regeneration. Self-triggered writes MUST NOT cause a recompilation cycle. External edits to the backing file (e.g. from a text editor) MUST be detected and recompiled normally. [R4 S52]

### 15.6 Redefinition [Tested tests/repl_lifecycle::redefinition_replaces_value] [Tested+Neg tests/repl_persist::persist_typecheck_rejected_redefinition_not_written_by_later_regeneration, tests/repl_persist::persist_commit_gate_rejected_redefinition_not_written_by_later_regeneration]

When the user successfully redefines a name that already exists in the session,
the regenerated source file MUST contain only the latest definition — the
previous definition MUST be replaced, not duplicated. A rejected redefinition
MUST NOT change the regenerated source. [R4 S52] [S121]

The declaration-class rules, atomic rejection behavior, and template
reconstruction qualifications are specified in §18. [S121]

A live redefinition cannot change an existing callable or macro declaration's
visibility. Such a rejected attempt does not change this file. The visibility
may instead change when externally changed persisted source is loaded at reload
or restart; introducing a new canonical name is the live-session alternative.

### 15.7 Backing-File Content — Definitions and Structural Forms Only [S106]

The regenerated backing `.cl` file MUST contain **definitions and structural forms only**.
Transient, **non-defining top-level expression evaluations are session-only and MUST NOT be
persisted** to the backing source file. [S106]

The boundary is precise:

- **Persisted (module content):** definitions — `defn`, `deftype`, `deftrait`, `impl`, `defmacro`
  — and structural forms — `mod`, `import`, `export`, `declare-platform` (the §15.4 rule-4
  structural sections). These are the module the user is building. [S106]
- **NOT persisted (transient session output):** bare top-level **expression** evaluations
  (e.g. `(+ 1 2)`, `(print "hello")`). A REPL top-level expression is recorded internally as a
  synthetic `__expr`-named entry so it can be evaluated and displayed; that entry is **session
  state, not module content**, and MUST be excluded from source regeneration. Persisting it would
  re-materialise the expression as module content on the next load — re-running it or leaving dead
  code — polluting the module the user is building. [S106]

Excluding expressions loses no behaviour: top-level expressions are a REPL-interactive-only
construct (`spec/02-grammar.md` §2.1, `spec/08-modules.md` §8.16.6), and batch mode runs `main`,
so no module-initialisation semantics evaluate them. [S106]
