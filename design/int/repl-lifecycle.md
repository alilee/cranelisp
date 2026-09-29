# REPL lifecycle

Int's design for the file watcher, `/reset`, the `/sh` shell escape, REPL
cache use, `--link` wiring and project-root resolution. The normative
experience is `repl/spec/00-cli-invocation.md`, `13-shell-escape.md`,
`14-file-watching.md` and `15-session-persistence.md`. Project configuration
is [cranelisp-toml.md](cranelisp-toml.md).

## 1. File watching

`src/watch.rs::FileWatcher` wraps notify's `RecommendedWatcher`. The session
holds it as `CompilerSession.watcher`, which is absent if the OS watcher cannot
start.

### 1.1 What is watched

The watcher watches the parent directory of every loaded source file,
non-recursively. It watches directories rather than files, because editors
that save by atomic rename would lose a per-file watch.

- `init_watcher` arms it once modules have loaded at start-up.
- `sync_watcher` runs after every REPL or agent turn and adds the directories
  of newly loaded files.

### 1.2 Poll and reload

- **Poll point.** After each turn and before the next prompt, `poll_and_reload`
  drains queued events with a non-blocking `try_recv`.
- **Filter.** The watcher keeps only create and modify events on `.cl` files,
  excluding `.cl.tmp`, with canonical paths.
- **Content hash.** A file is changed only when its source hash differs from
  the stored baseline, so metadata-only events do nothing.
  - The baseline is recorded on first encounter.
  - When the session regenerates a backing file itself, it updates the stored
    hash so its own write is not reported.
- **Reload edges.** One private predicate answers "module A depends on module
  B" for both selection and ordering (Principle 7). A's edges are:
  - each `import` and `export` target, resolved through A's declared children
    ([int §6.9](int.md#69-bare-module-names-in-import-and-export));
  - `prelude`, when A's fallback bit is on;
  - A's recorded edges, `cache::dependency_record::recorded_edges`: callee
    modules and lookup dependencies. These carry qualified function, type,
    trait, constructor, pattern, accessor and macro-head references, including
    through a re-exporter ([int §7.6.1–§7.6.2](int.md#76-dependency-record-and-validity));
  - while A holds an established reference, the same edges of that reference
    ([session transaction §7.3.2](session-transaction.md#732-the-established-reference)).
    A failed compile records neither callees nor lookup dependencies, so this
    keeps a failed module reachable from the dependency whose repair releases
    it.

  Declared children are not reload edges: a `mod` declaration drives loading
  and compiles no reference into the child. They remain cache-validity edges.
  Over-selection through a stale edge costs only a recompile.
- **Reload set.** The changed modules plus every module that reaches one of
  them transitively over reload edges. A dependent is admitted when
  `file_to_module` maps a file to it; any other is skipped
  ([session transaction §7.3.3](session-transaction.md#733-slot-reuse-and-the-plan-invariant)
  names the residual).
- **Order.** Condense the plan over the same edges and emit components
  dependency first; lexical order applies only inside a component and between
  unrelated components. The order is load-bearing: a whole-file rebuild
  reuses GOT slot indices, so a module compiled before a dependency the same
  plan rebuilds would call through reused slots.
- **Order check.** The plan is ordered from edges recorded before it runs. A
  changed root whose new source adds a reference to another plan member can
  therefore compile before it. After the plan runs, check each module it
  rebuilt successfully against its new edges. One that reaches a module this
  plan rebuilt later is rebuilt again, with its dependents, in a follow-on
  plan, until no such module remains. Compile-time cycles are rejected, so
  this converges; with no new cross-reference it adds no work. Each module's
  last outcome is its notification.
- **One executor.** Every reload of a saved file runs as a plan through one
  private executor: the watcher poll, `/mod`'s recompile of a cache-installed
  module (`session-persistence.md` §2.4.5), and the superseded T1 and T2
  residue ([session transaction §10](session-transaction.md#10-t1-and-module-grain-reload-superseded-residue)).
  A caller supplies roots; the executor adds dependents, orders, reloads each
  module, runs the order check and returns each module's outcome. The watcher
  prints every notification, `/mod` reports each failed module's, and T1 and
  T2 read their root's outcome. `reload_module` is visible only to the
  session's own modules, so no other caller can rebuild outside a plan.
- **Reload.** `reload_module` replaces the module's typecheck product with the
  file it re-read, keeping the backing path and recording that text for
  verbatim slices. It waits for the module's in-flight pass to settle, runs
  the whole-file rebuild's prologue
  ([session transaction §7.3.1](session-transaction.md#731-the-whole-file-rebuild)),
  captures the preamble onto the fresh table, re-parses and re-registers the
  module with whole-source provenance, and waits for that module's own outcome
  (§1.3). Regeneration writes to the recorded path
  (`session-persistence.md` §3.2), so a reload must not drop it.
- **Guards (module).**
  - A module whose only edge to the changed module is a recorded edge is
    selected, transitively; a module with no edge is not.
  - A dependent whose last rebuild failed on a qualified reference to the
    changed module is still selected when that module changes.
  - A qualified-reference-only dependent whose name sorts before its
    dependency is ordered after it.
  - Order check: two roots changed together, where the earlier-sorting one's
    new source adds a qualified call into the other, end with the caller
    rebuilt after the callee.

  End to end: FQR-1
  (`tests/repl_persist.rs::watch_qualified_caller_fails_on_removed_callee_until_it_is_restored`),
  FQR-2
  (`tests/repl_persist.rs::watch_qualified_type_dependent_locked_until_its_module_compiles`)
  and FL-3.

### 1.3 Failed reload

A failed reload adds the module to the session's error set and locks it
(§1.3.1). There is no last-known-good restore: the module keeps the partial
table its failed rebuild produced
([session transaction §7.3.1](session-transaction.md#731-the-whole-file-rebuild)).

- While the set is non-empty, an expression turn is refused with `Cannot
  evaluate: module '<name>' has errors. Fix the source file and save.`
- A definition turn is admitted unless its current module is locked. In an
  unlocked module it can be the repair of a startup failure
  (`15-session-persistence.md` §15.2.3).
- A later successful reload clears the module's error, failed-form state and
  lock.

**Outcome.** A reload's outcome, success or failure, is the reloaded module's
own terminal state, never another module's.

- **Wait.** `reload_module` waits on the reloaded module alone, through the
  scheduler's existing single-module in-memory wait. It fails with that
  module's own error when the module stands `Failed`, and succeeds once the
  module's in-memory publication is complete.
- **Why not the every-module wait.** That wait returns the first `Failed`
  module in map order. While another module still stands `Failed` from an
  earlier plan, it reports that module's error, possibly before this module
  settles, and turns a successful reload into a failure.
- **Other failed modules.** A module that still stands `Failed` is not this
  reload's outcome. It keeps its error-set membership until its own reload,
  which the plan orders after its dependencies (§1.2).
- **Ordering.** The wait cannot end before the reloaded module settles. The
  worker publishes before it notifies in-memory completion, and it records a
  structural refusal before it reports the module failed (§1.3.1).
- **Coverage.** Every module the reload registers is a dependency of the
  reloaded module. The module's body waits at the signature barrier until each
  such dependency reaches a terminal typecheck pool. A source-compiled
  dependency notifies in-memory completion before it reaches `TypecheckDone`,
  so the single-module wait also covers it. Falsifier: a reload that adds an
  import of an unloaded module returns while that module's in-memory codegen
  is incomplete.
  - **Limit: a cache-restored dependency is not covered.** It enters
    `TypecheckDone` before its object is loaded into memory
    (`ModuleState::new_cached` in `src/scheduler.rs`). The barrier therefore
    opens, and the reload can return `Ok`, while that load is still pending.
    The eval path's per-module dependency wait has the same shape for a
    cache-restored transitive dependency. Grade: asserted with a named
    falsifier. The window is observed from source; its consequence, a
    `null-got-slot` crash, is unobserved. Falsifier: a reload that adds an
    import of a cache-restored module, then immediately calls that module's
    function through the reloaded module, crashes or observes an unloaded
    slot.
- **Liveness.** The wait ends because every path that would wait on a `Failed`
  module fails fast
  ([error cascade §4.1](step9-error-cascade.md#41-cascade-construction)). A
  stranded reloaded module would hang the reload in every session, not only
  in some map orders.
- **Guards.** In `src/session_v4/persistence_tests.rs`,
  `reload_beside_a_failed_module_succeeds_and_lifts_its_restart_marker`
  is the deterministic discriminator: a successful reload beside a `Failed`
  module succeeds and clears its marker.
  `structural_reload_beside_a_failed_module_reports_its_own_refusal` checks
  a refusal beside `Failed` modules. It detects the wrong outcome only when
  map order puts another failed module first. Neither
  exercises the coverage falsifier.

#### 1.3.1 Module lock

A module whose saved file the session has not accepted is locked: the REPL
writes nothing over that file until a reload of it succeeds
(`14-file-watching.md` §14.5 item 5; `15-session-persistence.md` §15.2.3,
unparsable backing file). One lock serves every cause. The restart-required
refusal (`14-file-watching.md` §14.8) is one of its causes, not a separate
mechanism.

- **State.** The session holds a crate-private map from each locked module
  to its cause. It is session state and is never persisted, so a restart
  compiles the saved source afresh (§14.6). The cause is one of two:
  - **restart-required**, carrying the refused type: the reload was refused
    under §14.8 (the guard is
    [session transaction §2.6](session-transaction.md#26-type-re-establishment-repl-185-148));
  - **failed source**: every other failure, whether the file could not be
    read, parsed, typechecked, compiled or published, or the module failed
    in the cascade from a failed dependency. At startup, an entry backing
    file that does not parse and every non-entry module the failed start
    left `Failed` have this cause too.
- **Set.** Two sites write the lock, and each also adds the module to the
  error set.
  - `reload_module` locks on every failure it returns, including the read
    and parse failures before re-registration. It records restart-required
    when the reloaded module's scheduler refusal record names a type; the
    read is keyed by the reloaded module and follows that module's own
    `Failed` outcome (§1.3 Outcome), so it cannot precede the worker's
    record, and the returned error is the module's own refusal, naming the
    type and the restart remedy (§14.8). Otherwise it records failed source
    unless the module is already locked. Every caller reaches it through the
    one executor (§1.2), so no reload of a saved file can fail without
    locking.
  - Startup recovery (`recover_startup_failure`) records failed source in
    two cases.
    - **Entry that does not parse.** Such a file yields no failed form: it
      has no definition source to retain (§15.2.3), so the lock, not
      re-emission (`session-persistence.md` §2.1), keeps it. The startup
      report still prints `[errors: <file>]` with the parse error. The file
      stays mapped and watched, because entry registration maps it before
      parsing.
    - **Failed non-entry modules.** Recovery locks every module other than
      the entry that its scheduler reset returns, that is, every module the
      failed start left `Failed`, whether by its own failure or in the
      cascade. Recovery forgets them before the degraded entry re-drive, so
      nothing re-establishes them. Without the lock, `/mod` to one of them
      plus a definition would regenerate its file from a table that never
      compiled, overwriting the failing source (ACT-1010 M1; REPL §14.6: a
      restart does not bypass a failure). Such a module is not a backing
      file (§15.1), so the §15.2.3 repair does not apply to it. Each was
      mapped for the watcher when its load read the file, so its own
      compiling save releases it.
- **Not set.** A startup backing file that parses keeps the §15.2.3 repair:
  its failed forms are retained and definition turns are admitted.
- **Stands.** A later failing reload of any cause leaves the lock, as do
  `/reset` (§2.1) and `/mod`. A later §14.8 refusal replaces a failed-source
  cause with restart-required; a later failure of another cause keeps the
  recorded cause.
- **Clears.** Only `reload_module`'s success branch clears it, beside the
  error-set and failed-form clears and the drop of the module's established
  reference
  ([session transaction §7.3.2](session-transaction.md#732-the-established-reference)),
  including while another module stands
  `Failed` (§1.3 Outcome). A dependent locked in a cascade is released by its
  own successful reload, which the plan orders after its fixed dependency
  (§1.2). Process exit also ends it.
- **Invariant.** A locked module is always in the error set. The set sites
  maintain it, and `/reset` keeps locked modules. The failed-form repair
  clear (`clear_repaired_failed_form`) follows only an admitted definition
  turn, which the lock refuses in its own module.
- **Turn admission.** `process_commands` rejects, inside its §14.4 gate, a
  definition or structural turn whose current module is locked. The session
  and the file are unchanged. The message names the module and the remedy
  for the cause: restart-required names the type and the restart remedy;
  failed source says that the saved file does not compile and that a
  successful save releases the module. The wording is `dev`'s.
  - A turn in a module that is not locked keeps the admission rules above,
    even when another module is locked.
  - This one site covers typed REPL input and the agent's submit, which
    routes through it (`submit_clean_form`).
  - The agent's document edits bypass it, so `run_document_edit` makes the
    same refusal before asking for consent.
- **Write chokepoint.** `regenerate_backing_file` returns before reading or
  writing when the current module is locked. This covers every
  regeneration caller, including any that admission does not enumerate:
  `main.rs`, `agent/pull.rs` and the `redefine.rs` residue.
- **Why both.** Admission keeps the session unchanged; the chokepoint keeps
  the file intact whatever the caller.
- **Imported modules.** A failure in a non-entry module that another module
  imports is reported after parsing, inside a worker. Its importer fails
  through the barrier's fail-fast on an already-failed member
  ([error cascade §4.1](step9-error-cascade.md#41-cascade-construction)), so
  the reload plan returns. The watcher prints its notifications only after
  the whole plan returns, so any wait that never ends withholds the
  diagnostic. The end-to-end guards are
  `tests/repl_persist.rs::watch_imported_type_field_reorder_fails_requiring_restart`
  and `tests/repl_watch.rs::watch_type_error_reload_of_imported_module_blocks_without_hanging`.
  A `/mod` into a failed cache-installed module reaches the same barrier, so
  the fail-fast covers it by construction. No cell exercises that route.
- **Guards.** In `tests/repl_persist.rs`, for the restart-required cause:
  - `persist_external_edit_changing_field_type_fails_requiring_restart`
    checks the refusal.
  - `persist_structural_reload_failure_keeps_saved_edit_until_restart`
    checks the retained file and the restart.
  - `persist_compatible_save_after_structural_reload_failure_releases_the_file`
    checks the clear.

  The lock's lifecycle, admission and chokepoint units are in
  `src/session_v4/persistence_tests.rs`. They include one row per executor
  caller: a failed root or dependent reached through the watcher plan,
  `/mod`'s recompile and a T1-rooted plan each leaves its module locked and
  in the error set. For a failed non-entry module at
  startup, the ACT-1010 M1 cell is the end-to-end guard. Its unit checks
  that recovery locks the failed dependency and not a parseable entry.

### 1.4 Notification

Each reloaded module prints one dim metadata line: `[updated: <file>]`, or
`[errors: <file>]` followed by the reloaded module's own indented error
(§1.3 Outcome). `<file>` is the file's bare
name (§7, gap 1).

## 2. `/reset` Command

**Status: not implemented.** `/help` lists it as `(not yet available)`, and no
REPL specification section defines it.

### 2.1 Current behaviour

`/reset` replies `command not yet available in v4 REPL` and changes only two
things:

- **It clears the watcher.** It unwatches every directory, drops the stored
  hashes and drains pending events. Watching resumes at the next
  `sync_watcher`, with hashes re-baselined.
- **It keeps failed modules.** A module holding unrepaired failed source stays
  in the error set, because `/reset` is not a repair (§15.2.3). So does a
  locked module (§1.3.1), whose lock stands until a reload of it succeeds.

Symbol tables, compiled code, macros, the prelude and the disk cache are
untouched.

### 2.2 Open question

A full reset has no requirement and no design. Clearing the watcher can hide an
external repair made before the next turn. Whether `/reset` should keep the
watcher, gain a full-reset design or be withdrawn is a `spec` question routed
through `sprint`.

### 2.3 Prelude reload after reset

None. `/reset` reloads no prelude. `tests/cache.rs::cache_repl_writer_survives_slash_reset`
observes that the session and its cache keep working after `/reset`, which
holds because nothing is cleared.

## 3. Shell escape

`/sh <command>` runs the command through `sh -c` with inherited stdio and
waits for it to finish (`src/repl/mod.rs::run_shell_command`). Its input line is
exempt from paren-balance accumulation.

| Case | Output |
|---|---|
| Empty command | `Usage: /sh <command>` |
| Non-zero exit | `exit status: N` |
| Killed by a signal | `killed by signal: N` |
| Spawn failure | `error: <e>` |

Environment and working-directory changes in the child do not affect the
session.

## 4. REPL cache integration

The REPL uses the same cache path as `--run` (`int.md` §7).

### 4.1 Cache write after module compilation

The nice workers write each loaded module's `.meta` and `.o` and record its
manifest entry ([dependency record](int.md#76-dependency-record-and-validity)).
There is no separate cache-writer thread.

- A defining turn regenerates the backing file, records its new source hash
  and marks the module's object stale, so a nice worker rewrites it.
- The manifest flushes in `wait_object_complete`, after deferred entries are
  retried. The REPL calls it at exit, after the final persist.

### 4.2 Cache load on startup/reset

Every dependency, prelude and submodule handler calls `try_cache_hit_load`
before a fresh build ([cache-hit flow](int.md#71-cache-hit-flow-inside-register_module)).
The restore recurses through the restored module's dependencies. The CLI
target itself is always compiled fresh. `/reset` loads nothing (§2). A
cache-installed module is recompiled from source before `/mod` makes it
current (`session-persistence.md` §2.4.5).

## 5. `--link`

- **Arguments.** `--link` selects the link action and `-o`/`--output` names
  the output. Each of these is an argument error with exit 1:
  - `--link` with `--run`;
  - `--link` with `--no-cache`;
  - `-o` without `--link`;
  - `-o` without a path.
- **Flow.** Start-up compiles exactly as `--run` does and then waits for
  object codegen. `link_by_name` then:
  1. validates that `main` is `(Fn [] (IO _))`;
  2. rejects development-session externs;
  3. finds the runtime bundle;
  4. links the cached objects with the startup stub (`exe::link_executable`).
- **Output path.** The default output is `{project_root}/<entry-stem>` plus
  the platform's executable suffix. An `-o` path is used verbatim. An output
  path that is an existing directory is rejected with a diagnostic.

## 6. Project root resolution

`main.rs::resolve_target_from` derives the project root and the entry module
from the working directory and the CLI target (`00-cli-invocation.md`
§0.5.1):

| Target | Project root | Entry module |
|---|---|---|
| None | the working directory | `user` |
| Contains `/` | the target's parent directory, made absolute | the target's stem |
| An existing directory with no `<target>.cl` beside it | that directory | `user` |
| Otherwise | the working directory | the target |

- Only the third case triggers `Cranelisp.toml` scaffolding
  (`cranelisp-toml.md` §4).
- The cache directory is `{project_root}/.cranelisp-cache`, created eagerly.
  There is none under `--no-cache`.
- Library directories and platform directories are assembled as in
  `cranelisp-toml.md` §2.
- The prelude resolves from `{project_root}/prelude.cl` first, then from each
  library directory.
- No search walks up to parent directories.

## 7. Open conformance gaps

Each gap was read from source on 2026-09-25 and has no failing test. `qa` owns
attribution.

1. **Notification path.** `14-file-watching.md` §14.3 requires `<file>` to be
   relative to the project root. The source prints the bare file name, which
   differs for any file below the root.
   - Falsifier: edit a watched `lib/m.cl` and observe `[updated: m.cl]`.
2. **Qualified-only dependents are not reloaded.** The dependent set reads
   imports, re-exports and the prelude bit only. A module that reaches the
   changed module only through a qualified reference is not reloaded, although
   §14 requires dependents to be recompiled.
   - This is a third enumeration of module edges, beside the cache record and
     the restore walk (`int.md` §7.6). Whether a stale dependent is observable
     after GOT indirection is unmeasured.
   - Falsifier: `a` calls `b/f` without importing `b`, then `b` changes
     `f`'s arity. Observe whether `a` is re-typechecked.
