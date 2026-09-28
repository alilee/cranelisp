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
- **Reload set.** The changed modules plus their transitive dependents,
  ordered by strongly connected component and then topologically. A dependent
  is a module that imports or re-exports a reached module, or that has its
  prelude fallback on when the prelude is reached.
- **Reload.** `reload_module` replaces the module's typecheck product with the
  file it re-read, keeping the backing path and recording that text for
  verbatim slices. It then re-parses and re-registers the module and waits for
  that module's own outcome (§1.3). Displaced code enters the retention pool
  (`session-transaction.md`). Regeneration writes to the recorded path
  (`session-persistence.md` §3.2), so a reload must not drop it.
- **Other callers.** `/mod` into a cache-installed module uses the same
  operation (`session-persistence.md` §2.4.5).

### 1.3 Failed reload

A failed reload adds the module to the session's error set. There is no
last-known-good restore and no module lock.

- While the set is non-empty, an expression turn is refused with `Cannot
  evaluate: module '<name>' has errors. Fix the source file and save.`
- A definition turn is still admitted, because it can be the repair
  (`15-session-persistence.md` §15.2.3).
- A later successful reload clears the module's error and failed-form state.

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

#### 1.3.1 Restart-required failure

A reload refused because it would change a live type's structure
(`14-file-watching.md` §14.8; the guard is
[session transaction §2.6](session-transaction.md#26-type-re-establishment-repl-185-148))
also retains the module's saved file until the failure ends.

- **Marker.** The session holds a crate-private map from each
  restart-required module to its refused type. It is session state and is
  never persisted.
- **Set.** `reload_module` sets it on its failure branch, when the reloaded
  module's scheduler refusal record names a type. It adds the module to the
  error set in the same step. Every reload caller is covered: the watcher,
  `/mod`'s cache-installed recompile and the superseded T1 residue.
  - The read is keyed by the reloaded module and follows that module's own
    `Failed` outcome (§1.3 Outcome), so it cannot precede the worker's record.
  - The returned error is the module's own refusal, so the notification
    names the type and the restart remedy (§14.8).
  - A read or parse failure returns before re-registration and reads nothing.
- **Stands.** A later failing reload of any cause leaves the marker, as do
  `/reset` (§2.1) and `/mod`.
- **Clears.** Only `reload_module`'s success branch clears it, beside the
  existing error-set and failed-form clears, including while another module
  stands `Failed` (§1.3 Outcome). Process exit also ends it.
- **Invariant.** A restart-required module is always in the error set. The
  set site maintains it, and `/reset` keeps such modules.
- **Turn admission.** `process_commands` rejects, inside its §14.4 gate, a
  definition or structural turn whose current module is restart-required.
  The session and the file are unchanged. The message names the module, the
  type and the restart remedy.
  - A turn in a module that is not restart-required keeps the admission
    rules above, even when another module is restart-required.
  - This one site covers typed REPL input and the agent's submit, which
    routes through it (`submit_clean_form`).
  - The agent's document edits bypass it, so `run_document_edit` makes the
    same refusal before asking for consent.
- **Write chokepoint.** `regenerate_backing_file` returns before reading or
  writing when the current module is restart-required. This covers every
  regeneration caller, including any that admission does not enumerate:
  `main.rs`, `agent/pull.rs` and the `redefine.rs` residue.
- **Why both.** Admission keeps the session unchanged; the chokepoint keeps
  the file intact whatever the caller.
- **Scope.** A failure of any other cause sets no marker. What the file must
  hold then is ACT-0998 face 2
  (`session-persistence.md` §2.4.4).
- **Imported modules.** A refusal in a non-entry module that another module
  imports fails after parsing, inside a worker. Its importer fails through
  the barrier's fail-fast on an already-failed member
  ([error cascade §4.1](step9-error-cascade.md#41-cascade-construction)), so
  the reload plan returns. The watcher prints its notifications only after
  the whole plan returns, so any wait that never ends withholds the §14.8
  diagnostic. The end-to-end guard is
  `tests/repl_persist.rs::watch_imported_type_field_reorder_fails_requiring_restart`.
  A `/mod` into a failed cache-installed module reaches the same barrier, so
  the fail-fast covers it by construction. No cell exercises that route.
- **Guards.** In `tests/repl_persist.rs`:
  - `persist_external_edit_changing_field_type_fails_requiring_restart`
    checks the refusal.
  - `persist_structural_reload_failure_keeps_saved_edit_until_restart`
    checks the retained file and the restart.
  - `persist_compatible_save_after_structural_reload_failure_releases_the_file`
    checks the clear.

  The marker's lifecycle unit is
  `restart_required_stands_until_a_successful_reload`, in
  `src/session_v4/persistence_tests.rs`.

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
  restart-required module (§1.3.1), whose failure stands until a successful
  reload or restart (§14.8).

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
