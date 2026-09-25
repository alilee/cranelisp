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
- **Reload.** `reload_module` discards the module's typecheck products,
  re-parses and re-registers it, then waits for in-memory completion.
  Displaced code enters the retention pool (`session-transaction.md`).

### 1.3 Failed reload

A failed reload adds the module to the session's error set. There is no
last-known-good restore and no module lock.

- While the set is non-empty, an expression turn is refused with `Cannot
  evaluate: module '<name>' has errors. Fix the source file and save.`
- A definition turn is still admitted, because it can be the repair
  (`15-session-persistence.md` §15.2.3).
- A later successful reload clears the module's error and failed-form state.

### 1.4 Notification

Each reloaded module prints one dim metadata line: `[updated: <file>]`, or
`[errors: <file>]` followed by the indented error. `<file>` is the file's bare
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
  in the error set, because `/reset` is not a repair (§15.2.3).

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
target itself is always compiled fresh. `/reset` loads nothing (§2).

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
