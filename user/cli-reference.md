# Command-line reference

The `cranelisp` binary has one job: take an entry module and either run it, run
its tests, link it into a standalone executable, or open an interactive REPL on
it. This page is
the practical reference for the command line. The normative contract lives in
[`repl/spec/00-cli-invocation.md` §0](../repl/spec/00-cli-invocation.md) — this
page re-presents it for everyday use.

## Synopsis

```
cranelisp [--run | --test | --link] [-o <path> | --output <path>] [--no-color] [--no-cache] [--priority-workers N] [--nice-workers N] [--no-agent] [target]
```

This synopsis shows the default build’s options before the target. An agent-capable build prints
`[--agent | --no-agent] [--yes]` in place of `[--no-agent]`.

- `[target]` is an optional positional argument naming the entry module / project
  root. With no target, the REPL opens on the `user` module in the current
  directory. See [Choosing what to compile](#choosing-what-to-compile-the-target).
- The mode flags `--run`, `--test` and `--link` are **mutually exclusive** —
  passing more than one is an error.
- With no mode flag, `cranelisp` starts the **REPL**.
- The target may appear before, after or between options: `cranelisp app --run` and
  `cranelisp --run app` are equivalent. Keep an option’s value immediately after
  that option, as in `--priority-workers 4`.
- `-o <path>` (long form `--output <path>`) is accepted only together with `--link`; with any other mode it is
  an error.
- An agent-capable build additionally accepts `--agent` and `--yes` (or `-y`).
  A binary built without that feature rejects both flags and does not advertise
  them in its usage line.

> **Note:** there is no working `--help` or `--version` yet. Passing them today
> reports `unknown flag` and prints the usage line. They are specified as Future
> in [`repl/spec/00-cli-invocation.md` §0.4](../repl/spec/00-cli-invocation.md).

## Modes

The four modes are mutually exclusive. Exactly one is selected per invocation.

### REPL (default — no mode flag)

`cranelisp [target]`

Opens the interactive read-eval-print loop on the resolved entry module. The REPL
loads the prelude, prints a banner, and presents a prompt. Definitions you enter
are type-checked, evaluated, and persisted back to the entry module's source file.
If the entry source file does not exist, the REPL creates an empty one and proceeds
— so `cranelisp` in an empty directory is a valid way to start a new project.

The REPL is self-documenting: every symbol and expression you enter responds with
its type and value in `:Type value` notation, and slash commands (`/sig`, `/doc`,
`/list`, `/run-tests`, …) introspect the session. The full REPL experience —
display formats, commands, error presentation, cache and file-watch behaviour — is
specified in the [REPL specification](../repl/spec/index.md); the slash-command
catalogue is
[`repl/spec/03-slash-commands.md` §3](../repl/spec/03-slash-commands.md).

#### Recall language syntax — `/syntax`

Run bare `/syntax` to list the available core-language topics, then
`/syntax <topic>` for a compact form-and-example reference. An unknown topic
prints the topic list again rather than leaving you at a dead end. The command
is a static REPL asset: it works without an agent and in a feature-off binary.

#### Finding a function before importing it — `/search`

`/list` and `/imports` show what is already in scope. `/search` answers the other
question — *"is there already a function that does this, somewhere I could import
from?"* — by searching public symbols reachable on the lib search path and the
project root. An exact query can also show an eligible public callable already in
scope.

Search results are public, non-macro callable symbols. Macro declarations are
intentionally outside this index. Source indexing does not expand macros, so it
can omit ordinary definitions that require expansion; a successfully loaded
module or cache entry can contribute eligible ordinary definitions. Importing a
module remains the authority for its complete contents.

Search by **name** or by **type signature**, exact or partial:

```
user> /search filter
:(Fn [(Fn [a] primitives/Bool) (seq.lazy/Seq a)] (seq.lazy/Seq a)) seq-filter
  in seq.lazy   — (import [seq.lazy [seq-filter]])

user> /search (Fn [Int Int] Int)
```

- **By name** — exact, or a case-insensitive substring (`/search grid` finds
  `grid-get`, `grid-set`, `make-grid`).
- **By signature** — a type shape, matched up to renaming of type variables;
  partial match means the shape appears *anywhere* inside a candidate's type (so
  `/search (Vec Int)` matches a function taking a `(Vec Int)`, and `/search Int`
  matches any signature mentioning `Int`).

Each result row gives you everything you need to decide and act: the symbol name,
its full `:Type` signature, the **module it comes from**, and — the payoff — the
exact **`(import …)` form to copy-paste** to bring it into scope. The workflow is:
search, see the import line, paste it.

If nothing matches you get a plain `no importable symbols matched '<query>'` note,
never an error. The library index builds in the background, so a `/search` issued
the moment the REPL starts may report partial results with an `indexing N modules…`
note — repeat the search a moment later for the fuller set. The full contract is in
[`repl/spec/17a-agent-language-awareness.md` §17.19](../repl/spec/17a-agent-language-awareness.md).

**Artifact:** none on disk beyond the regenerated entry-module source file; the
session is interactive.

### Run (`--run`)

`cranelisp --run [target]`

Compiles the module graph rooted at the entry module, then calls the entry module's
zero-argument `main` function and exits. The binary prints nothing itself — all
output comes from IO effects inside your program.

- `main` must be defined in the entry module as a zero-argument function
  returning `IO _`; any other `main` is rejected before execution. `--link`
  applies the same check.
- **Exit code:** if `main`'s result (after unwrapping `IO`) is an `Int`, that value
  becomes the process exit code; any other result yields exit code `0`. A
  compilation error prints to stderr and exits non-zero. The **linked executable
  applies the identical rule** — see [Link](#link---link).
- A program that references `discover-tests` is refused before it runs; see
  [Test discovery is REPL-only](#test-discovery-is-repl-only).

**Artifact:** none — the program runs and the process exits with the program's code.

### Test (`--test`)

`cranelisp --test [target]`

Compiles the module graph exactly as `--run` does, then finds and runs your
tests and exits. It does **not** call `main`, and the entry module does not
need one.

A test is a zero-argument function whose name starts with `test-` and whose type
is exactly `(Fn [] (Option String))`: it returns `None` when it passes and
`(Some reason)` when it fails.

```clojure
(defn test-add [] :(Option String)
  (if (= (+ 2 2) 4) None (Some "2 + 2 should be 4")))
```

A `test-` function with any other type is not run; you get a warning on stderr
naming it, so a mistyped test cannot pass silently. The convention is
[`repl/spec/16-test-discovery.md` §16.1](../repl/spec/16-test-discovery.md#161-test-function-convention).

`--test` uses the same runner as the REPL's `/run-tests` and `/run-all-tests`,
so the report looks the same in all three. Only which modules are searched and
what happens afterwards differ. The report goes to stdout, one line per test by
fully-qualified name, then a summary:

```
  user/test-add ........................... ok
  user/test-div-zero ...................... FAILED: expected error

1 passed, 1 failed in 2.34ms
```

A test that fails does not stop the run. A test that hits a runtime error, such
as division by zero, is reported as `PANIC: <message>`, counts as failed, and
the remaining tests still run. If there are no tests, the report is
`No tests found`. The runner is specified in
[`repl/spec/16-test-discovery.md` §16.2](../repl/spec/16-test-discovery.md#162-running-tests).

#### Which modules are searched

`--test` follows your program's imports outward from the entry module. It runs
the tests of the entry module and of every **project module** it reaches:

- modules you `import` or `export` with a names list, such as
  `(import [app.math [square]])`;
- submodules you declare with `(mod …)` or `(mod- …)`, even if you do not also
  import them; and
- the prelude, if it is a project module.

It does not follow a null import, an alias-only import, or a fully-qualified
reference that loads a module on first use. It also stops at **library
modules** — modules found through the lib search path, including the default
`{project-root}/stdlib/`. A library module's tests are not run, and neither are
the tests of project modules reachable only through it. Test files are never
found by scanning the disk: a module your program does not reach is not tested.
The exact rules are in
[`repl/spec/00-cli-invocation.md` §0.2.2](../repl/spec/00-cli-invocation.md#022-test-mode---test-s122).

#### Exit code

- **`0`** when no test failed or panicked, including when no test was found.
- **`1`** when any test failed or panicked.
- A compilation error, including a missing entry file, prints to stderr and exits
  non-zero; no test runs and no report is printed.

`-o`/`--output` is rejected with `--test`; the other options behave as they do
for `--run`.

**Artifact:** none.

#### Test discovery is REPL-only

The `discover-tests` builtin, which lets a program find and run its own tests,
is available only in the REPL. `--run`, `--test` and `--link` all refuse a
program in which any compiled function references it, even a function that is
never called, before anything runs or is written. The error names
`discover-tests` and a function that references it, and points you to the REPL,
or to `--test` to have the compiler run your tests. Importing the name without
using it is not refused. See
[`repl/spec/16-test-discovery.md` §16.6](../repl/spec/16-test-discovery.md#166-availability-by-invocation-mode-s122).

### Link (`--link`)

`cranelisp --link [-o <path> | --output <path>] [target]`

Compiles the module graph and produces a **standalone executable** from the object
output. It does not execute any code and writes nothing to stdout (beyond a
`; Linking: …` progress line). Standalone executables can be produced on aarch64
Linux and aarch64 macOS hosts; on any other host `--link` reports that
executable generation is unsupported.

A program that references `discover-tests` is refused before the system linker
runs; see [Test discovery is REPL-only](#test-discovery-is-repl-only).

#### Where the executable is written

By default the executable is named after the **entry module's source-file stem** and
written **beside that source file** — not into the current directory, and not after
the project-directory name. One rule covers both target shapes:

- **File target** — `cranelisp --link demo/hello.cl` (or bare `cranelisp --link
  mymod`, which resolves to `mymod.cl`) writes `demo/hello` (respectively
  `mymod`), beside the source.
- **Directory-project target** — `cranelisp --link myproject` (where `myproject/`
  exists with no `myproject.cl` beside it, so the entry module is `user`) writes
  `myproject/user`, beside `myproject/user.cl` — not `myproject/myproject`, and
  not a `user` file in the current directory.

Because the artifact lands next to its source rather than in the current directory,
the common `entry.cl` + `entry/`-submodule layout links cleanly: `cranelisp --link
app` writes `app` beside `app.cl`, never colliding with the `app/` submodule
directory in the current directory.

#### Choosing the output path — `-o <path>` / `--output <path>`

Pass `-o <path>` (or its long form `--output <path>`) to set the output path explicitly, overriding the derivation above
(the standard `cc -o` / `rustc -o` escape hatch). The resolved path is used verbatim;
a relative path is resolved against the current directory.

```
cranelisp --link -o build/myapp myproject
```

#### Output-path collision with a directory

If the resolved output path is an **existing directory**, `cranelisp` emits a clear
diagnostic naming the path and telling you to pass `-o`, rather than surfacing a raw
linker error:

```
error: output path 'user' is a directory — use -o <path> to choose a different output
```

This is the case you hit if, for example, an entry module named `user` would write
its executable next to a sibling `user/` directory. Choose a different path with
`-o`.

The output-artifact name, location, the `-o` override, and the collision-diagnostic
floor are normatively specified in
[`repl/spec/00-cli-invocation.md` §0.2.1.1](../repl/spec/00-cli-invocation.md).

**Artifact:** a linked standalone executable, named after the entry module's source
stem and written beside that source (or at the `-o` path).

#### Exit code of the linked executable

Running the produced executable applies exactly the same rule as `--run`: an `Int`
result becomes the process exit code, **any other result exits `0`**. A program
whose `main` yields, say, a `String` exits `0` under both.

## Options

These options do not select a mode. They are boolean modifiers or take a single
numeric argument.

| Option | Effect | Default |
|---|---|---|
| `--no-color` | Disable ANSI colour in REPL / diagnostic output. | colour on |
| `--no-cache` | Bypass the on-disk module cache (recompile from source). **Error if combined with `--link`.** | cache on |
| `--priority-workers N` | Number of priority compilation workers. `N` must be numeric (non-numeric is an error). | `1` |
| `--nice-workers N` | Number of background ("nice") compilation workers. `N` must be numeric. | `1` |
| `--agent` | On an agent-capable binary, request the embedded agent for a REPL session. It still needs a configured provider at runtime; in `--run`, `--test` or `--link` it is accepted but has no effect. A feature-off binary rejects this flag. See [`repl/spec/00-cli-invocation.md` §0.6.1](../repl/spec/00-cli-invocation.md). | agent off |
| `--no-agent` | Force the embedded agent off; it wins when paired with `--agent`. It is accepted in both build variants and is a no-op in a feature-off binary. | — |
| `--yes` (short: `-y`) | On an agent-capable binary, auto-answer the agent's write-consent prompts. It does not enable the agent and is inactive in `--run`, `--test` and `--link`; a feature-off binary rejects it. See [`repl/spec/00-cli-invocation.md` §0.6.2](../repl/spec/00-cli-invocation.md). | off |

Notes:

- `--no-cache` with `--link` is rejected — link mode relies on the object cache, so
  the two cannot be combined.
- An unknown flag, or a second positional argument, prints an error plus the usage
  line and exits with status `1`.
- On an agent-capable build, the agent flags are REPL-session knobs: in
  `--run`, `--test` and `--link` they are accepted and do nothing. The embedded agent experience
  itself is specified in
  [`repl/spec/17-embedded-agent.md` §17](../repl/spec/17-embedded-agent.md).

## Choosing what to compile (the target)

The optional `[target]` resolves to a `(project root, entry module)` pair. The
project root is the directory containing the entry file (per
[`spec/08-modules.md §8.11`](../spec/08-modules.md)); the entry module is the module
the binary runs, tests, links, or opens the REPL on. A trailing `.cl` is always optional and
stripped — `cranelisp app` and `cranelisp app.cl` are equivalent.

Resolution applies these rules in order:

1. **No target** → project root is the current directory, entry module is `user`.
   This is what plain `cranelisp` does.
2. **Target contains a `/`** → the directory part is the project root and the final
   component is the entry module. `cranelisp dir/app` runs the `app` module with
   project root `dir/`. Prefix a bare name with `./` to force "this module in the
   current directory" rather than letting rule 3 or 4 decide.
3. **Target is an existing directory** (no `/`, and there is *no* same-named
   `<target>.cl` file beside it) → that directory is the project root and the entry
   module is `user`. `cranelisp myproject` (where `myproject/` exists and there is no
   `myproject.cl`) opens `myproject/user.cl`.
4. **Bare name** → project root is the current directory and the entry module is the
   name. `cranelisp app` opens `app.cl` in the current directory.

### Worked example: a `.cl` file vs a same-named directory

A project's entry file can declare submodules with `(mod child)`, which live in a
sibling directory named after the entry file. So it is normal for both `app.cl` and
`app/` to exist side by side:

```
app.cl          ; the entry module — contains (mod child) and (defn main ...)
app/
  child.cl      ; the `child` submodule, referenced as child/...
```

When both `app.cl` and `app/` exist, the **file wins**: `cranelisp app` (and
`cranelisp app.cl`) resolves the entry to `app.cl`, with the project root being the
current directory and `app/` holding the submodules. Rule 3 (directory-as-project)
only fires when there is a directory and *no* same-named `.cl` file beside it. This
is why a project whose entry declares submodules still compiles with a bare
`cranelisp app`.

The full resolution rules, the directory-component detection edge cases, and the
ambiguity/error handling are normatively specified in
[`repl/spec/00-cli-invocation.md` §0.5](../repl/spec/00-cli-invocation.md).

## Where Cranelisp looks for libraries (`Cranelisp.toml`)

When a program imports a module — the prelude, the standard library, or one of your
own shared modules — the binary resolves the name against a **lib search path**.
Understanding how that path is built matters as soon as you reach for `stdlib/`.

### The search path is additive — sources only ever *add*

The resolved lib-directory set is the **union** of every source below; no source
replaces or suppresses another. A directory listed anywhere is searched.

1. The `CRANELISP_LIB` environment variable — a colon-separated list of directories.
2. A `Cranelisp.toml` `lib-dirs` entry in the project root.
3. The default `{project-root}/stdlib/`, if that directory exists.

The `cranelisp` command line has no lib-directory flag; set `CRANELISP_LIB` or
`Cranelisp.toml` instead.

When the same module name resolves in more than one of these, the **first match
wins**, in the order above (`CRANELISP_LIB` → `Cranelisp.toml` →
`{project-root}/stdlib/` last). `CRANELISP_LIB` is searched **before**
`Cranelisp.toml` — environment over config file, matching Cargo's precedence.

The key consequence: **a `Cranelisp.toml` can only add paths, never turn one off.**
An absent file, an empty file, and `lib-dirs = []` all mean exactly the same thing —
they contribute nothing and suppress nothing. The normative rules are in
[`spec/08-modules.md §8.11.4`](../spec/08-modules.md) (lib dirs) and `§8.11.5`
(platform DLL dirs, which follow the same additive model under `platform-dirs`).

A minimal `Cranelisp.toml` looks like this:

```toml
# Paths are relative to this file, or absolute. Entries are ADDED to whatever
# CRANELISP_LIB and {project-root}/stdlib/ already contribute.
lib-dirs = ["../shared-lib"]
platform-dirs = ["target/debug"]
```

### The REPL scaffolds one for you

When you open the REPL **on a project-root directory** — `cranelisp myproject`
where `myproject/` exists and there is no `myproject.cl` beside it (resolution rule
3 above) — and that directory has no `Cranelisp.toml`, the REPL writes a commented
template there and tells you:

```
$ cranelisp myproject
[created Cranelisp.toml]
cranelisp REPL — type /help for help
0+0ms; user>
```

This is the `cargo new` / `git init` ergonomic: pointing the tool at a fresh project
directory leaves behind a discoverable config you can edit. The generated file is
**all comments** — it changes resolution by nothing until you uncomment a key — which
is safe precisely because the model is additive (there is no tier for an empty file
to accidentally switch off).

Three things to know about the scaffold:

- **REPL only.** `--run`, `--test` and `--link` never write a config file — a
  batch compile must not mutate your project tree. The scaffold fires only when you open the REPL.
- **Project-root directory only.** Plain `cranelisp` (no target) and bare-module
  targets (`cranelisp app`) do **not** scaffold — otherwise every launch would litter
  the current directory. Only the explicit "treat this directory as a project"
  gesture triggers it.
- **Never overwrites.** If a `Cranelisp.toml` already exists, the REPL leaves it
  byte-for-byte untouched and prints no notice — a second launch is a silent no-op.
  If the directory is read-only, the REPL warns to stderr and starts normally; the
  config is a convenience, never a requirement.

The trigger, mode, notice, and safety guarantees are specified in
[`repl/spec/00-cli-invocation.md` §0.5.7](../repl/spec/00-cli-invocation.md).

## Environment variables

A few environment variables tune behaviour outside the flag set. The path-related
ones (`CRANELISP_LIB`, `CRANELISP_PLATFORM_PATH`) are covered inline above and in
[`getting-started.md`](getting-started.md); this is their consolidated home.

| Variable | Effect |
|---|---|
| `CRANELISP_LIB` | Colon-separated list of extra lib directories, searched before `Cranelisp.toml` and `{project-root}/stdlib/`. See [the lib search path](#where-cranelisp-looks-for-libraries-cranelisptoml). |
| `CRANELISP_PLATFORM_PATH` | Directory to find the platform DLL when no checked-in symlink is present (e.g. `target/debug`). See [getting-started](getting-started.md). |
| `CRANELISP_SPARK_BUDGET=N` | Caps how much pure computation runs in parallel at once (see [automatic parallelism](getting-started.md#automatic-parallelism)). `0` disables auto-parallelism entirely (everything runs serially). Unset uses a sensible default scaled to the number of cores. |
| `CRANELISP_NO_LENIENT=1` | Also disables auto-parallelism, forcing strictly serial left-to-right evaluation. Useful for a serial baseline when measuring or for debugging. |

`CRANELISP_SPARK_BUDGET` and `CRANELISP_NO_LENIENT` are user-facing knobs over the
parallel evaluation described in
[`spec/12-runtime.md §12.4.3`](../spec/12-runtime.md) (lenient evaluation); because
that parallelism is semantically invisible, neither variable changes what a program
computes — only how it is scheduled. They apply identically in **REPL, `--run`, and
`--link`** modes, and each is read **once per process**. Their normative home — exact
effect, defaults, and scope — is
[`repl/spec/00-cli-invocation.md` §0.7](../repl/spec/00-cli-invocation.md)
(Execution Environment Variables); the rows above re-present that contract for
everyday use.

### Memory-safety diagnostics (developer tools)

Cranelisp manages memory automatically, so everyday programs never need these. When
you are chasing a suspected use-after-free, double-free, or leak — for example while
narrowing down a compiler or platform bug — a set of **env-gated allocator modes**
makes such faults deterministic. They are **all off by default**: with every variable
unset the runtime behaves exactly as normal (byte-for-byte identical output), and
they apply identically in **REPL, `--run`, and `--link`** modes. They add cost and
retain memory, so leave them off for normal use.

| Variable | Effect |
|---|---|
| `CRANELISP_QUARANTINE_FREED=1` | **No reuse after free.** Freed blocks are retained instead of returned to the allocator, so a stale pointer can never land on reused memory — any dangling access is caught at the point of use rather than silently succeeding. |
| `CRANELISP_QUARANTINE_MAX_BYTES=N` | Caps quarantine retention at `N` bytes (oldest freed blocks released first). Use for long-running sessions where unbounded retention would exhaust memory; unset = unbounded (the strongest signal, best for short repros). |
| `CRANELISP_SCRUB_FREED=1` | **Poison freed memory.** Overwrites each freed block with a sentinel pattern, so a use-after-free reads obvious garbage (or faults immediately) instead of stale-but-plausible data. Strongest combined with quarantine. |
| `CRANELISP_ALLOC_PARITY=1` | **Balance check.** At process exit, asserts the number of allocations equals the number of frees, reporting any imbalance — a double-free (more frees) or a leak (more allocations) that produces otherwise-correct output. |
| `CRANELISP_ALLOC_PARITY_DUMP=1` | Prints the current allocation/free ledger mid-run (print-and-continue) rather than only at exit. |
| `CRANELISP_RC_DEC_CHECK=1` | **Check at the seam.** Arms the reference-count/allocator seam checks — a decrement of an already-freed pointer, an underflowing release, an implausible block header — so the run stops at the offending operation with a located message instead of continuing on corrupt state. Some of these checks are always active in a debug build; this variable arms the full set, including in release and `--link` builds. |

The modes compose freely; quarantine + scrub + parity together is the strongest
configuration, and `CRANELISP_RC_DEC_CHECK=1` adds the point-of-fault report. These are debugging aids, not a language feature — their design home is
`design/intrinsics/diagnostic-modes.md`.

## Cross-links

- **REPL experience** — display formats, prompts and exit conditions: the
  [REPL specification](../repl/spec/index.md). CLI modes:
  [`repl/spec/00-cli-invocation.md` §0](../repl/spec/00-cli-invocation.md).
  Slash commands:
  [`repl/spec/03-slash-commands.md` §3](../repl/spec/03-slash-commands.md).
  Tests: [`repl/spec/16-test-discovery.md` §16](../repl/spec/16-test-discovery.md).
- **Language** — semantics, types, special forms: [`spec/`](../spec/).
- **Project layout / modules** — project root, entry file, submodule directories:
  [`spec/08-modules.md §8.11`](../spec/08-modules.md).
