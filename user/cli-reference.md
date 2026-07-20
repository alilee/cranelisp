# Command-line reference

The `cranelisp` binary has one job: take an entry module and either run it, link
it into a standalone executable, or open an interactive REPL on it. This page is
the practical reference for the command line. The normative contract lives in
[`repl/spec.md §0`](../repl/spec.md) — this page re-presents it for everyday use.

## Synopsis

```
cranelisp [target] [--run | --link [-o <path>]] [--no-color] [--no-cache] [--priority-workers N] [--nice-workers N] [--agent | --no-agent] [--yes]
```

- `[target]` is an optional positional argument naming the entry module / project
  root. With no target, the REPL opens on the `user` module in the current
  directory. See [Choosing what to compile](#choosing-what-to-compile-the-target).
- The mode flags `--run` and `--link` are **mutually exclusive** — passing both is
  an error.
- With no mode flag, `cranelisp` starts the **REPL**.
- The target may appear before or after the flags: `cranelisp app --run` and
  `cranelisp --run app` are equivalent.

> **Note:** there is no working `--help` or `--version` yet. Passing them today
> reports `unknown flag` and prints the usage line. They are specified as Future
> in [`repl/spec.md §0.4`](../repl/spec.md).

## Modes

The three modes are mutually exclusive. Exactly one is selected per invocation.

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
specified in [`repl/spec.md`](../repl/spec.md); the slash-command catalogue is in
[`repl/spec.md §3`](../repl/spec.md).

#### Finding a function before importing it — `/search`

`/list` and `/imports` show what is already in scope. `/search` answers the other
question — *"is there already a function that does this, somewhere I could import
from?"* — by searching every module reachable on the lib search path **and** the
project root that you have **not yet imported**.

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
[`repl/spec.md §17.19`](../repl/spec.md).

**Artifact:** none on disk beyond the regenerated entry-module source file; the
session is interactive.

### Run (`--run`)

`cranelisp [target] --run`

Compiles the module graph rooted at the entry module, then calls the entry module's
zero-argument `main` function and exits. The binary prints nothing itself — all
output comes from IO effects inside your program.

- `main` must be defined in the entry module and must be an `IO` action; a non-`IO`
  `main` is rejected before execution.
- **Exit code:** if `main`'s result (after unwrapping `IO`) is an `Int`, that value
  becomes the process exit code; any other result yields exit code `0`. A
  compilation error prints to stderr and exits non-zero.

**Artifact:** none — the program runs and the process exits with the program's code.

### Link (`--link`)

`cranelisp [target] --link [-o <path>]`

Compiles the module graph and produces a **standalone executable** from the object
output. It does not execute any code and writes nothing to stdout (beyond a
`; Linking: …` progress line). Linux/aarch64 ELF standalone executables are
supported.

#### Where the executable is written

By default the executable is named after the **entry module's source-file stem** and
written **beside that source file** — not into the current directory, and not after
the project-directory name. One rule covers both target shapes:

- **File target** — `cranelisp examples/hello.cl --link` (or bare `cranelisp mymod
  --link`, which resolves to `mymod.cl`) writes `examples/hello` (respectively
  `mymod`), beside the source.
- **Directory-project target** — `cranelisp myproject --link` (where `myproject/`
  exists with no `myproject.cl` beside it, so the entry module is `user`) writes
  `myproject/user`, beside `myproject/user.cl`. **Not** `myproject/myproject`, and
  **not** `./user`.

On a platform with an executable suffix (Windows) the suffix is added:
`examples/hello.exe`, `myproject/user.exe`.

Because the artifact lands next to its source rather than in the current directory,
the common `entry.cl` + `entry/`-submodule layout links cleanly: `cranelisp app
--link` writes `app` beside `app.cl`, never colliding with the `app/` submodule
directory in the current directory.

#### Choosing the output path — `-o <path>`

Pass `-o <path>` to set the output path explicitly, overriding the derivation above
(the standard `cc -o` / `rustc -o` escape hatch). The resolved path is used verbatim;
a relative path is resolved against the current directory.

```
cranelisp myproject --link -o build/myapp
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
[`repl/spec.md §0.2.1.1`](../repl/spec.md).

**Artifact:** a linked standalone executable, named after the entry module's source
stem and written beside that source (or at the `-o` path).

## Options

All options are boolean modifiers or take a single numeric argument; none change
which mode is selected except `--run` / `--link` above.

| Option | Effect | Default |
|---|---|---|
| `--no-color` | Disable ANSI colour in REPL / diagnostic output. | colour on |
| `--no-cache` | Bypass the on-disk module cache (recompile from source). **Error if combined with `--link`.** | cache on |
| `--priority-workers N` | Number of priority compilation workers. `N` must be numeric (non-numeric is an error). | `1` |
| `--nice-workers N` | Number of background ("nice") compilation workers. `N` must be numeric. | `1` |
| `--agent` | Enable the embedded LLM agent for the session (REPL only). Opt-in-twice: it only takes effect on a binary **built** with the agent feature *and* with a provider key configured at runtime — otherwise the agent stays dormant. Always accepted (a no-op, never `unknown flag`) on default builds and in `--run`/`--link`. See [`repl/spec.md §0.6.1`](../repl/spec.md). | agent off |
| `--no-agent` | Force the embedded agent off for the session, even on an agent build with a key present. Wins when both `--agent` and `--no-agent` are given. Always accepted. | — |
| `--yes` (short: `-y`) | Autonomous-submit: auto-accept the agent's write-consent `[y/N]` gates, so an active agent submits code and edits docs without per-action confirmation. Consent only — the agent's pre-flight validator still checks every submission. It does not itself enable the agent (pair it with `--agent`), and it is a no-op whenever no agent is active. See [`repl/spec.md §0.6.2`](../repl/spec.md). | off |

Notes:

- `--no-cache` with `--link` is rejected — link mode relies on the object cache, so
  the two cannot be combined.
- An unknown flag, or a second positional argument, prints an error plus the usage
  line and exits with status `1`.
- The three agent flags are REPL-session knobs: in `--run`/`--link` they are
  accepted and do nothing. The embedded agent experience itself is specified in
  [`repl/spec.md §17`](../repl/spec.md).

## Choosing what to compile (the target)

The optional `[target]` resolves to a `(project root, entry module)` pair. The
project root is the directory containing the entry file (per
[`spec/08-modules.md §8.11`](../spec/08-modules.md)); the entry module is the module
the binary runs, links, or opens the REPL on. A trailing `.cl` is always optional and
stripped — `cranelisp app` and `cranelisp app.cl` are equivalent.

Resolution applies these rules in order:

1. **No target** → project root is the current directory, entry module is `user`.
   This is what plain `cranelisp` does.
2. **Target contains a `/`** → the directory part is the project root and the final
   component is the entry module. `cranelisp dir/app` runs `app` with project root
   `dir/`. Use `./app` to force "the `app` module in the current directory" rather
   than letting rule 3 or 4 decide.
3. **Target is an existing directory** (no `/`, and there is *no* same-named
   `<target>.cl` file beside it) → that directory is the project root and the entry
   module is `user`. `cranelisp myproject` (where `myproject/` exists and there is no
   `myproject.cl`) opens `myproject/user.cl`.
4. **Bare name** → project root is the current directory and the entry module is the
   name. `cranelisp app` opens `./app.cl`.

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
[`repl/spec.md §0.5`](../repl/spec.md).

## Where Cranelisp looks for libraries (`Cranelisp.toml`)

When a program imports a module — the prelude, the standard library, or one of your
own shared modules — the binary resolves the name against a **lib search path**.
Understanding how that path is built matters as soon as you reach for `stdlib/`.

### The search path is additive — sources only ever *add*

The resolved lib-directory set is the **union** of every source below; no source
replaces or suppresses another. A directory listed anywhere is searched.

1. A directory passed programmatically / via a CLI lib-dir flag.
2. The `CRANELISP_LIB` environment variable — a colon-separated list of directories.
3. A `Cranelisp.toml` `lib-dirs` entry in the project root.
4. The default `{project-root}/stdlib/`, if that directory exists.

When the same module name resolves in more than one of these, the **first match
wins**, in the order above (command line → `CRANELISP_LIB` → `Cranelisp.toml` →
`{project-root}/stdlib/` last). Note `CRANELISP_LIB` is searched **before**
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

- **REPL only.** `--run` and `--link` never write a config file — a batch compile
  must not mutate your project tree. The scaffold fires only when you open the REPL.
- **Project-root directory only.** Plain `cranelisp` (no target) and bare-module
  targets (`cranelisp app`) do **not** scaffold — otherwise every launch would litter
  the current directory. Only the explicit "treat this directory as a project"
  gesture triggers it.
- **Never overwrites.** If a `Cranelisp.toml` already exists, the REPL leaves it
  byte-for-byte untouched and prints no notice — a second launch is a silent no-op.
  If the directory is read-only, the REPL warns to stderr and starts normally; the
  config is a convenience, never a requirement.

The trigger, mode, notice, and safety guarantees are specified in
[`repl/spec.md §0.5.7`](../repl/spec.md).

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
[`repl/spec.md §0.7`](../repl/spec.md) (Execution Environment Variables); the rows
above re-present that contract for everyday use.

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

The three modes compose freely; quarantine + scrub + parity together is the strongest
configuration. These are debugging aids, not a language feature — their design home is
`design/intrinsics/diagnostic-modes.md`.

## Cross-links

- **REPL experience** — display formats, prompts, exit conditions, and the CLI
  modes normatively: [`repl/spec.md §0`](../repl/spec.md). Slash commands:
  [`repl/spec.md §3`](../repl/spec.md).
- **Language** — semantics, types, special forms: [`spec/`](../spec/).
- **Project layout / modules** — project root, entry file, submodule directories:
  [`spec/08-modules.md §8.11`](../spec/08-modules.md).
