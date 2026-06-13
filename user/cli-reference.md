# Command-line reference

The `cranelisp` binary has one job: take an entry module and either run it, link
it into a standalone executable, or open an interactive REPL on it. This page is
the practical reference for the command line. The normative contract lives in
[`repl/spec.md §0`](../repl/spec.md) — this page re-presents it for everyday use.

## Synopsis

```
cranelisp [target] [--run | --link] [--no-color] [--no-cache] [--priority-workers N] [--nice-workers N]
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

`cranelisp [target] --link`

Compiles the module graph and produces a **standalone executable** from the object
output. It does not execute any code and writes nothing to stdout. Linux/aarch64
ELF standalone executables are supported.

**Artifact:** a linked standalone executable for the entry module.

## Options

All options are boolean modifiers or take a single numeric argument; none change
which mode is selected except `--run` / `--link` above.

| Option | Effect | Default |
|---|---|---|
| `--no-color` | Disable ANSI colour in REPL / diagnostic output. | colour on |
| `--no-cache` | Bypass the on-disk module cache (recompile from source). **Error if combined with `--link`.** | cache on |
| `--priority-workers N` | Number of priority compilation workers. `N` must be numeric (non-numeric is an error). | `1` |
| `--nice-workers N` | Number of background ("nice") compilation workers. `N` must be numeric. | `1` |

Notes:

- `--no-cache` with `--link` is rejected — link mode relies on the object cache, so
  the two cannot be combined.
- An unknown flag, or a second positional argument, prints an error plus the usage
  line and exits with status `1`.

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

## Cross-links

- **REPL experience** — display formats, prompts, exit conditions, and the CLI
  modes normatively: [`repl/spec.md §0`](../repl/spec.md). Slash commands:
  [`repl/spec.md §3`](../repl/spec.md).
- **Language** — semantics, types, special forms: [`spec/`](../spec/).
- **Project layout / modules** — project root, entry file, submodule directories:
  [`spec/08-modules.md §8.11`](../spec/08-modules.md).
