# Getting started

> **Stub.** This page covers the essentials — building the binary, opening the
> REPL, running your first program, and where to find the showcase. The
> progressive tutorial lives under `user/tutorial/` (not yet authored — see
> [Where to go next](#where-to-go-next)). For the full command line see
> [`cli-reference.md`](cli-reference.md).

## Build the binary

Cranelisp builds with Cargo from the workspace root:

```
cargo build
```

This produces `target/debug/cranelisp`. (A release build — `cargo build --release`
— produces `target/release/cranelisp`.)

## Start the REPL

Run the binary with no arguments to open the interactive REPL in the current
directory:

```
$ cranelisp
cranelisp REPL — type /help for help
0+0ms; user> (+ 1 2)
:primitives/Int 3
```

Every result is printed in `:Type value` notation — here, the `Int` value `3` lives
in the `primitives` module. The prompt shows compile and eval timings and the
current module (`user`). Type `/help` to list the slash commands, `/quit` (or
Ctrl-D) to exit. The full REPL experience is specified in
[`repl/spec.md`](../repl/spec.md).

## Your first program

A runnable program defines a zero-argument `main` and runs under `--run`. The
clearest worked introductions live in [`examples/`](../examples/) — a numbered
learning sequence of self-contained `.cl` files you can run directly.

### A pure program (runs everywhere)

Start with [`examples/01-integers.cl`](../examples/01-integers.cl). It defines a
few arithmetic functions and combines them in `main`:

```
cranelisp examples/01-integers --run
```

It prints nothing — a program's only output comes from IO effects, and this one is
pure. Its `main` returns an `Int`, which becomes the **process exit code**
(`01-integers` computes `69`, so the process exits with code `69`). You can confirm
it ran cleanly by inspecting the exit code:

```
$ cranelisp examples/01-integers --run
$ echo $?
69
```

A pure example like this needs nothing beyond the binary — no platform DLL, no
environment — so it is the safest place to confirm your build works on any host.

### A program that does IO

To actually print, a program performs IO. Start with
[`examples/21-hello-io.cl`](../examples/21-hello-io.cl), which walks through the IO
model step by step:

```
$ cranelisp examples/21-hello-io --run
Hello, world!
Hello,
world!
Computing...
Cranelisp
```

IO requires a **platform** — a small native library that provides the host's
side-effecting operations (here, `print`). The `examples/` directory ships a
checked-in platform symlink for the common hosts (`stdio.so` on Linux, `stdio.dylib`
on macOS) pointing at the `libcranelisp_stdio` library Cargo builds, so the example
runs with **no environment variable** on those hosts.

On a host with no checked-in symlink, point the binary at the built library with
`CRANELISP_PLATFORM_PATH`:

```
CRANELISP_PLATFORM_PATH=target/debug cranelisp examples/21-hello-io --run
```

If the platform cannot be found you will see `platform 'stdio' not found` — that
means the DLL was not on the search path, not that your program is wrong.

## Platforms and IO

Cranelisp makes side effects visible in the type system. A function that performs
IO returns `(IO a)` rather than plain `a`, so the compiler can tell pure code from
effectful code — pure functions cannot accidentally perform IO. A program's `main`
returns an `IO` action, and the runtime *forces* that action to run the effects and
extract the result.

A **platform** is a native library that supplies the host operations an `IO` action
ultimately calls — `print`, `read-line`, and so on. Different platforms provide
different capabilities (a CLI `stdio` platform, a web platform, and so on), which is
why an IO program names the platform it needs and the runtime loads the matching DLL.

Independent IO actions run **in parallel automatically** (auto-IO): when the
compiler can see that two effects do not depend on one another, it schedules them
concurrently — you write straight-line effectful code and get the parallelism for
free, without threads or futures in the source. See
[`examples/28-parallel.cl`](../examples/28-parallel.cl) and
[`examples/30-parallel-map-reduce.cl`](../examples/30-parallel-map-reduce.cl) for
worked cases. The IO model and the effect/parallelism semantics are specified
normatively in [`spec/`](../spec/).

## Where to go next

- **The showcase — Sudoku solver.** The [`exemplar/`](../exemplar/) project is the
  headline program: it parses a puzzle, solves it, and renders the solution as both
  ASCII and HTML, exercising ADTs, traits, modules, and IO together. It needs the
  standard library and a platform on the search path:

  ```
  CRANELISP_LIB=stdlib CRANELISP_PLATFORM_PATH=target/debug \
    cranelisp exemplar/user.cl --run
  ```

- [`examples/`](../examples/) — the numbered learning sequence, from
  `01-integers` through `30-parallel-map-reduce`. Work through it in order.
- [`cli-reference.md`](cli-reference.md) — every command-line mode and option, how
  the entry-module target is resolved, how the lib search path / `Cranelisp.toml`
  works, and the `/search` command for finding an importable function.
- **Guide** — feature-by-feature pages: [`guide/bitwise.md`](guide/bitwise.md)
  (bit-level arithmetic and the `num.bits` module),
  [`guide/field-accessors.md`](guide/field-accessors.md) (`Type.field` accessors and
  the bare-name alias).
- [`repl/spec.md`](../repl/spec.md) — the normative REPL experience: display
  formats, slash commands, errors, caching.
- [`spec/`](../spec/) — the language specification.
- **Progressive tutorial (forthcoming).** A guided `/learn` tutorial is planned: an
  in-REPL, step-by-step introduction that parallels the `examples/` sequence and
  will be published under `user/tutorial/`. It is not yet authored — until then, the
  numbered examples and the Sudoku showcase are the recommended learning path.
