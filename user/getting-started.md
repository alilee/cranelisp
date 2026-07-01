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

## Automatic parallelism

Cranelisp parallelizes work for you — you never write threads, futures, or locks in
the source. It applies in two places:

- **Independent IO actions run concurrently.** When the compiler can see that two
  effects do not depend on one another, it schedules them at the same time. You write
  straight-line effectful code and the parallelism comes for free — even a server's
  per-connection handlers fan out with **no `spawn` in the source**. See
  [`examples/28-parallel.cl`](../examples/28-parallel.cl) and the
  [concurrency guide](guide/concurrency.md). The one honest scope: effects that share
  one resource are bounded by that resource's **capacity** — a ceiling the platform
  declares, not the program — so a connection pool of *N* admits up to *N*
  concurrently and the (N+1)th waits. Distinct resources overlap freely. The normative
  rule is [`spec/10-io.md §10.12.4.1`](../spec/10-io.md).
- **Independent pure computations run in parallel too.** The arguments of a call that
  do not depend on each other can be evaluated at the same time. So the two recursive
  branches of a divide-and-conquer function run at once. The standard library packages
  this for collections as **`par-map`, `par-reduce`, and `par-map-reduce`** (in the
  `collections.parallel` module) — ordinary functions that map/reduce element-wise in
  parallel and return exactly what their sequential twins do. See
  [`guide/parallel-collections.md`](guide/parallel-collections.md) for how to use them
  and [`examples/30-parallel-map-reduce.cl`](../examples/30-parallel-map-reduce.cl) for
  the worked divide-and-conquer case.

**When it pays off — and when it does not.** Parallelism is a performance property with
a known limit, not a blanket speedup. It is worth it when each piece of work is
**compute-bound and substantial** — roughly a microsecond or more of arithmetic-style
work per element gives real speedup (around 2–3× has been observed on the compute-bound
map-reduce example), and on that kind of work it is never meaningfully slower than
serial. For **allocation-heavy or reference-counting-heavy** work, though — code that
copies or builds large heap structures per element rather than crunching numbers — the
parallel run can currently be **slower** than serial, because independent branches
contend on the shared allocator and atomic reference counts. So the "never slower than
serial" floor holds unconditionally only for compute-bound work; for allocation-/RC-heavy
work, measure against a serial baseline (`CRANELISP_NO_LENIENT=1`) before relying on it.
You can cap or disable the parallelism with environment variables; see
[`cli-reference.md`](cli-reference.md#environment-variables). The floor, its scope, and
the known contention limit are documented in
[`design/arch/effect-concurrency.md §3.1`](../design/arch/effect-concurrency.md).

This is all semantically invisible: a parallel run computes exactly what a sequential
left-to-right run would. The effect and evaluation semantics are specified normatively
in [`spec/12-runtime.md §12.4.3`](../spec/12-runtime.md) (lenient evaluation) and the
[`spec/`](../spec/) IO model.

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
  the bare-name alias),
  [`guide/parallel-collections.md`](guide/parallel-collections.md) (`par-map`,
  `par-reduce`, `par-map-reduce`),
  [`guide/concurrency.md`](guide/concurrency.md) (the two-halves concurrency model:
  inferred fan-out + the `sleep`/`race`/`select`/`timeout` control combinators), and
  [`guide/writing-platforms.md`](guide/writing-platforms.md) (authoring a platform
  DLL: poll-shape effect leaves, the poll-in / wake-out reactor boundary, the
  handle model).
- [`repl/spec.md`](../repl/spec.md) — the normative REPL experience: display
  formats, slash commands, errors, caching.
- [`spec/`](../spec/) — the language specification.
- **Progressive tutorial (forthcoming).** A guided `/learn` tutorial is planned: an
  in-REPL, step-by-step introduction that parallels the `examples/` sequence and
  will be published under `user/tutorial/`. It is not yet authored — until then, the
  numbered examples and the Sudoku showcase are the recommended learning path.
