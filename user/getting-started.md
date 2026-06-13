# Getting started

> **Stub.** This page covers the essentials — building the binary, opening the
> REPL, and where to find runnable programs. The progressive tutorial lives under
> `user/tutorial/` (not yet authored). For the full command line see
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

Runnable programs define a zero-argument `main` that returns an `IO` action, and run
under `--run`:

```
cranelisp myprogram --run
```

The clearest worked introductions live in [`examples/`](../examples/) — start with
`examples/21-hello-io.cl`, which walks through the IO model step by step, and work
through the numbered sequence. Each example is a self-contained `.cl` file you can
run directly:

```
cranelisp examples/21-hello-io --run
```

## Where to go next

- [`cli-reference.md`](cli-reference.md) — every command-line mode and option, and
  how the entry-module target is resolved.
- [`repl/spec.md`](../repl/spec.md) — the normative REPL experience: display
  formats, slash commands, errors, caching.
- [`spec/`](../spec/) — the language specification.
- [`examples/`](../examples/) — the learning-sequence programs.
