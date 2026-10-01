# Getting started

This page covers the essentials: building the binary, opening the REPL, running
your first program, platforms and automatic parallelism. [Where to go
next](#where-to-go-next) points to the learning sequence, the showcase and the
feature guides. For the full command line see [`cli-reference.md`](cli-reference.md).

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

One thing to know about `+` in that transcript: operators come from the standard
prelude, which is optional — in a bare directory with no `stdlib/` on the
[lib search path](cli-reference.md#where-cranelisp-looks-for-libraries-cranelisptoml),
the REPL starts with no prelude and `+` is not defined (fully-qualified
primitives such as `(primitives/add-i64 1 2)` always work). Run the REPL from
this repository's root, as above, and the prelude is found in `stdlib/`.

The REPL is a live development environment: redefine a function and the change
takes effect immediately — body edits are picked up by every caller on the next
call. A different type with a direct blocking dependent is rejected before it
replaces the old definition. The REPL also watches the module files it has
loaded, so saving a file in your editor recompiles it in the running session.
See the [live development guide](guide/live-development.md).

### A REPL session resumes prior state — a sharp edge for piped input

A REPL persists your definitions to a `user.cl` file in the working directory, and
a REPL started in a directory that already holds one **resumes** those definitions.
Everything you then type or **pipe in** is *session input*, evaluated against the
restored state — not a fresh, self-contained program. So `cranelisp < script.cl`
run in a directory carrying prior state will resolve any name the script does not
itself redefine to the **previous session's** binding; the same script piped into
an **empty** directory can give a different result. (Redefinitions always win — a
`(defn f …)` in the piped input takes effect over the stored one.)

If you want fresh-program semantics — a self-contained program with no resumed
state — use `cranelisp --run script.cl` (see the
[CLI reference](cli-reference.md)) or run the REPL in an empty directory. The
normative model is [`repl/spec.md §15.2.1`](../repl/spec.md).

## Your first program

A runnable program defines a zero-argument `main` and runs under `--run`. The
clearest worked introductions live in [`examples/`](../examples/) — a numbered
learning sequence of self-contained `.cl` files you can run directly.

### A pure program (runs everywhere)

Start with [`examples/01-integers.cl`](../examples/01-integers.cl). It defines a
few arithmetic functions and combines them in `main`:

```
cranelisp --run examples/01-integers
```

It prints nothing — a program's only output comes from IO effects, and this one
performs none. Every `main` returns an `IO` action; this one wraps its result in
`Pure`, which performs no effect. When that result is an `Int`, it becomes the
**process exit code** (`01-integers` computes `69`, so the process exits with
code `69`). You can confirm it ran cleanly by inspecting the exit code:

```
$ cranelisp --run examples/01-integers
$ echo $?
69
```

A `main` that returns a plain `Int` is rejected before anything runs, with
``main must return `IO _` ``.

An example like this needs nothing beyond the binary and the `examples/`
directory — no platform DLL, no environment — so it is the safest place to
confirm your build works on any host.

### A program that does IO

To actually print, a program performs IO. The smallest complete IO program is the
platform two-step plus a `main` that prints:

```clojure
;; hello.cl
(platform stdio)
(import [platform.stdio [*]])

(defn main [] (print "hello world"))
```

```
$ CRANELISP_PLATFORM_PATH=/path/to/cranelisp/target/debug cranelisp --run hello.cl
hello world
```

The worked IO examples [`examples/21-hello-io.cl`](../examples/21-hello-io.cl)
and [`examples/23-io-sequence.cl`](../examples/23-io-sequence.cl) are part of the
learning sequence and run with the platform setup above.

IO requires a **platform** — a small native library that provides the host's
side-effecting operations (here, `print`). The binary looks for platforms in a
`platforms/` directory under the project root and under each lib directory. The
learning sequence puts its own `lib/` on the lib search path, and
`examples/lib/platforms/` holds checked-in symlinks to the libraries Cargo builds
in `target/debug/`. Only Linux links (`stdio.so`, `test-capture.so`) are checked
in, so on Linux an entry module **inside `examples/`** finds the platform with
**no environment variable**, once `cargo build` has run.

On macOS, and for any program outside `examples/` — including the `hello.cl`
above, written in a directory of your own — point the binary at the directory
holding the built library with `CRANELISP_PLATFORM_PATH`:

```
CRANELISP_PLATFORM_PATH=/path/to/cranelisp/target/debug cranelisp --run hello.cl
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

Using a platform is **two steps** — and missing the second is the usual first
stumble:

```clojure
(platform stdio)                 ; step 1 — load the DLL, register the platform.stdio module
(import [platform.stdio [*]])    ; step 2 — bring print/read-line into scope

(defn main [] (print "hello world"))
```

`(platform stdio)` loads the library and registers a module named `platform.stdio`
(**singular `platform`**, not `platforms`), but it does **not** put `print` into
scope by itself — the `(import [platform.stdio [*]])` does. Without it, `(print …)`
fails with `undefined variable: print`. For the full walkthrough — the two steps, the
`platform.<name>` naming, and a troubleshooting checklist — see
[guide/using-platforms.md](guide/using-platforms.md).

At the REPL, an expression whose type is `IO` runs as soon as you enter it. The
REPL prints `Executing IO…`, then whatever the action outputs, then the value it
returns under that value's own type. Start the REPL with `CRANELISP_PLATFORM_PATH`
set as above so it can find the platform:

```
user> (platform stdio)
user> (import [platform.stdio [print]])
user> (print "hello")
Executing IO…
hello
:primitives/Int 0
```

An ordinary expression such as `(+ 1 2)` prints no notice. The presentation is
specified in [`repl/spec/01-display-format.md` §1.2.1](../repl/spec/01-display-format.md#121-io-expression-results).

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
the known contention limit are documented in the
[floor-scope section of the effect-concurrency design](../design/arch/effect-concurrency.md#31-floor-scope--contention-is-the-boundary-not-compute-s94-port-finding).

This is all semantically invisible: a parallel run computes exactly what a sequential
left-to-right run would. The effect and evaluation semantics are specified normatively
in [`spec/12-runtime.md §12.4.3`](../spec/12-runtime.md) (lenient evaluation) and the
[`spec/`](../spec/) IO model.

## Where to go next

- [`examples/`](../examples/) — the numbered learning sequence, starting at
  `01-integers`. Work through it in order.
- **The showcase — Sudoku solver.** The [`exemplar/`](../exemplar/) project is the
  headline program: it parses a puzzle, solves it, and renders the solution as both
  ASCII and HTML, exercising ADTs, traits, modules, and IO together. It needs the
  standard library and a platform on the search path:

  ```
  CRANELISP_LIB=stdlib CRANELISP_PLATFORM_PATH=target/debug \
    cranelisp --run exemplar/user.cl
  ```

- **Guide** — feature-by-feature pages:
  - [`guide/live-development.md`](guide/live-development.md) — redefining
    functions in a live session, editing module files while the REPL runs, and
    moving between modules with `/mod`.
  - [`guide/testing.md`](guide/testing.md) — writing tests and running them with
    `/run-tests` or `cranelisp --test`.
  - [`guide/functions.md`](guide/functions.md) — `fn` is single-arity; multi-arity
    `defn` and how its clauses infer like separate mutually-recursive functions.
  - [`guide/constructors.md`](guide/constructors.md) — `Type.Ctor` constructors, the
    bare-name alias, and disambiguating two types that share a constructor name, in
    value and pattern position.
  - [`guide/field-accessors.md`](guide/field-accessors.md) — `Type.field` accessors
    and the bare-name alias.
  - [`guide/traits.md`](guide/traits.md) — declaring and implementing traits,
    default methods, return-type dispatch, higher-kinded traits and importing
    trait methods.
  - [`guide/bitwise.md`](guide/bitwise.md) — bit-level arithmetic and the
    `num.bits` module.
  - [`guide/parallel-collections.md`](guide/parallel-collections.md) — `par-map`,
    `par-reduce`, `par-map-reduce`.
  - [`guide/concurrency.md`](guide/concurrency.md) — the two-halves concurrency
    model: inferred fan-out plus the `sleep`/`race`/`select`/`timeout` control
    combinators.
  - [`guide/using-platforms.md`](guide/using-platforms.md) — consuming a platform:
    the `(platform <name>)` + `(import [platform.<name> [*]])` two-step and the
    `platform.<name>` naming.
  - [`guide/writing-platforms.md`](guide/writing-platforms.md) — authoring a
    platform DLL: poll-shape effect leaves, the poll-in / wake-out reactor
    boundary, the handle model.
- **Errors** — [`errors/trait-impl-diagnostics.md`](errors/trait-impl-diagnostics.md)
  explains the diagnostics for traits, impls, method dispatch and definition
  binders, with the fix each one names.
- [`guide/syntax-command.md`](guide/syntax-command.md) — the `/syntax`
  command for recalling a language form at the REPL, and reader annotations for
  macro authors.
- [`cli-reference.md`](cli-reference.md) — every command-line mode and option,
  including the [`--test` mode](cli-reference.md#test---test), how the
  entry-module target is resolved, how the lib search path / `Cranelisp.toml`
  works, and the `/search` command for finding an importable function.
- [`repl/spec.md`](../repl/spec.md) — the normative REPL experience: display
  formats, slash commands, errors, caching.
- [`spec/`](../spec/) — the language specification.
