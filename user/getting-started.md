# Getting started

This page covers the essentials: building the binary, opening the REPL, running
your first program, platforms and automatic parallelism. [Where to go
next](#where-to-go-next) points to the learning sequence, the showcase and the
feature guides. For the full command line see [`cli-reference.md`](cli-reference.md).

## Build the binary

Cranelisp builds with Cargo from the workspace root:

<!-- sample: {"kind":"illustrative","reason":"Shell build command"} -->
```
cargo build
```

This produces `target/debug/cranelisp`. (A release build — `cargo build --release` <!-- doc-check: literal reason="Example symbol or generated runtime path, not a source citation" -->
— produces `target/release/cranelisp`.) Add the chosen build directory to your <!-- doc-check: literal reason="Example symbol or generated runtime path, not a source citation" -->
`PATH`, for example `export PATH="$PWD/target/debug:$PATH"` from the repository
root, so the `cranelisp` commands below find it.

## Start the REPL

Run the binary with no arguments to open the interactive REPL in the current
directory:

<!-- sample: {"kind":"repl"} -->
```
cranelisp REPL — type /help for help
agent: dormant (/ask shows what to set)
0+0ms; user> (+ 1 2)
:primitives/Int 3
```

The default build includes the embedded agent and enables it, but activation
requires an explicit provider and its configuration. Without them it is
**dormant**, as shown above; `/ask` explains what to set. Supply settings in the
process environment, project `.env`, or user configuration file; see
[agent configuration](cli-reference.md#agent-configuration) and
[environment files](cli-reference.md#environment-files). `cranelisp --no-agent`
starts with the agent off. Later prompt-only transcripts on this page are
excerpts, with startup and timing details omitted.

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
an **empty** directory can give a different result. (Successful replacements win: a
`(defn f …)` takes effect over the stored definition only if the replacement is
accepted under the live-development rules above.)

If you want fresh-program semantics — a self-contained program with no resumed
state — use `cranelisp --run script.cl` (see the
[CLI reference](cli-reference.md)) or run the REPL in an empty directory. The
normative model is [`repl/spec.md §15.2.1`](../repl/spec.md).

## Panics end the process

A runtime panic, such as primitive integer division by zero, prints a diagnostic
to stderr and ends the process with status `1`. In the REPL it ends the session,
so later input does not run. Use a checked operation when failure is an expected
result. In a fresh REPL with the default prelude:

<!-- sample: {"kind":"repl"} -->
```
user> (primitives/checked-quot 7 -2)
:(primitives/Option primitives/Int) (Option.Some -3)
user> (primitives/checked-quot 10 0)
:(primitives/Option primitives/Int) Option.None
user> (primitives/checked-quot -9223372036854775808 -1)
:(primitives/Option primitives/Int) Option.None
user> (primitives/div-i64 -9223372036854775808 -1)
:primitives/Int -9223372036854775808
```

`checked-quot` returns `None` for zero divisors and for `Int.MIN / -1`.
Primitive `div-i64` wraps that latter pair to `Int.MIN`; its zero divisor panics.
These primitive operations have their own contract; a standard-library trait
such as `Num` supplies library policy. See [runtime arithmetic and panics,
spec §12.7](../spec/12-runtime.md#127-error-model)
and [library numeric traits, §7.7.1](../spec/07-traits.md#771-num).
The [testing guide](guide/testing.md) explains how the compiler runner isolates
a test panic so the remaining tests can still run.

## Your first program

A runnable program defines an ordinary zero-argument `main` returning IO and
runs under `--run`. A trait method named `main` or a multi-arity `main` does not
supply this entry point; see [batch entry requirements](cli-reference.md#run---run). The
clearest worked introductions live in [`examples/`](../examples/) — a numbered
learning sequence of self-contained `.cl` files you can run directly.

### A program without effects (runs everywhere)

Start with [`examples/01-integers.cl`](../examples/01-integers.cl). It defines a
few arithmetic functions and combines them in `main`:

<!-- sample: {"kind":"illustrative","reason":"Shell invocation"} -->
```
cranelisp --run examples/01-integers
```

It prints nothing — a program's only output comes from IO effects, and this one
performs none. Every `main` returns an `IO` action; this one uses the built-in
`primitives/pure` function to lift its result into an action that yields it without
performing an effect. When that result is an `Int`, it becomes the
**process exit code** (`01-integers` computes `69`, so the process exits with
code `69`). You can confirm it ran cleanly by inspecting the exit code:

<!-- sample: {"kind":"illustrative","reason":"Shell exit status walkthrough"} -->
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

<!-- sample: {"kind":"definition"} -->
```clojure
;; hello.cl
(platform stdio)
(import [platform.stdio [*]])

(defn main [] (print "hello world"))
```

<!-- sample: {"kind":"illustrative","reason":"Shell launch and stdout"} -->
```
$ CRANELISP_PLATFORM_PATH=/path/to/cranelisp/target/debug cranelisp --run hello.cl
hello world
```

The worked IO example [`examples/21-hello-io.cl`](../examples/21-hello-io.cl)
teaches sequencing actions with `pure` and `bind`, including a recursive
countdown. It is part of the learning sequence and runs with the platform setup
above.

IO requires a **platform** — a small native library that provides the host's
side-effecting operations (here, `print`). The binary looks for platforms in a
`platforms/` directory under the project root and under each lib directory. The
learning sequence puts its own `lib/` on the lib search path, and
`examples/lib/platforms/` holds checked-in symlinks to the libraries Cargo builds
in `target/debug/`. Only Linux links (`stdio.so`, `test-capture.so`) are checked <!-- doc-check: literal reason="Example symbol or generated runtime path, not a source citation" -->
in, so on Linux an entry module **inside `examples/`** finds the platform with
**no environment variable**, once `cargo build` has run.

On macOS, and for any program outside `examples/` — including the `hello.cl`
above, written in a directory of your own — point the binary at the directory
holding the built library with `CRANELISP_PLATFORM_PATH`:

<!-- sample: {"kind":"illustrative","reason":"Shell environment setup"} -->
```
CRANELISP_PLATFORM_PATH=/path/to/cranelisp/target/debug cranelisp --run hello.cl
```

If the platform cannot be found you will see `platform 'stdio' not found` — that
means the DLL was not on the search path, not that your program is wrong.

## Platforms and IO

Calling a Cranelisp function performs no effect, even when it returns `IO`:
all functions are pure in this sense. Effects happen when the runtime executes an
`IO` action. A function whose result type contains no `IO` computes a value
without describing an IO action. See [purity and IO](../spec/03-types.md#323-io-type).

`IO` is opaque: user code cannot construct it through a constructor or
pattern-match on it. Use the built-in `primitives/pure` function (re-exported as
`pure` by the standard-library prelude) to lift a value into `IO`, and `bind` to
sequence IO actions. The name `pure` is the conventional name for this lift;
it does not distinguish the function's purity from that of other functions.
See [the IO type](../spec/10-io.md#101-io-type),
[`pure`](../spec/10-io.md#102-pure), and [`bind`](../spec/10-io.md#103-bind).
A program's `main` returns an `IO` action, and the runtime *forces* that action
to run the effects and extract the result.

A **platform** is a native library that supplies the host operations an `IO` action
ultimately calls — `print`, `read-line`, and so on. Different platforms provide
different capabilities (a CLI `stdio` platform, a web platform, and so on), which is
why an IO program names the platform it needs and the runtime loads the matching DLL.

Using a platform is **two steps** — and missing the second is the usual first
stumble:

<!-- sample: {"kind":"definition"} -->
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

<!-- sample: {"kind":"repl"} -->
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
- **Independent CPU computations run in parallel too.** The arguments of a call that
  do not depend on each other can be evaluated at the same time. So the two recursive
  branches of a divide-and-conquer function run at once. The standard library packages
  this for collections as **`par-map`, `par-reduce`, and `par-map-reduce`** (in the
  `collections.parallel` module) — ordinary functions that map/reduce element-wise in
  parallel and return exactly what their sequential twins do. See
  [`guide/parallel-collections.md`](guide/parallel-collections.md) for how to use them
  and [`examples/30-parallel-map-reduce.cl`](../examples/30-parallel-map-reduce.cl) for
  the worked divide-and-conquer case.

**Measure your workload.** Historical compute-bound map-reduce measurements
showed roughly 2–3× speedup; they are not current performance guarantees.
Allocation-heavy work can become slower because workers contend on allocation
and reference counting. Compare ordinary execution with a serial baseline using
`CRANELISP_NO_LENIENT=1`, and see
[parallel collections](guide/parallel-collections.md) for choosing work and
[the environment reference](cli-reference.md#environment-variables) for controls.
A [trace](guide/tracing.md) runs CPU work sequentially and adds instrumentation,
so its timings cannot measure ordinary parallel speedup.

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

  <!-- sample: {"kind":"illustrative","reason":"Shell showcase launch"} -->
  ```
  CRANELISP_LIB=stdlib CRANELISP_PLATFORM_PATH=target/debug \
    cranelisp --run exemplar/user.cl
  ```

- **Write functions and data.** Start with [functions](guide/functions.md), then
  [constructors](guide/constructors.md) and [field accessors](guide/field-accessors.md).
  [Traits](guide/traits.md) builds on those ideas, including parametric
  implementations and `derive`. [Bitwise operations](guide/bitwise.md) cover
  integer masks and shifts.
- **Organize a project.** [Modules](guide/modules.md) explains file layout and
  public names. Read it before [macros](guide/macros.md), whose expansion helpers
  live in dependencies. [Live development](guide/live-development.md) covers
  editing loaded files, authored entries and persistence.
- **Investigate behavior.** [Testing](guide/testing.md) covers the test runner;
  [tracing](guide/tracing.md) shows calls and returned values. The
  [error guide](errors/trait-impl-diagnostics.md) explains trait and binder
  diagnostics. [`/syntax`](guide/syntax-command.md) recalls syntax at the prompt.
- **Use IO and concurrency.** [Using platforms](guide/using-platforms.md) explains
  loading an effect library. Continue with [concurrency](guide/concurrency.md)
  for races and deadlines, or [parallel collections](guide/parallel-collections.md)
  for computations whose result types contain no `IO`.
  [Writing platforms](guide/writing-platforms.md) is for Rust authors implementing
  their own effect library.
- **Look up an invocation or function.** The [CLI reference](cli-reference.md)
  covers modes, targets, library paths and `/search`.
- [`repl/spec.md`](../repl/spec.md) — the normative REPL experience: display
  formats, slash commands, errors, caching.
- [`spec/`](../spec/) — the language specification.
