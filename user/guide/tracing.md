# Tracing — inspect a call tree

Use `(trace expr)` to evaluate an expression once and inspect its calls.
It returns a `Trace` value; it does not print a report or return the body's
original typed value. Read [functions](functions.md) and
[constructors](constructors.md) first if function definitions and data values
are new to you.

## Inspect the result

The `trace` form needs no import. Its data type and accessors live in
`primitives`; import the accessors you use:

<!-- sample: {"kind":"repl"} -->
```
user> (import [primitives [result]])
user> (result (trace 42))
:primitives/String "42"
```

The root's `result` contains the body's formatted value. This is text, so use
the original computation separately if you need a typed value for further work.
`TraceCall` stores these fields:

| Accessor | What you can inspect |
|---|---|
| `name` | A recorded function's qualified name. Generic calls use the template name, such as `user/identity`, without type arguments. | <!-- doc-check: literal reason="Example symbol or generated runtime path, not a source citation" -->
| `params` | Formatted arguments, as an `SList` of strings. |
| `result` | The formatted returned value. |
| `children` | Child calls, as an `SList` of `Trace` values. |
| `nanos` | Elapsed wall-clock nanoseconds. |

`SList` uses `macros/SCons` and `macros/SNil`, rather than the ordinary
standard-library `List`. Import those constructors to traverse children with
`match`. The exact data definition is
[spec §4.12.4](../../spec/04-expressions.md#4124-the-trace-adt).

For a readable report, the optional `core.trace` module supplies `trace-show`
for one node and `trace-show-tree` for a tree. Both return strings:

<!-- sample: {"kind":"definition"} -->
```clojure
(import [core.trace [trace-show-tree]])
(defn identity [x] x)
(trace-show-tree (trace (identity 7)))
```

The report includes a call named `user/identity`, argument `7`, result `7` <!-- doc-check: literal reason="Example symbol or generated runtime path, not a source citation" -->
and a variable elapsed time. It is a string value at the REPL; pass it to a
platform's `print` if you want plain output.

**Root shape remains unsettled (S124-Q13).** The current compiler adds a
synthetic root with no parameters above the recorded calls;
`trace-show-tree` currently hides it. Do not depend on its name or on a direct
call always occupying a particular tree level. The specification's direct-call
examples differ from this representation; the
[open question](../../spec/appendix-d-open-questions.md#s124-q13-what-are-a-trace-roots-name-parameters-and-children)
awaits a user ruling. The root's formatted result is a separate, delivered
behavior.

## Choose where the trace form lives

A form in the entry file or entered at the REPL covers the program. A form in
a library covers that module, its transitive imports and built-in primitives.
Putting `(trace (f))` in a library helper does not make calls inside its caller's
supplied `f` visible. Put the trace at the call site when investigating your
own program. See [spec §4.12.3](../../spec/04-expressions.md#4123-what-is-traced).

Named functions and callable extern primitives can appear as frames. Inline
arithmetic and comparisons do not add frames. Anonymous `fn` calls have no
separate named frame; calls they make to covered named functions can appear.
Some runtime-provided entries, including `discover-tests` itself, are excluded.
An absent frame therefore does not by itself show a function never ran.

Two carried coverage defects also matter:

- **ACT-1087:** on a first launch, a declared child of a prelude dependency
  can omit calls reached through the prelude; restored and linked cases pass.
- **ACT-1090:** a launch mixing restored and newly compiled dependencies can
  omit a module's frames. Do not use a partial tree as a complete call census.

Two coverage questions also remain open: what a saved REPL definition containing
a trace records after a later module loads, and what a library-held form covers
when it reaches a module only through qualification. Their current behavior is
not a settled guarantee; see [the open coverage questions](../../design/arch/tracing.md#51-which-modules-a-form-covers).

## Read timings as traced execution

Evaluation is strict and sequential throughout a trace, including inside called
functions. Independent pure work does not run in parallel there, and the
standard library's `par-map`, `par-reduce` and `par-map-reduce` run sequentially
inside the trace too. Instrumentation and value formatting also cost time.
Use traces to investigate calls and values; measure ordinary execution outside
`trace` when assessing parallel speedup. See
[spec §4.12.2](../../spec/04-expressions.md#4122-semantics),
[parallel collections](parallel-collections.md) and [concurrency](concurrency.md).

A nested trace entered while this thread is actively tracing raises a runtime
error and ends the process. Tracing a computation that panics also ends the
process, rather than returning a partial tree. The skipped concurrent-trace
result and nesting inside a skipped trace still have open questions; avoid
relying on those cases. See [nested tracing](../../spec/04-expressions.md#4125-nested-trace)
and [the runtime questions](../../design/arch/tracing.md#6-nested-trace-guard).

For a failing test that returns a value, see
[investigating tests](testing.md#investigate-a-failing-test). The runner isolates
panics; a direct trace does not.
