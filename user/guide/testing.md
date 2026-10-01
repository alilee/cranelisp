# Testing — writing tests and running them

A test is an ordinary function. The REPL's test commands and `cranelisp --test`
find your tests, run them, and report each result. All three share one runner, so
they report the same way.

> **About the transcripts.** They were checked against the real binary with the
> standard prelude loaded. The prompt's timing prefix is elided to `user>`, and
> run times vary.

## Write a test

A test is a zero-argument function whose name starts with `test-` and whose type
is exactly `(Fn [] (Option String))`. It returns `None` when it passes and
`(Some reason)` when it fails:

```clojure
(defn test-add [] :(Option String)
  (if (= (+ 2 2) 4) None (Some "2 + 2 should be 4")))

(defn test-div [] :(Option String)
  (if (= (/ 10 0) 0) None (Some "unreachable")))
```

Tests can live in any module; no naming scheme for modules is required. The
convention is
[`repl/spec/16-test-discovery.md` §16.1](../../repl/spec/16-test-discovery.md#161-test-function-convention).

A `test-` function with any other type is not run. The runner warns, naming it,
so a mistyped test cannot pass silently:

```
; warning: `user/test-wrong` is not run as a test: its type is `(Fn [] Int)`, and a test must have type `(Fn [] (Option String))`
```

## Run tests at the REPL

`/run-tests` runs the tests of the current module. Each line names a test by its
fully-qualified name; a summary follows:

```
user> /run-tests
  user/test-add ........................... ok
  user/test-div ........................... PANIC: runtime panic: division by zero

1 passed, 1 failed in 0.01ms
```

- A test that returns `(Some reason)` reports `FAILED: reason`.
- A test that hits a runtime error, such as division by zero, reports
  `PANIC: message` and counts as failed.
- A failure never stops the run; every selected test runs.
- When the selected modules hold no test, the report is `No tests found`.

Give a module name to run another module's tests, or use `/run-all-tests` for
every loaded project module. Library modules, found through the lib search path,
are left out:

```
user> /run-tests mathx
  mathx/test-square ....................... ok

1 passed in 0.00ms
user> /run-all-tests
  mathx/test-square ....................... ok
  user/test-add ........................... ok
  user/test-div ........................... PANIC: runtime panic: division by zero

2 passed, 1 failed in 0.00ms
```

The runner is specified in
[`repl/spec/16-test-discovery.md` §16.2](../../repl/spec/16-test-discovery.md#162-running-tests).

## Run tests from the command line

`cranelisp --test` compiles your program and runs the tests of the entry module
and the project modules it reaches through its imports and declared submodules.
It does not call `main`. The report goes to stdout and warnings to stderr, and
the exit status is `0` when every test passed (or none was found) and `1`
otherwise:

```
$ cranelisp --test .
  mathx/test-square ....................... ok
  user/test-add ........................... ok
  user/test-div ........................... PANIC: runtime panic: division by zero

2 passed, 1 failed in 0.01ms
$ echo $?
1
```

Which modules are searched, and the rest of the mode's behaviour, are in the
[CLI reference](../cli-reference.md#test---test).

## Investigate a failing test

The runner does not trace failures. To see what a failing test called, trace it
yourself at the REPL: `(trace (test-div))` returns a `Trace` value holding the
test's call tree. See
[`repl/spec/16-test-discovery.md` §16.4](../../repl/spec/16-test-discovery.md#164-tracing-failures).

## Discovering tests from your own code

At the REPL, a program can find and run tests itself with the `discover-tests`
builtin together with `catch-runtime-error`; the spec shows a complete runner
written this way
([§16.5](../../repl/spec/16-test-discovery.md#165-programmatic-use)).
`discover-tests` is available only in the REPL: `--run`, `--test` and `--link`
refuse a program that references it
([CLI reference](../cli-reference.md#test-discovery-is-repl-only)).
`catch-runtime-error` works in every mode.

## See also

- [`cli-reference.md`](../cli-reference.md#test---test) — the `--test` mode.
- [`repl/spec/16-test-discovery.md`](../../repl/spec/16-test-discovery.md) — the
  normative test convention, runner and primitives.
