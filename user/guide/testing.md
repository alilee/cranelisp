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

<!-- sample: {"kind":"definition","group":"tests"} -->
```clojure
(defn test-add [] :(Option String)
  (if (= (+ 2 2) 4) None (Some "2 + 2 should be 4")))

(defn test-div [] :(Option String)
  (if (= (/ 10 0) 0) None (Some "unreachable")))
```

For the other-module transcripts below, also create `mathx.cl` in the same
project directory with this default-prelude setup:

<!-- sample: {"kind":"definition"} -->
```clojure
;; mathx.cl
(defn square [:Int n] (primitives/mul-i64 n n))
(defn test-square [] :(Option String)
  (if (= (square 3) 9) None (Some "square should be 9")))
```

Add `(import [mathx [square]])` to `user.cl` alongside the first two test
definitions. This makes `mathx` part of the project graph for `--test`, and loads
it for the REPL commands below. Keep `test-returned` in the later investigation
group separate when reproducing the runner counts.

Tests can live in any module; no naming scheme for modules is required. The
convention is
[`repl/spec/16-test-discovery.md` §16.1](../../repl/spec/16-test-discovery.md#161-test-function-convention).

A `test-` function with any other type is not run. The runner warns, naming it,
so a mistyped test cannot pass silently:

<!-- sample: {"kind":"illustrative","reason":"Output-only runner warning; focused evidence: tests/test_runner.rs, mistyped_test_warns_once_beside_panicking_test"} -->
```
; warning: `user/test-wrong` is not run as a test: its type is `(Fn [] Int)`, and a test must have type `(Fn [] (Option String))`
```

## Run tests at the REPL

`/run-tests` runs the tests of the current module. Each line names a test by its
fully-qualified name; a summary follows:

<!-- sample: {"kind":"illustrative","reason":"Runner elapsed time varies and panic stderr is relayed; exact replay is unsupported. Focused evidence: tests/test_runner.rs, panicking_test_does_not_end_run_or_repl"} -->
```
user> /run-tests
  user/test-add ........................... ok
  user/test-div ........................... PANIC: division by zero

1 passed, 1 failed in 2576.90ms
```

- A test that returns `(Some reason)` reports `FAILED: reason`.
- A test that hits a runtime error, such as division by zero, reports
  `PANIC: message` and counts as failed.
- A failure never stops the run; every selected test runs. The compiler runner
  executes tests in a child process. A panic ends that child; the parent records
  the result and starts another child for the remaining tests. The REPL parent
  survives. This is process isolation, not panic recovery.
- A child's panic diagnostic also appears on stderr as
  `error: runtime panic: division by zero`; the `PANIC:` line above is stdout.
- When the selected modules hold no test, the report is `No tests found`.

Give a module name to run another module's tests, or use `/run-all-tests` for
every loaded project module. Library modules, found through the lib search path,
are left out:

<!-- sample: {"kind":"illustrative","reason":"Runner elapsed time varies and panic stderr is relayed; exact replay is unsupported. Focused evidence: tests/test_runner.rs, panicking_test_does_not_end_run_or_repl"} -->
```
user> /run-tests mathx
  mathx/test-square ....................... ok

1 passed in 1063.89ms
user> /run-all-tests
  mathx/test-square ....................... ok
  user/test-add ........................... ok
  user/test-div ........................... PANIC: division by zero

2 passed, 1 failed in 2149.11ms
```

The runner is specified in
[`repl/spec/16-test-discovery.md` §16.2](../../repl/spec/16-test-discovery.md#162-running-tests).

## Run tests from the command line

`cranelisp --test` compiles your program and runs the tests of the entry module
and the project modules it reaches through its imports and declared submodules.
It does not call `main`. The report goes to stdout and warnings to stderr, and
the exit status is `0` when every test passed (or none was found) and `1`
otherwise:

<!-- sample: {"kind":"illustrative","reason":"Shell test invocation, process status and variable elapsed time"} -->
```
$ cranelisp --test .
  mathx/test-square ....................... ok
  user/test-add ........................... ok
  user/test-div ........................... PANIC: division by zero

2 passed, 1 failed in 2540.82ms
$ echo $?
1
```

Which modules are searched, and the rest of the mode's behaviour, are in the
[CLI reference](../cli-reference.md#test---test).

## Investigate a failing test

The runner does not trace failures. To see what a failing test called, trace it
yourself at the REPL. Use a test that returns a failure value, for example,
in the same default-prelude session:

<!-- sample: {"kind":"definition"} -->
```clojure
(defn test-returned [] :(Option String) (Some "inspect this failure"))
(trace (test-returned))
```

The trace holds the call tree and the returned failure. Calling or tracing
`test-div` directly panics and ends the REPL process; it does not return a trace.
See
[`repl/spec/16-test-discovery.md` §16.4](../../repl/spec/16-test-discovery.md#164-tracing-failures).

## Discovering tests from your own code

At the REPL, import `primitives/discover-tests` to obtain test names and
zero-argument callables for a module. Invoke a callable normally and inspect its
returned `None` or `(Some reason)`. A direct panic ends this process; there is no
`catch-runtime-error` builtin. To keep running after a test panic, use the
compiler's `/run-tests`, `/run-all-tests` or `--test` runner and its child-process
isolation. The programmatic discovery interface is described in
[§16.5](../../repl/spec/16-test-discovery.md#165-programmatic-use).
`discover-tests` is available only in the REPL: `--run`, `--test` and `--link`
refuse a program that references it
([CLI reference](../cli-reference.md#test-discovery-is-repl-only)).

## See also

- [`cli-reference.md`](../cli-reference.md#test---test) — the `--test` mode.
- [`repl/spec/16-test-discovery.md`](../../repl/spec/16-test-discovery.md) — the
  normative test convention, runner and primitives.
