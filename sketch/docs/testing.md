# Testing

## Overview

Testing in Cranelisp is built on two general-purpose features — **inline modules**
and **convention-based test discovery** — with a lightweight assertion library
(`lib/testing.cl`) and a REPL command (`/run-tests`) for running tests.

## Language features used

### Inline modules: `(mod name ...)`

Defines a submodule inline within a source file. On first compilation, the inline
body is extracted to a separate file (`parent_dir/parent_stem/name.cl`) and the
parent is rewritten with `(mod name)`. From then on, the submodule is file-based.

```clojure
;; math.cl
(defn add [x y] (+ x y))

(mod test
  (import [super [*]])
  (import [testing [*]])
  (defn test-addition [] (assert-eq 7 (add 3 4))))
```

After first compilation, this creates `math/test.cl` containing the test module,
and `math.cl` is rewritten to contain `(mod test)` (without the inline body).

- `(mod name ...)` creates submodule `parent.name` (e.g. `math.test`)
- `super` in imports refers to the enclosing module: `(import [super [*]])`
- Not test-specific — useful for general code organization within a file

### `super` import

Inside a submodule, `(import [super [*]])` imports all public definitions from
the parent module. This is the standard way for test modules to access the code
under test.

`super` resolves to the parent module path by stripping the last component.
Using `super` in a top-level module (no parent) produces an error.

## Assertion library: `lib/testing.cl`

Import with `(import [testing [*]])` in test modules.

### Assertions

All assertions return `(Option String)`: `None` = pass, `(Some "reason")` = fail.

```clojure
(assert-eq expected actual)  ;; Uses = and show (constrained polymorphic)
(assert-true x)              ;; Expects true
(assert-false x)             ;; Expects false
```

`assert-eq` is constrained polymorphic — it requires `Eq` and `Display` traits on
its arguments, and is monomorphised at each call site.

### `check` macro

Chains assertions, returning the first failure (first `Some`):

```clojure
(check
  (assert-eq 7 (add 3 4))
  (assert-eq 0 (add 0 0))
  (assert-eq -1 (add 1 -2)))
```

Expands to nested `match` expressions that short-circuit on the first `Some`.

### Default fold helpers

`lib/testing.cl` provides fold functions for the `(run-tests ...)` special form:

```clojure
(run-tests-pass-default acc name nanos)
;; Appends "  name ... ok\n" to the report string acc.

(run-tests-fail-default acc name nanos reason trace)
;; Appends "  name ... FAILED: reason\n<trace tree>" to acc.

(run-tests-report)
;; Convenience wrapper: (run-tests "" run-tests-pass-default run-tests-fail-default)
;; Returns a formatted human-readable report string.
```

## Test conventions

- **Test modules**: submodules named `*.test` (e.g. `math.test`, `user.test`)
- **Test functions**: zero-arg functions named `test-*` that return `(Option String)`
- **No registration needed**: test functions are discovered by naming convention

## Running tests

### `(run-tests init pass-fn fail-fn)` — Special Form (REPL only)

A REPL-only special form that discovers and runs all `test-*` functions in loaded
`.test` modules, collecting results via user-supplied fold functions.

```
(run-tests init pass-fn fail-fn)

pass-fn :: (Fn [a String Int] a)          ;; acc, test-name, nanos
fail-fn :: (Fn [a String Int String Trace] a)  ;; acc, test-name, nanos, reason, trace
returns :: a
```

For each test, `run-tests`:
1. Swaps all module GOTs to install trace wrappers (same mechanism as `(trace ...)`)
2. Calls the zero-arg test function, capturing a full call tree
3. Restores GOTs
4. Calls `pass-fn` if the result is `None`, or `fail-fn` if `(Some reason)`

In batch mode (`--run`), `run-tests` returns `init` unchanged (no tests run).

Example using the defaults from `lib/testing.cl`:

```clojure
user> (run-tests-report)
;; "  test-add ... ok\n  test-div-by-zero ... FAILED: expected 0, got 1\n..."
```

Custom folds (count results):

```clojure
(run-tests 0
  (fn [acc _ _] (+ acc 1))           ;; count passes
  (fn [acc _ _ _ _] acc))            ;; ignore failures
```

### REPL: `/run-tests [prefix]`

Discovers and runs test functions in loaded `.test` modules:

```
user> /run-tests
Running tests in user.test...
  test-add ................................ ok
  test-double ............................. ok
  test-negative ........................... FAILED: expected -2, got 2

2 passed, 1 failed in 0.15ms
```

With a prefix, only modules matching the prefix are tested:
```
user> /run-tests math
```

### Batch mode

In batch mode (`--run`), test modules are compiled but not automatically executed.
Users can import test modules and call test functions directly from `main`:

```clojure
(defn main []
  (match (test/test-add)
    [None 0
     (Some msg) 1]))
```

## Example

See `examples/test-demo.cl` for a complete example with inline test module,
assertions, and the `check` macro.

## Design properties

- **Minimal language additions**: Only `(mod ...)` and `super` — both general-purpose
- **Convention over configuration**: `*.test` modules, `test-*` functions
- **Option-based results**: `None`/`Some` instead of panic — composable, inspectable
- **`check` macro**: chains assertions like `or` for `Option`
- **No reflection primitives needed**: `/run-tests` uses existing module metadata
