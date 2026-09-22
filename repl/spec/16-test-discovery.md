> [REPL specification index](index.md)

## 16. Test Discovery and Execution [R4]

The REPL provides commands for discovering and running test functions. Test infrastructure rests on two ordinary `primitives`-module entries — `discover-tests` and `catch-runtime-error` — plus the existing macro system. Both parse as plain applications, type by ordinary scheme resolution, and require import or FQ reference like any other `primitives` name (zero frontend and zero typecheck special-casing). Everything above them — selection, filtering, iteration, result interpretation, reporting, timing — is ordinary in-language code in the stdlib.

See `design/arch/test-discovery.md` (SETTLED, fourth convergence) for the full subsystem design.

### 16.1 Test Function Convention

A **test function** is any zero-argument function whose name begins with `test-` and whose return type is exactly `(Fn [] (Option String))`:

- `None` — the test passed
- `Some(reason)` — the test failed, with a human-readable reason string

There is no module naming requirement. Test functions may be defined in any module. A `test-`prefixed function whose scheme is not exactly `(Fn [] (Option String))` is **excluded from discovery and warned** at discovery time, so a mistyped test cannot silently masquerade as "no failures."

### 16.2 Slash Commands

#### 16.2.1 `/run-tests [module]` [R4]

Discover and run test functions. With no argument, searches the current module. With a module path argument, searches that module. The command is sugar over the in-language runner (§16.5).

```
user> /run-tests
  test-add ................................ ok
  test-div-zero .......................... FAILED: expected error

1 passed, 1 failed in 2.34ms
```

```
user> /run-tests user.math.test
  test-factorial ......................... ok

1 passed in 0.45ms
```

On failure, the trace tree for the failing test MUST be displayed after the failure reason (see §16.4).

#### 16.2.2 `/run-all-tests` [R4]

Discover and run all test functions in all loaded modules whose source files are under the project root. Library modules (discovered through the lib search path) are excluded.

```
user> /run-all-tests
  user/test-add .......................... ok
  user.math/test-factorial ............... ok
  user.io/test-read ...................... FAILED: file not found

2 passed, 1 failed in 5.67ms
```

### 16.3 The Primitives [Uncovered S122]

`discover-tests` and `catch-runtime-error` are ordinary `primitives`-module symbols — imported (or FQ-referenced) like any other primitive, not special forms and not always-in-scope root names.

**`discover-tests`** — discovery primitive:

```
discover-tests :: (Fn [(Vec String)] (Vec (Pair String (Fn [] (Option String)))))

(discover-tests [])              ; the session's current module
(discover-tests ["user.math"])   ; a named module
(discover-tests ["a" "b"])       ; union over the named modules
```

The primitive takes exactly one argument, an ordinary `(Vec String)` value of module-path strings — not a bare module path.

The result MUST be the vector itself, not an `IO` action: discovery is pure-typed, and its result is treated notionally as a constant. Introspection is deliberately not modelled as an effect, so that test discovery does not require an introspective platform. The freshness requirement below still applies.

Returns one `(Pair name callable)` per eligible `test-*` function:

- **`name`** — the fully-qualified test name `"module/test-name"` as a `String`, for selection, sorting, and reporting.
- **`callable`** — a language fn value of type `(Fn [] (Option String))` that, when invoked, performs a **GOT-slot-indirect call** to the test. The wrapper closes over the test's GOT slot, not a baked code pointer, so a *redefined* test runs its current body.

**Freshness.** The callables are late-bound GOT-slot wrappers. Calling `discover-tests` again re-scans live state: a `test-*` defined after a previous call is included on the next call, and a redefined test runs its new body. Selection and reporting compose over these values and stay fresh by construction — freshness lives in the returned values, not in expansion timing. (This is why discovery returns callables, not a `(Vec String)` of names threaded through a macro runner, which would freeze the test set at the macro's expansion time. The macro-runner approach is retired.)

**Module scope.** Discovery searches only the modules its `(Vec String)` argument names. An empty vector means the session's current module, not the module lexically containing the discovery call: a helper defined in one module that calls `(discover-tests [])` discovers the tests of whichever module is current when it runs. Discovery does not extend its scope through imports; a module imported by a searched module is searched only if it is itself named.

**Library convenience (non-normative).** The reference standard library's `testing.runner` module provides optional sugar over the vector form, the `discover-here` macro: `(discover-here)` expands to `(primitives/discover-tests [])`, and `(discover-here "user.math")` or `(discover-here "a" "b")` collects the individual module arguments into the vector. `discover-here` is library code, not a shape of the primitive; a program that does not use it calls `discover-tests` with a vector.

`Pair` and `Result` are seeded as primitives bootstrap types (alongside `Option`), so both are available to discovery results and to `catch-runtime-error`.

**`catch-runtime-error`** — protected-call combinator:

```
catch-runtime-error :: forall a. (Fn [(Fn [] a)] (Result a String))
```

Promoted out of the test feature to a standalone `primitives` entry usable by any user code and by the stdlib — it is the language's only way to turn a runtime panic into a value. It invokes the thunk on the calling thread; if the thunk hit a language-level runtime error (match non-exhaustion, division by zero, vec out-of-bounds), it clears the error slot and returns `(Err message)`; otherwise it returns `(Ok result)`.

`TestResult`, `TestPass`, `TestFail`, and `run-test` are **retired**: a test's outcome is its own `(Option String)` (`None` = pass, `Some reason` = fail); the FQ name lives in the discovered `Pair`; timing comes from `trace`'s nanos.

### 16.4 Tracing Failures

The slash commands do NOT automatically trace failing tests. To trace a failing test, use `(trace (test-fn))` at the REPL:

```
user> /run-tests
  test-factorial ......................... FAILED: expected 120, got 0

0 passed, 1 failed in 1.23ms
user> (trace (test-factorial))
;; => Trace ADT with full call tree
```

Trace and test are independent, composable features — the user decides when tracing overhead is worthwhile.

### 16.5 Programmatic Use

The in-language runner is ordinary code — no macro. `discover-tests` returns `(name, callable)` pairs; `catch-runtime-error` brackets each callable; the runner folds a three-way outcome per test over the resulting `(Result (Option String) String)`:

- `(Err msg)` — the test panicked (match non-exhaustion, div-by-zero, …)
- `(Ok None)` — the test passed
- `(Ok (Some why))` — the test ran and reported an assertion failure

```clojure
(import [primitives [discover-tests catch-runtime-error]])

;; Run one discovered test: returns a human-readable line.
(defn run-one [pair]
  (match pair
    [(Pair name run)
     (match (catch-runtime-error run)
       [(Err msg)        (str-concat name " PANIC: " msg)]
       [(Ok None)        (str-concat name " ok")]
       [(Ok (Some why))  (str-concat name " FAIL: " why)])]))

;; Run every test in the current module.
(defn run-all []
  (map run-one (discover-tests [])))

;; Run only the tests whose name contains a substring — selection is in-language,
;; over the SAME pairs, and stays fresh because the callables are late-bound.
(defn run-matching [substr]
  (map run-one
       (filter (fn [p] (match p [(Pair nm _) (contains? nm substr)])) (discover-tests []))))
```

`catch-runtime-error` is usable by any code, not just tests:

```clojure
(import [primitives [catch-runtime-error]])

;; Try a risky computation; recover with a default on panic.
(defn safe-div [a b]
  (match (catch-runtime-error (fn [] (/ a b)))
    [(Ok q)   q]
    [(Err _)  0]))           ; division by zero panicked — recover with 0
```

Standard library convenience functions (e.g., `format-test-run`, `failures-only`, `test-passed?`) MAY be provided in a `core.testing` module but are not required by this specification.

### 16.6 `--link` Interim Behaviour

`discover-tests` is **REPL / `--run` only**. A `--link` build of a program that calls `discover-tests` is accepted at compile time, but the missing host symbol surfaces as an unresolved-symbol failure at link/load (the standalone executable has no live session to scan). This is documented interim behaviour — no friendly rejection yet; a future sprint may add a diagnostic.

`catch-runtime-error`, by contrast, **works in all modes including `--link`**: it is a self-contained intrinsic (it calls a closure already present in the linked program and constructs a `Result` heap value — no live session needed). Error capture is a pure runtime capability available everywhere; discovery is a dev-session capability.
