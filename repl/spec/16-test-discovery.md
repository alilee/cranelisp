> [REPL specification index](index.md)

## 16. Test Discovery and Execution [R4]

The REPL provides commands for discovering and running test functions, and `--test` discovers and runs them from the command line (§0.2.2). The slash commands and `--test` use one runner that belongs to the compiler (§16.2); they do not rely on the primitives below or on library code.

Programs discover and run tests with two ordinary `primitives`-module entries — `discover-tests` and `catch-runtime-error` — plus the existing macro system. Both parse as plain applications, type by ordinary scheme resolution, and require import or FQ reference like any other `primitives` name (zero frontend and zero typecheck special-casing). Everything a program builds above them — selection, filtering, iteration, result interpretation, reporting, timing — is ordinary in-language code. `discover-tests` is available only in the REPL (§16.6).

See `design/arch/test-discovery.md` (SETTLED, fourth convergence) for the full subsystem design.

### 16.1 Test Function Convention

A **test function** is any zero-argument function whose name begins with `test-` and whose return type is exactly `(Fn [] (Option String))`:

- `None` — the test passed
- `Some(reason)` — the test failed, with a human-readable reason string

There is no module naming requirement. Test functions may be defined in any module. A `test-`prefixed function whose scheme is not exactly `(Fn [] (Option String))` is **excluded from discovery and warned** at discovery time, so a mistyped test cannot silently masquerade as "no failures." [Tested+Neg tests/test_runner.rs::test_mode_runs_every_test_reports_fq_lines_and_matches_run_tests, tests/test_runner.rs::test_mode_selects_exactly_the_import_chain_fresh_and_cached, tests/spec_12_runtime::discover_tests_excludes_mistyped_test_neg — `None` passes and `(Some reason)` fails with its reason; tests in several modules run; the pinned bare-`None` test runs and a mistyped `(Fn [] (Option Int))` test is excluded, and the shared runner warns by FQ name under `--test` and `/run-tests`; the excluded-signature matrix is unit-pinned at src/session_v4/test_runner/discovery/tests.rs::each_mistyped_test_is_excluded_with_one_warning_naming_it. In-language `discover-tests` excludes without a warning, so the warning clause is unrealized there (design/int/test-runner.md §12; ACT-0986)]

### 16.2 Running Tests

`/run-tests`, `/run-all-tests` and `--test` (§0.2.2) are one test runner. They
differ only in the modules they select, and in what the host does with the
outcome: `--test` writes the report to stdout and sets the process exit status
(§0.2.2), and the REPL continues. Everything else in this section is the same
for all three. [Tested+Neg tests/test_runner.rs::test_mode_runs_every_test_reports_fq_lines_and_matches_run_tests, tests/test_runner.rs::test_mode_empty_run_reports_no_tests_found_and_exits_zero, tests/spec_12_runtime::run_tests_empty_module_reports_no_tests — one runner: `--test` and `/run-tests` print identical FQ result lines and summaries; a failure and a panic do not stop the run; `ok`, `FAILED: <reason>` and `PANIC: <message>`; a mistyped test is excluded; the empty run is `No tests found` in both hosts. The blank line before the summary is unit-pinned at src/session_v4/test_runner/run/tests.rs::report_text_and_exit_code_come_from_the_same_outcomes. The Tracing bullet has no committed evidence]

- **Eligibility.** The runner runs the test functions (§16.1) of the selected
  modules. A mis-typed `test-` function is excluded and warned (§16.1).
- **Execution.** A failing test does not stop the run. Each test runs with its
  runtime errors captured, so a test that panics is reported, counts as failed,
  and the remaining tests still run.
- **Report.** One result line per test, naming it by its fully-qualified name
  (§16.3) and ending in `ok`, in `FAILED: <reason>` when it returns
  `(Some reason)`, or in `PANIC: <message>` when it raises a runtime error; then
  a blank line and one summary line counting the tests passed and failed.
- **Empty run.** When the selected modules contain no test, the report is the
  single line `No tests found`.
- **Tracing.** The runner does not trace failing tests (§16.4).

#### 16.2.1 `/run-tests [module]` [R4]

Run the tests of one module. With no argument, it selects the current module;
with a module path argument, it selects that module. [Tested tests/test_runner.rs::test_mode_runs_every_test_reports_fq_lines_and_matches_run_tests, tests/cache.rs::cache_restored_parent_enrols_private_test_child — no argument, and a module-path argument naming a module other than the current one]

```
user> /run-tests
  user/test-add ........................... ok
  user/test-div-zero ...................... FAILED: expected error

1 passed, 1 failed in 2.34ms
```

```
user> /run-tests user.math.test
  user.math.test/test-factorial ........... ok

1 passed in 0.45ms
```

#### 16.2.2 `/run-all-tests` [R4]

Run the tests of all loaded modules whose source files are under the project root. Library modules (discovered through the lib search path) are excluded. [Tested+Neg tests/test_runner.rs::run_all_tests_neg_excludes_library_modules_under_the_project_root — a project module loaded only through a library module is included; a library module in a lib directory inside the project, and its child, are excluded]

```
user> /run-all-tests
  user/test-add ........................... ok
  user.math/test-factorial ................ ok
  user.io/test-read ....................... FAILED: file not found

2 passed, 1 failed in 5.67ms
```

### 16.3 The Primitives [Uncovered S122 — partial: the direct-vector result, eligibility, module scope, FQ names and the vector-only call shape are evidenced as recorded on [Appendix A](../../spec/appendix-a-builtins.md#test-discovery-and-error-capture); `catch-runtime-error`'s `Ok` and `Err` arms by tests/spec_12_runtime::catch_runtime_error_ok_arm_run, tests/spec_12_runtime::catch_runtime_error_err_arm_run and tests/spec_12_runtime::catch_runtime_error_err_arm_link; freshness across a later definition or redefinition, the `["a" "b"]` union and absence without an import are unevidenced end to end]

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

The test runner (§16.2) does NOT automatically trace failing tests. To trace a failing test, use `(trace (test-fn))` at the REPL:

```
user> /run-tests
  user/test-factorial ..................... FAILED: expected 120, got 0

0 passed, 1 failed in 1.23ms
user> (trace (test-factorial))
;; => Trace ADT with full call tree
```

Trace and test are independent, composable features — the user decides when tracing overhead is worthwhile.

### 16.5 Programmatic Use

In the REPL, a program can run tests with ordinary code — no macro. `discover-tests` returns `(name, callable)` pairs; `catch-runtime-error` brackets each callable; the runner folds a three-way outcome per test over the resulting `(Result (Option String) String)`:

- `(Err msg)` — the test panicked (match non-exhaustion, div-by-zero, …)
- `(Ok None)` — the test passed
- `(Ok (Some why))` — the test ran and reported an assertion failure

```clojure
(import [primitives [discover-tests catch-runtime-error
                     Pair Some None Ok Err
                     str-concat contains? add-i64 eq-i64
                     vec-len vec-get vec-push]])

;; Run one discovered test: returns a human-readable line.
(defn run-one [pair]
  (match pair
    [(Pair name run)
     (match (catch-runtime-error run)
       [(Err msg) (str-concat name (str-concat " PANIC: " msg))
        (Ok outcome)
          (match outcome
            [None       (str-concat name " ok")
             (Some why) (str-concat name (str-concat " FAIL: " why))])])]))

;; Run the pairs from index i whose name satisfies keep?, appending one line each.
(defn run-selected [pairs keep? i lines]
  (if (eq-i64 i (vec-len pairs))
      lines
      (let [pair (vec-get pairs i)]
        (run-selected pairs keep? (add-i64 i 1)
          (match pair
            [(Pair name _)
             (if (keep? name) (vec-push lines (run-one pair)) lines)])))))

;; Run every test in the current module.
(defn run-all []
  (run-selected (discover-tests []) (fn [name] true) 0 []))

;; Run only the tests whose name contains a substring — selection is in-language,
;; over the SAME pairs, and stays fresh because the callables are late-bound.
(defn run-matching [substr]
  (run-selected (discover-tests []) (fn [name] (contains? name substr)) 0 []))
```

`catch-runtime-error` is usable by any code, not just tests:

```clojure
(import [primitives [catch-runtime-error div-i64 Ok Err]])

;; Try a risky computation; recover with a default on panic.
(defn safe-div [a b]
  (match (catch-runtime-error (fn [] (div-i64 a b)))
    [(Ok q)  q
     (Err _) 0]))            ; division by zero panicked — recover with 0
```

Standard library convenience functions (e.g., `format-test-run`, `failures-only`, `test-passed?`) MAY be provided in a `core.testing` module but are not required by this specification.

### 16.6 Availability by Invocation Mode [S122]

`discover-tests` is a test-harness capability, available only in the REPL. It
is not available under `--run`, `--link` or `--test`. Under `--test` the
compiler discovers and runs the tests itself (§0.2.2). [Tested+Neg tests/spec_12_runtime::discover_tests_and_catch_runtime_error_user_composition, tests/test_runner.rs::batch_modes_neg_refuse_uncalled_discover_tests_reference_with_one_diagnostic, tests/test_runner.rs::test_mode_runs_every_test_reports_fq_lines_and_matches_run_tests — the REPL calls it; `--run`, `--link` and `--test` refuse it; `--test` runs the tests without it]

Under `--run`, `--link` and `--test`, a program in which any function compiled
for the program references `discover-tests` MUST be rejected before any code
executes or any artifact is written, whether or not that function is ever
called. The
diagnostic MUST name `discover-tests` and a function that references it. Its
remedy MUST name the REPL as where `discover-tests` is available, and MUST
name `--test` (§0.2.2) only as the way to have the compiler discover and run
the program's tests, not as a mode in which `discover-tests` can be called.
The process exits with a non-zero status. An `import` of the name alone is not
a reference and is not rejected. [Tested+Neg tests/test_runner.rs::batch_modes_neg_refuse_uncalled_discover_tests_reference_with_one_diagnostic, tests/test_runner.rs::run_neg_refuses_discover_tests_reference_restored_from_cache, tests/test_runner.rs::batch_modes_accept_import_only_of_discover_tests, tests/link.rs::link_module_referencing_discover_tests_extern_fails_with_friendly_message — an uncalled reference, including one in an imported module and one in a cache-restored body, is refused with exit 1 before `main` runs, an executable is written or a report is printed; one diagnostic, identical in the three modes, names `discover-tests`, the referencing function, the REPL and `--test`; an import alone is accepted. The remedy's phrasing is matched by substring against its single source in `src/exe.rs`, not asserted as a phrase. A reference in a macro clause executed during expansion is unevidenced (design/int/test-runner.md §12)]

`catch-runtime-error` is not a test-harness capability. It is a self-contained
runtime combinator and works in every mode, including `--link`. [Tested tests/spec_12_runtime::catch_runtime_error_err_arm_run, tests/spec_12_runtime::catch_runtime_error_err_arm_link — `--run` and `--link`]
