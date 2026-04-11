# Continue: REPL Module Rework

## Completed

- **Phase 1-3**: FileWatcher integration, error_modules, src/repl/ deletion — all done
- **Expr::Trace AST fix**: AST builder produces Expr::Trace directly, name-based interception removed
- **Expr::RunTests deletion**: removed from AST, all crates cleaned up (~420 lines deleted)
- **Trace infrastructure**: build_traced_fns, repl_trace_format, TraceDisplayState, program_needs_trace
- **Spec updates**: trace scope (§4.12.3), TestResult type (§3.2.5), test forms (appendix-a §A.4), REPL test commands (repl/spec.md §16)

## Current: Test Infrastructure Implementation

### Design (specced)

Three special forms + one root type:

```clojure
(deftype TestResult
  (TestPass [:String name :Int nanos])
  (TestFail [:String name :Int nanos :String reason])
  (TraceFail [:String name :Int nanos :String reason :Trace trace]))

(discover-tests)              ;; => :(IO (SList Sexp))
(discover-tests user.math)    ;; => :(IO (SList Sexp))
(run-test user/test-add)      ;; => :(IO TestResult) — fast, no tracing
(trace-test user/test-add)    ;; => :(IO TestResult) — with GOT-swap tracing
```

- TestResult is a root type (always in scope)
- discover-tests/run-test/trace-test are special forms (always in scope)
- Arguments: bare module paths / qualified symbols, or Sexp variables
- run-test returns TestPass/TestFail, trace-test returns TestPass/TraceFail

### Architecture Decision

No new Expr variants. All three compile as Expr::Apply to extern Rust functions:
- AST builder recognizes keywords, converts bare symbols to SexpSym constructors
- Typechecker assigns correct types via special-form Def entries
- Backend compiles as normal function calls to externs
- Extern functions use thread-local session state (same pattern as repl_trace_format)

### Implementation Steps

1. **Seed TestResult type** in builtins.rs (3 constructors, field accessors)
2. **Register discover-tests/run-test/trace-test** as special form Def entries in builtins.rs
3. **AST builder handlers** for keyword recognition + bare symbol conversion
4. **Implement extern functions** in session_v4.rs with thread-local state:
   - discover_tests_extern: scan symbol tables
   - run_test_extern: call test fn, interpret result, build TestResult
   - trace_test_extern: GOT swap + call + restore + trace collect + build TestResult
5. **Register externs as JIT symbols** in codegen_and_execute
6. **Rewire /run-tests**: run fast, re-run failures with tracing
7. **Add /run-all-tests**: all project-root modules

### Slash Commands

- `/run-tests [module]` (`/rt`): discover + run-test (fast), re-run failures with trace-test
- `/run-all-tests`: all project-root modules, same fast+trace pattern

## Verification

```bash
cargo nextest run -E "binary(ring0)" --max-fail 3
cargo nextest run -E "binary(v4_repl_eval)" --max-fail 3
cargo nextest run -E "binary(ring0) | binary(ring1) | binary(ring2) | binary(ring3_repl) | binary(macros) | binary(modules) | binary(v4_pipeline) | binary(v4_repl_eval) | binary(rc)" --no-fail-fast
```

Pre-existing failures (24 total): 2 ring0, 4 macros, ~18 modules/ring2/v4_pipeline.
