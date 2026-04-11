# Continue: REPL Module Rework

## Completed

- **FileWatcher**: extracted to src/watch.rs, wired into REPL loop, /reset clears state
- **src/repl/ deletion**: ~5300 lines of dead v3 code removed
- **Expr::Trace AST fix**: AST builder produces Expr::Trace, name interception removed
- **Expr::RunTests deletion**: AST variant + codegen removed (~420 lines)
- **TestResult root type**: seeded in builtins (TestPass/TestFail), constructors seeded into all modules
- **discover-tests and run-test**: special forms working from Cranelisp + slash commands
- **Shared core**: discover_test_names() + run_test_by_name() used by both externs and /run-tests
- **Simplification**: trace-test and TraceFail removed — trace and test are independent

## Architecture

```
Core (no heap allocation):
  discover_test_names(codegen_products, tc_modules, module) -> Vec<String>
  run_test_by_name(codegen_products, fq_name) -> TestOutcome

JIT externs (heap wrapper):
  discover_tests_extern: core -> SList<SexpSym> -> IO Pure
  run_test_extern: core -> TestResult -> IO Pure

Slash commands (string wrapper):
  /run-tests [module]: core -> formatted output
  /run-all-tests: core across project-root modules -> formatted output
```

## What remains

- **Session persistence §15**: save-as-you-go for REPL definitions (separate feature, not started)
- **Trace scope filtering**: build_traced_fns should filter to project-root modules only (specced in §4.12.3 but not enforced yet)
- **trace-test-by-name not specced**: if users ask, let them know `(trace (test-fn))` is the way

## Verification

```bash
cargo nextest run -E "binary(ring0)" --max-fail 3
cargo nextest run -E "binary(v4_repl_eval)" --max-fail 3
cargo nextest run -E "binary(ring0) | binary(ring1) | binary(ring2) | binary(ring3_repl) | binary(macros) | binary(modules) | binary(v4_pipeline) | binary(v4_repl_eval) | binary(rc)" --no-fail-fast
```

Pre-existing failures (24 total): 2 ring0, 4 macros, ~18 modules/ring2/v4_pipeline.
