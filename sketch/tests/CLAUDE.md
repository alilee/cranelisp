# Tests

## Running Tests

- `just test` runs all tests (~930 total). Takes ~2 minutes with default parallelism.
- When debugging failures, run individual tests: `cargo test --test integration test_name -- --nocapture 2>&1`
- `just test` builds platform DLLs first (required for integration tests).

## Test Files

- `tests/integration.rs` — ~470 integration tests (batch + REPL)
- `tests/rc.rs` — reference counting tests (serial, `--test-threads=1`)
- `tests/platform.rs` — platform DLL loading tests
- `tests/test_prelude.cl` — trimmed prelude for test fixtures (no macros/Sexp/macro helpers)
- `src/unittest_prelude.cl` — trimmed prelude for unit tests

## Batch Test Helpers

Three compile helpers for batch-mode tests, from fastest to most capable:

- **`compile_and_run_simple(src)`** — No macro expansion. For tests that don't use prelude macros (`list`, `cond`, `do`, `bind!`, `vec`, `str`, `->`, `->>`, `case`, `derive`, `const`, `def`). ~0.1s per test.
- **`compile_and_run(src)`** — Uses a shared global macro session (prelude loaded once per process). For tests that use prelude macros but don't define their own. ~0.4s per test after first use.
- **`compile_and_run_with_macros(src)`** — Uses the shared macro session + handles user `defmacro` forms with `begin` flattening and defmacro-in-results. For tests that define custom macros. ~0.4s per test.

When writing new tests, use `compile_and_run_simple` unless the test source uses macros.
