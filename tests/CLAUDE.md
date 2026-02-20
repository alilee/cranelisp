# Tests

## Running Tests

- **Never run the full integration test suite without capturing output.** It takes many minutes. Always use `2>&1 | tee /tmp/test-output.txt` or redirect to a file so you can inspect failures without rerunning.
- When debugging failures, run individual tests: `cargo test --test integration test_name -- --nocapture 2>&1`
- Only rerun the full suite when you expect all tests to pass.
- `just test` builds platform DLLs first (required for integration tests).

## Test Files

- `tests/integration.rs` — ~400 integration tests (batch + REPL)
- `tests/rc.rs` — reference counting tests (serial, `--test-threads=1`)
- `tests/platform.rs` — platform DLL loading tests
- `tests/test_prelude.cl` — trimmed prelude for test fixtures (no macros/Sexp/macro helpers)
- `src/unittest_prelude.cl` — trimmed prelude for unit tests
