# tests/

Integration tests, E2E tests, and performance benchmarks for the Cranelisp reimplementation. Owned by `/qa`.

## Test Book

The test strategy, risk assessment, and per-ring test plans live in `tests/plan/`:

| File | Contents |
|---|---|
| `plan/strategy.md` | Test strategy: quality model, skill interactions, communication protocol, portability classification |
| `plan/risks.md` | QA risk review: 10 ranked risks with mitigations, spec coverage gaps |
| `plan/ring0.md` | Ring 0 test plan: core expressions, types, functions (~80 tests) |
| `plan/ring1.md` | Ring 1 test plan: heap, ADTs, closures, RC (~130 additional tests) |
| `plan/ring2.md` | Ring 2 test plan: traits, modules, constrained poly (~160 additional tests) |
| `plan/ring3.md` | Ring 3 test plan: macros, prelude, stdlib (~100 additional tests) |
| `plan/ring4.md` | Ring 4 test plan: IO, platforms, REPL, cache, perf (~120 additional tests) |

## Test Methodology

### Test Levels

1. **Unit tests** (`#[cfg(test)] mod tests` in source crates) — owned by each compiler skill, not by `/qa`
2. **Integration tests** (`tests/ring*/`) — owned by `/qa`, validate pipeline end-to-end
3. **E2E transcript tests** (`tests/ring4/e2e.rs`) — validate REPL output against expected transcripts
4. **Performance benchmarks** (`tests/ring4/perf.rs`) — track regression against prototype baselines

### Test Helpers

| Helper | Description | Available from |
|---|---|---|
| `compile_and_run_simple(src)` | No macros. Parse → AST → typecheck → codegen → execute. | Ring 0 |
| `compile_and_run(src)` | Shared prelude session with macros. | Ring 3 |
| `compile_and_run_with_macros(src)` | Shared session + user defmacro compilation. | Ring 3 |
| `repl_session()` | Creates a REPL session for interactive-mode tests. | Ring 0 |
| `compile_both(src)` | Runs in both batch and REPL, asserts identical results. | Ring 0 |
| `assert_type_error(src, msg_substr)` | Asserts compilation fails with a type error containing `msg_substr`. | Ring 0 |
| `assert_parse_error(src, msg_substr)` | Asserts parsing fails with a parse error containing `msg_substr`. | Ring 0 |
| `assert_rc_balanced(src)` | Compiles, runs with RC tracing, asserts all allocs are freed. | Ring 1 |

When writing new tests, use `compile_and_run_simple` unless the test source uses macros.

### Test File Organization

```
tests/
  CLAUDE.md              — this file: methodology, standards, plan index
  plan/                  — test book (strategy, risks, per-ring plans)
  ring0/
    batch.rs             — batch-mode integration tests (expressions, types, functions)
    repl.rs              — REPL-mode integration tests
    errors.rs            — error path tests (parse errors, type errors)
  ring1/
    batch.rs             — ADT, string, closure tests (batch)
    repl.rs              — ADT, string, closure tests (REPL)
    rc.rs                — reference counting correctness tests (serial)
  ring2/
    modules.rs           — module graph, imports, visibility, exports
    traits.rs            — trait dispatch, constrained poly, monomorphisation
    repl.rs              — REPL module navigation, trait introspection
  ring3/
    macros.rs            — macro compilation, expansion, quasiquote
    prelude.rs           — prelude macro tests (list, vec, cond, case, threading)
    stdlib.rs            — standard library tests
  ring4/
    io.rs                — IO model, platform calls, par-let, par-bind!
    e2e.rs               — transcript tests
    trace.rs             — execution tracing tests
    run_tests.rs         — run-tests special form
    platform.rs          — platform DLL loading
    cache.rs             — module caching and invalidation
    repl_commands.rs     — slash command smoke tests
    perf.rs              — performance benchmarks
  helpers/
    mod.rs               — shared test helpers (compile_and_run_simple, etc.)
  fixtures/
    test_prelude.cl      — trimmed prelude for test fixtures
```

### Test Standards

- **Test names describe behavior, not implementation.** `test_let_polymorphism_infers_identity` not `test_case_47`.
- **Every language-behavior test runs in both batch and REPL.** Use `compile_both()` or write separate batch/REPL variants.
- **RC tests run serially.** Mark RC test files with `#[serial]` or document `--test-threads=1`.
- **Error tests use substring matching.** `assert_type_error(src, "expected Int")` — not exact message comparison.
- **No test is silently dropped.** Every prototype test gets a disposition (port, adapt, rewrite) in the test plan.
- **Each ring is a regression gate.** All prior ring tests must pass before advancing.

### Build Commands

```bash
# Run all tests (once workspace exists)
cargo test

# Run a specific ring's tests
cargo test --test ring0_batch

# Run RC tests serially
cargo test --test ring1_rc -- --test-threads=1

# Run ignored tests (panic-path tests)
cargo test -- --ignored --test-threads=1

# Run with RC tracing
CRANELISP_RC_TRACE=1 cargo test --test ring1_rc -- --test-threads=1
```

### Adding Tests

1. Identify the ring: which features does the test exercise?
2. Choose the right file within that ring (batch, repl, errors, rc, etc.)
3. Choose the right helper (`compile_and_run_simple` for non-macro tests)
4. Name the test after the behavior being validated
5. Add both batch and REPL variants for language-behavior tests
6. If porting from prototype, note the original test name in a comment

### Prototype Test Oracle

The prototype's tests serve as acceptance criteria:

```bash
# Run the prototype's test suite for comparison
cd sketch && just test

# Run a specific prototype test
cd sketch && cargo test --test integration test_name -- --nocapture
```

See `sketch/tests/CLAUDE.md` for prototype test conventions.
