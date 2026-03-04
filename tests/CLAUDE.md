# tests/

Test infrastructure for the Cranelisp reimplementation. Owned by `/qa`.

## Test Book

The test strategy, risk assessment, and per-ring test plans live in `tests/plan/`:

| File | Contents |
|---|---|
| `plan/strategy.md` | Test strategy: quality model, test pyramid, diagnostic requirements, skill demands, usability register |
| `plan/risks.md` | QA risk review: 10 ranked risks with mitigations, spec coverage gaps |
| `plan/ring0.md` | Ring 0 test plan: core expressions, types, functions |
| `plan/ring1.md` | Ring 1 test plan: heap, ADTs, closures, RC |
| `plan/ring2.md` | Ring 2 test plan: traits, modules, constrained poly |
| `plan/ring3.md` | Ring 3 test plan: macros, prelude, stdlib |
| `plan/ring4.md` | Ring 4 test plan: IO, platforms, REPL, cache, perf |

## Test Pyramid

Four layers, from fastest/narrowest to slowest/broadest. See `plan/strategy.md` for full details.

### Layer 1: Unit Tests (stage internals)

**Owned by**: each compiler skill. **Location**: `#[cfg(test)] mod tests` in source crates.

Tests internal algorithms in isolation. `/qa` specifies minimum coverage requirements per ring but does not write these tests. Every `Expr` variant, every error path, and every `debug_assert!` must have a companion unit test.

### Layer 2: Boundary Tests (contract verification)

**Owned by**: `/qa`. **Location**: `tests/boundary/`.

Tests data crossing crate boundaries against `design/arch/interfaces.md`. Each test constructs input for one stage, runs that stage alone, and validates the output structure — without running the full pipeline. Catches interface misunderstandings between skills.

### Layer 3: Integration Tests (pipeline verification)

**Owned by**: `/qa`. **Location**: `tests/integration/`.

Stages wired together via `compile_unit()`, from source text to execution result. Calls Rust APIs and can inspect intermediate state. Most prototype tests map here.

### Layer 4: E2E Tests (black-box verification)

**Owned by**: `/qa`. **Location**: `tests/e2e/`.

The `cranelisp` binary invoked as a subprocess. No Rust APIs. Checks stdout, stderr, exit code. **This is the release gate.** E2E tests survive any internal restructuring — they verify the user experience, not the implementation.

## Diagnostic Requirements

`/qa` specifies observability that compiler skills **must implement**. See `plan/strategy.md` §"Diagnostic Requirements" for full details.

### Runtime Assertions

`debug_assert!` for invariants in every skill. Fire during test runs (debug builds), compiled out in release. Examples: span monotonicity, no unresolved type vars in output, GOT slot uniqueness, RC never negative.

### Diagnostic Logging

Controlled by environment variables, silent by default:

| Variable | Shows |
|---|---|
| `CRANELISP_RC_TRACE=1` | Every alloc, inc, dec, free with pointer + type |
| `CRANELISP_INFER_TRACE=1` | Unification steps, constraint generation |
| `CRANELISP_CODEGEN_TRACE=1` | CLIF IR before/after optimization |
| `CRANELISP_MODULE_TRACE=1` | Module discovery, compile order, cache hits |
| `CRANELISP_MACRO_TRACE=1` | Macro expansion steps |

## Usability Register

`/qa` maintains a usability register (`tests/plan/usability.md`) — the structured destination for findings from user-proxy skills (`/stdlib`, `/examples`, `/docs`, `/port`, `/repl`, `/platform`). These skills file corner cases, unhelpful errors, inference friction, missing APIs, and ergonomic issues they encounter while exercising the language. See `plan/strategy.md` §"Usability Register" for the full process.

Findings are triaged as **blocking** (must fix before ring advance), **important** (should fix), or **deferred**. Blocking findings are part of the ring gate — a ring cannot advance with open blocking usability findings.

## Test File Organization

```
tests/
  CLAUDE.md              — this file
  plan/                  — test book (strategy, risks, per-ring plans, usability register)
  boundary/              — Layer 2: crate boundary contract tests
    reader.rs            — Sexp output structure and spans
    ast_builder.rs       — Expr/TopLevel from Sexp
    typecheck.rs         — CheckResult from AST
    codegen.rs           — compiled code from typed AST
  integration/           — Layer 3: pipeline integration tests
    ring0.rs             — core expressions, types, functions
    ring1.rs             — ADTs, strings, closures, RC
    ring2.rs             — traits, modules, constrained poly
    ring3.rs             — macros, prelude, stdlib
    ring4.rs             — IO, platforms, cache, REPL commands
    rc.rs                — RC correctness tests (serial)
    errors.rs            — error path tests across all rings
  e2e/                   — Layer 4: black-box subprocess tests
    runner.rs            — test runner (iterate cases, invoke binary, assert)
    cases/               — one directory per test case
      factorial/
        input.cl
        expected_stdout
      repl_basic/
        input.session
        expected_output
      type_error/
        input.cl
        expected_stderr
        expected_exit
  helpers/
    mod.rs               — shared test helpers
  fixtures/
    test_prelude.cl      — trimmed prelude for test fixtures
```

## Test Helpers

| Helper | Layer | Description | Available from |
|---|---|---|---|
| `compile_and_run_simple(src)` | Integration | No macros. Full pipeline. | Ring 0 |
| `compile_and_run(src)` | Integration | Shared prelude session with macros. | Ring 3 |
| `compile_and_run_with_macros(src)` | Integration | Shared session + user defmacro. | Ring 3 |
| `repl_session()` | Integration | Creates a REPL session. | Ring 0 |
| `compile_both(src)` | Integration | Batch + REPL, assert identical. | Ring 0 |
| `assert_type_error(src, msg)` | Integration | Assert type error with substring. | Ring 0 |
| `assert_parse_error(src, msg)` | Integration | Assert parse error with substring. | Ring 0 |
| `assert_rc_balanced(src)` | Integration | Compile + run with RC tracing. | Ring 1 |
| `run_binary(args, stdin)` | E2E | Invoke `cranelisp` subprocess. | Ring 0 |
| `assert_output(case_dir)` | E2E | Check stdout/stderr/exit against expected. | Ring 0 |

## Test Standards

- **Test names describe behavior, not implementation.** `test_let_polymorphism_infers_identity` not `test_case_47`.
- **Every language-behavior test runs in both batch and REPL.** Use `compile_both()` or write separate variants.
- **RC tests run serially.** Use `--test-threads=1` for any test that reads `CRANELISP_RC_TRACE`.
- **Error tests use substring matching.** Not exact message comparison.
- **Boundary tests test one stage at a time.** No full-pipeline invocations in boundary tests.
- **E2E tests invoke the binary.** No Rust API calls. No internal state inspection.
- **Each ring is a regression gate.** All prior-ring tests at all layers must pass before advancing.
- **No test is silently dropped.** Every prototype test gets a disposition in the ring plans.

## Build Commands

```bash
# Run all tests
cargo test

# Run a specific layer
cargo test --test boundary_reader        # boundary
cargo test --test integration_ring0      # integration
cargo test --test e2e_runner             # E2E

# Run RC tests serially
cargo test --test integration_rc -- --test-threads=1

# Run with diagnostics
CRANELISP_RC_TRACE=1 cargo test --test integration_rc -- --test-threads=1
CRANELISP_INFER_TRACE=1 cargo test --test boundary_typecheck -- --nocapture

# Run E2E tests only (release gate)
cargo test --test e2e_runner
```

## Adding Tests

1. **Choose the layer**: Is this testing one stage's output (boundary), the pipeline (integration), or the user experience (E2E)?
2. **Choose the file**: within that layer, by ring or by concern
3. **Choose the helper**: `compile_and_run_simple` for integration, `run_binary` for E2E
4. **Name the test**: after the behavior being validated
5. **Add dual-mode**: for language-behavior integration tests, test both batch and REPL
6. **Note provenance**: if porting from prototype, note the original test name in a comment

## Prototype Test Oracle

The prototype's tests are acceptance criteria:

```bash
cd sketch && just test                                           # full suite
cd sketch && cargo test --test integration test_name -- --nocapture  # one test
```

See `sketch/tests/CLAUDE.md` for prototype test conventions.
