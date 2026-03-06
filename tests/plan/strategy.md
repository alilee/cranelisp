# Test Strategy

How `/qa` manages quality across the Cranelisp reimplementation.

## Core Principle

`/qa` is not a test porter. `/qa` is the authority that defines what the compiler must provide for testability, specifies the observability requirements for each skill, and owns the test pyramid from boundary tests upward. The prototype's tests are acceptance criteria, not the test design.

## Quality Model

Quality has five dimensions:

1. **Correctness**: does the compiler produce the right output for every input?
2. **Parity**: do batch and REPL produce identical results for identical input?
3. **Soundness**: are memory, types, and modules internally consistent?
4. **Observability**: can failures be diagnosed without a debugger?
5. **Usability**: is the language and environment simple and powerful enough for real software delivery?

Each ring must satisfy all five before the next ring begins. `/review` gates ring transitions.

---

## Test Pyramid

Four layers, from fastest/narrowest to slowest/broadest:

### Layer 1: Unit Tests (stage internals)

**Owned by**: each compiler skill (`/frontend`, `/typecheck`, `/backend`)

**Location**: `#[cfg(test)] mod tests` inside each source module

**What they test**: internal algorithms in isolation — parser combinators, unification steps, IR emission for individual expression forms, RC inc/dec emission patterns, scope push/pop correctness.

**QA's role**: `/qa` does not write these, but **specifies minimum coverage requirements** per ring. Each ring plan lists which internal behaviors must have unit tests before the ring gate passes. `/qa` reviews unit test coverage at ring gates.

**Minimum coverage requirements**:
- Every `Expr` variant has at least one unit test in both typecheck and codegen
- Every error path that returns `CranelispError` has a unit test that triggers it
- Every `debug_assert!` has a companion unit test that exercises the asserted invariant

### Layer 2: Boundary Tests (contract verification)

**Owned by**: `/qa`

**Location**: `tests/boundary/`

**What they test**: the data that crosses crate boundaries matches the contracts in `design/arch/interfaces.md`. Each boundary test constructs input for one stage, runs that stage, and validates the output type/structure — without running the full pipeline.

**Examples**:
- Reader produces well-formed `Sexp` with correct spans for all syntactic forms
- AST builder produces the right `Expr` variant for each `Sexp` pattern
- TypeChecker produces `CheckResult` with correct `expr_types` for known inputs
- Codegen produces executable code that returns correct values for hand-constructed typed AST
- `SymbolTable` entries have correct visibility, schemes, and DefKind after type checking

**Why this layer matters**: boundary tests catch interface misunderstandings between skills *before* integration. If `/frontend` produces `Sexp::List` where `/typecheck` expects `Sexp::Bracket`, a boundary test catches it without wiring the full pipeline.

### Layer 3: Integration Tests (pipeline verification)

**Owned by**: `/qa`

**Location**: `tests/integration/`

**What they test**: stages wired together via `compile_unit()`, exercising the full pipeline from source text to execution result. These call Rust APIs (not the binary) and can inspect intermediate state.

**Sub-categories**:
- **Batch mode**: `compile_and_run_simple(src)` → assert result value
- **REPL mode**: `repl_session()` → define, eval, assert
- **Dual-mode**: `compile_both(src)` → assert batch and REPL agree
- **Error paths**: `assert_type_error(src, msg)`, `assert_parse_error(src, msg)`
- **RC correctness**: `assert_rc_balanced(src)` — serial, with allocation tracking
- **Module graph**: multi-file compilation with imports, exports, visibility

**Relation to prototype tests**: most of the ~591 prototype tests map to this layer. They are acceptance criteria — the expected source/result pairs are ported, but the test harness and helpers are new.

### Layer 4: E2E Tests (black-box verification)

**Owned by**: `/qa`

**Location**: `tests/e2e/`

**What they test**: the `cranelisp` binary invoked as a subprocess, checking stdout, stderr, and exit code. No Rust APIs. No internal state inspection. This is what the user sees.

**Sub-categories**:
- **Batch programs**: `cranelisp --run file.cl` → check stdout + exit code
- **REPL sessions**: scripted stdin → check stdout line-by-line
- **Compiler errors**: invalid programs → check stderr contains useful error message + exit code != 0
- **Module projects**: multi-file projects → `cranelisp --run main.cl` → check output
- **Executable generation**: `cranelisp --compile file.cl` → run generated binary → check output
- **Performance**: wall-clock timing of representative programs

**Why this layer matters**: E2E tests are the **release gate**. They are independent of all internal structure. If every crate is rewritten, renamed, or restructured, E2E tests still pass as long as the user experience is correct. They are the only tests that survive a hypothetical second reimplementation.

**E2E test format**: each test is a directory containing:
```
tests/e2e/cases/
  factorial/
    input.cl           — source file(s)
    expected_stdout     — expected stdout (or stdout_contains for substring match)
    expected_exit       — expected exit code (default: 0)
  repl_basic/
    input.session       — scripted REPL input (one line per command)
    expected_output     — expected REPL output (line-by-line or pattern match)
  type_error/
    input.cl
    expected_stderr     — expected error message (substring match)
    expected_exit       — 1
```

A test runner iterates over `tests/e2e/cases/`, invokes the binary, and asserts. This runner is simple enough to write in shell or Rust, and it is entirely decoupled from compiler internals.

---

## Diagnostic Requirements

`/qa` specifies observability hooks that compiler skills **must implement**. These are not tests — they are infrastructure that makes tests (and debugging) possible.

### Runtime Assertions

Every skill must use `debug_assert!` for internal invariants that should never be violated. These fire during test runs (debug builds) but are compiled out in release. `/qa` requires:

| Skill | Required Assertions |
|---|---|
| `/frontend` | Span monotonicity (child spans within parent), no empty symbol names, bracket/paren nesting consistency |
| `/typecheck` | No unresolved `Var` in `CheckResult.expr_types`, substitution idempotency after unification, scheme vars are a subset of free vars in the type, no duplicate entries in `MethodResolutions` |
| `/backend` | GOT slot uniqueness within a module, stack balance at function boundaries (push count == pop count), no code emission after function finalization, RC inc/dec balance within a scope (debug mode) |
| `/runtime` | Allocation size > 0, RC never goes negative, no double-free (tracked via `LIVE_ALLOCS` set in debug mode) |

### Diagnostic Logging

Controlled by environment variables. Silent by default. `/qa` requires these knobs:

| Variable | Skill | What it shows |
|---|---|---|
| `CRANELISP_RC_TRACE=1` | `/backend` + `/runtime` | Every alloc, inc, dec, free with pointer + type + location |
| `CRANELISP_INFER_TRACE=1` | `/typecheck` | Unification steps, constraint generation, instantiation, generalization |
| `CRANELISP_CODEGEN_TRACE=1` | `/backend` | CLIF IR for each function before/after optimization |
| `CRANELISP_MODULE_TRACE=1` | `/qa` (binary crate) | Module discovery, compile order, import resolution, cache hits/misses |
| `CRANELISP_MACRO_TRACE=1` | `/frontend` + binary | Macro expansion steps, input sexp → output sexp |

These are not test infrastructure — they are diagnostic infrastructure that `/qa` uses to write better tests and diagnose failures. Each skill implements its own trace points; `/qa` specifies what must be traceable.

### Structured Intermediate State

Each pipeline stage must expose its intermediate output for inspection in tests:

| Stage | Inspectable Output | How |
|---|---|---|
| Reader | `Vec<Sexp>` | `Frontend::parse(src) -> Result<Vec<Sexp>>` |
| AST Builder | `Vec<TopLevel>` | `Frontend::build(sexps) -> Result<Vec<TopLevel>>` |
| Macro Expander | expanded `Vec<Sexp>` | `MacroExpander::expand_all(sexps) -> Result<Vec<Sexp>>` |
| TypeChecker | `CheckResult` + updated `SymbolTable` | `TypeChecker::check(program) -> Result<CheckResult>` |
| Codegen | CLIF IR string, disassembly | `Backend::compile(program, check_result) -> Result<CompileResult>` |
| Execution | raw `i64` result | `Backend::execute(symbol) -> Result<i64>` |

Boundary tests exercise these interfaces directly. Integration tests use the composed `compile_unit()`.

---

## Skill Interaction Model

### What /qa demands from each skill

```
Skill          /qa Demands                       /qa Provides Back
─────────────  ───────────────────────────────── ─────────────────────────────────
/frontend      Inspectable Sexp/AST output       Boundary tests for reader + AST
               debug_assert! on span invariants  Parse error quality reports
               CRANELISP_MACRO_TRACE support     Macro expansion regression tests

/typecheck     Inspectable CheckResult           Boundary tests for inference
               debug_assert! on type invariants  Type error quality reports
               CRANELISP_INFER_TRACE support     Cross-module inference tests
               No unresolved Var in output       Constrained-poly regression tests

/backend       Inspectable CLIF IR + disasm      Boundary tests for codegen
               debug_assert! on GOT + RC         RC correctness test results
               CRANELISP_RC_TRACE support        Performance measurements
               CRANELISP_CODEGEN_TRACE support   Panic handler requirements
               Recoverable panic (not exit(1))   Codegen regression tests

/runtime       LIVE_ALLOCS tracking in debug     RC balance verification
               debug_assert! on RC invariants    Double-free detection
               No undefined behavior in alloc    Memory safety verification

/arch          Testable crate boundaries         Ring gate test reports
               compile_unit() single entry       Boundary test coverage data
               CompileMode for batch/REPL        Parity verification

/platform      test-capture platform DLL         Platform loading tests
               Deterministic test IO             IO integration tests

/spec          Testable examples in every        Test-to-spec coverage mapping
               spec section                      Spec gap reports
```

### Communication Protocol

1. **Diagnostic request**: `/qa` specifies a diagnostic requirement (e.g., "typecheck must expose `CRANELISP_INFER_TRACE`"). The owning skill implements it. `/qa` validates the diagnostic output is useful.

2. **Test failure triage**: When a test fails, `/qa` identifies the layer (boundary, integration, E2E) and the responsible skill. Diagnostic logging narrows the root cause.

3. **Ring gate**: At ring completion, `/qa` produces a test report:
   - Unit test coverage: per-crate, per-module
   - Boundary tests: all boundary contracts verified (yes/no)
   - Integration tests: N passing, M failing, K skipped
   - E2E tests: all black-box tests pass (yes/no)
   - RC balance: all allocation tracking clean (yes/no)
   - Parity: batch and REPL agree on all tests (yes/no)
   - Runtime assertions: no debug_assert! fires during any test run (yes/no)
   - Usability: no blocking `FIXME` findings from user-proxy skills open (yes/no)
   - Regressions: any prior-ring tests broken (yes/no)

4. **Feedback to /spec**: When a test reveals ambiguous behavior, `/qa` reports to `/spec` with the test source, expected behavior, and actual behavior.

5. **Usability feedback**: User-proxy skills (`/stdlib`, `/examples`, `/docs`, `/port`, `/repl`, `/platform`) file usability findings as `FIXME(/skill-name)` comments on the relevant spec or design doc — the same cross-skill FIXME protocol used by all skills.

---

## Pipeline Wiring Responsibility

`/qa` owns the pipeline orchestration — wiring frontend, typecheck, and backend into a working compiler:

- **Ring 0**: `/qa` writes `compile_unit()` in the binary crate, connecting `cranelisp-frontend` → `cranelisp-typecheck` → `cranelisp-backend`.
- **Ring 2**: `/qa` extends `compile_unit()` with module graph discovery and ordered compilation.
- **Ring 3**: `/qa` implements the `MacroExpander` trait in the binary crate.
- **Ring 4**: `/qa` adds caching, linking, REPL session management, and file watching.

Each compiler skill implements its crate in isolation against interface stubs. `/qa` is the first to connect real implementations and the first to discover interface mismatches.

---

## Test Portability (from prototype)

The prototype's 591 tests are acceptance criteria, not the test design. They map to test pyramid layers:

| Prototype Source | Reimplementation Layer | Count |
|---|---|---|
| `integration.rs` batch tests | Integration (Layer 3) | ~300 |
| `integration.rs` REPL tests | Integration (Layer 3) | ~120 |
| `integration.rs` error tests | Integration (Layer 3) + E2E (Layer 4) | ~20 |
| `integration.rs` example files | E2E (Layer 4) | ~16 |
| `integration.rs` cache tests | Integration (Layer 3) | ~15 |
| `integration.rs` module tests | Integration (Layer 3) | ~35 |
| `rc.rs` | Integration (Layer 3) — serial, with diagnostics | 57 |
| `trace.rs` | Integration (Layer 3) | 14 |
| `run_tests.rs` | Integration (Layer 3) | 9 |
| `platform.rs` | Integration (Layer 3) | 9 |
| `e2e/*.cl/*.out` | E2E (Layer 4) | 4 |

**New tests not in prototype** (per layer):
- **Boundary**: contract tests for every crate boundary (none exist in prototype)
- **Integration**: dual-mode parity tests, cross-module RC tests
- **E2E**: compiler error output tests, multi-file project tests, `--compile` tests, performance benchmarks

---

## Performance Baselines

Capture before Ring 0, running against the prototype:

| Metric | How to Measure | Target |
|---|---|---|
| Reader throughput | Parse `lib/prelude.cl` + `lib/core/*.cl` | Within 2x of prototype |
| Type inference time | Check all example files | Within 2x of prototype |
| Codegen time | Compile all example files | Within 2x of prototype |
| Test suite total | `just test` wall clock | Within 2x of prototype |
| REPL startup | Time to first prompt | <500ms |
| Expression eval | `(+ 1 2)` at REPL | <100ms |

E2E performance tests verify these on every ring.
