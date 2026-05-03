# tests/

Test infrastructure for the Cranelisp reimplementation. Owned by `/qa`.

## Plan documents

| File | Purpose |
|---|---|
| `plan/PLAN.md` | **Normative**: spec → tests bridge. The plan obligation per `qa.md`. |
| `plan/helpers.md` | E2E helper API design (`tests/helpers/`). |
| `plan/ledger.md` | Failure ledger (renamed from `baseline.md` 2026-05-03). |
| `plan/risks.md` | Qualitative risk register. |
| `plan/coverage-gaps.md` | Per-crate coverage analysis. |
| `plan/negative-coverage.md` | `[Tested]` → `[Tested+Neg]` upgrade register. |
| `plan/legacy/` | Superseded plans (rings, four-layer strategy, S61 retros). Provenance only. |

## Two tiers, no middle

Cranelisp tests fall into exactly two tiers (strategy pinned 2026-05-03,
recorded in `memory/project_test_strategy.md`):

1. **e2e tests** — `tests/`, owned by `/qa`. Run the `cranelisp` exe
   directly: REPL via stdin, `--run file.cl`, or `--link` then run the
   produced binary. Helpers are process-spawn + stdin/stdout capture +
   isolated tmpdir + on-disk fixture files. See `plan/helpers.md` for
   the harness API. **This is the release gate.**

2. **Unit tests** — `crates/{crate}/src/` `#[cfg(test)]` modules,
   owned by `/dev` for that crate (per
   `memory/feedback_unit_tests_with_dev.md`). `/qa` does not author
   these.

There is **no middle integration tier.** Tests do NOT construct
`Sess`, `SharedState`, `SymbolTable`, or any other internal session
primitive. If a feature cannot be expressed e2e, that is a gap in the
binary's testability surface — file an `/int` or `/arch` FIXME, do
not bridge with an internal-API helper.

The earlier four-layer pyramid (unit → boundary → integration → e2e)
is preserved at `plan/legacy/strategy.md` for provenance but is NOT
authoritative. The current `tests/helpers/mod.rs::ReplSession` is a
back-compat shim for ~30 pre-existing test files; it is **frozen**
(no new methods, no new entry points). New tests use the e2e helper
API in `plan/helpers.md`. Existing integration-tier tests are
rewritten as e2e on touch (typically when an internal-API change
breaks them), not en masse.

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

## Test file organisation (current shape)

```
tests/
  CLAUDE.md              — this file
  plan/                  — PLAN.md + helpers.md + ledger.md + risks/coverage/neg + legacy/
  helpers/
    mod.rs               — shared helpers (ReplSession back-compat shim + subprocess primitives).
                            New e2e helper surface lives here per plan/helpers.md.
  fixtures/
    prelude.cl           — QA-owned test prelude (Option, Result, Num, Eq, Ord)
    preamble_primitives.cl — bare primitive imports
    stdlib_project/      — read-only project fixture for stdlib conformance tests
    user/, num/, num.cl, reload_target.cl — feature-specific fixtures
  e2e.rs                 — original e2e tests (subprocess-driven; predates helpers.md API)
  e2e/                   — per-suite .runs/ subdirectories (gitignored)
  {topic}.rs             — feature-grouped tests (cache.rs, macros.rs, modules.rs, io.rs,
                            rc.rs, repl_*.rs, stdlib.rs, scheduler.rs, …) — currently a mix of
                            integration-tier (Rust API via ReplSession) and e2e-tier
                            (subprocess); migration to e2e is opportunistic per plan/PLAN.md.
  ring{0..4}.rs, sprint{NN}*.rs, wave{N}_*.rs — historical groupings carried forward
```

The test directory contains both e2e-tier (subprocess-driven) and
integration-tier (Rust-API via `ReplSession`) tests. The two-tier
strategy applies going forward: new tests go in as e2e, integration-tier
files migrate when touched. See `plan/PLAN.md §"Strategy — two tiers,
no middle"`.

## Test Isolation Strategy (Prelude & Stdlib)

Tests MUST NOT depend on `stdlib/`. Only the exemplar (`exemplar/`) and production binary (`src/main.rs`) may use the standard library. The test suite uses its own QA-owned fixtures to validate language features independently.

### Test Prelude Fixture

`tests/fixtures/prelude.cl` is a QA-owned, stable fixture providing:
- **ADTs**: `Option` (None, Some), `Result` (Ok, Err)
- **Traits**: `Num` (+, -, *, /), `Eq` (=, !=), `Ord` (<, >, <=, >=)
- **Impls**: Int, Float for Num/Ord; Int, Float, Bool, String for Eq

This is NOT a copy of `stdlib/prelude.cl` — it is a minimal, stable subset that tests can depend on without coupling to stdlib evolution.

### E2E Test Isolation

E2E tests use two helpers depending on whether they need the prelude:

- **`run_repl(input, label)`** — bare REPL, no prelude loaded. Use for tests of core language features, slash commands, and error handling that don't need operators or ADTs.
- **`run_repl_with_test_prelude(input, label)`** — sets `CRANELISP_LIB=tests/fixtures/` so the binary loads `tests/fixtures/prelude.cl` as the prelude. Use for tests requiring operators (+, -, etc.), Option/Result types, or trait dispatch.

### Integration Test Isolation

Integration tests use two helpers:

- **`repl_session()`** — bare REPL session via Rust API, no prelude.
- **`repl_session_with_test_prelude()`** — REPL session with `tests/fixtures/prelude.cl` loaded via `ReplSession::new_with_prelude()`. Uses the same fixture as E2E tests.

### Inline Trait Preludes (Legacy)

Some older E2E tests define traits inline using constants (`NUM_TRAIT_PRELUDE`, `EQ_TRAIT_PRELUDE`, `ORD_TRAIT_PRELUDE`) at the top of `e2e.rs`. These are still valid but new tests should prefer `run_repl_with_test_prelude()` for consistency and to avoid duplicating trait definitions across tests.

## Test Helpers

| Helper | Layer | Description |
|---|---|---|
| `compile_and_run_simple(src)` | Integration | No macros. Full pipeline. |
| `compile_and_run(src)` | Integration | Shared prelude session with macros. |
| `compile_and_run_with_macros(src)` | Integration | Shared session + user defmacro. |
| `repl_session()` | Integration | Creates a bare REPL session (no prelude). |
| `repl_session_with_test_prelude()` | Integration | REPL session with test prelude (Option, traits). |
| `test_fixtures_dir()` | Both | Path to `tests/fixtures/` directory. |
| `compile_both(src)` | Integration | Batch + REPL, assert identical. |
| `assert_type_error(src, msg)` | Integration | Assert type error with substring. |
| `assert_parse_error(src, msg)` | Integration | Assert parse error with substring. |
| `assert_rc_balanced(src)` | Integration | Compile + run with RC tracing. |
| `run_repl(input, label)` | E2E | Invoke REPL binary with piped stdin (no prelude). |
| `run_repl_with_test_prelude(input, label)` | E2E | Invoke REPL binary with test prelude loaded. |
| `run_binary(args, stdin)` | E2E | Invoke `cranelisp` subprocess. |
| `assert_output(case_dir)` | E2E | Check stdout/stderr/exit against expected. |

The "Available from" Ring column is retired as of Sprint 64 — ring-based
phasing is no longer the project model. The integration-tier helpers above
will be superseded by the new `Cranelisp` builder per `tests/plan/helpers.md`
on opportunistic migration (rewrite-on-touch).

## Test Standards

- **Test names describe behavior, not implementation.** `test_let_polymorphism_infers_identity` not `test_case_47`.
- **Every language-behavior test runs in both batch and REPL.** Use `compile_both()` or write separate variants.
- **RC tests run serially.** Use `--test-threads=1` for any test that reads `CRANELISP_RC_TRACE`.
- **Error tests use substring matching.** Not exact message comparison.
- **Boundary tests test one stage at a time.** No full-pipeline invocations in boundary tests.
- **E2E tests invoke the binary.** No Rust API calls. No internal state inspection.
- **No test is silently dropped.** Every test has a row in `tests/plan/PLAN.md` (or its predecessor `ledger.md`) tracing it to a spec section.
- **Negative tests verify absence, not just presence.** For any MUST requirement that constrains what appears, write a companion test that verifies wrong things are absent. See below.

### Fresh Temp Directory per Test

**Rule**: Tests that write to the filesystem MUST use a fresh
`tempfile::TempDir` per test. Tests MUST NOT write to checked-in paths
(`exemplar/`, `examples/`, `stdlib/`, `tests/fixtures/`, `src/`, …) or
to `project_root()`.

**Why**: Sprint 60 Round 3 discovered that `user.cl` persistence in
the exemplar's working directory accumulated across test runs,
masking a defect's disposition (the "pre-existing" claim was
environmental luck, not truth). Cross-test state pollution also masks
races that fire only under specific filesystem preconditions.

**How to apply**:

- If a test needs a Cranelisp project directory (for `Cranelisp.toml`,
  a module tree, `user.cl`, …), copy the minimal fixture into a fresh
  `TempDir` at the start of the test. See
  `tests/helpers/mod.rs::tempdir_project_from_fixture` for the shared
  helper, or inline a recursive `copy_dir` when the set of source
  files is variable (see `tests/sprint59_defects456_repro.rs::copy_exemplar_tree`).
- If a test is genuinely read-only on checked-in paths, `project_root()`
  is acceptable for locating the binary (`target/debug/cranelisp`),
  the stdlib directory (for `CRANELISP_LIB`), or test fixtures under
  `tests/fixtures/`. When used this way, the callsite MUST carry a
  `// read-only on project_root` comment so future audits can
  distinguish intentional from accidental usage.
- Writes under `tests/{suite}/.runs/{RUN_TS}/{n_label}/` (the
  `e2e.rs::test_dir()` pattern, now also in `tests/helpers/mod.rs::runs_dir`)
  are permitted: the `.runs/` tree is `.gitignore`'d and per-test
  labels provide isolation. Any new suite adopting this pattern MUST
  also add its `.runs/` path to `.gitignore`.
- `tempfile::TempDir` MUST be bound to a variable that lives for the
  duration of the test (`let td = tempfile::tempdir().unwrap();` or
  stored on a helper struct). Dropping the handle before the test ends
  triggers eager cleanup and causes spurious failures under
  concurrent runs.

**Exception**: the `tests/*/.runs/{RUN_TS}/{n_label}/` pattern
(`tests/e2e.rs::test_dir`, `tests/helpers/mod.rs::runs_dir`) is
permitted. It uses `project_root()` to locate the suite's `.runs/`
parent, then allocates an isolated per-test directory under
`.gitignore`. When adopting this pattern in a new test suite, also add
the corresponding `.runs/` path to `.gitignore`.

**CI lint candidate**: a pre-commit check that greps for
`project_root` + `fs::write|fs::create|File::create|Command::.*current_dir`
in the same file, absent the `// read-only` annotation. Sprint 61
Slice 5 E-1 audit found this lint would have flagged `d45_*`, `d6_*`,
`d7_*`, `s60_run_tests_reduction_1_*`, and the default
`ReplSessionBuilder` path — all of which are now converted.

## Negative Test Convention

Positive tests verify correct behavior. Negative tests verify **incorrect behavior does not occur**. Both are required for full coverage — a test suite that only checks "the right thing appears" will pass green while the system also does wrong things.

**Naming**: Negative test names use `_neg_` or `_not_` to distinguish them from positive tests:
```rust
// Positive: /list shows user-defined functions
fn e2e_s3_3_list() { ... }
// Negative: /list does NOT show primitives in user module
fn e2e_s3_3_list_neg_no_primitives_in_user() { ... }
```

**Spec annotation**: When negative tests exist alongside positive tests, the spec annotation upgrades from `[Tested ...]` to `[Tested+Neg ...]`. This makes coverage gaps visible at the spec level.

**Priority areas for negative tests:**
- **Module boundaries**: Symbols from `primitives` must NOT appear as `user/` entries
- **Category boundaries**: `/list` categories must NOT contain items from other categories
- **Error boundaries**: Valid input must NOT produce errors; invalid input must NOT succeed silently
- **Display format**: Output must NOT contain unqualified names where qualified names are required

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

## Isolating Cross-Crate Failures

When an integration test fails and the root cause could be in any crate (typecheck? backend? integration wiring?), follow this process to isolate before fixing. Do NOT guess-and-patch — that creates workarounds that mask the real problem.

### Step 1: Minimal integration test

Write the smallest test that reproduces the failure. Strip everything: no prelude, no stdlib, no imports unless required. Use `repl_session()` (bare session). The test should fail with the same error as the original.

```rust
#[test]
fn repl_defmacro_rest_splice() {
    let mut s = repl_session();
    s.eval("(defmacro my-begin ([] 0) ([x &rest] `(begin ~x ~@rest)))").unwrap();
    let val = repl_eval(&mut s, "(my-begin 42)");
    assert_eq!(val, 42);
}
```

### Step 2: Inspect compiler state at the failure point

The error message names a symbol (e.g., "undefined function: macros/sconcat"). Inspect the compiler's state for that symbol at the point where the error occurs. Use `ReplSession::show_entry("module/name")` to dump the symbol table entry, or add temporary diagnostics at the error site in the backend/integration code. Run with `cargo test --test <file> <test> -- --nocapture`.

```rust
s.show_entry("macros/sconcat");  // what does the compiler know about this symbol?
s.eval("...").unwrap();          // fails here
```

The goal: determine whether the data is **missing** (never created), **incomplete** (created but missing a field like `got_slot` or `resolved_call`), or **present but not reached** (exists in the symbol table but the code path doesn't look it up). This determines which crate owns the fix.

### Step 3: Unit test in the owning crate

Write a `#[cfg(test)]` unit test in the crate that should produce the correct output. Use `cranelisp_frontend::parse` + `build_program` (via `[dev-dependencies]`) to build AST from source — don't hand-construct `Expr` trees.

```rust
#[test]
fn test_ast_annotation_qualified_extern_resolved_call() {
    let mut tc = tc_with_prims();
    let sexps = cranelisp_frontend::parse(
        "(defn f [] (macros/sconcat macros/SNil macros/SNil))"
    ).unwrap();
    let program = cranelisp_frontend::build_program(&sexps).unwrap();
    let _result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();
    // Assert the symbol table entry has the expected annotation
    let entry = tc.symbol_table().get("f").unwrap();
    // ... assert resolved_call, inferred_type, etc.
}
```

### Step 4: Interpret the result

- **Unit test passes, integration test fails** → bug is in the integration wiring (`src/worker.rs`, `src/pipeline.rs`, `src/session_v4.rs`). The crate produces correct output but the integration layer isn't using it.
- **Unit test fails** → bug is in the crate. Fix there.
- **Unit test can't be written** (crate doesn't have the right test infrastructure) → add the infrastructure first.

### Step 5: Fix at the right level

Don't patch the integration layer to work around a crate bug. Don't patch a crate to compensate for integration wiring. Each crate's output must be correct independently.

## Prototype Test Oracle

The prototype's tests are acceptance criteria:

```bash
cd sketch && just test                                           # full suite
cd sketch && cargo test --test integration test_name -- --nocapture  # one test
```

See `sketch/tests/CLAUDE.md` for prototype test conventions.

## Coverage

Code coverage is measured with `cargo-llvm-cov`, which uses LLVM's source-based instrumentation.

### Installation

```bash
rustup component add llvm-tools-preview
cargo install cargo-llvm-cov
```

### Running Coverage Reports

```bash
# Combined (all tests, root crate only)
cargo llvm-cov --html --output-dir coverage/all

# Per-layer reports:
# Unit (lib tests — inline #[cfg(test)] modules)
cargo llvm-cov --lib --html --output-dir coverage/unit

# Integration (ring tests, RC, macros, modules, IO, stdlib)
cargo llvm-cov --test ring0 --test ring1 --test ring2 --test ring3_repl --test ring4_trace --test rc --test macros --test modules --test io --test stdlib --html --output-dir coverage/integration

# API (REPL experience tests)
cargo llvm-cov --test repl_experience --test repl_negative --html --output-dir coverage/api

# E2E (subprocess tests, examples, exemplar)
cargo llvm-cov --test e2e --test examples --test exemplar --html --output-dir coverage/e2e

# Text summary (after any of the above)
cargo llvm-cov report
```

### Baseline Numbers (2026-03-20, Sprint 21)

**Workspace-wide** (after `str_as_str` fix):

| Metric | Value |
|---|---|
| **Total line coverage** | **86.72%** (25,906 lines, 3,420 missed) |
| **Function coverage** | 86.00% (2,079 functions, 291 missed) |
| **Tests** | 1241 (8 ignored) |

Per-crate breakdown:

| Crate | Lines | Missed | Coverage |
|---|---|---|---|
| cranelisp-types | ~1,070 | ~106 | ~90% |
| cranelisp-frontend | ~4,450 | ~550 | ~88% |
| cranelisp-typecheck | ~11,070 | ~590 | ~95% |
| cranelisp-backend | ~9,550 | ~1,400 | ~85% |
| cranelisp-runtime | ~800 | ~170 | ~79% |
| cranelisp-platform | ~70 | ~70 | 0% |
| platforms (stdio, test-capture) | ~90 | ~90 | 0% |
| src/ (binary crate) | ~4,450 | ~1,200 | ~73% |

Key file-level gaps:

| File | Coverage | Notes |
|---|---|---|
| `src/repl.rs` | 56% | Largest single gap — 832 missed lines, 17 untested slash command handlers |
| `backend/compiler/builtins.rs` | ~52% | Many primitive implementations untested |
| `backend/compiler/operators.rs` | ~5% | Trait operator codegen mostly untested |
| `platform/src/lib.rs` | 0% | DLL boundary — tested indirectly |
| `src/main.rs` | 0% | Binary entry — tested via E2E subprocess |

See `tests/plan/coverage-gaps.md` for full gap analysis and prioritized remediation plan.

### Known Limitations

1. **JIT code not covered**: Cranelisp compiles user code via Cranelift JIT at runtime. LLVM source-based instrumentation only covers the Rust compiler code, not the generated machine code. Coverage numbers reflect how much of the *compiler* is exercised, not how much of the *language surface* is tested.

2. **JIT code not covered**: Cranelisp compiles user code via Cranelift JIT at runtime. LLVM source-based instrumentation only covers the Rust compiler code, not the generated machine code. Coverage numbers reflect how much of the *compiler* is exercised, not how much of the *language surface* is tested.

3. **E2E subprocess profiling**: E2E tests invoke `cranelisp` as a subprocess. The subprocess binary is not instrumented by `cargo-llvm-cov` unless built with `LLVM_PROFILE_FILE` set. Current E2E coverage numbers only reflect test harness code, not the binary code paths exercised by the subprocess. The low E2E line coverage (27%) is expected for this reason.

4. **`main.rs` at 0%**: The binary entry point is never exercised by integration tests (they use the library API). Only E2E subprocess tests would cover it, but see limitation 3.

5. **Serial test coordination**: RC tests require `--test-threads=1`. Coverage runs all tests in the same invocation, which may cause RC trace contention. If RC coverage numbers look off, run `cargo llvm-cov --test rc --html --output-dir coverage/rc` separately.

6. **`coverage/` is gitignored**: Reports are local-only build artifacts. Regenerate with the commands above.
