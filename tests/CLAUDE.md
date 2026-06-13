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
authoritative. As of Sprint 64 Phase 3 close, the migration is
**complete**: all 25 active e2e files in `tests/*.rs` use the
`Cranelisp` builder API in `tests/helpers/e2e.rs`. The 41 superseded
integration-tier files have been quarantined under `tests/legacy/`
with harvest FIXMEs against `/qa`; they remain only for provenance
and are not compiled. The `ReplSession` back-compat shim that
previously bridged Rust-API tests has been deleted —
`tests/helpers/mod.rs` is now a one-line module declaration.

## Spec-traceability linter

`tests/plan/spec_link_check.py` is a structural verifier for `// spec:`
annotations. For every `// spec: <path> §<anchor>` in `tests/*.rs`, it
opens the cited file and checks that the anchor matches a Markdown
heading. Built in Sprint 64 Wave 3.5b in response to the 42 mis-cites
the Wave 3.5 audit corrected; see `tests/plan/wave-3.5-audit.md` for
the audit history that motivated it.

What it checks:

- **MIS-CITED** — file exists, anchor (`§X.Y` or `§"Named Section"`)
  does not match any heading in the cited file.
- **MALFORMED** — annotation cites a file path that does not exist on
  disk (typo, renamed file, missing directory prefix).
- Free-form notes (`// spec: (same anchor) — ...`) are skipped, not
  flagged.

Run it before `cargo nextest run` on any commit landing new tests:

```bash
python3 tests/plan/spec_link_check.py                  # scan everything
python3 tests/plan/spec_link_check.py --scope foo.rs   # one file
python3 tests/plan/spec_link_check.py --verbose        # show every OK
```

What it does NOT check: semantic match between the assertion and the
spec promise. That is a human-review concern at audit time per
`memory/feedback_validate_tests_against_spec.md`. The linter only
verifies that the cited anchor structurally exists.

Pre-commit / CI integration is a future commitment, not a Sprint 64
deliverable. As of Sprint 64 close, the seven Wave-3.5-audited files
(`cache.rs`, `spec_11_stdlib.rs`, `build_confidence.rs`,
`repl_introspection.rs`, `repl_lifecycle.rs`, `repl_negative.rs`,
`spec_10_io.rs`) plus newly-fixed `e2e.rs` / `cache.rs` /
`build_confidence.rs` MIS-CITED hits all pass clean. ~76 pre-existing
findings remain in older files (`sketch_port.rs`, `ring{0,1,2}.rs`,
`v4_*`, `sprint23.rs`, `sprint60_*`, `sprint61_*`,
`exemplar_solver_correctness.rs`, `wave6_demo_repros.rs`) — these are
durable findings now visible for Wave 4+ cleanup.

## Public-API enforcement

Sprint 66 introduces `cargo public-api` as the mechanical drift detector between as-designed (per-crate facade in `design/arch/facades/{crate}.md`) and as-built (the crate's actual public surface). One `public-api.txt` baseline lives in each crate's directory; a top-level `cargo xtask api-check` (or `just api-check`) wrapper runs the diff per crate in CI alongside `cargo nextest run`. **Triad ownership** (per `tests/plan/implementation-slice-s66.md` §1.1): `/dev` runs `cargo +nightly public-api -s --omit auto-derived-impls > crates/{crate}/public-api.txt` (the canonical flags — `-s`/`--simplified` once omits blanket-impls, `--omit auto-derived-impls` drops the `Clone`/`Debug`/`Eq`/`Serialize` impl lines while KEEPING auto-trait impls like `Send`/`Sync`; `tests/public_api_relocations.rs` diffs against exactly this format) and commits the baseline in the same change set as the source change; `/design` (per crate) verifies the baseline matches the facade target — no scope creep; `/review` approves the baseline diff against `/arch`'s facade approval. `cargo public-api` requires the **nightly Rust toolchain** (`rustup toolchain install nightly && cargo +nightly install cargo-public-api`); the xtask wrapper invokes `cargo +nightly public-api` explicitly. The 8 final-state baselines (`cranelisp-types`, `cranelisp-frontend`, `cranelisp-typecheck`, `cranelisp-backend`, `cranelisp-primitives`, `cranelisp-intrinsics`, `cranelisp-platform`, `cranelisp` binary / int) are bound by the S66 facade adoption + D43 runtime split. Drift-resolution workflow: intentional facade-shape change → author updates the facade `.md` first, regenerates the baseline, commits both atomically; unintentional drift → fix the source to match the facade, baseline does not regenerate. Reviewers always look at the facade first to distinguish the two cases. **`CRANELISP_RC_TRACE` + `CRANELISP_CODEGEN_TRACE` are reserved for the D43 Phase-4 stdlib trait-impl audit** (highest-risk reshape per the slice §2.3); concurrent agents should not contend on those env-var outputs during Phase 4.

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
    mod.rs               — module declarations only (pub mod e2e; pub mod regex;).
    e2e.rs               — e2e harness: `Cranelisp` builder + subprocess primitives
                            + tmpdir/fixture management. The only test-side helper API.
    regex.rs             — named regex library for matching compiler output.
  fixtures/
    prelude.cl           — QA-owned test prelude (Option, Result, Num, Eq, Ord)
    preamble_primitives.cl — bare primitive imports
    stdlib_project/      — read-only project fixture for stdlib conformance tests
    user/, num/, num.cl, reload_target.cl — feature-specific fixtures
  legacy/                — quarantined Rust-API/integration-tier tests (Sprint 64
                            Phase 2). Frozen archive; not compiled. Carries harvest
                            FIXMEs against `/qa` for any spec coverage not yet
                            reproduced in the canonical e2e files.
  e2e/                   — per-suite .runs/ subdirectories (gitignored)
  spec_*.rs, repl_*.rs, build_confidence.rs, cache.rs, regression.rs,
  examples.rs, exemplar.rs, link.rs               — 25 canonical e2e files; all use
                            `helpers::e2e::Cranelisp`.
```

All active tests are e2e. There is no integration tier in the active
suite — the previous Rust-API helpers (`ReplSession` and friends) were
deleted in Sprint 64 Phase 3. Discipline is now simply "tests are e2e
or unit, no middle tier" per `memory/project_test_strategy.md`.

## Test Isolation Strategy (Prelude & Stdlib)

Tests MUST NOT depend on `stdlib/`. Only the exemplar (`exemplar/`) and production binary (`src/main.rs`) may use the standard library. The test suite uses its own QA-owned fixtures to validate language features independently.

### Test Prelude Fixture

`tests/fixtures/prelude.cl` is a QA-owned, stable fixture providing:
- **ADTs**: `Option` (None, Some), `Result` (Ok, Err)
- **Traits**: `Num` (+, -, *, /), `Eq` (=, !=), `Ord` (<, >, <=, >=)
- **Impls**: Int, Float for Num/Ord; Int, Float, Bool, String for Eq

This is NOT a copy of `stdlib/prelude.cl` — it is a minimal, stable subset that tests can depend on without coupling to stdlib evolution.

### Prelude variant selection

E2E tests select the prelude through the `Cranelisp` builder's
`PreludeVariant` parameter:

- **`PreludeVariant::None`** — bare REPL/`--run`, no prelude loaded. Use
  for tests of core language features, slash commands, and error
  handling that don't need operators or ADTs.
- **`PreludeVariant::TestPrelude`** — sets `CRANELISP_LIB=tests/fixtures/`
  so the binary loads `tests/fixtures/prelude.cl`. Use for tests
  requiring operators (`+`, `-`, …), `Option` / `Result`, or trait
  dispatch.

## Test Helpers

The only helper API is the `Cranelisp` builder in
`tests/helpers/e2e.rs`. Every active test file imports it via:

```rust
mod helpers;
use helpers::e2e::{Cranelisp, PreludeVariant};
```

Highlights:

| Method | Description |
|---|---|
| `Cranelisp::new(label)` | Allocate a fresh per-test tmpdir under `tests/{suite}/.runs/...`. |
| `.with_prelude(PreludeVariant)` | Choose `None` or `TestPrelude`. |
| `.with_source(src)` | Inline source for `--run` mode. |
| `.with_project(fixture_dir)` | Copy a fixture project into the tmpdir. |
| `.repl_capture(input)` | Pipe `input` to the REPL, capture stdout/stderr/exit. |
| `.run()` | `--run` mode. |
| `.link()` | `--link` mode. |
| `run_through_all_modes(...)` | Run a source program through every mode and assert mode-equivalence. |

See `plan/helpers.md` for the full API and `tests/helpers/e2e.rs` for
the source of truth. Mode canonicalisation, fresh-tmpdir-per-test
discipline, and on-disk fixture management all live behind this builder.

## Test Standards

- **Test names describe behavior, not implementation.** `test_let_polymorphism_infers_identity` not `test_case_47`.
- **Every language-behavior test runs through all modes.** Use `run_through_all_modes` (REPL + `--run` + `--link`) for tests that assert language semantics.
- **RC tests run serially.** Use `--test-threads=1` for any test that reads `CRANELISP_RC_TRACE`.
- **Error tests use substring matching.** Not exact message comparison.
- **E2E tests invoke the binary.** No Rust API calls. No internal state inspection. The `Cranelisp` builder is the only sanctioned harness.
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
  a module tree, `user.cl`, …), copy the minimal fixture into the
  per-test tmpdir provided by `Cranelisp::new(label)`. The builder
  exposes `with_project(fixture_dir)` for the common case of cloning
  a checked-in fixture under `tests/fixtures/` into the tmpdir.
- If a test is genuinely read-only on checked-in paths, `project_root()`
  is acceptable for locating the binary (`target/debug/cranelisp`),
  the stdlib directory (for `CRANELISP_LIB`), or test fixtures under
  `tests/fixtures/`. When used this way, the callsite MUST carry a
  `// read-only on project_root` comment so future audits can
  distinguish intentional from accidental usage.
- Writes under `tests/{suite}/.runs/{RUN_TS}/{n_label}/` (allocated by
  the `Cranelisp` builder when the test names a label) are permitted:
  the `.runs/` tree is `.gitignore`'d and per-test labels provide
  isolation. Any new suite adopting this pattern MUST also add its
  `.runs/` path to `.gitignore`.
- `tempfile::TempDir` handles owned by the test MUST be bound to a
  variable that lives for the duration of the test
  (`let td = tempfile::tempdir().unwrap();`). The `Cranelisp` builder
  manages this internally for its own tmpdir; tests that allocate
  their own TempDir directly are responsible for keeping it alive.

**Exception**: the `tests/*/.runs/{RUN_TS}/{n_label}/` pattern is
permitted. The `Cranelisp` builder uses `project_root()` to locate
the suite's `.runs/` parent, then allocates an isolated per-test
directory under `.gitignore`. When adopting this pattern in a new
test suite, also add the corresponding `.runs/` path to `.gitignore`.

**CI lint candidate**: a pre-commit check that greps for
`project_root` + `fs::write|fs::create|File::create|Command::.*current_dir`
in the same file, absent the `// read-only` annotation. Sprint 61
Slice 5 E-1 audit found this lint would have flagged `d45_*`, `d6_*`,
`d7_*`, `s60_run_tests_reduction_1_*`, and the default project-root
write paths in the deleted Rust-API session helpers — all of which
are now converted (or quarantined under `tests/legacy/`).

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

## `--link` / platform e2e prerequisites (nextest setup script)

The `--link` and platform e2e tests invoke the `cranelisp` binary, whose
`--link` path links five workspace members it has **no Cargo dependency
edge to** — it resolves them at runtime by scanning `target/debug/`:
`cranelisp-exe-bundle` (`libcranelisp_exe_bundle.a`), `cranelisp-stdio`,
`cranelisp-test-capture`, `cranelisp-shapes`, `cranelisp-shapes-badabi`,
`cranelisp-boom` (`lib*.{rlib,so}`). Because nothing depends on them, a
plain `cargo nextest run` never compiles them, and the `--link` path
fails with `could not find libcranelisp_exe_bundle.a`.

The fix is a **nextest setup script** (`.config/nextest.toml` →
`tests/scripts/build-link-prereqs.sh`) that builds all five in **one
`cargo build -p` invocation** before any test runs. One invocation =>
one consistent snapshot of the shared crates (closes the rlib-vs-bundle
skew hazard). Cheap no-op when current. Design + root-cause:
`tests/plan/e2e-architecture.md`.

**Rules:**

- **A test MUST NOT shell out to `cargo build`.** The artifact set is a
  suite-level invariant owned by the setup script. Do not re-introduce
  per-binary `std::sync::Once` build helpers (the retired
  `ensure_platform_cdylibs_built()` band-aid).
- **A new platform/link fixture extends the script**, not a per-test
  build. Add the crate to `tests/scripts/build-link-prereqs.sh`.
- `CRANELISP_PLATFORM_PATH` env wiring is per-test runtime config (lives
  in the harness / test), NOT a build step — that is fine to keep.

## Build Commands

Always use `cargo nextest run` (per `memory/feedback_test_serialization.md`).

```bash
# Run all tests
cargo nextest run

# Run a specific binary
cargo nextest run --test spec_04_expressions
cargo nextest run --test cache

# Run a single test
cargo nextest run --test cache cache_multi_module_transitive_imports

# Run with diagnostics (sets env on the spawned subprocess)
CRANELISP_RC_TRACE=1     cargo nextest run --test spec_12_runtime
CRANELISP_INFER_TRACE=1  cargo nextest run --test spec_04_expressions
CRANELISP_CODEGEN_TRACE=1 cargo nextest run --test regression
```

## Adding Tests

1. **Choose the file**: by spec section (`spec_NN_*.rs`) or by concern
   (`repl_*.rs`, `cache.rs`, `regression.rs`, …).
2. **Use the harness**: `Cranelisp::new(label)` from `helpers::e2e`.
3. **Pick a prelude variant**: `PreludeVariant::None` for core-language
   tests; `PreludeVariant::TestPrelude` if the test needs operators
   or `Option` / `Result`.
4. **Name the test**: after the behavior being validated.
5. **Run it through all modes** if it tests language semantics: use
   `run_through_all_modes` to assert REPL / `--run` / `--link`
   equivalence.
6. **Add the spec annotation**: `// spec: <path> §<anchor>` on every
   `#[test]` function.

## Isolating Cross-Crate Failures

When an e2e test fails and the root cause could be in any crate
(typecheck? backend? integration wiring?), follow this process to
isolate before fixing. Do NOT guess-and-patch — that creates
workarounds that mask the real problem.

### Step 1: Minimal e2e repro

Write the smallest test that reproduces the failure. Strip everything:
no prelude (`PreludeVariant::None`), no stdlib, no imports unless
required. The test should fail with the same error as the original.

```rust
#[test]
fn defmacro_rest_splice() {
    let cap = Cranelisp::new("defmacro_rest_splice")
        .with_prelude(PreludeVariant::None)
        .repl_capture(
            "(defmacro my-begin ([] 0) ([x &rest] `(begin ~x ~@rest)))\n\
             (my-begin 42)\n",
        );
    assert!(cap.stdout.contains("42"), "stdout={}", cap.stdout);
}
```

### Step 2: Inspect compiler state at the failure point

The error message names a symbol (e.g., "undefined function:
macros/sconcat"). Use the REPL's introspection commands inside
`repl_capture` to inspect what the compiler knows about that symbol:
`/sig`, `/info`, `/list`, `/sexp`, `/clif`, `/ast`. Combine with
`CRANELISP_CODEGEN_TRACE=1` (or the other trace env vars in the
Diagnostic Logging table) for compiler-side observability. Small
repros also produce small CLIF that can be inspected by eye.

```rust
let cap = Cranelisp::new("inspect_macros_sconcat")
    .with_prelude(PreludeVariant::TestPrelude)
    .repl_capture("/info macros/sconcat\n");
println!("{}", cap.stdout);
```

The goal: determine whether the data is **missing** (never created),
**incomplete** (created but missing a field like `got_slot` or
`resolved_call`), or **present but not reached** (exists in the
symbol table but the code path doesn't look it up). This determines
which crate owns the fix.

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

- **Unit test passes, e2e test fails** → bug is in the integration wiring (`src/worker.rs`, `src/pipeline.rs`, `src/session_v4.rs`). The crate produces correct output but the integration layer isn't using it.
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
