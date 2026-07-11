# tests/

Test infrastructure for the Cranelisp reimplementation.

**Ownership.** `tests/plan/` is owned by `/qa` (strategy, risk, coverage
process, attribution; `plan/PLAN.md` is the normative spec → tests bridge).
Everything else here — `tests/*.rs`, `tests/helpers/`, `tests/fixtures/`,
`tests/scripts/`, `plan/ledger.md` upkeep, and this file — is owned by
`/testing`. Per-crate `#[cfg(test)]` unit tests are `/dev`'s and live in
`crates/{crate}/src/`, not here.

## Two tiers, no middle

Cranelisp tests fall into exactly two tiers:

1. **e2e tests** — `tests/*.rs`. Run the `cranelisp` binary directly: REPL
   via stdin, `--run file.cl`, or `--link` then run the produced executable.
   Helpers are process-spawn + stdout/stderr/exit capture + isolated tmpdir +
   on-disk fixture files. **This is the release gate.**
2. **Unit tests** — `crates/{crate}/src/` `#[cfg(test)]` modules, authored by
   `/dev` alongside the implementation.

There is **no middle integration tier.** Tests do NOT construct `Sess`,
`SharedState`, `SymbolTable`, or any internal session primitive. If a feature
cannot be expressed e2e, that is a gap in the binary's testability surface —
file a FIXME (`target: /qa` or `/arch`), do not bridge with an internal-API
helper. The earlier four-layer pyramid is retired; `plan/legacy/strategy.md`
preserves it for provenance only.

## Plan documents (`plan/`, owned by `/qa`)

| File | Purpose |
|---|---|
| `PLAN.md` | Normative spec → tests bridge; every e2e test traces to a row. |
| `ledger.md` | Failure ledger — current intentional REDs + per-defect owners. `/testing` keeps it current. |
| `risks.md` | Qualitative risk register. |
| `coverage-gaps.md` | Per-crate coverage analysis. |
| `negative-coverage.md` | `[Tested]` → `[Tested+Neg]` upgrade register. |
| `helpers.md` | E2E helper API design (contract for `tests/helpers/`). |
| `legacy/` | Superseded plans (rings, four-layer strategy). Provenance only. |

Per-sprint plans accumulate as `plan/s{NN}-*.md` (and `spec_*.py` traceability
tooling); those are `/qa`'s working documents, not durable references.

## Test file organisation

All active test files are e2e and live flat under `tests/`. Naming is by
convention — list them with `ls tests/*.rs`; do not maintain a count here.

- `spec_NN_*.rs` — one file per spec chapter (`spec_04_expressions.rs`,
  `spec_10_io.rs`, …). The primary spec-coverage suite.
- `repl_*.rs` — REPL experience (introspection, lifecycle, persistence, …).
- `concurrency_*.rs` — the effect/concurrency track.
- Concern-named files — `cache.rs`, `regression.rs`, `link.rs`,
  `examples.rs`, `exemplar*.rs`, `trace.rs`, plus targeted repro files named
  after the defect or property they pin (`tco_tail_arg_alias_uaf.rs`,
  `vec_cow_value_use_leak.rs`, …).

Supporting directories:

```
tests/
  CLAUDE.md              — this file
  plan/                  — /qa's plan + ledger + tooling (see above)
  helpers/
    mod.rs               — module declarations only (pub mod e2e; pub mod regex;)
    e2e.rs               — the e2e harness: `Cranelisp` builder + subprocess
                            primitives + tmpdir/fixture management. Source of truth.
    regex.rs             — named regex library for matching compiler output
  fixtures/              — on-disk fixtures (preludes/, stdlib_project/, golden/, …)
  scripts/               — build-link-prereqs.sh and other suite-level scripts
  perf/                  — measurement harnesses (per-sprint attribution/perf)
  legacy/                — quarantine archive, HARVEST COMPLETE (0 .rs files);
                            see tests/legacy/README.md. Provenance only.
```

## Test helpers

The only sanctioned helper API is the `Cranelisp` builder in
`tests/helpers/e2e.rs` — the source of truth. Every test file imports it:

```rust
mod helpers;
use helpers::e2e::{Cranelisp, PreludeVariant};
```

The builder composes in three stages: **construct + configure**, **select
mode**, **capture + assert**.

- `Cranelisp::new()` — fresh builder backed by a per-test `tempfile::TempDir`.
- Mode (mutually exclusive): `.repl()` (default), `.run(file)`, `.link(file)`,
  `.link_then_run(file)`.
- Fixture composition: `.file(rel, contents)`, `.user(contents)`,
  `.prelude(contents)`, `.with_prelude(variant)`, `.fixture(src, dst)`,
  `.fixture_tree(src_dir, dst_dir)` (copies from `tests/fixtures/`).
- Input/env: `.stdin(lines)`, `.stdin_lines(&[…])`, `.env(k, v)`, `.timeout(d)`.
- Terminal: `.output()` → `CrOutput` (panics on spawn/timeout error);
  `.try_output()` returns the error instead.
- `CrOutput` carries fluent assertions: `.assert_ok()`, `.assert_exit(code)`,
  `.assert_stdout_contains(…)`, `.assert_stdout_does_not_contain(…)`,
  `.assert_golden(name)`, and more.
- Shortcuts for piped-REPL captures: `Cranelisp::repl_capture(lines)` (bare
  REPL) and `Cranelisp::repl_prims_capture(lines)` (with `PrimitivesOnly`).
- Cross-mode equivalence: `run_through_all_modes(program, prelude)` runs a
  program through REPL + `--run` + `--link` and asserts mode-equivalence.

Consult `tests/helpers/e2e.rs` for exact signatures — do not treat the summary
above as complete; it drifts, the source does not.

### Prelude variants

Tests select the prelude through `.with_prelude(PreludeVariant)`. Variants
materialise a file from `tests/fixtures/preludes/`:

- **`PreludeVariant::None`** — no prelude. Core language, slash commands, error
  handling that need no operators or ADTs.
- **`PreludeVariant::PrimitivesOnly`** — bare primitive imports, no traits/ADTs
  (`preludes/primitives-only.cl`).
- **`PreludeVariant::TestStandard`** — Option, Result, Num, Eq, Ord
  (`preludes/test-standard.cl`). Use when the test needs operators, `Option`/
  `Result`, or trait dispatch.

## Test isolation (prelude & stdlib)

Tests MUST NOT depend on `stdlib/` (root `CLAUDE.md` §"Design Principles" —
Stdlib separation). The suite uses its own QA-owned fixtures under
`tests/fixtures/` to validate language features independently of stdlib
evolution. The single named exception is stdlib conformance, gated behind the
verbosely-named `.use_workspace_stdlib_for_stdlib_conformance_only()` so misuse
is visible in review and `git grep`.

## Fresh temp directory per test

**Rule:** filesystem-writing tests MUST use a fresh per-test tmpdir and MUST
NOT write to checked-in paths (`exemplar/`, `examples/`, `stdlib/`,
`tests/fixtures/`, `src/`, …) or to `workspace_root()`.

**Why:** Sprint 60 found that `user.cl` persistence in a shared working
directory accumulated across runs, masking a defect's disposition; cross-test
state pollution also hides races that fire only under specific filesystem
preconditions.

**How:** `Cranelisp::new()` allocates a `tempfile::TempDir` and manages its
lifetime for the duration of the builder — compose fixtures into it with
`.file` / `.fixture` / `.fixture_tree`, never into the source tree. A test that
is genuinely read-only on checked-in paths may reference `workspace_root()` (to
locate the binary, `CRANELISP_LIB`, or a fixture), but the callsite MUST carry a
`// read-only on project_root` comment so audits can distinguish intentional
from accidental use.

## Test standards

- **Names describe behaviour, not implementation.**
  `let_polymorphism_infers_identity`, not `test_case_47`.
- **Language-semantics tests run through all modes.** Use
  `run_through_all_modes` (REPL + `--run` + `--link`) — a REPL/`--run`/`--link`
  divergence is always a defect.
- **RC tests run serially.** `--test-threads=1` for any test reading
  `CRANELISP_RC_TRACE`.
- **Error tests use substring matching**, not exact message comparison.
- **E2E tests invoke the binary only.** No Rust-API calls, no internal state
  inspection; the `Cranelisp` builder is the only sanctioned harness.
- **No test is silently dropped.** Every test traces to a spec section via
  `// spec:` and to a `plan/PLAN.md` row.
- **Negative tests verify absence, not just presence** (see below).

## Negative test convention

Positive tests verify correct behaviour; negative tests verify **incorrect
behaviour does not occur**. Both are required for full coverage — a suite that
only checks "the right thing appears" passes green while the system also does
wrong things.

- **Naming:** negative test names carry `_neg_` or `_not_`
  (`e2e_s3_3_list_neg_no_primitives_in_user`).
- **Spec annotation:** when negatives exist alongside positives, the spec tag
  upgrades `[Tested …]` → `[Tested+Neg …]`, making gaps visible at spec level.
- **Priority areas:** module boundaries (`primitives` symbols must NOT appear
  as `user/` entries), category boundaries (`/list` categories must not
  cross-contaminate), error boundaries (valid input must not error; invalid
  input must not succeed silently), display format (no unqualified names where
  qualified are required).

## `--link` / platform prerequisites (nextest setup script)

The `--link` path links five workspace members it has **no Cargo dependency
edge to** — it resolves them by scanning `target/debug/` at runtime. A plain
`cargo nextest run` never compiles them, so `--link` fails with
`could not find libcranelisp_exe_bundle.a`. The fix is a nextest **setup
script** (`.config/nextest.toml` → `tests/scripts/build-link-prereqs.sh`) that
builds all of them in one `cargo build -p` invocation before any test runs —
one snapshot, no rlib-vs-bundle skew.

- **A test MUST NOT shell out to `cargo build`.** The artifact set is a
  suite-level invariant owned by the setup script.
- **A new platform/link fixture extends the script**, not a per-test build —
  add the crate to `tests/scripts/build-link-prereqs.sh`.
- `CRANELISP_PLATFORM_PATH` wiring is per-test runtime config (in the harness),
  not a build step.

## Diagnostic env vars & assertions

Silent by default, controlled by environment variables — set them on the
spawned subprocess via `.env(…)`, or export before `cargo nextest run`:

| Variable | Shows |
|---|---|
| `CRANELISP_RC_TRACE=1` | Every alloc, inc, dec, free with pointer + type |
| `CRANELISP_INFER_TRACE=1` | Unification steps, constraint generation |
| `CRANELISP_CODEGEN_TRACE=1` | CLIF IR before/after optimization |
| `CRANELISP_MODULE_TRACE=1` | Module discovery, compile order, cache hits |
| `CRANELISP_MACRO_TRACE=1` | Macro expansion steps |

Compiler skills back invariants with `debug_assert!` (span monotonicity, no
unresolved type vars in output, RC never negative, GOT slot uniqueness). At the
host↔platform-DLL marshaling boundary these must assert heap-header integrity
after each construct/consume crossing (`/platform` + `/backend` obligation) —
a few-bytes-per-crossing overrun is silent under the system allocator until it
trips a glibc abort many crossings later. Every marshaling boundary therefore
also needs a **sustained-repetition** guard (drive it 200–2000 crossings in
both directions, assert exit 0), and `--link` capabilities guard
link-then-RUN-under-load, not link-success-only. First such guard:
`tests/link.rs::link_repeated_platform_adt_marshal_does_not_corrupt_heap`.

## Spec traceability

Every `#[test]` carries a `// spec:` comment naming the section it validates:

```rust
// spec: repl/spec.md §1.2 — Int display format
```

`/testing` adds the test-side `// spec:`; `/qa` audits the two-sided match and
adds the spec-side `[Tested …]` annotation. Two structural verifiers live in
`plan/` (owned by `/qa`; run them before landing annotation changes):

- `plan/spec_link_check.py` — test → spec: every `// spec:` anchor must match a
  real heading in the cited file.
- `plan/spec_coverage_reconcile.py` — spec → test: every `[Tested tests/FILE::name]`
  citation must resolve to an existing file + `fn name`. Guards against
  citation rot after suite reorgs.

`tests/public_api_relocations.rs` and `tests/facade_compliance.rs` are the
mechanical public-API drift guards against the per-crate facades in
`design/arch/facades/`; the baseline regeneration workflow is `/dev` + `/design`
+ `/review`'s (see `plan/implementation-slice-s66.md`).

## Isolating Cross-Crate Failures

When an e2e test fails and the root cause could be in any crate (typecheck?
backend? integration wiring?), isolate before fixing. Do NOT guess-and-patch —
that creates workarounds that mask the real problem.

**Step 1 — Minimal e2e repro.** Write the smallest test that reproduces the
failure. Strip everything: `PreludeVariant::None`, no stdlib, no imports unless
required. It should fail with the same error as the original.

```rust
#[test]
fn defmacro_rest_splice() {
    Cranelisp::repl_capture(
        "(defmacro my-begin ([] 0) ([x &rest] `(begin ~x ~@rest)))\n\
         (my-begin 42)\n",
    )
    .assert_stdout_contains("42");
}
```

**Step 2 — Inspect compiler state at the failure point.** The error names a
symbol (e.g. "undefined function: macros/sconcat"). Use REPL introspection
inside a capture (`/info`, `/sig`, `/list`, `/sexp`, `/clif`, `/ast`) combined
with the trace env vars to determine whether the data is **missing** (never
created), **incomplete** (created but missing a field like `got_slot`), or
**present but not reached** (in the symbol table but the code path doesn't look
it up). Small repros produce small CLIF that can be read by eye.

**Step 3 — Unit test in the owning crate.** Write a `#[cfg(test)]` test in the
crate that should produce the correct output. Build the AST from source with
`cranelisp_frontend::parse` + `build_program` (via `[dev-dependencies]`) — do
not hand-construct `Expr` trees.

**Step 4 — Interpret.** Unit passes but e2e fails → bug is in integration wiring
(`src/worker.rs`, `src/pipeline.rs`, `src/session_v4.rs`). Unit fails → bug is
in the crate; fix there. Unit can't be written → add the crate's test
infrastructure first.

**Step 5 — Fix at the right level.** Don't patch integration to work around a
crate bug, or patch a crate to compensate for integration wiring. Each crate's
output must be correct independently.

## Coverage

Code coverage is measured with `cargo-llvm-cov` (LLVM source-based
instrumentation; `rustup component add llvm-tools-preview` + `cargo install
cargo-llvm-cov`).

```bash
cargo llvm-cov --html --output-dir coverage/all     # combined, root crate
cargo llvm-cov --lib --html --output-dir coverage/unit
cargo llvm-cov --test spec_04_expressions --html --output-dir coverage/one
cargo llvm-cov report                               # text summary
```

Name real `--test` targets (see `ls tests/*.rs`); there are no `ringN` binaries.
Current baseline figures and per-crate gap analysis live in
`plan/ledger.md` and `plan/coverage-gaps.md` — not restated here, they decay.

**Known limitation — JIT code not covered:** Cranelisp compiles user code via
Cranelift JIT at runtime; LLVM instrumentation covers only the Rust compiler
code, not the generated machine code. Coverage numbers reflect how much of the
*compiler* is exercised, not how much of the *language surface* is tested. E2E
subprocess coverage likewise reflects only harness code unless the subprocess is
built with `LLVM_PROFILE_FILE` set. `coverage/` is gitignored.

## Build & run

Always use `cargo nextest run --no-fail-fast` (never `cargo test`; alias
`cargo nt`). Full suite ~60s post-build; anything past ~3 minutes including
build is wrong — kill and investigate. Never run tests in the background; only
one agent runs tests at a time.

```bash
cargo nextest run --no-fail-fast                       # full suite
cargo nextest run --test spec_04_expressions           # one binary
cargo nextest run --test cache cache_multi_module_transitive_imports  # one test
CRANELISP_RC_TRACE=1 cargo nextest run --test spec_12_runtime         # with a trace
```

## Adding a test

1. **Choose the file** by spec section (`spec_NN_*.rs`) or concern
   (`repl_*.rs`, `cache.rs`, `regression.rs`, a defect-named repro file).
2. **Use the harness** — `Cranelisp::new()` (or a `repl_capture` shortcut).
3. **Pick a prelude variant** — `None` for core-language tests,
   `PrimitivesOnly` or `TestStandard` when operators/ADTs are needed.
4. **Name after the behaviour** validated.
5. **Run through all modes** if it asserts language semantics.
6. **Add `// spec:`** on every `#[test]` and a `plan/PLAN.md` row.

## Unit-test-per-fix discipline

Every fix lands with a unit test, and the e2e need is assessed
**before** the fix is written; failing test(s) first, fix flips them green, both
in the same change-set. This is stated canonically in root `CLAUDE.md`
§Testing and `sprints/METHOD.md` §2.2 — follow those; not restated here.
