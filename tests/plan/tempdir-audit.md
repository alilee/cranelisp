# Fresh-TempDir-per-test Audit (Sprint 61, Slice 5 E-1)

**Purpose**: Sprint 60 Round 3 found that tests using `project_root()` or
writing to checked-in paths (`exemplar/`, `examples/`, `stdlib/`, …)
accumulate cross-test state. In that round, `user.cl` persistence in the
exemplar working directory was load-bearing in a defect's
mis-disposition — "pre-existing" was environmental luck, not truth. This
audit catalogues the current state so the Wave-2 conversion to
`tempfile::TempDir` has a known scope.

**Audit date**: 2026-04-22
**Commit SHA**: `a9028c0`
**Auditor**: `/qa` (Sprint 61 Phase 3)

## Methodology

Three grep patterns were run against `tests/` via the project's Grep
tool (not `rg` in bash):

```
pattern: project_root
pattern: exemplar/
pattern: examples/
pattern: TempDir|tempfile|tempdir
```

Spot-reads of `tests/e2e.rs`, `tests/wave6_demo_repros.rs`,
`tests/sprint59_defects456_repro.rs`, `tests/sprint60_reduction.rs`,
`tests/sprint60_run_tests_reduction.rs`, `tests/examples_run.rs`, and
`tests/helpers/mod.rs` calibrated the disposition classifications.

## Classification Legend

- **KEEP — read-only binary/fixture path.** `project_root()` is used to
  locate `target/debug/cranelisp`, the `stdlib/` directory used via
  `CRANELISP_LIB`, `target/debug` for `CRANELISP_PLATFORM_PATH`, or
  `tests/fixtures/` fixtures. No writes to checked-in paths. Allowed;
  annotate `// read-only on project_root` in Wave 2.
- **KEEP — writes only under `tests/*/.runs/{RUN_TS}/{n_label}/`.** This
  is the `e2e.rs::test_dir()` pattern. Each test gets an isolated
  directory under a `.runs/` tree that is already `.gitignore`'d. No
  pollution of checked-in source paths; cross-test state within a single
  run is bounded by the per-test `n_label` subdirectory. Allowed.
- **CONVERT — writes to a checked-in path (`exemplar/`, `examples/`, or
  under `stdlib/`).** Must move to `tempfile::TempDir` with a fresh
  copy of the relevant fixture files. These are the tests that have been
  observed (or could plausibly) accumulate cross-test state.
- **ALREADY TEMPDIR.** Test already uses `tempfile::tempdir()`;
  `project_root()` callsites are for binary / stdlib / platform path
  lookup only, not for cwd or write targets. No change needed in Wave 2
  beyond the `// read-only on project_root` annotation where the env
  vars are set.

## Findings

| # | Test file (test fn or helper) | Pattern | Writes? | Disposition |
|---|---|---|---|---|
| 1 | `tests/e2e.rs` (`test_dir`, entire file) | `project_root()` → binary/fixtures; writes under `tests/e2e/.runs/` | yes — isolated | KEEP — `.runs/` pattern |
| 2 | `tests/sprint23.rs` (`test_dir` + tempdir helpers) | `project_root()` → binary/fixtures/stdlib; most tests use `tempfile::tempdir()` | yes — mostly in tempdirs | KEEP — hybrid; `project_root()` uses are read-only |
| 3 | `tests/sprint59_cache_repro.rs` | `project_root()` → binary only | no | KEEP — read-only |
| 4 | `tests/sprint60_observability.rs` | `project_root()` → binary only | no | KEEP — read-only |
| 5 | `tests/v4_repl_eval.rs` | `project_root()` → binary only | no | KEEP — read-only |
| 6 | `tests/v4_pipeline.rs` | `project_root()` → binary / fixtures | no (fixtures are read-only) | KEEP — read-only |
| 7 | `tests/sprint60_cache_build_marker.rs` | `project_root()` → binary only | no | KEEP — read-only |
| 8 | `tests/sprint60_reduction.rs` | `project_root()` → binary / stdlib / platform; writes go to `tempdir()` | no to checked-in; yes to tempdir | ALREADY TEMPDIR |
| 9 | `tests/sprint60_run_tests_reduction.rs::s60_run_tests_reduction_1_exemplar_batched_failing` | writes `exemplar/user.cl` (empty) via `project_root().join("exemplar")` as cwd | **YES — WRITES `exemplar/user.cl`** | **CONVERT** |
| 10 | `tests/sprint60_run_tests_reduction.rs::s60_run_tests_reduction_2/3/4...` | `tempfile::tempdir()` for cwd; `project_root()` only for binary/stdlib/platform env | no | KEEP — read-only |
| 11 | `tests/wave6_demo_repros.rs::d7_html_run_tests_no_crash` (`exemplar_html_test_discovery_and_run`) | writes `exemplar/user.cl`; cwd = `project_root().join("exemplar")` | **YES — WRITES `exemplar/user.cl`** | **CONVERT** |
| 12 | `tests/wave6_demo_repros.rs::exemplar_solver_does_not_stack_overflow_on_small_puzzle` | cwd = `project_root()`; `--run exemplar/solver.cl`; reads but does not write checked-in files (though `.cranelisp-cache/` under exemplar/ is populated by the run — potentially problematic) | yes — populates `exemplar/.cranelisp-cache/` | **CONVERT** (or annotate + verify cache isolation) |
| 13 | `tests/wave6_demo_repros.rs` (other tests using tempfile) | `tempfile::tempdir()` at 208; helpers | no | KEEP / ALREADY TEMPDIR |
| 14 | `tests/sprint59_defects456_repro.rs::d45_real_exemplar_html_run_tests_no_crash` | writes `exemplar/user.cl`; drives REPL in `exemplar/` cwd | **YES — WRITES `exemplar/user.cl`** | **CONVERT** |
| 15 | `tests/sprint59_defects456_repro.rs::d45_real_exemplar_html_single_run_test_no_crash` | writes `exemplar/user.cl`; drives REPL in `exemplar/` cwd | **YES — WRITES `exemplar/user.cl`** | **CONVERT** |
| 16 | `tests/sprint59_defects456_repro.rs::d6_exemplar_solve_minimal_puzzle_no_io_does_not_segv` | writes `exemplar/d6_repro_no_io.cl` with scope-guarded best-effort cleanup; fails to clean on panic | **YES — WRITES `exemplar/d6_*.cl`** | **CONVERT** |
| 17 | `tests/sprint59_defects456_repro.rs::d6_exemplar_propagate_only_does_not_segv` | writes `exemplar/d6_propagate_only.cl` (scope-guarded cleanup) | **YES** | **CONVERT** |
| 18 | `tests/sprint59_defects456_repro.rs::d6_exemplar_solve_all_dots_does_not_segv` | writes `exemplar/d6_all_dots.cl` | **YES** | **CONVERT** |
| 19 | `tests/sprint59_defects456_repro.rs::d6_one_pass` / `d6_elim_peers` / `d6_make_grid` | write `exemplar/d6_*.cl` with scope-guarded cleanup | **YES** | **CONVERT** |
| 20 | `tests/sprint59_defects456_repro.rs` (tempdir module-dir / two-file-dir helpers; other tests) | `tempfile::tempdir()` throughout `module_dir`, `two_file_dir`, `html_with_trimmed_grid`, `html_reduction` | no to checked-in | KEEP / ALREADY TEMPDIR |
| 21 | `tests/examples_run.rs::every_example_file_runs_under_examples_prelude` | cwd = `examples_dir()` = `project_root().join("examples")`; `--run` subprocess may populate `examples/.cranelisp-cache/` | **LIKELY YES — populates `examples/.cranelisp-cache/`** | **CONVERT** (or verify cache env-var isolates writes) |
| 22 | `tests/ring2.rs::…` | uses `tempfile::tempdir()` for module graph tests; `project_root_shadows_stdlib` name is a test name not a path | no to checked-in | KEEP / ALREADY TEMPDIR |
| 23 | `tests/modules.rs` (`create_test_project`) | uses `tempfile::tempdir()` | no | ALREADY TEMPDIR |
| 24 | `tests/cache.rs` (`create_cache_test_project` + 20 tempdir sites) | `tempfile::tempdir()` exclusively for write surface | no | ALREADY TEMPDIR |
| 25 | `tests/io.rs` | `tempfile::tempdir()` at two sites | no | ALREADY TEMPDIR |
| 26 | `tests/ring1.rs` | `tempfile::tempdir()` | no | ALREADY TEMPDIR |
| 27 | `tests/wave2_g6.rs` | `tempfile::tempdir()` | no | ALREADY TEMPDIR |
| 28 | `tests/exemplar.rs` (three test sites) | `tempfile::tempdir()` | no — does NOT touch checked-in `exemplar/` | ALREADY TEMPDIR |
| 29 | `tests/sprint59_neg.rs::create_test_project` | `tempfile::tempdir()` | no | ALREADY TEMPDIR |
| 30 | `tests/stdlib.rs` (most tests) | `project_root` variable points at `tests/fixtures/stdlib_project/` — read-only fixture | no | KEEP — read-only fixture |
| 31 | `tests/stdlib.rs` (4 tempdir sites) | `tempfile::tempdir()` | no | ALREADY TEMPDIR |
| 32 | `tests/wave4_g9.rs` | uses `tempfile::tempdir()` via helper that creates a project_root under the tempdir | no to checked-in | ALREADY TEMPDIR |
| 33 | `tests/helpers/mod.rs` (`ReplSessionBuilder`, `repl_session`, `repl_session_with_test_prelude`) | uses `CARGO_MANIFEST_DIR/tests/fixtures/` as `project_root`; the ReplSession writes `{name}.cl` into its `project_root()` when `install_def` is called | **YES — writes under `tests/fixtures/`** | **CONVERT** (helper-level fix) |
| 34 | `tests/examples.rs` | pure read of example files via `{}/examples/{}` format | no | KEEP — read-only |

## Summary

- `project_root()` callsites (function + direct usage): **15 test files** define or use `project_root()`.
- **KEEP — read-only (binary/fixture/stdlib/platform path lookup)**: ~10 files. Acceptable in Wave 2 with `// read-only on project_root` annotation.
- **KEEP — writes only under `tests/*/.runs/…`**: 2 files (`e2e.rs`, `sprint23.rs`). Acceptable pattern; the `.runs/` tree is already `.gitignore`'d.
- **ALREADY TEMPDIR**: 11 test files (`cache.rs`, `modules.rs`, `ring1.rs`, `ring2.rs`, `io.rs`, `exemplar.rs`, `wave2_g6.rs`, `wave4_g9.rs`, `stdlib.rs` tempdir sites, `sprint59_neg.rs`, `sprint60_reduction.rs`). Reference patterns for Wave 2 conversion.
- **CONVERT — writes to checked-in paths**: **~10 test functions across 4 files** (`wave6_demo_repros.rs`, `sprint59_defects456_repro.rs`, `sprint60_run_tests_reduction.rs`, `examples_run.rs`) plus **1 helper-level fix** in `tests/helpers/mod.rs` (`ReplSession` with default `project_root` = `tests/fixtures/` writes `.cl` files there from `install_def`).

**Headline**: K = ~10 test functions + 1 shared helper require conversion. N = 34 catalogued test-file dispositions. M = ~10 write to checked-in paths today.

### Top priority for Wave 2

1. **`tests/helpers/mod.rs::ReplSessionBuilder` default path** — highest
   leverage. Changing the default `project_root` from
   `tests/fixtures/` to a fresh tempdir per test (or requiring callers
   to pass one) would remove an entire class of cross-test state.
2. **The exemplar-writing tests** (`d45_*`, `d6_*`, `d7_*`,
   `s60_run_tests_reduction_1_*`) — these literally mutate
   `exemplar/user.cl` and `exemplar/d6_*.cl`. The `user.cl` overwrite
   was observed load-bearing in Sprint 60 Round 3's mis-disposition.
3. **`examples_run.rs`** — populates `examples/.cranelisp-cache/` via
   subprocess. Less visible, but a shared-directory cache is exactly
   the write-pattern the rule forbids. Verify via `ls examples/` after
   `cargo nextest run` to confirm the cache is (or is not) materialised.

### Surprise findings

- **`tests/helpers/mod.rs` defaults `project_root` to
  `tests/fixtures/`** (lines 30–45). The `ReplSession::install_def`
  path writes `{name}.cl` into that directory (line 173: `path =
  self.session.project_root().join(format!("{name}.cl"))`). Integration
  tests using the default builder therefore scatter `.cl` files
  throughout `tests/fixtures/`. This is a larger scope than the
  originally-suspected exemplar-only pattern.
- **The `exemplar_solver_does_not_stack_overflow_on_small_puzzle`
  test** runs with cwd = `project_root()` and the subprocess populates
  `.cranelisp-cache/` somewhere — needs verification whether the
  v4-pipeline's default cache root is `project_root/.cranelisp-cache`
  (per `tests/cache.rs:998` comment) or the example-relative
  `exemplar/.cranelisp-cache/`. Either way, the checked-in workspace
  is mutated.
- **Four tests use `struct Cleanup(PathBuf); impl Drop` scope guards**
  to remove `exemplar/d6_*.cl` on normal exit. These fail to clean on
  panic (`Drop` runs, but intermediate state between `std::fs::write`
  and test panic still leaves artefacts visible to concurrent tests).
  TempDir eliminates this race.
- **`.gitignore` already carries `tests/sprint60/.runs/`** — Slice 5 F
  (S60 /review I-1) may already be satisfied. Wave 2 should verify and
  close-out or widen if a different `.runs/` tree is missing.

## Conversion pattern

Wave 2 should establish a shared helper (proposed at
`tests/helpers/mod.rs` or a new `tests/helpers/tempdir_project.rs`)
with the following shape:

```rust
/// Create a fresh temp project directory and copy the named fixture
/// files (relative to `tests/fixtures/` or `exemplar/`) into it.
/// Returns (TempDir handle — keep alive for test duration, cwd).
pub fn tempdir_project_from_fixture(
    fixture_root: &str,        // e.g. "tests/fixtures/stdlib_project"
    files: &[&str],            // file names to copy
) -> (tempfile::TempDir, std::path::PathBuf) {
    let td = tempfile::tempdir().unwrap();
    let dst = td.path().to_path_buf();
    for name in files {
        let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join(fixture_root)
            .join(name);
        let dst_file = dst.join(name);
        if let Some(parent) = dst_file.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::copy(&src, &dst_file).unwrap();
    }
    (td, dst)
}
```

For tests that drive the binary as a subprocess (the
`d45_*`, `d7_*`, `s60_…_1`, and `examples_run` shapes), the pattern
is:

1. Copy `exemplar/*.cl` or `examples/*.cl` into the tempdir.
2. Set `cmd.current_dir(td.path())` instead of the checked-in path.
3. Keep `CRANELISP_LIB=project_root/stdlib` and
   `CRANELISP_PLATFORM_PATH=project_root/target/debug` because those
   are genuinely read-only.

For the `ReplSessionBuilder` helper fix, the default `project_root`
becomes a fresh `TempDir` created inside the builder, kept alive via a
field on the returned `ReplSession` wrapper (or returned to the caller
as `(ReplSession, TempDir)` so lifetime is explicit).

## Proposed `tests/CLAUDE.md` rule

_Do NOT commit the text below to `tests/CLAUDE.md` in Wave 1. It is
staged here for /review in Wave 2 before insertion._

```markdown
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
  `tests/helpers/tempdir_project_from_fixture` for the shared helper.
- If a test is genuinely read-only on checked-in paths, `project_root()`
  is acceptable for locating the binary (`target/debug/cranelisp`),
  the stdlib directory (for `CRANELISP_LIB`), or test fixtures under
  `tests/fixtures/`. When used this way, the callsite MUST carry a
  `// read-only on project_root` comment so future audits can
  distinguish intentional from accidental usage.
- Writes under `tests/{suite}/.runs/{RUN_TS}/{n_label}/` (the
  `e2e.rs::test_dir()` pattern) are permitted: the `.runs/` tree is
  `.gitignore`'d and per-test labels provide isolation. Any new suite
  adopting this pattern MUST also add its `.runs/` path to
  `.gitignore`.
- `tempfile::TempDir` MUST be bound to a variable that lives for the
  duration of the test (`let _td = tempfile::tempdir().unwrap();` or
  stored on a helper struct). Dropping the handle before the test ends
  triggers eager cleanup and causes spurious failures under
  concurrent runs.

**CI lint candidate**: a pre-commit check that greps for
`project_root` + `fs::write|fs::create|File::create|Command::.*current_dir`
in the same file, absent the `// read-only` annotation. The prototype
rule would flag `d45_*`, `d6_*`, `d7_*`, `s60_run_tests_reduction_1_*`,
and the default `ReplSessionBuilder` path.

**Exception**: the `tests/*/.runs/{RUN_TS}/{n_label}/` pattern
(`tests/e2e.rs::test_dir`) is permitted. It uses `project_root()` to
locate the suite's `.runs/` parent, then allocates an isolated
per-test directory under `.gitignore`. When adopting this pattern in a
new test suite, also add the corresponding `.runs/` path to
`.gitignore`.
```

## Out of scope for this audit

- **Stdlib-writing tests** — none found. `/stdlib` discipline around
  immutability of checked-in files holds.
- **`.cranelisp-cache/` writes under tempdirs** — the normal case; not
  pollution.
- **Concurrent cache writes from subprocess E2E runs under
  `tests/e2e/.runs/`** — acceptable; isolated by `RUN_TS` + `n_label`.
- **Compile-time fixtures under `tests/fixtures/`** — the
  `stdlib_project/` fixture is stable and should remain read-only.
  The audit's concern is runtime writes to that tree, not the tree
  itself.

## Next step (Wave 2)

1. `/review` reviews this audit and the proposed rule text.
2. `/qa` authors the shared tempdir helper in `tests/helpers/`.
3. Convert the ~10 callsites + the `ReplSessionBuilder` default.
4. Insert the finalised rule into `tests/CLAUDE.md` under §"Test
   Standards".
5. Verify via re-run of the audit greps — the `CONVERT` row count
   should drop to zero (or to a consciously-annotated allowlist).
