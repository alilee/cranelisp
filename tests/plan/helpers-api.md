# E2E Helper API — concrete signatures

Owner: `/qa`. Companion to `helpers.md`.

This document is the contract Phase 1 implements. `helpers.md` is the
intent; this is the API. Every signature has a one-line `///` docstring
stating intent. No implementation bodies — those land in
`tests/helpers/e2e.rs` and `tests/helpers/regex.rs` during Phase 1 §3.

## Module layout

```
tests/helpers/
  e2e.rs       — Cranelisp builder, CrInvocation, CrOutput, PreludeVariant
  regex.rs     — named regex library (compiler::*) + masking helpers
  mod.rs       — pub use re-exports + (during Phases 1-2) the legacy ReplSession
                 shim, deleted in Phase 3.
```

## `tests/helpers/e2e.rs`

### Errors

```rust
/// Failure modes the harness can hit before `CrOutput` is produced.
#[derive(Debug)]
pub enum CrError {
    /// `target/debug/cranelisp` not found at the expected path.
    BinaryNotFound(PathBuf),
    /// Spawn failed (permission, ENOENT on a CWD, etc.).
    SpawnFailed(io::Error),
    /// Child did not exit within the configured timeout.
    Timeout(Duration),
    /// Writing piped stdin failed (broken pipe, child died early).
    StdinWriteFailed(io::Error),
    /// Fixture source path is missing or unreadable.
    FixtureMissing(PathBuf),
}
```

### `Cranelisp` — the builder

```rust
/// One Cranelisp invocation. Builder pattern: configure, then run.
pub struct Cranelisp { /* opaque */ }

impl Cranelisp {
    /// Construct a fresh builder backed by a per-test `tempfile::TempDir`.
    pub fn new() -> Self;

    // === Mode (mutually exclusive) ============================================

    /// Run as REPL (default). Equivalent to no `--run`/`--link`.
    pub fn repl(self) -> Self;
    /// Batch run via `--run <file>`.
    pub fn run(self, file: &str) -> Self;
    /// Link via `--link <file>` only — produces an executable, does not run it.
    pub fn link(self, file: &str) -> Self;
    /// Link via `--link <file>` and then exec the produced binary.
    pub fn link_then_run(self, file: &str) -> Self;

    // === On-disk fixture composition =========================================

    /// Drop a file at `rel_path` under the per-test TempDir; creates parent dirs.
    pub fn file(self, rel_path: &str, contents: &str) -> Self;

    /// Convenience: drop `user.cl` with the given contents (the conventional entry).
    pub fn user(self, contents: &str) -> Self;

    /// Convenience: drop `prelude.cl` with the given contents at TempDir root.
    pub fn prelude(self, contents: &str) -> Self;

    /// Materialise a named prelude variant from the catalogue.
    pub fn with_prelude(self, variant: PreludeVariant) -> Self;

    /// Copy `tests/fixtures/<src>` into TempDir at `<dst>`. Read-only on src.
    pub fn fixture(self, src: &str, dst: &str) -> Self;

    /// Recursive variant: copy `tests/fixtures/<src_dir>/` tree into `<dst_dir>/`.
    pub fn fixture_tree(self, src_dir: &str, dst_dir: &str) -> Self;

    // === Search-path & platform configuration ================================

    /// Add a directory under TempDir to `CRANELISP_LIB`.
    pub fn lib_dir(self, dir_under_tmpdir: &str) -> Self;

    /// **Gated escape hatch — only `tests/stdlib.rs` may legitimately call this.**
    /// Sets `CRANELISP_LIB` to the workspace `stdlib/` directory. Named
    /// verbosely so misuse is visible in PR review and `git grep` audits;
    /// stdlib conformance is the single named exception to the
    /// "tests must not depend on stdlib" rule (root `CLAUDE.md`
    /// §"Design Principles" — Stdlib separation).
    pub fn use_workspace_stdlib_for_stdlib_conformance_only(self) -> Self;

    /// Sets `CRANELISP_PLATFORM_PATH` to the workspace `target/debug/` so the
    /// child can `dlopen` the workspace platform DLLs (`stdio`, `test-capture`).
    pub fn use_workspace_platforms(self) -> Self;

    // === Stdin ==============================================================

    /// Pipe a literal string to the child's stdin.
    pub fn stdin(self, lines: &str) -> Self;

    /// Pipe a slice of lines joined by `\n` (with a trailing newline).
    pub fn stdin_lines(self, lines: &[&str]) -> Self;

    // === Environment & flags ================================================

    /// Append a `(key, val)` to the child's env. Last write wins.
    pub fn env(self, key: &str, val: &str) -> Self;

    /// Append a raw CLI flag passed to the cranelisp binary. Escape hatch.
    pub fn cli_flag(self, flag: &str) -> Self;

    // === Run ================================================================

    /// Materialise the invocation, spawn the child, capture output.
    /// Panics on any `CrError` (binary missing, spawn fail, timeout, IO).
    pub fn output(self) -> CrOutput;

    /// Non-panicking variant — returns the `CrError` instead.
    pub fn try_output(self) -> Result<CrOutput, CrError>;

    // === REPL one-liner shortcuts ============================================

    /// Pipe `lines` to a fresh REPL (no prelude) and return the captured
    /// output. Equivalent to `Cranelisp::new().repl().stdin(lines).output()`.
    pub fn repl_capture(lines: &str) -> CrOutput;

    /// Pipe `lines` to a fresh REPL with the `PrimitivesOnly` prelude variant
    /// and return the captured output. Equivalent to
    /// `Cranelisp::new().repl().with_prelude(PreludeVariant::PrimitivesOnly).stdin(lines).output()`.
    pub fn repl_prims_capture(lines: &str) -> CrOutput;
}
```

### `CrInvocation` — materialised, just before spawn

```rust
/// The fully-resolved invocation snapshot. Constructed by `Cranelisp::output`
/// just before `Command::spawn`. Kept as a separate type so the spawn step
/// is testable in isolation (does the right argv get assembled?).
pub struct CrInvocation {
    /// Path to `target/debug/cranelisp`.
    pub binary: PathBuf,
    /// Argv (excluding `argv[0]`).
    pub args: Vec<String>,
    /// Working directory the child sees (== project_root from its perspective).
    pub cwd: PathBuf,
    /// Environment overlay applied on top of the parent's env.
    pub env: Vec<(String, String)>,
    /// Stdin to pipe.
    pub stdin: String,
    /// Hard wall-clock cap for the child run.
    pub timeout: Duration,
}
```

### `CrOutput` — captured outcome

```rust
/// Captured outcome of a Cranelisp child process.
pub struct CrOutput {
    pub status: ExitStatus,
    pub stdout: String,
    pub stderr: String,
    pub elapsed: Duration,
    pub tmpdir: PathBuf,
    // _td: tempfile::TempDir held internally so cleanup runs on drop.
}

impl CrOutput {
    // === Exit-code shortcuts ================================================

    /// Assert the child exited with code 0.
    pub fn assert_ok(self) -> Self;
    /// Assert the child exited with a specific code.
    pub fn assert_exit(self, code: i32) -> Self;
    /// Assert the child terminated by signal (no exit code, e.g. SIGSEGV).
    pub fn assert_signaled(self) -> Self;

    // === Stdout assertions ==================================================

    /// Assert stdout equals expected exactly.
    pub fn assert_stdout_eq(self, expected: &str) -> Self;
    /// Assert stdout contains the literal substring.
    pub fn assert_stdout_contains(self, needle: &str) -> Self;
    /// Assert stdout contains EVERY substring in `needles`. Folds the
    /// `out.stdout.contains(a) && out.stdout.contains(b)` pattern into a
    /// single assertion that names the first missing needle in the panic
    /// message.
    pub fn assert_stdout_contains_all(self, needles: &[&str]) -> Self;
    /// Assert stdout does NOT contain the substring. Negative-coverage
    /// counterpart to `assert_stdout_contains`.
    pub fn assert_stdout_does_not_contain(self, needle: &str) -> Self;
    /// Assert stdout matches the given pre-compiled regex (use a helper from `regex::compiler`).
    pub fn assert_stdout_matches(self, re: &Regex) -> Self;

    // === Stderr assertions ==================================================

    /// **Spec-correct check**: when no `CRANELISP_*_TRACE` env var is set
    /// (the harness default), stderr MUST be empty per `repl/spec.md §5.1`.
    pub fn assert_stderr_empty(self) -> Self;
    /// Assert stderr contains the literal substring.
    pub fn assert_stderr_contains(self, needle: &str) -> Self;

    // === Snapshot / golden ==================================================

    /// Compare against `tests/fixtures/golden/<name>.txt` exactly.
    /// Updates with `CRANELISP_TEST_UPDATE_GOLDENS=1`.
    pub fn assert_golden(self, name: &str) -> Self;
    /// Compare against the golden after applying each regex as a mask
    /// (every match replaced with the regex's literal source string).
    /// Use for output containing pointer addresses, timing, etc.
    pub fn assert_golden_masked(self, name: &str, masks: &[&Regex]) -> Self;

    // === Tmpdir inspection ==================================================

    /// Read a file under the per-test TempDir. Panics if missing.
    pub fn read_tmp(&self, rel_path: &str) -> String;
    /// Test whether a path exists under the per-test TempDir.
    pub fn tmp_exists(&self, rel_path: &str) -> bool;

    // === Cache-hit pattern (run binary twice in same TempDir) ==============

    /// Re-launch a fresh `Cranelisp` builder bound to the same TempDir,
    /// preserving the prior invocation's on-disk state (notably
    /// `.cranelisp-cache/`). Used to test cache-hit behaviour:
    ///
    /// ```ignore
    /// let first = Cranelisp::new().run("user.cl").user("...").output();
    /// let second = first.run_again().output();
    /// ```
    ///
    /// The TempDir handle transfers from the consumed `CrOutput` into
    /// the new `Cranelisp`; `first.tmpdir` becomes invalid after the
    /// `run_again()` call.
    pub fn run_again(self) -> Cranelisp;
}
```

### `PreludeVariant` — named prelude catalogue

```rust
/// Curated test prelude variants. Stored as fixture files under
/// `tests/fixtures/preludes/`; the harness copies the right one to
/// `prelude.cl` in the per-test TempDir.
pub enum PreludeVariant {
    /// No prelude file dropped.
    None,
    /// `(import [primitives [*]])` only — bare primitive names, no
    /// traits, no ADTs, no operators. File: `preludes/primitives-only.cl`.
    PrimitivesOnly,
    /// Option, Result, Num, Eq, Ord — `tests/fixtures/preludes/test-standard.cl`
    /// (currently the existing `tests/fixtures/prelude.cl` content).
    TestStandard,
}
```

There is **no `WorkspaceStdlib` variant.** The workspace stdlib is
reached only via `use_workspace_stdlib_for_stdlib_conformance_only()`,
gated as documented above. Reasoning: making it a `PreludeVariant`
value puts it on the same shelf as `None`/`PrimitivesOnly`/`TestStandard`,
inviting casual selection. A separately-named, verbosely-named method
forces a deliberate decision and is greppable.

## Mode-equivalence helper — `run_through_all_modes`

Per `tests/plan/PLAN.md §"Mode canonicalisation"` and
`helpers.md §"Mode-equivalence"`, a curated subset of tests runs one
program through all six mode×cache permutations and asserts equivalent
observable behaviour. The helper lives in `tests/helpers/e2e.rs`
alongside `Cranelisp`.

### Inputs and shape

```rust
/// One observation reduced to canonical form. The integer is the value
/// `main` returned (or — for REPL paths — the integer `:primitives/Int N`
/// printed when `(main)` was invoked). `None` means the permutation
/// could not produce an observation (compilation error, link failure, …);
/// callers may use this to assert all-fail-the-same-way for negative tests.
#[derive(Debug, Clone)]
pub struct PermutationOutcome {
    /// The mode + cache state this outcome describes. Used by the
    /// equivalence assertion's diff messages.
    pub label: &'static str,
    /// Canonical observation: the Int value `main` returned. None on
    /// non-Int / failure paths.
    pub observed: Option<i32>,
    /// Raw stdout for diagnostics on failure.
    pub stdout: String,
    /// Raw stderr for diagnostics on failure.
    pub stderr: String,
    /// Process exit code (for --run / --link permutations) or REPL
    /// driver exit code (typically 0 if EOF clean).
    pub exit_code: Option<i32>,
}

/// All six permutations' observations.
#[derive(Debug)]
pub struct AllModesResult {
    pub repl_fresh:  PermutationOutcome,
    pub repl_cached: PermutationOutcome,
    pub run_fresh:   PermutationOutcome,
    pub run_cached:  PermutationOutcome,
    pub link_fresh:  PermutationOutcome,
    pub link_cached: PermutationOutcome,
}

impl AllModesResult {
    /// Assert all six observations agree on the canonical Int. Panics
    /// with a per-permutation diff when any path diverges.
    pub fn assert_all_equivalent(self) -> Self;

    /// Assert all six observations match the given expected Int.
    /// Stronger than `assert_all_equivalent` — also pins the value.
    pub fn assert_all_equal(self, expected: i32) -> Self;
}

/// Run one program through all six mode×cache permutations.
///
/// Program shape: `(defn main [] expr-returning-Int)`. The harness
/// materialises the program in `user.cl` under one shared TempDir,
/// runs each permutation in deterministic order (REPL fresh → REPL
/// cached → --run fresh → --run cached → --link fresh → --link
/// cached), and returns observations.
///
/// Use only for the mode-equivalence subset (per
/// `tests/plan/PLAN.md §"Mode canonicalisation"`). Bulk language
/// conformance MUST NOT use this helper — use REPL canonical directly.
///
/// `prelude` selects the prelude variant (typically `TestStandard`
/// for tests that use operators). `PreludeVariant::None` is valid for
/// programs that import primitives explicitly.
pub fn run_through_all_modes(
    program: &str,
    prelude: PreludeVariant,
) -> AllModesResult;
```

### Canonical observation form

Each test's program is `(defn main [] expr)` returning Int. For each
permutation:

| Permutation | Raw observation | Canonical reduction |
|---|---|---|
| REPL fresh | stdin pipes `(main)` after `user.cl` is auto-imported (or after the program is piped); stdout substring `:primitives/Int N` | parse the last `:primitives/Int N` line → `N` |
| REPL cached | re-spawn binary in same TempDir; replay stdin; observe again | same parse |
| `--run` fresh | process exit code | exit code → `N` |
| `--run` cached | re-spawn binary in same TempDir; observe exit | exit code → `N` |
| `--link` fresh | link, then run produced binary; produced exit code | produced exit code → `N` |
| `--link` cached | re-spawn link in same TempDir; produced exit | produced exit code → `N` |

For REPL paths, the harness pipes (in order):

```
<program>
(main)
```

— `user.cl` autoload is bypassed by piping the program directly into
the REPL. (The TempDir does not contain a `user.cl` for REPL
permutations; only `prelude.cl` if `prelude != None`.) For `--run` /
`--link` permutations, `user.cl` is materialised in the TempDir.

### Cached-permutation shape

For each cached permutation, the harness:

1. Runs the fresh permutation first to populate `.cranelisp-cache/`.
2. Re-spawns the same mode invocation in the same TempDir,
   transferring the on-disk state (`.cranelisp-cache/`, `user.cl`,
   `prelude.cl`, link artefacts) from fresh-run to cached-run.
3. Asserts the second run's observation equals the first.

The TempDir is shared across all six permutations using a single
`tempfile::TempDir` held by the helper for its full duration. Per the
existing `Cranelisp::run_again()` pattern, the implementation transfers
TempDir ownership through `CrOutput::run_again()` rather than
constructing fresh TempDirs.

### Why a separate helper, not a `Cranelisp` method

The cross-mode harness needs to (a) reset stdin between REPL fresh and
REPL cached, (b) decide per-mode whether to materialise `user.cl` or
not, (c) parse stdout differently per permutation. A free function
keeps the `Cranelisp` builder narrow (one invocation per builder) and
makes the cross-mode orchestration explicit at the call site.

## `tests/helpers/regex.rs`

```rust
//! Named regex library. Tests reference the helper, never embed the
//! raw pattern. Discipline rule: every check that matches compiler
//! output uses a helper from first occurrence (see `helpers.md`
//! §"Regex helper library").

use once_cell::sync::Lazy;
use regex::Regex;

/// Compiler-output regexes. Each has documented capture groups.
pub mod compiler {
    use super::*;

    /// `/time` line. Matches: `elapsed: 1.234 ms` (or `µs`, `s`).
    /// Captures: (1) value, (2) unit.
    pub fn time_line() -> &'static Regex {
        static RE: Lazy<Regex> = Lazy::new(|| Regex::new(
            r"^elapsed:\s+(\d+(?:\.\d+)?)\s+(ms|µs|s)\s*$"
        ).unwrap());
        &RE
    }

    /// REPL prompt line — `<module> ` (no value).
    /// Captures: (1) module name.
    pub fn repl_prompt() -> &'static Regex {
        static RE: Lazy<Regex> = Lazy::new(|| Regex::new(
            r"^([a-zA-Z][a-zA-Z0-9._-]*)\s+$"
        ).unwrap());
        &RE
    }

    /// Compiler error: `error: <msg> at <file>:<line>:<col>`.
    /// Captures: (1) msg, (2) file, (3) line, (4) col.
    pub fn error_line() -> &'static Regex {
        static RE: Lazy<Regex> = Lazy::new(|| Regex::new(
            r"^error:\s+(.+?)\s+at\s+([^:]+):(\d+):(\d+)\s*$"
        ).unwrap());
        &RE
    }

    /// Hex pointer (any width). For golden masking out alloc addresses.
    /// Captures: (1) the hex literal.
    pub fn alloc_addr() -> &'static Regex {
        static RE: Lazy<Regex> = Lazy::new(|| Regex::new(
            r"\b0x[0-9a-fA-F]+\b"
        ).unwrap());
        &RE
    }
}

/// Convenience masking primitives — apply a regex to a string,
/// returning the masked copy with each match replaced by the
/// regex's source pattern (visible placeholder in golden diffs).

/// Replace every hex pointer in `s` with `<ADDR>`.
pub fn mask_alloc_addrs(s: &str) -> String;

/// Replace every `/time`-style line in `s` with `<TIME>`.
pub fn mask_timing(s: &str) -> String;
```

The library accretes one helper per stable-shape compiler-output
format the test suite depends on. New entries are added by Phase 2
ports as needed; first occurrence can be one-off; second occurrence
generalises.

## Gating mechanism for `use_workspace_stdlib_for_stdlib_conformance_only`

**Choice: rename to `use_workspace_stdlib_for_stdlib_conformance_only`.**

Of the three options /arch suggested (marker arg, `// SAFETY:` annotation,
verbose rename), the rename is preferred because: (a) it is enforced by
the type system — every call site reads `Cranelisp::new().use_workspace_stdlib_for_stdlib_conformance_only()`,
making misuse self-evident in code review and `git grep` audits;
(b) marker args clutter every callsite even in the legitimate
`tests/stdlib.rs`; (c) `// SAFETY:` annotations are not enforced and
drift over time as people forget the convention.

## `output_then_run_again` cache-hit pattern — design note

The cache-hit pattern needs to (1) preserve the per-test TempDir
across two invocations, (2) read the second invocation's output
without losing the first's, (3) keep the syntax linear/builder-style.

The chosen shape on `CrOutput` is `run_again() -> Cranelisp`: it
consumes the `CrOutput` (transferring TempDir ownership into a new
builder), keeping the assertion-then-run cadence linear:

```rust
let first = Cranelisp::new().run("user.cl").user("...").output().assert_ok();
let second = first.run_again().output().assert_ok();
assert_eq!(first.stdout, /* … but `first` is moved into run_again */);
```

In practice, tests that compare two outputs capture the relevant
fields off `first` (e.g. `let s1 = first.stdout.clone();`) before
calling `run_again()`. That keeps the API minimal — no separate
`output_into_then_run_again` variant.
