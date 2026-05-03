# E2E Helper Environment — design

Owner: `/qa`. Implementation lives in `tests/helpers/`.

This document specifies the e2e helper API surface. The goal is a
**streamlined harness that lets a test author assemble an isolated
cranelisp execution with controlled imports and preludes, in a few
lines of Rust**. Helpers are process-spawn + I/O capture + tmpdir
fixture machinery — never session builders.

## Design constraints

1. **Subprocess only.** Every helper spawns `target/debug/cranelisp` as
   a child process. No `cranelisp::session_v4::CompilerSession`, no
   `SharedState`, no internal-API construction. Per the strategy
   direction recorded in
   `memory/project_test_strategy.md` (2026-05-03).
2. **Isolated by construction.** Every test gets its own fresh
   tmpdir; no checked-in path is mutated. Reads from
   `project_root()` are limited to `target/debug/cranelisp`,
   `stdlib/`, `target/debug/*.so/.dylib/.dll` (platform DLLs),
   and `tests/fixtures/` — and require a `// read-only` annotation
   per `tests/CLAUDE.md §"Fresh Temp Directory per Test"`.
3. **Composable.** A test author should be able to specify "no
   prelude, this user.cl, these helper modules, this stdin" in a
   builder chain that reads as one expression. No manual file
   layout, no manual env-var assembly.
4. **One small surface.** The whole API fits in one file
   (`tests/helpers/e2e.rs`) and one struct family (`Cranelisp`,
   `CrInvocation`, `CrOutput`). Existing
   `tests/helpers/mod.rs::ReplSession` (the integration-tier wrapper)
   stays for back-compat with the ~30 pre-existing test files but
   is **frozen** — no new methods, no new entry points.
5. **Determinism via test-side exclusion + binary configuration.** The
   harness does NOT force a global "deterministic output mode" on the
   binary. Two narrower mechanisms cover the actual need:
   (a) Tests **exclude non-deterministic content** from golden / equality
   comparisons via the regex helper library (§"Regex helper library").
   `/time` output is matched by a named regex, not bytewise. Allocation
   pointers in trace lines are matched by `compiler::alloc_addr()`, etc.
   (b) Tests that depend on event **ordering** (scheduler trace, worker
   interleaving, cache-hit races) configure the binary via
   `Cranelisp.toml` and CLI flags (§"Configuration: Cranelisp.toml + CLI
   options") — e.g., set worker count to 1 to serialise event emission,
   pin scheduler quantum, etc. The harness exposes these as builder
   methods.
   The only universal "stable output" requirement is the REPL prompt
   shape (FIXME 0112) — needed for stdin scripting, not for golden
   determinism. The blanket `--deterministic` mode (the original FIXME
   0110 framing) is rejected as overdone.
6. **Fail loudly on environmental drift.** If the binary is missing,
   stdlib-relative path doesn't resolve, or the test prelude file
   isn't found, the harness panics with a clear diagnostic naming
   the missing path — not a silent fallback.

## Surface — pseudocode sketch

The pseudocode below is illustrative; final names land in the
implementation. Builder chains return `Self` to compose.

### Top-level entry: `Cranelisp::new()`

```rust
/// One Cranelisp invocation. Builder pattern: configure, then run.
///
/// Defaults:
///  - mode: REPL (no `--run`, no `--link`)
///  - prelude: NONE (auto-discovered prelude file is suppressed)
///  - stdin: empty
///  - lib_dirs: empty
///  - env: deterministic-output ON, no trace flags
///  - cwd: a fresh per-test TempDir (held inside the builder)
pub struct Cranelisp { /* ... */ }

impl Cranelisp {
    pub fn new() -> Self;

    // === Mode selection (mutually exclusive) ===
    pub fn repl(self) -> Self;          // default
    pub fn run(self, file: &str) -> Self;     // --run <file>
    pub fn link(self, file: &str) -> Self;    // --link <file>
    pub fn link_then_run(self, file: &str) -> Self; // --link, then exec the produced binary

    // === On-disk fixture composition ===
    /// Drop a file into the per-test tmpdir at the given relative path.
    /// Creates parent dirs. Path is interpreted relative to the cwd the
    /// child will see.
    pub fn file(self, rel_path: &str, contents: &str) -> Self;

    /// Convenience: the entry file. Usually `user.cl` for REPL mode.
    pub fn user(self, contents: &str) -> Self;        // file("user.cl", ...)

    /// Convenience: a prelude file at `prelude.cl`.
    pub fn prelude(self, contents: &str) -> Self;

    /// Convenience: well-known reusable preludes from the test prelude
    /// catalogue. See "Prelude variants" below.
    pub fn with_prelude(self, variant: PreludeVariant) -> Self;

    /// Copy a fixture file (or tree) from `tests/fixtures/<src>` into the
    /// tmpdir at <dst>. Read-only on `tests/fixtures/`.
    pub fn fixture(self, src: &str, dst: &str) -> Self;
    pub fn fixture_tree(self, src_dir: &str, dst_dir: &str) -> Self;

    // === Search-path & platform configuration ===
    pub fn lib_dir(self, dir_under_tmpdir: &str) -> Self;   // adds to CRANELISP_LIB
    pub fn use_workspace_stdlib(self) -> Self;              // CRANELISP_LIB=<root>/stdlib
    pub fn use_workspace_platforms(self) -> Self;           // CRANELISP_PLATFORM_PATH=<root>/target/debug

    // === Stdin ===
    pub fn stdin(self, lines: &str) -> Self;
    pub fn stdin_lines(self, lines: &[&str]) -> Self;       // joined with "\n"

    // === Environment ===
    pub fn env(self, key: &str, val: &str) -> Self;
    pub fn trace(self, kind: TraceKind) -> Self;            // CRANELISP_RC_TRACE=1, etc.

    // === Configuration: Cranelisp.toml + CLI options ===
    /// Use a named toml variant from the catalogue. See "Variants" in
    /// §"Configuration: Cranelisp.toml + CLI options".
    pub fn with_toml(self, variant: TomlVariant) -> Self;
    /// Drop a raw `Cranelisp.toml` into the tmpdir with the given
    /// contents. Escape hatch for one-off configurations.
    pub fn toml_raw(self, contents: &str) -> Self;
    /// Append a raw CLI flag passed to the cranelisp binary. Escape
    /// hatch — most tests use `.with_toml(...)`.
    pub fn cli_flag(self, flag: &str) -> Self;

    // === Timeouts ===
    /// Default: 10s. Tests that genuinely need longer announce it.
    pub fn timeout(self, d: Duration) -> Self;

    // === Run ===
    pub fn output(self) -> CrOutput;            // panics on spawn failure or timeout
    pub fn try_output(self) -> Result<CrOutput, CrError>;
}
```

### Output: `CrOutput`

```rust
/// Captured outcome of a Cranelisp child process.
pub struct CrOutput {
    pub status: ExitStatus,
    pub stdout: String,         // utf-8 lossy
    pub stderr: String,
    pub stderr_traces: Vec<TraceLine>,   // pre-parsed trace lines (FIXME 0111)
    pub stderr_non_trace: String,        // stderr minus trace lines
    pub elapsed: Duration,
    pub tmpdir: PathBuf,        // for inspecting cache, .o, etc.
    // _td: held internally so it lives until CrOutput drops
}

impl CrOutput {
    // === Exit-code shortcuts ===
    pub fn assert_ok(self) -> Self;
    pub fn assert_exit(self, code: i32) -> Self;
    pub fn assert_signaled(self) -> Self;       // exit=None (e.g., SIGSEGV)

    // === Stdout assertions ===
    pub fn assert_stdout_eq(self, expected: &str) -> Self;
    pub fn assert_stdout_contains(self, needle: &str) -> Self;
    pub fn assert_stdout_matches(self, regex: &str) -> Self;

    // === Stderr assertions ===
    /// Asserts NO non-trace lines on stderr. The spec rule
    /// (`repl/spec.md §5.1`) is "errors on stdout, stderr is for traces
    /// only"; this is the negative companion.
    pub fn assert_stderr_traces_only(self) -> Self;
    pub fn assert_stderr_contains(self, needle: &str) -> Self;
    pub fn assert_stderr_empty(self) -> Self;

    // === Snapshot ===
    /// Compare against a golden file under tests/fixtures/golden/<name>.txt;
    /// updates with CRANELISP_TEST_UPDATE_GOLDENS=1.
    pub fn assert_golden(self, name: &str) -> Self;

    // === Tmpdir inspection ===
    pub fn read_tmp(&self, rel_path: &str) -> String;
    pub fn tmp_exists(&self, rel_path: &str) -> bool;
}
```

### Errors

```rust
pub enum CrError {
    BinaryNotFound(PathBuf),
    SpawnFailed(io::Error),
    Timeout(Duration),
    StdinWriteFailed(io::Error),
}
```

### Trace toggles

```rust
pub enum TraceKind {
    Rc,        // CRANELISP_RC_TRACE=1
    Infer,     // CRANELISP_INFER_TRACE=1
    Codegen,   // CRANELISP_CODEGEN_TRACE=1
    Module,    // CRANELISP_MODULE_TRACE=1
    Macro,     // CRANELISP_MACRO_TRACE=1
    Scheduler, // CRANELISP_SCHEDULER_TRACE=1 (Sprint 61 Slice 0)
    IoTrampoline, // CRANELISP_IO_TRAMPOLINE_TRACE=1 (Sprint 61 Slice 0)
}
```

`TraceLine` holds `kind: TraceKind`, `payload: String`, `raw: String`.
Pre-parsing stderr trace lines into `stderr_traces` (and stripping them
from `stderr_non_trace`) is what enables `assert_stderr_traces_only` —
this depends on FIXME 0111 (binary tags trace output unambiguously).

### Prelude variants

A small named catalogue of stable test preludes lives in
`tests/fixtures/preludes/`:

```rust
pub enum PreludeVariant {
    /// Empty file. Prelude resolution finds it and loads nothing.
    /// Use to suppress auto-discovered `tests/fixtures/prelude.cl`
    /// without leaving the prelude tier ambiguous.
    Empty,

    /// The current `tests/fixtures/prelude.cl` — Option, Result, Num,
    /// Eq, Ord, basic impls. The default for tests that need
    /// operators or ADT types.
    TestStandard,

    /// Just `(import [primitives [*]])`. For tests that want bare
    /// primitive names but no traits, ADTs, or operators.
    PrimitivesOnly,

    /// The actual workspace stdlib (`stdlib/prelude.cl`). For
    /// stdlib conformance tests in `tests/stdlib.rs` only.
    WorkspaceStdlib,
}
```

A test that wants no prelude at all uses `Cranelisp::new()` without
calling `with_prelude` — the harness defaults to "no prelude file,
no auto-discovery". A test that wants a custom prelude uses
`.prelude("(deftype ...)")` to drop a `prelude.cl` into the tmpdir
and let prelude resolution pick it up.

## Usage examples

The pseudocode below shows the intended call sites. These are spec
illustrations, not committed tests.

### One-shot batch run

```rust
#[test]
fn arith_via_run() {
    // spec: 04-expressions §X — arithmetic
    Cranelisp::new()
        .run("user.cl")
        .user("(defn main [] (add-i64 1 2))")
        .output()
        .assert_ok()
        .assert_stdout_eq("3\n")
        .assert_stderr_empty();
}
```

### REPL session with stdin script

```rust
#[test]
fn repl_redefinition() {
    // spec: 12-runtime §X — REPL redefinition updates callers
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin_lines(&[
            "(defn f [] 1)",
            "(defn g [] (f))",
            "(g)",
            "(defn f [] 2)",
            "(g)",
        ])
        .output()
        .assert_ok()
        .assert_stdout_contains("1")
        .assert_stdout_contains("2");
}
```

### Multi-file project with imports

```rust
#[test]
fn cross_module_import() {
    // spec: 08-modules §X — qualified import
    Cranelisp::new()
        .run("user.cl")
        .file("helper.cl", "(defn helper-val [] 42)")
        .user("(import [helper [helper-val]]) (defn main [] (helper-val))")
        .output()
        .assert_ok()
        .assert_stdout_eq("42\n");
}
```

### No prelude, bare language

```rust
#[test]
fn bare_primitive_in_repl() {
    // spec: appendix-a-builtins — bare primitives load without prelude
    Cranelisp::new()
        .repl()
        // no .with_prelude(..) — fully bare
        .stdin("(primitives/add-i64 1 2)\n")
        .output()
        .assert_ok()
        .assert_stdout_contains("3");
}
```

### Trace assertion

```rust
#[test]
fn rc_balanced_for_string_concat() {
    // spec: 12-runtime §RC — alloc/dealloc balance for str-concat
    let out = Cranelisp::new()
        .run("user.cl")
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .user(r#"(defn main [] (str-concat "a" "b"))"#)
        .trace(TraceKind::Rc)
        .output()
        .assert_ok();
    let allocs = out.stderr_traces.iter().filter(|t| t.payload.contains("alloc")).count();
    let frees  = out.stderr_traces.iter().filter(|t| t.payload.contains("free")).count();
    assert_eq!(allocs, frees, "RC imbalance");
}
```

### Link-then-run (E2E for the executable-generation surface)

```rust
#[test]
fn link_produces_runnable_binary() {
    // spec: 12-runtime §linking — --link produces a standalone exe
    Cranelisp::new()
        .link_then_run("user.cl")
        .user("(defn main [] 99)")
        .output()
        .assert_exit(99);
}
```

### Snapshot / golden

```rust
#[test]
fn list_command_categorises_user_defs() {
    // spec: repl/spec.md §3.3 — /list categorisation
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .stdin("(defn foo [] 1)\n/list\n")
        .output()
        .assert_ok()
        .assert_golden("repl/list_after_one_defn");
}
```

## Regex helper library

Anything in compiler output (as opposed to user-program output) gets a
named helper in `tests/helpers/regex.rs` (or a `regex` submodule).
Tests reference the helper, never embed the raw pattern. If the
compiler's output format changes, ONE place updates and every dependent
test moves with it.

**Discipline:** every check that matches compiler output uses a
helper — even on first occurrence with a single caller. The first
helper for a pattern can be narrowly fitted to its one use case;
generalisation (parameterising, splitting, broadening) happens on the
second and subsequent callers. The point is the indirection: tests
never carry the literal regex, even when the helper is one-off,
because the first time the format changes (S-many sprints from now)
the search is `helpers/regex.rs`, not `git grep`.

```rust
// tests/helpers/regex.rs — illustrative
pub mod compiler {
    /// `/time` line: "elapsed: 1.234 ms" → captures unit
    pub fn time_line() -> &'static Regex { /* ... */ }
    /// REPL prompt: "<module> "
    pub fn repl_prompt() -> &'static Regex { /* ... */ }
    /// RC trace: "[rc] alloc 0x7f8a4c001000 len=24 type=String" → captures type+len
    pub fn rc_alloc_line() -> &'static Regex { /* ... */ }
    pub fn rc_free_line() -> &'static Regex { /* ... */ }
    /// Allocation address (any hex pointer) — for masking out of golden cmps
    pub fn alloc_addr() -> &'static Regex { /* ... */ }
    /// Compiler error: "error: ... at file.cl:LINE:COL" → captures msg/file/line/col
    pub fn error_line() -> &'static Regex { /* ... */ }
    /// Trace tag: any "[trace:CHANNEL] ..." line (depends on FIXME 0111)
    pub fn trace_line() -> &'static Regex { /* ... */ }
    // … one helper per stable-shape compiler output format
}
```

Used through `CrOutput` masking and matching primitives:

```rust
// Mask non-deterministic content before golden comparison
output.assert_golden_masked("repl/list_after_one_defn", &[
    helpers::compiler::alloc_addr(),
    helpers::compiler::time_line(),
]);

// Direct regex assertion via named helper
output.assert_stderr_matches(helpers::compiler::error_line());

// Filter trace lines from stderr (replaces force-determinise approach)
let non_trace = helpers::compiler::strip_traces(&output.stderr);
assert_eq!(non_trace.trim(), "");
```

(See "Discipline" above — every check uses a helper from first
occurrence; the library accretes one-off entries that get generalised
on second and subsequent uses. This is intentional: the library is the
catalogue of every compiler-output shape any test depends on, not just
the popular ones.)

## Configuration: `Cranelisp.toml` + CLI options

The binary reads `Cranelisp.toml` from its CWD (per
`design/int/cranelisp-toml.md`). Tests use this to control behaviour
that affects observable output — most importantly event ordering for
scheduler/worker traces and prompt stability.

### Variants — named toml configurations (mirror the prelude pattern)

Like `PreludeVariant`, common toml setups live in a small named
catalogue. Tests reference the variant; the harness materialises the
right `Cranelisp.toml` content into the tmpdir.

```rust
pub enum TomlVariant {
    /// No `Cranelisp.toml` file written. Binary uses its built-in
    /// defaults. The default for tests that don't care about
    /// configuration.
    None,

    /// `[scheduler] workers = 1` — single worker thread.
    /// Use for any test that asserts on scheduler-trace ordering.
    SerialWorkers,

    /// `[cache] enabled = false` — disable on-disk module cache.
    /// Use for tests exercising fresh-compile paths.
    NoCache,

    /// `[repl] show_times = false` — suppress prompt-timing display.
    /// Use for any stdin-scripted REPL test using `assert_stdout_eq`
    /// or `assert_golden` (the prompt shape must be byte-stable).
    StablePrompt,

    /// Combination: `SerialWorkers + NoCache + StablePrompt` — the
    /// catch-all "scriptable e2e" variant. Most stdin-driven REPL
    /// tests want this.
    Scriptable,
}
```

Stored in `tests/fixtures/tomls/` as named files (`serial-workers.toml`,
`no-cache.toml`, `stable-prompt.toml`, `scriptable.toml`); the harness
copies the right one into the tmpdir.

### Builder methods

```rust
Cranelisp::new()
    .with_toml(TomlVariant::Scriptable)   // serial workers + no cache + stable prompt
    .repl()
    .stdin_lines(&[ "(defn f [] 1)", "(f)" ])
    .output()
    .assert_ok()
    .assert_stdout_eq("user> 1\nuser> ");

// Targeted single-knob variant
Cranelisp::new()
    .with_toml(TomlVariant::SerialWorkers)
    .trace(TraceKind::Scheduler)
    .stdin("(defn f [] 1) (f)\n")
    .output()
    .assert_ok()
    .assert_stderr_traces_only();
```

Add a new variant when a SECOND test wants the same combination —
same discipline as the prelude catalogue and the regex helper library.
First occurrence of a new combination can use `.toml_raw(contents)`
inline; second occurrence triggers extraction to a named variant.

### Escape hatches

```rust
// Arbitrary toml content for one-off configurations
Cranelisp::new().toml_raw(r#"
    [scheduler]
    workers = 2
    quantum_ms = 10
"#);

// Append a raw CLI flag
Cranelisp::new().cli_flag("--no-cache");
```

The schema the binary recognises is owned by `/int`; harness named
variants are the curated, expected-stable subset. Any flag the harness
depends on contractually goes through a `/int` FIXME (per "Coupling to
CLI surface" trade-off below).

## What the harness does NOT provide

These were considered and explicitly rejected:

- **Session builders.** `let s = Cranelisp::session().bare()...` —
  no. The whole point is to detach from the in-process session
  shape. Use `repl()` and drive via stdin.
- **Stage-by-stage Rust APIs.** "Get me the AST", "get me the
  CheckResult", "get me the CLIF". Those belong inside the
  owning crate's unit tests. If `/qa` needs to verify a
  stage-output property at the spec level, the verification is
  through observable behaviour (REPL `/sexp`, `/ast`, `/clif`
  slash commands; a `--dump-ast` CLI flag if one is added).
- **Mock platform DLLs constructed in-test.** The
  `test-capture` DLL exists as a real artefact under
  `target/debug/`; the harness loads it via
  `use_workspace_platforms()`. If a test needs a different mock,
  it goes in as a real DLL crate.
- **Inline trait preludes pasted as `const &str`.** The current
  `e2e.rs::NUM_TRAIT_PRELUDE` / `EQ_TRAIT_PRELUDE` /
  `ORD_TRAIT_PRELUDE` are migration debt. Replace with
  `with_prelude(PreludeVariant::TestStandard)` (which already
  defines Num/Eq/Ord) during the dedicated port sprint.

- **Blanket `--deterministic` binary mode.** Test-side exclusion via
  the regex helper library + toml/CLI configuration covers the actual
  need. See §"Determinism" in design constraints (constraint 5).

## Implementation phasing

This is the implementation roadmap; not part of the normative API.

1. **Phase 1 — build**. Land `Cranelisp` / `CrOutput` / regex helper
   library / toml + CLI configuration. Implement against existing
   binary surface; FIXMEs 0111/0112 (trace channel separation, REPL
   ready sentinel) are the load-bearing `/int` dependencies.
2. **Phase 2 — port + coverage** (dedicated sprint). Port every test
   in `tests/` from the integration-tier helpers (`compile_and_run*`,
   `repl_session*`, etc.) into the e2e tier using `Cranelisp`. As each
   test ports, add or update its row in `tests/plan/PLAN.md` so
   coverage documentation builds in lockstep with the migration.
3. **Phase 3 — remove legacy**. Delete `tests/helpers/mod.rs::ReplSession`
   and the integration-tier helpers; delete or rewrite any tests that
   resisted the port (with explicit rationale per holdout).
4. **Phase 4 — crate refactors begin**. Only after Phase 3 is complete
   does FIXME 0109 (int decomposition) and other crate refactor work
   begin — by then the test suite is decoupled from internal session
   shapes and the refactors can proceed freely without breaking tests
   that reach into `session_v4`/`worker`.

This is a **dedicated migration sprint**, NOT opportunistic
rewrite-on-touch. Decision: maintaining two test patterns side-by-side
across multiple sprints accumulates more drift than a single port-pass
costs. Sprint sequencing lock-in: test-port sprint precedes any crate-
refactor sprint that touches `session_v4`/`worker`. Tracked by
FIXME 0115 (`/sprint` planning).

## Trade-offs the design accepts

- **Slower than in-process.** Subprocess spawn is ~50–100ms per
  test on a warm cache. Unit tests inside crates remain the place
  for sub-millisecond microbenchmark assertions. The full e2e
  suite needs to stay under the 30-second total cap
  (`tests/CLAUDE.md`); we manage that by parallelising via
  `cargo nextest run` and keeping each e2e test minimal.
- **No intermediate-state inspection.** A failing e2e test cannot
  ask "what did the type checker infer for x?". It can ask "what
  did `/type x` print?" via a stdin script. If that is not enough
  to diagnose, the next step is a `/dev`-owned unit test inside
  the suspected crate, per
  `tests/CLAUDE.md §"Isolating Cross-Crate Failures"`.
- **Coupling to CLI surface.** Every CLI flag the harness uses
  (FIXMEs 0110/0111/0112; `--run`, `--link`, etc.) is a contract
  with `/int`. Changes go through FIXME, not silent rename.
