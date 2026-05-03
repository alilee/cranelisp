# E2E Helper Environment — design

Owner: `/qa`. Implementation lives in `tests/helpers/`.

This document specifies the e2e helper API surface. The goal is a
**streamlined harness that lets a test author assemble an isolated
cranelisp execution with controlled imports and preludes, in a few
lines of Rust**. Helpers are process-spawn + I/O capture + tmpdir
fixture machinery — never session builders.

Companion: `helpers-api.md` — concrete Rust signatures the Phase 1
implementation codes against. This document is the design intent;
`helpers-api.md` is the contract.

## Design constraints

1. **Subprocess only.** Every helper spawns `target/debug/cranelisp` as
   a child process. No `cranelisp::session_v4::CompilerSession`, no
   `SharedState`, no internal-API construction. Per the strategy
   direction recorded in
   `memory/project_test_strategy.md` (2026-05-03).

   **Canonical mode for language-conformance bulk = REPL.** Per the
   Sprint 64 Wave 2.5 architecture decision recorded in
   `tests/plan/PLAN.md §"Mode canonicalisation — REPL is the canonical
   surface for language conformance"`: language-conformance tests run
   through REPL, not `--run`. The mode-equivalence subset
   (`build_confidence.rs`) additionally exercises a curated handful
   through all six mode×cache permutations, asserting equivalent
   observable behaviour — that's the empirical validation of single-
   pipeline convergence (Principles 11–13; Decisions 22, 25, 41).
   `--run` and `--link` remain in the harness surface for
   mode-specific tests (cache, examples, exemplar, build_confidence
   smoke) and the mode-equivalence permutations.

2. **Isolated by construction.** Every test gets its own fresh
   `tempfile::TempDir`, used as the child's CWD. Because
   `project_root = std::env::current_dir()` (per
   `design/int/repl-lifecycle.md §"Project root resolution"`), this
   makes the TempDir the project root the binary sees — and per
   `design/backend/module-caching.md §"Cache directory layout"` the
   cache lives at `{project_root}/.cranelisp-cache/`, so cache state
   is isolated to the per-test TempDir by construction. No
   checked-in path is mutated. Reads from `project_root()` are
   limited to `target/debug/cranelisp`, `stdlib/`, the platform DLLs
   under `target/debug/`, and `tests/fixtures/` — and require a
   `// read-only` annotation per
   `tests/CLAUDE.md §"Fresh Temp Directory per Test"`.

3. **Composable.** A test author should be able to specify "no
   prelude, this user.cl, these helper modules, this stdin" in a
   builder chain that reads as one expression. No manual file
   layout, no manual env-var assembly.

4. **One small surface.** The whole API fits in two files:
   `tests/helpers/e2e.rs` (`Cranelisp`, `CrInvocation`, `CrOutput`,
   `PreludeVariant`) and `tests/helpers/regex.rs` (the named regex
   library). The legacy `tests/helpers/mod.rs::ReplSession` is
   retired in Phase 3.

5. **Non-deterministic content is excluded by named regex helper, not
   suppressed by binary mode.** The harness does NOT force a global
   "deterministic output mode" on the binary. Tests **exclude
   non-deterministic content** from golden / equality comparisons via
   the regex helper library (§"Regex helper library"): `/time` output
   is matched by a named regex, allocation pointers are masked by
   `compiler::alloc_addr()`, etc. The golden-file machinery
   (`assert_golden_masked`) takes a list of regex masks at the call
   site. Per-test isolation (fresh TempDir as project root, hence
   fresh `.cranelisp-cache/`) handles cache-state determinism without
   needing any binary knob.

6. **Fail loudly on environmental drift.** If the binary is missing,
   stdlib-relative path doesn't resolve, or the test prelude file
   isn't found, the harness panics with a clear diagnostic naming
   the missing path — not a silent fallback.

## Surface — design sketch

The shapes below are illustrative. Final names and signatures are
authored in `helpers-api.md`; this section conveys intent.

### Top-level entry: `Cranelisp::new()`

```rust
/// One Cranelisp invocation. Builder pattern: configure, then run.
///
/// Defaults:
///  - mode: REPL (no `--run`, no `--link`)
///  - prelude: NONE (no prelude file dropped; binary's auto-discovery
///    finds nothing in the fresh TempDir)
///  - stdin: empty
///  - lib_dirs: empty
///  - env: clean — no trace flags, no special vars
///  - cwd: a fresh per-test TempDir (held inside the builder)
pub struct Cranelisp { /* ... */ }
```

The full method set lives in `helpers-api.md`. Categories:

- Mode: `repl()`, `run(file)`, `link(file)`, `link_then_run(file)`
- Fixtures: `file(rel, contents)`, `user(contents)`, `prelude(contents)`,
  `with_prelude(variant)`, `fixture(src, dst)`, `fixture_tree(src, dst)`
- Search paths: `lib_dir(dir)`, `use_workspace_stdlib_for_stdlib_conformance_only()`,
  `use_workspace_platforms()`
- Stdin: `stdin(text)`, `stdin_lines(&[...])`
- Environment & flags: `env(k, v)`, `cli_flag(s)`
- Run: `output()`, `output_then_run_again()` (cache-hit pattern)

### Output: `CrOutput`

```rust
/// Captured outcome of a Cranelisp child process.
pub struct CrOutput {
    pub status: ExitStatus,
    pub stdout: String,        // utf-8 lossy
    pub stderr: String,
    pub elapsed: Duration,
    pub tmpdir: PathBuf,       // for inspecting cache, .o, etc.
    // _td: held internally so it lives until CrOutput drops
}
```

Assertion methods on `CrOutput`:

- Exit: `assert_ok`, `assert_exit(code)`, `assert_signaled`
- Stdout: `assert_stdout_eq`, `assert_stdout_contains`, `assert_stdout_matches`
- Stderr: `assert_stderr_empty`, `assert_stderr_contains`
- Snapshot: `assert_golden(name)`, `assert_golden_masked(name, &[regex])`
- Tmpdir: `read_tmp(rel)`, `tmp_exists(rel)`

**`assert_stderr_empty` is the spec-correct check.** The spec
(`repl/spec.md §5.1`) says "errors on stdout, stderr is for traces
only". When no `CRANELISP_*_TRACE` env var is set (the harness default),
stderr MUST be empty. Trace-channel parsing belongs to `/dev` unit
tests inside the runtime/backend crates; the e2e harness asserts the
empty-when-no-trace property, not the structure of trace output.

### Prelude variants

A small named catalogue of stable test preludes lives in
`tests/fixtures/preludes/`:

```rust
pub enum PreludeVariant {
    /// No prelude file dropped. Binary's auto-discovery finds nothing
    /// in the fresh TempDir.
    None,

    /// Just `(import [primitives [*]])`. For tests that want bare
    /// primitive names but no traits, ADTs, or operators.
    PrimitivesOnly,

    /// The current `tests/fixtures/prelude.cl` — Option, Result, Num,
    /// Eq, Ord, basic impls. The default for tests that need
    /// operators or ADT types.
    TestStandard,
}
```

A test that wants no prelude at all uses `Cranelisp::new()` without
calling `with_prelude` — equivalent to `with_prelude(PreludeVariant::None)`.
A test that wants a custom prelude uses `.prelude("(deftype ...)")` to
drop a `prelude.cl` into the tmpdir and let prelude resolution pick it up.

**Workspace stdlib is a separate, gated entry point.** Not a
`PreludeVariant` value — it's `use_workspace_stdlib_for_stdlib_conformance_only()`,
the only legitimate caller of which is `tests/stdlib.rs`. See
`helpers-api.md` for the gating rationale.

## Usage examples

The pseudocode below shows the intended call sites.

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

### Mode-equivalence (run one program through all six permutations)

```rust
#[test]
fn mode_equiv_arithmetic() {
    // spec: spec/07-traits.md §7.1 — Num operator dispatch
    // The mode-equivalence subset asserts that REPL fresh / REPL cached /
    // --run fresh / --run cached / --link fresh / --link cached all
    // produce N=3 for `(defn main [] (+ 1 2))`. A divergence in any
    // permutation panics with a per-permutation diff. Empirical
    // validation of Principles 11–13 + Decisions 22/25/41.
    run_through_all_modes(
        "(defn main [] (+ 1 2))",
        PreludeVariant::TestStandard,
        /* expected_int = */ 3,
    )
    .assert_all_equivalent();
}
```

The helper is for the mode-equivalence subset only. Bulk language
conformance uses REPL canonical directly (see §"Canonical mode" usage
above).

### Cache-hit equivalence (run binary twice in same TempDir)

```rust
#[test]
fn cache_hit_produces_same_output() {
    // spec: design/backend/module-caching.md §"Cache hit equivalence"
    let first = Cranelisp::new()
        .run("user.cl")
        .user("(defn main [] (add-i64 1 2))")
        .output()
        .assert_ok();
    // Second invocation reuses the same TempDir → cache hit.
    let second = first.run_again().output().assert_ok();
    assert_eq!(first.stdout, second.stdout);
    assert!(second.tmp_exists(".cranelisp-cache/user.meta.json"));
}
```

### Cache lives under project root (the spec property)

```rust
#[test]
fn cache_lives_under_project_root() {
    // spec: design/backend/module-caching.md §"Cache directory layout"
    let out = Cranelisp::new()
        .run("user.cl")
        .user("(defn main [] 0)")
        .output()
        .assert_ok();
    assert!(out.tmp_exists(".cranelisp-cache"),
            "cache must materialise under project_root (= TempDir)");
}
```

### Snapshot / golden with masked content

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
        .assert_golden_masked("repl/list_after_one_defn", &[
            regex::compiler::alloc_addr(),
            regex::compiler::time_line(),
        ]);
}
```

## Regex helper library

Anything in compiler output (as opposed to user-program output) gets a
named helper in `tests/helpers/regex.rs`. Tests reference the helper,
never embed the raw pattern. If the compiler's output format changes,
ONE place updates and every dependent test moves with it.

**Discipline:** every check that matches compiler output uses a
helper — even on first occurrence with a single caller. The first
helper for a pattern can be narrowly fitted to its one use case;
generalisation happens on the second and subsequent callers. The
point is the indirection: the first time the format changes the
search is `helpers/regex.rs`, not `git grep`.

The full enumeration with capture groups lives in `helpers-api.md §"regex"`.
Categories:

- `compiler::time_line()` — `/time` output line.
- `compiler::repl_prompt()` — REPL prompt shape.
- `compiler::error_line()` — compiler error line.
- `compiler::alloc_addr()` — any hex pointer (for golden masking).
- `mask_alloc_addrs(s)`, `mask_timing(s)` — convenience helpers.

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
  defines Num/Eq/Ord) during this sprint's port.
- **Trace-channel parsing on stderr.** No `stderr_traces` field, no
  `assert_stderr_traces_only`, no `TraceKind` enum on the harness.
  Trace channels are debugging aids without spec basis — `/dev`'s
  concern, tested inside the owning crate (e.g.,
  `cranelisp-runtime`'s unit tests for RC alloc/free balance). The
  e2e harness only asserts `assert_stderr_empty` (the spec rule
  when no trace flag is set).

## Implementation phasing

1. **Phase 1 — build** (this sprint).
   1. Trim this document per the Phase 0 collapse — done as the first
      Phase 1 deliverable so the harness is implemented against a
      clean spec, not stale prose.
   2. Author the cache-isolation regression test (`tests/cache_isolation.rs`
      or extend `tests/cache.rs`) asserting the spec property
      "`.cranelisp-cache/` lives under project_root" — first concrete
      e2e test against the new harness contract; gates Phase 2.
   3. Implement `tests/helpers/e2e.rs` and `tests/helpers/regex.rs`
      per `helpers-api.md`. The new harness lives **alongside**
      `tests/helpers/mod.rs::ReplSession` until Phase 3. `ReplSession`
      remains frozen (no new methods) but green.
2. **Phase 2 — port** (this sprint). Port every test in `tests/` from
   the integration-tier helpers (`compile_and_run*`, `repl_session*`,
   inline `const &str` trait preludes) into the e2e tier using
   `Cranelisp`. As each test ports, add or update its row in
   `tests/plan/PLAN.md` so coverage documentation builds in lockstep.
   Defects surfaced during port land as failing tests with FIXMEs;
   no defect-fixing in-sprint (parity rule).
3. **Phase 3 — remove legacy** (this sprint). Delete
   `tests/helpers/mod.rs::ReplSession` and the integration-tier
   helpers; delete or rewrite any tests that resisted the port
   (with explicit rationale per holdout).
4. **Phase 4 — crate refactors begin** (next sprint). FIXME 0109
   (`/int` decomposition) and other crate refactors that reshape
   `session_v4`/`worker` proceed against an e2e-only test surface
   that does not break under internal restructuring.

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
  (`--run`, `--link`, etc.) is a contract with `/int`. Changes go
  through FIXME, not silent rename. No new CLI surface is required
  by this design — the harness rides on the existing binary
  surface.
- **Trace assertions belong inside crates, not at e2e.** The harness
  cannot verify `[rc] alloc` / `[rc] free` balance on stderr — that
  is a `cranelisp-runtime` unit-test concern. The e2e tier only
  asserts the visible behavioural consequences (the program runs to
  completion, produces the right output, leaves the cache in the
  right state).
