# Test Plan — normative

Owner: `/qa`. This is the bridge from spec → tests. It supersedes the
former `tests/plan/baseline.md` (renamed to `ledger.md` and re-scoped to
its true purpose: the failure ledger). The old ring-by-ring plans, the
`strategy.md`, and the Sprint 61 retros now live under `legacy/` for
provenance — they are NOT consulted as ground truth.

## Strategy — two tiers, no middle

Cranelisp tests fall into exactly two tiers:

1. **e2e tests** — `tests/`, owned by `/qa`. Run the `cranelisp` exe
   directly: REPL via stdin, `--run file.cl`, or `--link` then run the
   produced binary. Helpers are process-spawn + stdin/stdout capture +
   isolated tmpdir + on-disk fixture files for controlled imports and
   prelude variants. See `helpers.md` for the harness API.

2. **Unit tests** — `crates/{crate}/src/` `#[cfg(test)]` modules,
   owned by `/dev` for that crate (per
   `memory/feedback_unit_tests_with_dev.md`). `/qa` does not author
   these.

There is **no middle integration tier.** Tests do NOT construct
`Sess`, `SharedState`, `SymbolTable`, or any other internal session
primitive. `/qa`-authored helpers in `tests/helpers/` are
e2e-harness machinery (process spawn, stdin/stdout, isolated tmpdir,
fixture-file scaffolding) — never session builders. If a feature
cannot be expressed e2e, that is a gap in the binary's testability
surface — file an `/int` or `/arch` FIXME, do not bridge with an
internal-API helper. Recorded by user
2026-05-03 in `memory/project_test_strategy.md`.

### Why two tiers, not three

The earlier four-layer pyramid (unit → boundary → integration → e2e)
predated the v4 `CompilerSession` architecture and the
`/qa` ↔ `/dev` ownership reaffirmation. It assumed `/qa` would
orchestrate the pipeline via `compile_unit()` and `repl_session()`
helpers; in practice that orchestration moved into `src/` (now
`session_v4.rs` + `worker.rs`) and the integration tier became a
parallel implementation of the same wiring, with predictable drift.

`session_v4.rs`, `worker.rs`, and `SharedState` change shape across
sprints (Decisions 38–42; the Sprint 64 architectural-configuration
work; FIXMEs 0098–0109 reshape the binary surface in S65+). A test
tier coupled to those shapes pays maintenance tax on every change for
no observable-behaviour benefit. The e2e/unit split puts each tier
against a stable surface: the user-facing exe (e2e) or the
crate-internal API (unit, owned by the crate).

## Plan structure

The plan lists every spec requirement with one row per behaviour, in
the order the spec presents them. Status uses the project traceability
convention from root `CLAUDE.md`:

- `[Tested tests/{file}::{name}]` — positive path covered.
- `[Tested+Neg tests/{file}::{name}]` — positive AND negative paths
  covered.
- `[S{M}]` — not yet tested, scheduled for sprint M.
- `[S{M} — tests/{file}::{name} IGNORED]` — test exists but is
  `#[ignore]`'d; reason cited.

The ring-axis (`R{N}`) is retired as of Sprint 64 — all ring-envisaged
functionality is delivered and the project is in maintenance/extension
mode. Sprint is the only scheduling axis. Ring annotations remaining
in `spec/*.md` headings are tracked for `/spec` removal under FIXME
0113; they remain meaningful as historical capability cohorts but are
not load-bearing for test-plan scheduling.

## Migration policy — dedicated sprint, not opportunistic

The integration-tier tests (using `compile_and_run*`, `repl_session*`,
inline `const &str` trait preludes, etc.) will be ported to the e2e
tier in a **dedicated migration sprint**, NOT opportunistically. The
sprint shape:

1. Build the e2e helper environment per `tests/plan/helpers.md` (Phase 1).
2. Port every test, building coverage documentation in `PLAN.md` in
   lockstep (Phase 2).
3. Delete `tests/helpers/mod.rs::ReplSession` and remaining
   integration-tier scaffolding (Phase 3).
4. Crate-refactor sprints (FIXME 0109 int decomposition, etc.) begin
   only after Phase 3 completes — the test suite must be decoupled from
   internal session shapes before refactors that change those shapes.

Tracked by FIXME 0115 (`/sprint` planning — sequence the test-port
sprint and lock it ahead of any crate-refactor sprint).

Provenance: every row cites the spec section that derives it; rows
that go beyond raw spec coverage (interaction boundaries, regression
guards) cite the per-crate design doc invariant they validate.

This file is **maintained, not accreted**. Rows are updated in place
as tests land, are renamed, or change status. A row with no test
file is in-flight work; a test file with no row is drift — fix one
side or the other, do not let them diverge.

### Sections (target shape, populated incrementally)

1. **Conformance** — every spec section, every MUST. The bulk of the
   plan. Authored from `spec/` + `repl/spec.md`.
2. **Regression guards** — minimum-repro tests committed for resolved
   defects. Each row cites the originating defect (sprint, FIXME,
   ledger entry). These exist forever per
   `memory/feedback_repros_join_suite.md`; their value as guards
   outlives the fix.
3. **Negative-coverage upgrades** — rows where a `[Tested ...]`
   should become `[Tested+Neg ...]`. Lives here so the gap is
   visible at the spec level. Subordinate analysis in
   `negative-coverage.md`.
4. **Build-confidence** — the e2e tests that gate sprint close: the
   binary builds, the binary starts, the binary executes the
   smoke set (a handful of representative `--run` programs and a
   one-line REPL transcript per surface). Not exhaustive; just the
   release gate per `qa.md §"Working build requirement"`.

The current `tests/` directory pre-dates the two-tier strategy and
contains many integration-tier files that exercise the Rust API
through `tests/helpers/mod.rs::ReplSession` (a `CompilerSession`
wrapper). Those tests are **not deleted in this plan refresh** — they
remain as living regression guards while the e2e helper environment
(see `helpers.md`) is built out. The migration policy is opportunistic,
test-by-test:

- **Defects surface against the e2e harness from now on.** New
  reductions land as e2e tests against `binary_path()`, not against
  `ReplSession`. Per `memory/feedback_repros_join_suite.md` they
  remain forever.
- **Existing integration tests stay green or get rewritten.** When an
  integration test breaks because the underlying internal-API surface
  shifts (Decisions 38–42, FIXME 0109 `session_v4`/`worker` split),
  the rewrite is into the e2e tier rather than chasing the new
  internal shape. Migration is done file-by-file, not en masse.
- **The `ReplSession` Rust-API helper is frozen.** No new methods, no
  new test entry points. It is a compatibility surface for the
  pre-existing 30-odd test files only. New integration-flavoured
  helper proposals are rejected; they belong in `helpers.md` as
  process-driven equivalents.

Rows added to this PLAN that target a future sprint cite the e2e
helper API in `helpers.md`, not `ReplSession`.

## Authoring discipline

These rules are non-negotiable; they are imported from `qa.md` and
enumerated here so this plan is self-contained for everyday use.

- **Spec-first.** Read the spec section before writing or reviewing
  the test. Use spec-defined names (`add-i64`, not whatever the
  implementation invented). A test that passes against a non-spec
  name is silent divergence, not coverage.
  (`memory/feedback_validate_tests_against_spec.md`.)
- **Failing-not-ignored.** In-scope failures stay visible. `#[ignore]`
  is reserved for future-sprint requirements not yet scheduled, and
  the form is `#[ignore = "reason — spec ref + target sprint"]`.
  Anything in scope and ignored is a defect against the methodology.
  (`memory/feedback_failing_not_ignored.md`.)
- **Repros join the suite.** Every reduction — complete or partial —
  is committed as a failing, un-ignored, `// spec:`-annotated test
  with a row in this plan or in the regression-guards section.
  Markdown notes never substitute. Small repros aid debugging twice:
  the fix often becomes obvious during isolation, and small CLIF is
  inspectable by eye via `/clif <name>` or
  `CRANELISP_CODEGEN_TRACE=1`.
  (`memory/feedback_repros_join_suite.md`,
  `memory/feedback_qa_reproduction.md`.)
- **Cross-skill defect handoff requires minimal repro.** Surface
  error signatures alone mask layered bugs. Before a handoff, reduce
  to the smallest case that still fires; the handoff brief names the
  repro test.
  (`memory/feedback_cross_skill_minimal_repro.md`.)
- **Repros live in `tests/`, not `exemplar/` or `examples/`.** When
  a user-proxy skill isolates a compiler bug, the user-proxy authors
  the repro in-session; `/qa` copies into `tests/` as the durable
  record. `exemplar/` and `examples/` can be removed/replaced at any
  time — regression guards must not couple to them.
  (`memory/feedback_repro_handoff.md`.)
- **Test-side traceability.** Every test function carries a
  `// spec:` comment naming the spec section it validates. The
  comment IS the back-trace; this plan is the forward-trace.
- **Negative coverage matters.** A `[Tested]` annotation without
  `+Neg` is a coverage gap. For every MUST that constrains *what
  appears*, write a companion test that verifies wrong things are
  absent. Naming convention: `_neg_` or `_not_` in the fn name.
  Track gaps in `negative-coverage.md`.
- **Fresh tmpdir per test.** Subprocess tests MUST NOT pollute
  checked-in paths (`exemplar/`, `examples/`, `stdlib/`,
  `tests/fixtures/`, `src/`, the repository root). The e2e harness
  in `helpers.md` enforces this by construction. The exception
  pattern (`tests/{suite}/.runs/{RUN_TS}/{n_label}/`) is permitted.
  (`tests/CLAUDE.md §"Fresh Temp Directory per Test"`.)

## Sprint participation

Per METHOD.md §2:

- **Phase 3 (Design).** `/qa` reads in-scope spec sections, the
  per-crate design doc updates from `/design`, and any cross-crate
  type changes from `/arch`. Updates this plan with rows for every
  in-scope requirement. By Phase 3 close, has enough rows to draft
  the failing tests Phase 5 will start with. Phase 3a defect-class
  derivation includes at least one property-level row per defect
  class independent of the owning skill's branch selection
  (lesson from Sprint 61, see `legacy/sprint-61-plan-gap-retro.md`).
- **Phase 5 (Language).** QA-first across the entire solution. Before
  any per-crate D/D/R cycle begins, `/qa` writes the failing e2e
  tests this plan calls for, sprint-wide. The failing tests scope
  what the per-crate triads make pass. Failing-not-ignored.
- **Phase 6/7 (Assess/Close).** `/qa` updates row statuses and ledger
  entries to reflect what shipped, what didn't, and what was
  ignored with reason. The Phase 7 outcome cites plan-vs-tests
  integrity and ledger integrity.

## Subordinate documents

- **`ledger.md`** — failure ledger. Every test currently failing in
  `cargo nextest run --no-fail-fast` MUST have an entry. Verified at
  every sprint open and close. Allowed dispositions:
  `under-investigation`, `out-of-scope (owner=/skill)`,
  `exemplar-gap (owner=/port)`. Forbidden: `flaky`, `pre-existing`,
  `documented race`, `timing-sensitive`.
- **`helpers.md`** — design of the e2e helper API surface in
  `tests/helpers/`. The "shiny e2e test helper environment" the
  Sprint 64 strategy direction calls for. Authored by `/qa`,
  implementation by `/qa` against the binary surface.
- **`risks.md`** — qualitative risk register; refreshed when risk
  shape changes. Most entries from the original were ring-era; the
  surviving load-bearing risks (RC non-locality, batch/REPL parity,
  performance regression invisibility, error-message quality) carry
  forward.
- **`coverage-gaps.md`** — per-crate coverage analysis. Living
  document; refreshed on cadence by `/qa`. Drives unit-test FIXMEs
  to `/dev` (target the owning crate); does not gate this plan.
- **`negative-coverage.md`** — running register of `[Tested]` →
  `[Tested+Neg]` upgrade candidates and landed promotions.
- **`legacy/`** — superseded plan documents kept for provenance:
  the four ring-era plans (`ring0..ring4.md`), `strategy.md`
  (the four-tier pyramid), `ring0-readiness.md`, the Sprint 61
  retros (`sprint-61-plan-gap-retro.md`,
  `tempdir-audit.md`), and the Sprint 61 negative-coverage
  shortlist (`neg-coverage-candidates.md`). Do NOT consult as
  ground truth.

## Audit findings affecting test architecture (2026-04-23)

The five 2026-04-23 audits (frontend, typecheck, backend, src/int,
target-state diagrams) carry observations relevant to test design.
Per the Sprint 63 supersession note in each audit, target-direction
sections are not authoritative; current-state observations are. The
following findings affect this plan or the e2e helper design:

- **`src/` is a complexity sink** (src audit Findings 1–5).
  `session_v4.rs` (5,417 LOC) and `worker.rs` (5,041 LOC) carry too
  much policy for an integration layer. FIXME 0109 tracks
  decomposition. **Implication for tests**: the integration-tier
  helpers in `tests/helpers/mod.rs::ReplSession` couple directly to
  `CompilerSession` and `SharedState`; every `session_v4`/`worker`
  refactor cascades into the test surface. The two-tier strategy
  (e2e against the exe, unit inside the crate) absorbs this risk by
  detaching the test surface from the internal decomposition. New
  defect repros land as e2e tests; existing integration-tier tests
  are rewritten as e2e on touch, not en masse.
- **`src/lib.rs` exports 18 modules** (src audit Finding 5). The
  binary crate is not currently a thin facade; tests can and do
  reach into internals. The two-tier strategy's e2e tier does not
  use this surface at all. Existing integration-tier tests do, and
  will likely break as the surface narrows under FIXME 0109 — those
  breaks are migration triggers (rewrite as e2e), not regressions.
- **Frontend `ast_builder.rs` is 2915 LOC** (frontend audit Finding 1).
  Frontend unit tests (234 passing per the audit) materially
  de-risk frontend refactoring. **Implication for `/qa`**: trust
  frontend's unit suite for AST-shape regressions; `/qa`'s e2e
  tests cover only observable behaviour (parser errors visible at
  the REPL/--run, AST-derived semantics). Do not duplicate
  AST-shape assertions at e2e level.
- **Frontend has duplicated batch/REPL top-level dispatch**
  (frontend audit Finding 2). `build_repl_input()` and
  `build_top_level()` carry near-duplicate logic. **Test implication**:
  every spec-feature test that lands in this PLAN MUST exercise
  both surfaces — `--run file.cl` AND a piped REPL session. The
  e2e helper API in `helpers.md` makes this convenient via a
  single test that runs both.
- **Tempdir-audit findings already absorbed** (Sprint 61 Wave 5).
  `tests/helpers/mod.rs::ReplSession` now owns a `tempfile::TempDir`
  by construction; the exemplar-writing tests are converted; the
  rule is in `tests/CLAUDE.md`. The new e2e helper API in
  `helpers.md` carries the same discipline forward — every
  spawn helper produces a fresh per-test tmpdir or a labelled
  per-test subdirectory under `tests/{suite}/.runs/`.

No new `/arch` FIXMEs surface from these findings — the architectural
work is already in flight (FIXMEs 0098, 0099, 0100, 0103, 0104,
0108, 0109).

## Testability gaps in the binary surface

These are filed as `/int` FIXMEs because they affect what `/qa` can
test e2e. Each names what the binary needs to expose; `/int`
implements; `/qa` consumes via the helper API in `helpers.md`.

- **0110 — Deterministic-output mode flag**. Per
  `helpers.md §"Determinism"`: the binary should accept a CLI flag
  or env var that suppresses non-deterministic output (timing
  numbers, allocation addresses, worker-thread scheduling order
  trace lines, cache-hit ordering between parallel workers). Without
  it, e2e snapshot/golden assertions must accommodate noise per
  test. With it, the harness can use exact-match assertion as the
  default.
- **0111 — Trace-output channel separation**. Per
  `helpers.md §"Trace toggles"`: the e2e harness needs to assert
  on stdout/stderr/trace separately. Today the
  `CRANELISP_*_TRACE=1` env vars emit to stderr, mixing trace lines
  with the spec-mandated stderr-as-trace channel. The plan rule
  (`repl/spec.md §5.1`) is "errors on stdout, stderr is for traces
  only"; the e2e harness needs to verify stderr-is-traces by
  matching trace patterns and rejecting non-trace stderr lines.
  This depends on the binary tagging trace output unambiguously
  (e.g., a stable line prefix `[trace:rc] ...` or a separate
  `CRANELISP_TRACE_FILE` redirect).
- **0112 — REPL "ready" sentinel for stdin scripting**. Per
  `helpers.md §"Driving the REPL"`: scripted REPL e2e tests today
  pipe input via stdin and read the entire stdout after the child
  exits. This works for one-shot transcripts but not for tests that
  need to send input *only after* a previous form has been
  evaluated (e.g., observe an error message, then send a recovery
  form). A stable ready-sentinel on stdout (the prompt line in a
  known shape) lets the harness drive the REPL request/response.

## Sprint 64 port plan

Per Sprint 64 §Phase 2 — for every test file in `tests/`, run a
**four-step pass**: (1) audit each assertion, (2) port language-behaviour
assertions forward into a reorganised e2e suite, (3) place them in the
new shape (by spec section / language area), (4) quarantine the
remainder in `tests/legacy/` for owning-crate harvest.

Parity rule: every spec-relevant assertion survives the transition —
either as a new e2e test, or via a FIXME-tracked harvest commitment with
the source preserved in `tests/legacy/`. No silent coverage drops.
Defects surfaced during port land as failing tests + FIXMEs (per
`memory/feedback_failing_not_ignored.md`); no defect-fixing in-sprint.

The user's four decisions (2026-05-03) shape this plan:
1. `tests/legacy/` is the quarantine path. Cargo only auto-discovers
   `tests/*.rs` at the top level — nested files under `tests/legacy/`
   become a source archive: preserved, not built, not run. Owning
   crates harvest into their own `#[cfg(test)]` unit tests in S65+.
2. `/qa` does the audit-and-extract NOW, this sprint — for every
   file, not just the awkward ones. No deferred coverage gap.
3. The new e2e suite is reorganised during port, not a 1:1 file
   rewrite. Reorganisation criterion: spec-coverage auditing reads
   naturally; the file set stays manageable.
4. Every file gets the four-step pass — even the previously
   `clean`-classified mechanical-port files. Redundant assertions are
   dropped; Rust-internal bits quarantined; language-behaviour bits
   placed in the new shape.

This expands Phase 2 from "mechanical port" to "audit, port, reorganise,
quarantine" — four-step pass per file.

### Per-file disposition framework

The previous taxonomy (`clean` / `port-with-defect-likely` /
`holdout-risk` / `delete`) is retired. It classified the file as a
whole; the four-step pass classifies **assertions within the file**.

Each file gets a per-file disposition with four numbers and three
pointers:

- **Carry-forward%** — fraction of assertions that become new e2e
  tests in the reorganised suite. Approximate; the precise count comes
  out of the audit pass itself.
- **Quarantine%** — fraction that goes to `tests/legacy/<file>.rs`
  for harvest into the owning crate's `#[cfg(test)]` unit tests.
- **Delete%** — fraction that is redundant, covered elsewhere, or
  obsolete (sprint-NN repros whose defect closed and whose
  minimum-repro form is already captured by a sibling); dropped
  outright.
- **Defect%** — fraction expected to surface a defect under the new
  e2e form (failing test + FIXME, no in-sprint fix).

(The four numbers add to 100; "Defect%" is a subset of Carry-forward%
that is expected to fail, surfaced separately because it determines
ledger pressure.)

- **Target file(s)** in the new suite — one or more files in the
  reorganised shape (see §"Sprint 64 reorganisation strategy") that
  receive the carried-forward assertions.
- **Quarantine FIXME target** — the owning crate's `/dev` skill that
  must harvest the quarantined assertions in S65+, named when
  Quarantine% > 0.
- **Defect-risk notes** — known shapes the new e2e port may surface
  (e.g., concurrent-load tail-latency, prompt-shape stability,
  cache-state leakage between `/reset` calls).

### Sprint 64 reorganisation strategy

**Chosen shape: spec-section-anchored with three pragmatic supplements.**

Rationale: the user's framing — "we want to be able to assess
spec-based test coverage at the end against a manageable set of
high-quality tests" — names spec coverage as the auditing axis. A
reviewer's question is "which spec section does this file cover?";
the file name should answer it directly. The supplements
(`repl/`, `regression/`, `build_confidence/`) cover behaviour that is
not in the language spec proper but still must live as e2e: the REPL
experience spec, durable defect repros, and the release gate.

**Target file tree** (new e2e suite under `tests/`):

```
tests/
  spec_03_types.rs               — Type system surface (primitives,
                                    ADTs, deftype, parameterised types).
                                    Covers spec/03-types.md.
  spec_04_expressions.rs         — Expressions, special forms, pattern
                                    binding, lenient evaluation.
                                    Covers spec/04-expressions.md.
  spec_05_definitions.rs         — defn/def/const, multi-clause defn,
                                    constrained polymorphism.
                                    Covers spec/05-definitions.md.
  spec_06_pattern_matching.rs    — match expressions, exhaustiveness,
                                    nested patterns, wildcards.
                                    Covers spec/06-pattern-matching.md.
  spec_07_traits.rs              — deftrait, impl, trait dispatch,
                                    operator-as-trait-method.
                                    Covers spec/07-traits.md.
  spec_08_modules.rs             — Imports, exports, module graph,
                                    cross-module resolution, qualified
                                    refs. Covers spec/08-modules.md.
  spec_09_macros.rs              — defmacro, multi-clause, quasiquote,
                                    bracket destructuring, macro
                                    hygiene. Covers spec/09-macros.md.
  spec_10_io.rs                  — bind!, IO scheduling via Par,
                                    capture-return-inc, IO trampoline.
                                    Covers spec/10-io.md.
  spec_11_stdlib.rs              — Stdlib conformance via the gated
                                    `use_workspace_stdlib_for_stdlib_conformance_only()`
                                    entry. Covers spec/11-stdlib.md.
                                    The single legitimate caller of
                                    the gated entry.
  spec_12_runtime.rs             — Lifecycle, RC observable behaviour,
                                    redefinition semantics, JIT
                                    reclaim observable through /mem.
                                    Covers spec/12-runtime.md.
  spec_appendix_a_builtins.rs    — Primitive function surface
                                    (add-i64, etc.) — bare-primitive
                                    paths that don't fit a section
                                    file. Covers
                                    spec/appendix-a-builtins.md.
  repl_introspection.rs          — Slash commands /list, /imports,
                                    /exports, /sig, /doc, /info,
                                    /source, /sexp, /ast, /clif,
                                    /disasm, /type, /mod, /reload,
                                    /help. Covers
                                    repl/spec.md §3 (introspection).
  repl_lifecycle.rs              — Module switching, prelude loading,
                                    REPL session boot, /run-tests,
                                    redefinition cycles. Covers
                                    repl/spec.md §1, §2, §4.
  repl_negative.rs               — Error paths for slash commands +
                                    REPL forms (negative tests).
                                    Covers repl/spec.md §5.
  cache.rs                       — Cache-hit equivalence, cache
                                    invalidation, cache-isolation
                                    (Phase 1 §2 seed test lives here).
                                    Covers
                                    design/backend/module-caching.md.
  examples.rs                    — Smoke runs every `examples/*.cl`.
                                    Covers spec/appendix-b-examples.md
                                    (worked examples).
  exemplar.rs                    — Sudoku Solver showcase. Covers
                                    end-to-end project-scale
                                    behaviour. Open Defect-6 ledger
                                    rows live here.
  regression.rs                  — Defect-repro tests committed
                                    forever per
                                    `memory/feedback_repros_join_suite.md`.
                                    Each test cites the originating
                                    sprint + ledger row. The home for
                                    sprint59/sprint60/sprint61/wave6
                                    repro content that survives the
                                    audit.
  build_confidence.rs            — Release gate per
                                    `qa.md §"Working build requirement"`:
                                    binary builds, binary starts, smoke
                                    set runs (a handful of representative
                                    `--run` programs and a one-line REPL
                                    transcript per surface). Authoritative
                                    sprint-close gate.
  legacy/                        — Quarantine archive (NOT auto-built).
    README.md                    — Index: file → FIXME number →
                                    owning crate → quarantine date.
    cache.rs                     — Direct cache::* API tests
                                    (FIXME → /backend).
    scheduler.rs                 — Direct CompileScheduler API tests
                                    (FIXME → /int).
    observability_*.rs           — Direct observability/io_trace API
                                    tests (FIXME → /int, /backend).
    v4_jit_reclaim.rs            — Counter atomics + symbol_tables()
                                    (FIXME → /backend, /int).
    wave2_g6.rs, wave3_g8.rs,
    wave4_g9.rs                  — Layer-3 internal-API observations
                                    (FIXME → /typecheck, /backend, /int).
    rc_alloc_trace.rs            — RC alloc/free balance assertions
                                    via stderr trace parsing
                                    (FIXME → /runtime via /backend).
    ring4_trace_taxonomy.rs      — Trace event taxonomy assertions
                                    (FIXME → /runtime, /backend).
```

**File-count estimate**: ~16 e2e top-level files + 1 `legacy/` dir
with ~8–10 archive files. Down from 42 source files. Manageable.

**Why not "by language area" alone?** Several files would still
straddle (e.g., `macros.rs` covers spec/09 plus interactions with
spec/08 modules; `io.rs` covers spec/10 plus spec/04 lenient `bind!`
semantics). Spec-section-anchored gives the cleanest 1:1 read.
Cross-cutting tests live in the supplement files (`regression.rs`,
`repl_*.rs`, `cache.rs`, `build_confidence.rs`) where the spec axis
doesn't naturally apply.

**Why not retire `regression.rs` and inline each defect repro into
its spec-section file?** Per `memory/feedback_repros_join_suite.md`,
defect repros are committed forever and must be greppable as a
cohort. A single `regression.rs` with `// spec:` comments naming the
relevant section gives both axes (defect cohort + spec coverage)
without forcing repros to colonise spec-section files.

### Per-file disposition table

| Source file | LOC | Tests | Carry% | Quarantine% | Delete% | Defect% | Target file(s) | Quarantine FIXME | Defect-risk notes |
|---|---:|---:|---:|---:|---:|---:|---|---|---|
| `cache.rs` | 2073 | 55 | 47 | 51 | 2 | 0 | `cache.rs` (S64 W2 ✓), `legacy/cache.rs` (S64 W2 ✓ FIXME 0120) | /backend (manifest serialise/round-trip, SymbolTable construction) | S64 Wave 2 Batch 1 landed: 24 e2e tests in new `tests/cache.rs` (cache-hit/miss equivalence, multi-module + transitive deps + prelude caching, mtime-preservation invariants, round-trip runtime parity). 55 tests preserved in `legacy/cache.rs` for /backend harvest under FIXME 0120 (direct cache::* / SymbolTable / serialize API). `cache_seed.rs` merged. |
| `e2e.rs` | 2701 | 309 | 70 | 0 | 30 | 5 | `spec_03_types.rs` (S64 W5 ✓ + W5.6 c1 ✓), `spec_04_expressions.rs` (S64 W5 ✓), `spec_05_definitions.rs` (S64 W5 ✓), `spec_07_traits.rs` (S64 W5 ✓), `spec_appendix_a_builtins.rs` (S64 W5 ✓), `spec_08_modules.rs` (S64 W5.6 c3 ✓), `repl_introspection.rs` (S64 W5.6 c1 ✓ + c2 ✓ + c3 ✓), `repl_lifecycle.rs` (S64 W5.6 c1 ✓ + c2 ✓ + c3 ✓), `repl_negative.rs` (S64 W5.6 c1 ✓), `spec_09_macros.rs` (S64 W5.6 c2 ✓), `spec_12_runtime.rs` (S64 W5.6 c1 ✓), `spec_platforms.rs` (S64 W5.6 c3 ✓), `build_confidence.rs` (S64 W5.6 c1 ✓ + c3 ✓), `legacy/e2e.rs` (S64 W5 ✓ FIXME 0134) | /int (with /frontend, /typecheck, /backend) | S64 Wave 5 Batch 2 landed initial bulk-dedupe carry-forward (language-conformance assertions consolidated into spec-section files via REPL-canonical authoring). Wave 5.6 chunk-1 per-test re-audit (`tests/plan/wave-5.6-e2e-reaudit.md` chunk 1 covering tests 1-50) added 17 GAP-COVER carry-forwards across 6 files (5 REGRESSION-GUARDs preserved): nullary/data ctor dot notation, 3 prelude-Option display angles (passing — historic BUG repros preserved as guards), `:Type expr` annotation form (positive + applied + neg-not-variable), `/info`+`/time` slash commands, `/run-tests` aggregation (multi/mixed/non-test-filter), bare primitive type lookup (Int absorbs Bool/Float/String), bare user-defined type lookup, §5.1 stderr-clean + session-survival neg-coverage, §7.1/§7.2 perf budgets (`#[ignore]`'d for nextest subprocess overhead). Wave 5.6 chunk-2 per-test re-audit (chunk 2 covering tests 51-100) added 17 GAP-COVER carry-forwards across 3 files (2 REGRESSION-GUARDs): bare special-form self-doc cluster (`fn`/`defn`/`deftype`/`match`/`defmacro`), bare-operator self-doc cluster (`+`/`=`/`<`), `/list` traits-after-deftrait + prefix-filter, `/expand` recursive-fixpoint, `/doc` macro variants (no-docstring + with-docstring), `/imports <module>` filter + neg-nonexistent-graceful, cross-session isolation regression-guard, §9.9.4 runtime-error-during-expansion clean-report (legacy "currently SIGILL" gap-doc — verified passing on current binary, preserved as durable REGRESSION-GUARD). Wave 5.6 chunk-3 per-test re-audit (chunk 3 covering tests 101-148) added 33 GAP-COVER carry-forwards across 5 files (5 REGRESSION-GUARDs): `/exports` cluster (no-arg usage + nonexistent + lists-symbols), `/imports nonexistent` silent-recovery (session continuity), universal-format section headers (`; match:` for deftype, `; defn:` for deftrait), bare-symbol classification tokens (`; defn` / `; deftype` / `; deftrait` / `; type` / `; special form` / `; defmacro`+clause-sig), `/list` neg-no-Fns-when-only-types, `/doc` builtin + no-arg-usage, slash-command positive paths (`/source` / `/sexp` / `/ast` / `/clif` / `/disasm`), `/mod` switch + round-trip, §7.4 SHOULD-level large-output bound, imported-fn-as-higher-order-arg REPL-mode REGRESSION-GUARD (spec/08 §8.3), Cranelisp.toml E2E cluster (lib-dirs resolves + precedence-over-env + missing-falls-through + malformed-no-crash, all REGRESSION-GUARDs per spec/08 §8.11.4), `/mem` cluster (snapshot + delta + zero-baseline + `/m` alias). All 33 tests passing on current binary; source preserved in legacy for harvest under FIXME 0134. |
| `examples_run.rs` | 193 | 1 | 100 | 0 | 0 | 5 | `examples.rs` (S64 W6 ✓), `legacy/examples_run.rs` (S64 W6 ✓ FIXME 0143) | /port | S64 Wave 6 batch 1 landed: umbrella subprocess test in `tests/examples.rs::every_example_runs_with_documented_exit` carries the 27-row `expected_exits` table verbatim (per audit recommendation A — newer/broader version is canonical). Source preserved for /port harvest under FIXME 0143. |
| `examples.rs` | 132 | 15 | 100 | 0 | 0 | 0 | `examples.rs` (S64 W6 ✓), `legacy/examples.rs` (S64 W6 ✓ FIXME 0143) | /port | S64 Wave 6 batch 1 landed: 15 row-tests collapsed into the umbrella in `tests/examples.rs` (per audit recommendation B — strictly subsumed by `examples_run.rs` shape). Source preserved for /port harvest under FIXME 0143. |
| `exemplar_solver_correctness.rs` | 302 | 2 | 100 | 0 | 0 | 50 | `exemplar.rs` (S64 W6 ✓ T-S2-1 inline), `regression.rs` (S64 W6 ✓ T-S2-2), `legacy/exemplar_solver_correctness.rs` (S64 W6 ✓ FIXME 0143) | /port | S64 Wave 6 batch 1 landed: T-S2-1 inline-rewritten in `tests/exemplar.rs::t_s2_1_eliminate_contract_on_given_returns_none` (no exemplar/ source dependency per `feedback_repro_handoff.md` — recommendation C). T-S2-2 routed to `tests/regression.rs::t_s2_2_inline_adt_arg_wrapping_vec_preserves_len` per audit recommendation E (self-contained codegen regression, not exemplar-specific). Source preserved for /port harvest under FIXME 0143. |
| `exemplar.rs` | 78 | 3 | 100 | 0 | 0 | 0 | `exemplar.rs` (S64 W6 ✓), `legacy/exemplar.rs` (S64 W6 ✓ FIXME 0143) | /port | S64 Wave 6 batch 1 landed: 3 batch-mode shapes carried forward in `tests/exemplar.rs` (`batch_const_macro_in_main`, `batch_cross_module_function_import`, `batch_cross_module_adt_export_and_pattern_match`), all using the new `Cranelisp` builder + `.run("main.cl")`. Source preserved for /port harvest under FIXME 0143. |
| `io_minimal.rs` | 120 | 5 | 100 | 0 | 0 | 5 | `spec_10_io.rs` (S64 W3 ✓), `legacy/io_minimal.rs` (S64 W3 ✓ FIXME 0127) | /int (Sprint 57 W6 reduction guards) | S64 Wave 3 Batch 4 landed: regression intent preserved in `tests/spec_10_io.rs::repl_pure_int_unwraps` + `repl_bind_pure_lambda_no_double_free` + `capture_return_inc_does_not_double_free`. Source preserved in legacy for /int crate-test harvest under FIXME 0127. |
| `io.rs` | 1360 | 76 | 75 | 15 | 10 | 20 | `spec_10_io.rs` (S64 W3 ✓), `legacy/io.rs` (S64 W3 ✓ FIXME 0127) | /int (with /typecheck, /backend, /runtime — IO type inference, trampoline, ABI string surface) | S64 Wave 3 Batch 4 landed: 26 e2e tests in `tests/spec_10_io.rs` (Pure constructor, bind primitive forms, IO type inference, --run mode exit codes from Pure / bind, capture-return-inc regression guard, IO branch consistency, match on IO). Source preserved in legacy for /int + /typecheck + /backend + /runtime harvest under FIXME 0127. |
| `lenient.rs` | 289 | 32 | 30 | 70 | 0 | 0 | `spec_04_expressions.rs` (S64 W5 ✓), `legacy/lenient.rs` (S64 W5 ✓ FIXME 0135) | /backend (with /runtime co-owner — sparkability analysis) | S64 Wave 5 Batch 2 landed: language-observable lenient-eval semantics (independent bindings produce correct sums; dependent bindings sequential) carried forward to `tests/spec_04_expressions.rs::lenient_*`. Sparkability heuristics + `CRANELISP_NO_LENIENT=1` opt-out + Par-node IR observations preserved in legacy for /backend harvest under FIXME 0135. |
| `macros.rs` | 441 | 58 | 80 | 20 | 0 | 5 | `spec_09_macros.rs` (S64 W5 ✓; W5.6 +11 carry-forwards), `legacy/macros.rs` (S64 W5 ✓ FIXME 0137) | /frontend (with /typecheck — macro pipeline internals) | S64 Wave 5 Batch 3 landed: 10 e2e tests in `tests/spec_09_macros.rs` (defmacro, multi-clause, quasiquote, begin, errors, persistence, REPL display). **W5.6 file 3 of 8 dedupe-recovery (2026-05-04)**: per `tests/plan/wave-5.6-dedupe-audit.md §3`, of 29 legacy tests — 13 COVERED, 1 DUPLICATE-IN-LEGACY (`batch_defmacro_quasiquote` dropped, canonical = `mode_equiv_macro_user_defined`), 4 GAP-HARVEST (covered by FIXME 0137), 11 GAP-COVER carry-forwards (6 REGRESSION-GUARD): `repl_macro_produces_if_both_branches`, `repl_macro_produces_let_binding_form`, `repl_macro_begin_splicing_defn_then_call`, `repl_defmacro_in_results_macro_generates_macro`, `batch_defmacro_begin_splicing` (--run), `batch_macro_uses_earlier_macro` (--run), `repl_multiple_macros_sequential_composition`, `neg_macro_expansion_depth_limit_exceeded`, `repl_defmacro_rest_splice`, `repl_error_recovery_no_partial_macro`, `repl_error_recovery_bad_macro`. All 11 pass on first run; no defect surfaced; no FIXME filed. File total: 21 e2e tests. Macro-expansion-shape Rust-API tests + symbol-table inspection preserved in legacy for /frontend harvest under FIXME 0137. |
| `modules.rs` | 530 | 39 | 60 | 40 | 0 | 5 | `spec_08_modules.rs` (S64 W5 ✓; W5.6 +13 carry-forwards), `legacy/modules.rs` (S64 W5 ✓ FIXME 0138) | /frontend (with /int — discover_module_graph internals) | S64 Wave 5 Batch 3 landed: 9 e2e tests in `tests/spec_08_modules.rs` (import specific + glob, qualified names, visibility, primitives synthetic module, non-existent name error, cycle detection, super-rejection, local shadowing). S64 Wave 5.6 audit added 13 carry-forward tests (1 GAP-HARVEST → covered by FIXME 0138, 1 DUPLICATE-IN-LEGACY dropped); 9 of the 13 surfaced FIXME 0121 cluster (--run mode `(mod ...)` discovery). `discover_module_graph` Rust-API tests + multi-dot path edge cases preserved in legacy for /frontend harvest under FIXME 0138. |
| `rc.rs` | 1191 | 81 | 30 | 65 | 5 | 0 | `spec_12_runtime.rs` (S64 W4 ✓), `legacy/rc_alloc_trace.rs` (S64 W4 ✓ FIXME 0129) | /runtime (with /backend co-owner — alloc/free balance via direct counter inspection) | S64 Wave 4 Batch 6 landed: language-observable RC properties preserved as 12 e2e tests in `tests/spec_12_runtime.rs` (string alloc/drop, ADT product/sum match, ADT with String field, closure captures, Vec COW, Vec of strings). The 81 source tests' alloc/free-balance assertions (`assert_rc_balanced` parsing CRANELISP_RC_TRACE=1 stderr) and Rust-API value witnesses preserved in `legacy/rc_alloc_trace.rs` for /runtime + /backend harvest under FIXME 0129. No defects surfaced. |
| `repl_experience.rs` | 3120 | 190 | 90 | 5 | 5 | 15 | `repl_introspection.rs` (S64 W3 ✓), `repl_lifecycle.rs` (S64 W3 ✓), `legacy/repl_experience.rs` (S64 W3 ✓ FIXME 0124) | /int (with /typecheck, /backend — symbol-table inspection + format_result direct calls) | S64 Wave 3 Batch 7 sub-batches 1+2 landed: 39 e2e tests in `tests/repl_introspection.rs` (display format, slash commands, /list categories, defmacro display, /expand, /imports), 29 in `tests/repl_lifecycle.rs` (boot, eval persistence, recursion, ADT lifecycle, redefinition, error recovery, /reset semantics, macro persistence, /mod). Defect surfaced: `/reset` not implemented (FIXME 0123, ledger entry); failing test landed un-ignored. Source preserved in legacy for /int harvest under FIXME 0124. |
| `repl_negative.rs` | 917 | 31 | 100 | 0 | 0 | 5 | `repl_negative.rs` (S64 W3 ✓), `legacy/repl_negative_old.rs` (S64 W3 ✓ FIXME 0124) | /int (with /typecheck — `session.shared.symbol_tables` reach-throughs) | S64 Wave 3 Batch 7 landed: 28 e2e tests in `tests/repl_negative.rs` (type errors, parse errors, unbound symbols, arity, constructor shape errors, defmacro shape errors, /list category boundaries (negative), display format negative, error recovery, slash command negative paths). The original integration-tier file (917 LOC) used `helpers::collect_list_categories(&session)` to inspect `session.shared.symbol_tables` directly — those reach-throughs preserved in `legacy/repl_negative_old.rs` for /int + /typecheck harvest under FIXME 0124. |
| `ring0.rs` | 1135 | 216 | 60 | 0 | 40 | 5 | `spec_03_types.rs` (S64 W5 ✓), `spec_04_expressions.rs` (S64 W5 ✓), `spec_05_definitions.rs` (S64 W5 ✓), `spec_appendix_a_builtins.rs` (S64 W5 ✓; W5.6 +8 carry-forwards; W5.6 supplement +6 carry-forwards), `repl_negative.rs` (W5.6 +1 + W5.6 supplement +1 = +2 carry-forwards), `repl_lifecycle.rs` (W5.6 supplement +1 carry-forward), `spec_12_runtime.rs` (W5.6 +6 carry-forwards), `legacy/ring0.rs` (S64 W5 ✓ FIXME 0134) | /typecheck (with /backend, /int — consolidated under FIXME 0134) | S64 Wave 5 Batch 2 landed: full quarantine. Ring 0 spec-anchored coverage absorbed into the 8 new spec-section e2e files via REPL-canonical authoring. **W5.6 file 4 (cluster mode 2026-05-04, commit `15e32b3`)**: 8 carry-forwards (5 TCO `#[ignore]` FIXME 0141, 1 div-min-by-neg-one, 1 deeply-nested-let, 1 duplicate-param-names). **W5.6 file 4 supplement (per-test re-audit 2026-05-04, `tests/plan/wave-5.6-ring0-reaudit.md`)**: cluster-mode missed 3 + 3 hard-to-call → user approved authoring all 6: `parse_error_unclosed_paren_neg` (failing, FIXME 0142 — `/int` REPL silently exits on EOF with unclosed `(`), `redefinition_updates_live_callers`, `if_nested_three_way_ladder`, `lambda_bound_in_let_and_called`, `lambda_passed_as_argument_invoked_inside_callee`, `defns_mutual_forward_references`. Methodology takeaway: cluster mode 97% accurate for ring0 (markedly better than W5.5 sketch_port 75%); per-test review remains warranted for sketch_port/e2e/ring1/ring2. Source preserved in legacy for unit-tier harvest. |
| `ring1.rs` | 2253 | 380 | 65 | 0 | 35 | 5 | `spec_05_definitions.rs` (S64 W5 ✓; W5.6 +1 chunks 1-3 carry-forward; W5.6 +1 chunk 4 carry-forward), `spec_06_pattern_matching.rs` (S64 W5 ✓; W5.6 +1 chunks 1-3 carry-forward; W5.6 +8 chunk 4 carry-forwards), `spec_07_traits.rs` (S64 W5 ✓), `spec_08_modules.rs` (S64 W5 ✓), `spec_09_macros.rs` (S64 W5 ✓), `spec_appendix_a_builtins.rs` (S64 W5 ✓; W5.6 +8 chunks 1-3 carry-forwards; W5.6 +3 chunk 4 carry-forwards), `spec_03_types.rs` (W5.6 +4 chunks 1-3 carry-forwards; W5.6 +7 chunk 4 carry-forwards), `spec_04_expressions.rs` (W5.6 +7 chunks 1-3 carry-forwards; W5.6 +3 chunk 4 carry-forwards), `spec_12_runtime.rs` (W5.6 +1 chunks 1-3 carry-forward), `repl_introspection.rs` (W5.6 +2 chunks 1-3 carry-forwards; W5.6 +1 chunk 4 carry-forward), `legacy/ring1.rs` (S64 W5 ✓ FIXME 0134) | /typecheck (with /backend, /int — consolidated under FIXME 0134) | S64 Wave 5 Batch 2 landed: full quarantine. Ring 1 spec-anchored coverage absorbed into spec-section e2e files. **W5.6 (per-test re-audit 2026-05-05, `tests/plan/wave-5.6-ring1-reaudit.md`)**: cluster-mode 72% accurate (136/190); 51 GAP-COVER + 3 DUPLICATE-IN-LEGACY findings. User approved all 51 GAP-COVER (chunked authoring). Chunks 1-3 (commit `07231cb`) landed 26 carry-forwards across 7 files. Chunk 4 (this commit) lands 23 net distinct carry-forwards (25 - 2 subsumed: #22 subsumes #8, #24 subsumes #9; #15 consolidates #173+#188 nested-pattern duplicate pair; #25 consolidates #189+#190 pattern-arity pair) across 6 files. Total: ~49 carry-forwards from ring1.rs across all chunks. All passing on current binary. Source preserved in legacy for unit-tier harvest. |
| `ring2.rs` | 2484 | 405 | 70 | 0 | 30 | 5 | `spec_03_types.rs` (W5.6 +3 chunk 4 carry-forwards), `spec_04_expressions.rs` (W5.6 +4 chunk 4 carry-forwards), `spec_05_definitions.rs` (S64 W5 ✓; W5.6 +2 chunk 4 carry-forwards), `spec_06_pattern_matching.rs` (S64 W5 ✓), `spec_07_traits.rs` (S64 W5 ✓; W5.6 +9 chunks 1-3 carry-forwards; W5.6 +4 chunk 4 carry-forwards), `spec_08_modules.rs` (S64 W5 ✓; W5.6 +3 chunk 4 carry-forwards), `repl_introspection.rs` (W5.6 +3 chunks 1-3 carry-forwards), `legacy/ring2.rs` (S64 W5 ✓ FIXME 0134) | /typecheck (with /backend, /int — consolidated under FIXME 0134) | S64 Wave 5 Batch 2 landed: full quarantine. Ring 2 ADT + trait coverage absorbed into spec-section e2e files. **W5.6 (per-test re-audit 2026-05-04, `tests/plan/wave-5.6-ring2-reaudit.md`)**: 30 GAP-COVER findings (7 REGRESSION-GUARD); ~70% COVERED density highest of the four ring2 chunks. User approved all ~30 GAP-COVER (chunked authoring). Chunks 1-3 (commit `df02ed6`) landed 12 net carry-forwards. **Chunk 4 (this commit)** lands 16 net distinct carry-forwards (#178 dropped on per-test review as DUPLICATE of #172 / `glob_import_excludes_private_neg`; #182/#190/#191 deferred to FIXME 0134 harvest scope per Wave 5.5 disposition): 3 module-visibility regression-guards → spec_08_modules.rs (#176/#177/#179); 3 type-system corner cases → spec_03_types.rs (#180 occurs check, #181 constrained-fn-in-let, #185 fn arity); 4 multi-sig + auto-curry → spec_04_expressions.rs (#186 multi-sig bare value, #195/#196 make-adder Int+Float monomorphisation, #197 auto-curry-on-lambda rejection w/ message text REGRESSION-GUARD); 4 HKT + trait auto-curry → spec_07_traits.rs (#187/#188/#189 HKT cluster RECLASSIFIED GAP-HARVEST→GAP-COVER per per-test review of spec/03 §3.7, spec/05 §5.4.4, spec/07 §7.2; #192 trait-op `(+ 5)` auto-curry); 2 docstring → spec_05_definitions.rs (#155 deftype, #156 deftrait). All 16 pass on current binary. Total ring2.rs carry-forwards: 28 across all 4 chunks. FIXME 0134 updated with HKT reclassification note. Source preserved in legacy for unit-tier harvest. |
| `ring3_repl.rs` | 825 | 50 | 95 | 0 | 5 | 10 | `repl_introspection.rs` (S64 W3 ✓), `repl_lifecycle.rs` (S64 W3 ✓), `legacy/ring3_repl.rs` (S64 W3 ✓ FIXME 0125) | /int (with /typecheck — macro-expansion internals + 16 stub tests) | S64 Wave 3 Batch 7 landed: macro introspection coverage absorbed into `repl_introspection.rs` (defmacro display single+multi-clause, bare macro lookup, /list shows defmacros, /list MUST NOT classify defmacros as Fns negative, /expand of user macro, /imports lists special forms) and `repl_lifecycle.rs` (defmacro persists across evals, multi-clause defmacro dispatches). Source preserved in legacy for /int + /typecheck harvest under FIXME 0125; the 16 stub tests recommend deletion at harvest. |
| `ring4_trace.rs` | 578 | 31 | 30 | 65 | 5 | 0 | `spec_12_runtime.rs` (S64 W4 ✓), `legacy/ring4_trace_taxonomy.rs` (S64 W4 ✓ FIXME 0130) | /typecheck (with /runtime co-owner — Type-shape assertions via repl_eval_typed Rust API) | S64 Wave 4 Batch 6 landed: the `(trace expr)` REPL-observable subset carried forward into `tests/spec_12_runtime.rs` (4 tests: trace returns Trace, nested trace, TraceCall pattern match, trace-form-without-import) plus `/run-tests` slash command (3 tests: passes, failures-with-reason, empty-module). 31 source tests' Type-shape assertions via `repl_eval_typed` preserved in `legacy/ring4_trace_taxonomy.rs` for /typecheck + /runtime harvest under FIXME 0130. No defects surfaced. |
| `scheduler.rs` | 571 | 18 | 0 | 100 | 0 | 0 | — | /int (entire file relocates as `#[cfg(test)]` inside scheduler crate post FIXME 0109 split) | All tests construct `cranelisp::scheduler::CompileScheduler` directly. Zero e2e analogue. Full quarantine. The scheduler's observable behaviour is covered indirectly by every other e2e test in the new suite. |
| `sketch_port.rs` | 1886 | 296 | 50 | 0 | 50 | 30 | `spec_03_types.rs` thru `spec_appendix_a_builtins.rs` (distributed via Wave 5; previous waves W3/W4 absorbed io/runtime parts), `spec_04_expressions.rs` (W5.6 +2), `spec_05_definitions.rs` (W5.6 +4), `spec_06_pattern_matching.rs` (W5.6 +1), `spec_07_traits.rs` (W5.6 +9), `spec_appendix_a_builtins.rs` (W5.6 +3), `spec_12_runtime.rs` (W5.6 +6), `repl_negative.rs` (W5.6 +2), `repl_lifecycle.rs` (W5.6 +1), `spec_platforms.rs` (W5.6 +2 NEW FILE), `legacy/sketch_port.rs` (S64 W5 ✓ FIXME 0136) | /qa (test-shape harvest; mostly self-resolved) | S64 Wave 5 Batch 2 landed: full quarantine. Spec-anchored coverage carried forward across Waves 3/4/5; sketch-port duplicated ring0/1/2 coverage extensively. **W5.6 file 5 (per-test re-audit 2026-05-04, `tests/plan/wave-5.6-sketch-port-reaudit.md`)**: 30 carry-forwards across 9 spec/repl files (consolidated from 33 GAP-COVER findings — chunk-3 #4 list-head-tail consolidated with chunk-2 #58 nested-match into one carry-forward with both Option/Some-None and Cons/Nil shapes; chunk-3 #16/#17 sigsegv consolidated with chunk-1 #38 default-method-used and chunk-3 #134 polymorphic-impl-on-concrete-ADT respectively). New `spec_platforms.rs` file holds the two platform DLL integration tests using `use_workspace_platforms()` + test-capture differential observation against stdio. All 30 carry-forwards land green at file 5 close (no failing-not-ignored required — implementation supports default-method synthesis, multi-sig type dispatch, polymorphic ADT impl on concrete instantiation, etc.). Methodology takeaway: cluster mode 73% accurate for sketch_port (vs ring0's 97%) confirms per-test audit is the right grain for files with high REGRESSION-GUARD density (`sigsegv_isolation_*`, `sketch_default_method_*`, RC + platform clusters). Pre-existing failure cluster historical at this point — recommended deletion at S65 alongside ReplSession removal. FIXME 0136 covers /qa-internal harvest verification. |
| `sprint23.rs` | 2744 | 61 | 80 | 5 | 15 | 25 | `regression.rs`, `repl_lifecycle.rs`, `spec_08_modules.rs`, `link.rs` (S64 W6 b2 Part A, NEW), `repl_shell.rs` (S64 W6 b2 Part A, NEW), `cache.rs` (S64 W6 b2 Part A, +3 cache_repl_*) | /int (heisenbug-race race-related internals) | Includes `heisenbug_race_reduced_concurrent_import_pairs` ledger entry — preserves signature. Defect risk: H6 residue ratecard may shift under e2e cadence. 5% quarantine isolates internal-API observation; 15% delete is duplication with sibling sprint-NN files. **S64 W6 ✓ — quarantined (2026-05-05)**. Part A (commit `3b10234`) + Part B authoring complete; `tests/sprint23.rs` quarantined to `tests/legacy/sprint23.rs` with FIXME 0144 → /int. Total carry-forward: **58 tests across 7 files** (Part A: 25 in link.rs/repl_shell.rs/cache.rs; Part B: 33 across repl_watch.rs/repl_persist.rs/repl_persist_race.rs + #57 in build_confidence.rs). All 58 PASS on current binary. #56 dropped per audit DUPLICATE-IN-LEGACY. The 4 inline `FIXME(/int)` markers in `tests/legacy/sprint23.rs` (lines 343/1304/2119/2194) folded into FIXME 0144's harvest scope for /int review. |
| `sprint59_cache_repro.rs` | 152 | 2 | 100 | 0 | 0 | 0 | `cache.rs` (S64 W6 b3 +2), `legacy/sprint59_cache_repro.rs` (S64 W6 b3 ✓ FIXME 0145) | /backend | **S64 W6 b3 ✓ — quarantined (2026-05-05)**. Both Sprint 59 Workstream A regression guards carried forward as siblings of `cache.rs::cache_repl_second_session_loads_prelude_from_cache` (W6 b2 carry): `cache_repl_minimal_plain_fn_prelude_restored_on_session_2` (minimum-viable plain-fn prelude angle) + `cache_repl_empty_prelude_session_2_evaluates_literal` (negative-control empty-prelude angle). Both PASS on current binary. Source preserved in legacy under FIXME 0145 → /backend. |
| `sprint59_defects456_repro.rs` | 1766 | 34 | 100 | 0 | 0 | 0 | `regression.rs` (S64 W6 b3 +34), `legacy/sprint59_defects456_repro.rs` (S64 W6 b3 ✓ FIXME 0145) | /backend | **S64 W6 b3 ✓ — quarantined (2026-05-05)**. All 34 d45/d6 reduction rungs carried forward into `tests/regression.rs` as defect-repro cohort siblings of T-S2-2 (Wave 6 batch 1). Per `tests/plan/wave-6-batch-3-audit.md` 100% GAP-COVER REGRESSION-GUARD (zero DUPLICATE, zero COVERED, zero GAP-HARVEST). 30/34 PASS on current binary; 4 FAIL un-ignored — the four open Defect 6 ledger entries (`d6_exemplar_solve_minimal_puzzle_no_io`, `d6_exemplar_propagate_only`, `d6_exemplar_solve_all_dots`, `d6_exemplar_propagate_single_pass`) per `memory/feedback_failing_not_ignored.md` and existing `tests/plan/ledger.md` lines 83–131 entries. Six clusters (§A synthetic single-file, §B cross-module synthetic, §C real exemplar, §D html-source ladder, §E Vec/ADT/Grid COW, §F+§G real exemplar). 24 inline `// FIXME(/backend)` hypothesis comments preserved verbatim in carry-forward; legacy file inline FIXMEs migrate to numbered fixme files at FIXME 0145 close per Sprint 63 M7 protocol. |
| `sprint59_neg.rs` | 271 | 12 | 80 | 20 | 0 | 5 | `spec_08_modules.rs` (S64 W5 ✓), `legacy/sprint59_neg.rs` (S64 W5 ✓ FIXME 0139) | /int (optional — carry-forward complete) | S64 Wave 5 Batch 3 landed: module-boundary negative-coverage subset (import non-existent name, super-rejection at top level) absorbed into `tests/spec_08_modules.rs::*_neg`. Defect-8 latent-gap regression guard (`defn_body_with_trace_triggers_extern_registration_neg`) preserved in legacy for /int harvest under FIXME 0139 (optional — `tests/spec_04_expressions.rs::trace_returns_trace_type` provides language-level coverage). |
| `sprint60_cache_build_marker.rs` | 261 | 3 | 100 | 0 | 0 | 0 | `cache.rs` (S64 W6 b4 +3), `legacy/sprint60_cache_build_marker.rs` (S64 W6 b4 ✓ FIXME 0146) | /backend | **S64 W6 b4 ✓ — quarantined (2026-05-05)**. All 3 build-id e2e tests carried forward to `tests/cache.rs` as user-surface wrappers around the unit-tier serialise/deserialise tests in `crates/cranelisp-backend/src/cache/serialize.rs`: `cache_meta_carries_build_id_after_first_compile` (write-side), `cache_meta_with_stale_build_id_triggers_recompile` (invalidation), `cache_meta_without_build_id_field_triggers_recompile` (schema-evolution). All 3 PASS on current binary. Source preserved in legacy under FIXME 0146 → /backend. |
| `sprint60_observability.rs` | 182 | 4 | 0 | 100 | 0 | 0 | `legacy/sprint60_observability.rs` (S64 W4 ✓ FIXME 0131) | /backend (CRANELISP_CODEGEN_DUMP env-var filter; debugging aid not a spec'd surface) | S64 Wave 4 Batch 6 landed: full quarantine. The CRANELISP_CODEGEN_DUMP env var is a backend debugging aid (`tests/CLAUDE.md` §"Diagnostic Logging"), not a spec'd language behaviour — no e2e analogue. 4 subprocess-launch tests preserved in `legacy/sprint60_observability.rs` for /backend harvest under FIXME 0131; existing `clif_dump_matches_*` `#[cfg(test)]` units in cranelisp-backend are the natural home. |
| `sprint60_reduction.rs` | 721 | 17 | 100 | 0 | 0 | 0 | `regression.rs` (S64 W6 b4 +17), `legacy/sprint60_reduction.rs` (S64 W6 b4 ✓ FIXME 0146) | /backend | **S64 W6 b4 ✓ — quarantined (2026-05-05)**. All 17 cache-reuse + drop-glue reduction rungs carried forward to `tests/regression.rs`: §A cache-reuse cluster (11 tests: step 1 baseline + 2.1–2.7 reductions + 3 controls); §B drop-glue cluster (6 tests: minimal 14-LOC + 5 controls). All 17 PASS on current binary (the underlying defects were resolved by Sprint 60 Workstream A single-GOT fix + W2 R2 drop-glue fix). 10 inline `// FIXME(/backend)` hypothesis comments preserved verbatim in carry-forward + legacy file; "resolved-by-passing-carry-forward" disposition pending /backend harvest verification. Source preserved in legacy under FIXME 0146 → /backend. |
| `sprint60_run_tests_reduction.rs` | 325 | 5 | 100 | 0 | 0 | 0 | `regression.rs` (S64 W6 b4 +5), `legacy/sprint60_run_tests_reduction.rs` (S64 W6 b4 ✓ FIXME 0146) | /backend (with /int co-owner — REPL session_v4 lifecycle) | **S64 W6 b4 ✓ — quarantined (2026-05-05)**. All 5 REPL-eval persistence-collapse reductions carried forward to `tests/regression.rs`: 4 `_failing` reductions + 1 `_passes_control`. The cluster is INTERMITTENTLY flaky — different tests fail across consecutive full-suite runs (race condition in entry-module sexp-lifecycle wiring). Original shutdown-path symptom ("no parsed sexps for module 'user'") has shifted to active-path panic (`register_dep_for_eval MUST publish dep_sexps` in src/session_v4.rs:1572). Per `memory/feedback_failing_not_ignored.md`, lands un-ignored. Co-ownership: /int (REPL session_v4 wiring) is secondary observer; /backend is primary harvest target per Wave 6 b2/b3 precedent. Source preserved in legacy under FIXME 0146. |
| `sprint61_bare_primitive.rs` | 267 | 5 | 100 | 0 | 0 | 0 | `repl_introspection.rs` (S64 W6 b5 +5), `legacy/sprint61_bare_primitive.rs` (S64 W6 b5 ✓ FIXME 0147) | /int | **S64 W6 b5 ✓ — quarantined (2026-05-05)**. All 5 Slice 1 bare-primitive-value-path regression guards carried forward into `tests/repl_introspection.rs` as siblings of the existing `bare_primitive_type_int_displays_type_info` (which covers bare primitive **type** lookup; these five cover bare primitive **fn** lookup — different resolution path). All 5 PASS on current binary. Source preserved in legacy under FIXME 0147 → /int (Slice 1 fix area: `src/session_v4.rs::resolve_entry_for_display` + `check_bare_symbol_introspection`). Spec-link linter pre-port findings (1 MIS-CITED, 1 MALFORMED) addressed in carry-forward annotations. |
| `sprint61_io_closure_regression.rs` | 215 | 2 | 100 | 0 | 0 | 0 | `spec_10_io.rs` (S64 W3 ✓), `legacy/sprint61_io_closure_regression.rs` (S64 W3 ✓ FIXME 0127) | /backend (capture-return-inc; optional — carry-forward complete) | S64 Wave 3 Batch 4 landed: 7-line minimum repro preserved in `tests/spec_10_io.rs::capture_return_inc_does_not_double_free`. Source legacy'd for provenance under FIXME 0127. |
| `sprint61_observability_io.rs` | 446 | 7 | 30 | 70 | 0 | 5 | `legacy/observability_io.rs` (S64 W3 ✓ FIXME 0128) | /runtime (io_trace direct API + ring buffer + cache .meta.json leakage) | S64 Wave 3 Batch 4 landed: full quarantine — every assertion calls `cranelisp_runtime::io_trace::*` directly. Renamed `legacy/observability_io.rs` (dropped sprint61_ prefix). The harness-robustness ledger entry (`io_trace_off_path_subprocess_completes_within_generous_ceiling`) implicitly resolves under the new harness's per-test TempDir isolation; recommended deletion at harvest. Source preserved for /runtime harvest under FIXME 0128. |
| `sprint61_observability_scheduler.rs` | 483 | 9 | 0 | 100 | 0 | 0 | `legacy/sprint61_observability_scheduler.rs` (S64 W4 ✓ FIXME 0132) | /int (with /runtime co-owner — post FIXME-0098/0103/0040 the trace module may relocate from cranelisp-runtime to src/) | S64 Wave 4 Batch 6 landed: full quarantine. 6 Rust-API tests + 3 subprocess tests; both clusters reach into `cranelisp::observability::*` directly. CRANELISP_SCHEDULER_TRACE is a debugging aid; no e2e analogue. Source preserved in `legacy/sprint61_observability_scheduler.rs` for /int harvest under FIXME 0132 (consolidated with the shared file). |
| `sprint61_observability_shared.rs` | 251 | 3 | 0 | 100 | 0 | 0 | `legacy/sprint61_observability_shared.rs` (S64 W4 ✓ FIXME 0132) | /int (with /runtime co-owner — `trace_instant_anchor` + boundary-crate hygiene scan) | S64 Wave 4 Batch 6 landed: full quarantine. Cross-cutting trace invariants between scheduler + IO trace channels (shared anchor, merge-sort key compatibility, boundary-crate hygiene scan). All Rust-API. Consolidated under FIXME 0132 with the scheduler file. |
| `stdlib.rs` | 699 | 54 | 100 | 0 | 0 | 0 | `spec_11_stdlib.rs` (S64 W2 ✓) | — | S64 Wave 2 Batch 5 landed: 54 e2e tests in `tests/spec_11_stdlib.rs`, all passing. The named exception — single caller of `use_workspace_stdlib_for_stdlib_conformance_only()`. Each test encodes the assertion as `(defn main [] expr)` with i64 return = exit code; non-Int witnesses (Bool/String/ADT) wrapped via if/match returning 0 on success. Source `tests/stdlib.rs` deleted. |
| `v4_jit_reclaim.rs` | 700 | 6 | 0 | 100 | 0 | 0 | `legacy/v4_jit_reclaim.rs` (S64 W4 ✓ FIXME 0133) | /backend (with /runtime co-owner — `cranelisp_runtime::*_count()` atomics, `cranelisp_backend::jit::jit_free_memory_call_count`, `cranelisp::code::Code` enum reach-throughs) | S64 Wave 4 Batch 6 landed: full quarantine. Decision 31 Scenario 2 (per-redefn JIT reclaim) is observable through `/mem` (per `repl/spec.md §3.7`) but the precise byte-level deltas asserted here are finer than `/mem` text supports. Source preserved in `legacy/v4_jit_reclaim.rs` for /backend + /runtime harvest under FIXME 0133. A `/mem`-based reclaim smoke (live bytes don't grow monotonically across N redefns) is recommended for the e2e suite at harvest time once `/mem` output is stable. Note: per Decision 41, `Code` moves to cranelisp-backend — harvest must update import paths. |
| `v4_pipeline.rs` | 1206 | 47 | 57 | 0 | 43 | 0 | `spec_12_runtime.rs` (S64 W6 b6 +11), `spec_09_macros.rs` (S64 W6 b6 +11), `spec_08_modules.rs` (S64 W6 b6 +2), `spec_platforms.rs` (S64 W6 b6 +3), `legacy/v4_pipeline.rs` (S64 W6 b6 ✓ FIXME 0149) | /int (with /backend, /frontend, /platform co-owners) | **S64 W6 b6 ✓ — quarantined (2026-05-05)**. **FINAL Wave 6 batch.** 27 carry-forwards across 4 e2e files: §12.6 entry-point cluster (5 — first coverage of `[R4 S10]` UNTESTED) + §12.7.4.2 batch-mode error cluster (6 — first coverage of `[R4 S18]`) + §9.2.5 macro semantics + §H cross-module macros worker.rs:762 fix cluster (6) + §8.10.1 Step 5 resumption + §8.3 multi-import + Step 8 platform DLL trio. 18 tests DUPLICATE-IN-LEGACY (REPL-canonical equivalents in spec_04/05/08/09/appendix-a + cache.rs). 47/47 PASS on legacy; 27/27 PASS on carry-forwards. **Defect-discovery**: carry-forward of `v4_resumption_correctness` surfaced an open SEGV defect — the legacy test only checked stderr emptiness; the new carry-forward records the §8.10.1 resumption shape SEGVs at runtime (exit 139). Recorded as `XXX(/backend) FIXME 0149` inside the passing carry-forward (legacy spec invariant — clean stderr — preserved). Inline FIXME on legacy line 587 (Sprint 58 W2c cache-hit) preserved verbatim — resolved-by-passing-carry-forward. Source preserved in legacy under FIXME 0149 → /int (primary; with /backend, /frontend, /platform co-owners). |
| `v4_repl_eval.rs` | 567 | 14 | 100 | 0 | 0 | 5 | `repl_lifecycle.rs` (S64 W3 ✓), `legacy/v4_repl_eval.rs` (S64 W3 ✓ FIXME 0126) | /int (optional — carry-forward complete) | S64 Wave 3 Batch 7 landed: already e2e-shaped; 14 tests' spec coverage absorbed into `repl_lifecycle.rs` (defn-then-call, multi-form persistence, error cascade recovery) and `repl_introspection.rs` (defn display, type display). Bespoke `run_repl(input, label)` retired in favour of `Cranelisp::new().repl().stdin(...)`. Source preserved in legacy as provenance — FIXME 0126 recommends optional deletion at S65 cleanup. |
| `wave2_g6.rs` | 370 | 9 | 0 | 100 | 0 | 0 | — | /typecheck, /backend (Layer-3 `Code{ptr}` writes on `ModuleEntry::Def`) | Self-described "Layer 3 integration"; full quarantine. |
| `wave3_g8.rs` | 557 | 9 | 0 | 100 | 0 | 0 | — | /backend (Layer-3 internal observations) | Full quarantine. |
| `wave4_g9.rs` | 534 | 4 | 0 | 100 | 0 | 0 | — | /int (persistent-priority-worker observation) | Full quarantine. |
| `wave6_demo_repros.rs` | 495 | 5 | 100 | 0 | 0 | 5 | `repl_persist_race.rs` (S64 W6 b5 +1), `spec_08_modules.rs` (S64 W6 b5 +1), `repl_introspection.rs` (S64 W6 b5 +1), `regression.rs` (S64 W6 b5 +2), `legacy/wave6_demo_repros.rs` (S64 W6 b5 ✓ FIXME 0148) | /int (with /backend, /stdlib, /port co-owners) | **S64 W6 b5 ✓ — quarantined (2026-05-05)**. All 5 Wave 6 demo-defect repros carried forward across 4 e2e files (one per defect). Defect 1 (REPL dep-load race) → `repl_persist_race.rs::repl_dep_load_no_race_with_persistent_workers`. Defect 2 (stdlib seq.lazy null-import) → `spec_08_modules.rs::null_import_module_resolves_all_names_via_explicit_imports`. Defect 3 (docstring separator) → `repl_introspection.rs::display_defn_with_docstring_uses_dash_separator`. Defects 4+5 (/run-tests batched crash) → `regression.rs::wave6_run_tests_batched_html_completes_without_crash` (positive-completion angle on top of existing d45 cluster signal-crash check). Defect 6 (exemplar solver stack-overflow) → `regression.rs::wave6_exemplar_solver_full_run_does_not_stack_overflow` — **FAILING-NOT-IGNORED** (open Defect 6, joins four existing failing-not-ignored `d6_exemplar_*` guards from W6 b3; exercises the **real solver entry** `--run exemplar/solver.cl::main` including IO trampolines, distinct angle from synthetic single-form repros). 4/5 PASS on current binary; 1 FAIL (Defect 6, per ledger). 5 inline `// FIXME(/skill)` markers preserved verbatim; 4 are resolved-by-passing-carry-forward, 1 (Defect 6) is open and folds into FIXME 0145's parent /backend solver-recursion scope. Source preserved in legacy under FIXME 0148 → /int (with /backend + /stdlib + /port co-owners). |

**Aggregate** (rough): ~57% carry-forward, ~25% quarantine, ~13%
delete (mostly `ring*.rs` and `sketch_port.rs` deduplication against
broad-surface ports), ~5% expected defects (~80–110 failing tests
landing as ledger rows + FIXMEs).

### Mode canonicalisation — REPL is the canonical surface for language conformance

**Decision (Sprint 64 Wave 2.5, 2026-05-03)**: bulk language-conformance
tests run in **REPL mode only**. A small curated subset additionally
runs through all six mode×cache permutations (REPL fresh / REPL cached
/ `--run` fresh / `--run` cached / `--link` fresh / `--link` cached)
to validate that the three CLI surfaces converge on equivalent
observable behaviour. The mode-equivalence subset is the empirical
validation of Principles 11–13 (single pipeline, design for full
spec surface, `interfaces.md` is auditable) and Decisions 22, 25, 41
(pipeline-v4 single code path).

**Rationale.** The user's framing (2026-05-03):

> "we want the language tests to run the same through each path. on
> the other hand, we want to ensure that there is a single code path
> through all of them, so it shouldn't matter, and we don't want to
> provide assurance that three code paths are all working. the right
> answer is probably to do all the language testing through one path
> — maybe repl, and then establish additional tests that verify the
> other modes use the same code"

If three CLI surfaces are tested with three parallel test suites of
the same shape, the test suite implicitly grants three independent
implementations the same level of assurance — which is the opposite
of Principle 11 ("single pipeline, mode parameters"). Wave 2's
`spec_11_stdlib.rs` (54 tests through `--run` exit-code) and
`build_confidence.rs` (7 hand-mixed) reproduced this anti-pattern.
Wave 2.5 corrects it.

#### Canonical mode for bulk language conformance: REPL

**Why REPL, not `--run`:**

1. **More code per test.** Each form fed to the REPL exercises the
   form-by-form scheduler, the prompt loop, the per-form display
   pipeline, the symbol-table updates between forms, and the lazy
   prelude loading. `--run` executes one program through the batch
   driver and observes only the exit code — a thinner observation.
2. **Closer to dev-loop user experience.** The REPL is what users
   touch most often; conformance tested through the REPL is
   conformance under the same conditions as everyday use.
3. **Form-by-form decomposability.** Conformance tests assert
   per-form output (`:primitives/Int 3`, `:primitives/Bool true`)
   rather than packaging each test as a `defn main` returning Int.
   The encoded-as-Int wrapping (`(if cond 0 1)`) noise is gone.
4. **Tighter feedback in the failure path.** A REPL test that fails
   prints the offending form's stdout slice; `--run` prints only
   the exit code, hiding which assertion fired.

**Authoring pattern:**

```rust
Cranelisp::new()
    .repl()
    .with_prelude(PreludeVariant::TestStandard)
    .stdin("(+ 1 2)\n")
    .output()
    .assert_stdout_contains(":primitives/Int 3");
```

The `assert_stdout_contains` shape is the canonical default. For
multi-form sessions the test pipes additional lines and asserts each
result substring is present.

#### Mode-specific exceptions

Tests legitimately authored against a non-REPL mode:

| File / surface | Canonical mode | Why |
|---|---|---|
| `cache.rs` (cache hit/miss tests) | `--run` / `--link` | Cache materialisation is `--run`/`--link` semantics; the cache is what's under test, not language conformance. Cache assertions inspect tmpdir state (`tmp_exists`, `read_tmp`), exit code (does the cached build still run?), and `run_again()` parity. |
| `examples.rs` | `--run` | The natural shape of "given this `examples/*.cl`, the program runs and exits cleanly". Examples are user-facing programs, not REPL transcripts. |
| `exemplar.rs` | `--run` (or `--link`-then-run) | Same rationale as examples, plus exemplar exercises link-time bundling. |
| `repl_introspection.rs`, `repl_lifecycle.rs`, `repl_negative.rs` | REPL | These ARE the REPL-specific tests — slash commands, multi-form sessions, prompt shape, error recovery. They exist outside the language-conformance bulk by definition. |
| `build_confidence.rs` mode-equivalence subset | All 6 permutations | See below. The subset's job is to test that the modes converge. |
| `build_confidence.rs` smoke set | Mixed (one per mode) | A handful of tests verify each mode boots at all (REPL banner, `--run` exit, `--link` produces an executable). One test per mode, not a coverage matrix. |

A test file outside this list authored against `--run` or `--link` is
drift; the audit corrects it during port.

#### Mode-equivalence subset

A curated set of ~10–20 tests authored once and run through six
permutations:

1. **REPL fresh** (no cache; `(main)` piped after defn)
2. **REPL cached** (after first run completes, re-spawn the binary in
   the same TempDir, replay the same stdin, observe equivalent output)
3. **`--run` fresh** (no cache)
4. **`--run` cached** (re-spawn `--run` in the populated TempDir)
5. **`--link` fresh** (link, run produced binary; no cache)
6. **`--link` cached** (re-spawn `--link` in the populated TempDir)

**Inclusion criteria** (one test per language-feature class — the
goal is class coverage, not per-test density):

- arithmetic (operators, mixed types)
- ADTs (Option, Result construction + match)
- pattern match (nested patterns, wildcards)
- traits (operator-as-method dispatch via Num/Eq/Ord)
- modules (one entry + one helper module + import)
- macros (a basic `defmacro` body that expands and runs)
- IO (a `(print ...)` call returning Pure-wrapped value)
- error path (a compilation error reaches the user identically across all 6)

**Canonical observation form**: each test program is `(defn main [] expr)`
returning an `Int`. The cross-mode equivalence is "main returns N → all
6 paths produce N". For each permutation:

| Permutation | Observation |
|---|---|
| REPL fresh | `(main)` piped after defn; stdout contains `:primitives/Int N` |
| REPL cached | Same as REPL fresh after re-spawn in populated TempDir |
| `--run` fresh | Process exit code = N |
| `--run` cached | Process exit code = N after re-spawn in populated TempDir |
| `--link` fresh | Produced binary exit code = N |
| `--link` cached | Produced binary exit code = N after re-spawn |

The canonical form is "extracted Int". The harness reduces each
permutation's raw observation (REPL stdout substring; `--run` exit;
binary exit) to this canonical form and asserts all 6 values match.
A divergence in any permutation panics with a per-permutation diff.

Tests where Int-encoding distorts the assertion (e.g., string equality
checks) live in the bulk-conformance REPL suite, not the
mode-equivalence subset.

**Empirical validation of pipeline-v4.** The mode-equivalence subset
is the active assertion that Decisions 22/25/41 have landed: cache vs.
fresh-build does not branch behaviour (Decision 37 / Principle 11);
REPL vs. `--run` vs. `--link` differ only in mode parameter (Principle
11); all six paths share the same `compile_to_module` per-symbol
codepath (Decision 41). When a permutation diverges, that's a parity
defect — file a FIXME, ledger row, do not fix in-sprint (parity rule).

#### Audit workflow specification

The four-step pass is the unit of Phase 2 work. This section specifies
how to perform it concretely.

**Mode selection during audit pass.** During each file's audit:

1. **Default canonical mode = REPL** for any assertion whose property
   is language conformance. Port to the REPL pattern using
   `assert_stdout_contains(":Type value")`.
2. **Mode-specific exception** if the file is in the §"Mode-specific
   exceptions" table above. Cache, examples, exemplar, REPL-specific,
   build_confidence smoke, and the mode-equivalence subset are the
   named exceptions; all other files port to REPL canonical.
3. **Mode-equivalence inclusion check.** For each carried-forward
   assertion, ask: "is this test the cleanest representative of its
   language-feature class for the mode-equivalence subset?" If yes,
   author the test in `build_confidence.rs` using
   `run_through_all_modes()`; otherwise author in the spec-section
   file using REPL canonical.

#### What is a "language-behaviour assertion"?

An assertion is **language-behaviour** if and only if the property it
checks is observable from outside the binary: stdout, stderr, exit
code, or a filesystem artefact under the per-test TempDir, while
running `target/debug/cranelisp` as a subprocess.

Anything that requires inspecting one of the following is
**Rust-internal** and quarantines:

- `cranelisp::*` types — `CompilerSession`, `SharedState`, `SymbolTable`,
  `ModuleEntry`, `Code{ptr}`, `Sess` …
- `ReplSession::*` private getters — `symbol_tables()`,
  `show_entry(...)`, in-process module graph inspection.
- Runtime counter atomics — `cranelisp_runtime::bytes_current()`,
  `alloc_count()`, `dealloc_count()`, scheduler observability gauges.
- Direct construction of session primitives, `CompileScheduler`,
  `cranelisp_backend::cache::*`, `cranelisp_runtime::io_trace::*` ABIs.
- Reading internal struct fields by name (manifest serialisation
  shape, `CacheManifest::version`, etc.) when not also written through
  the binary's CLI/file surface.

#### Threshold rule for borderline assertions

Some assertions check a property that is observable BOTH internally
(e.g., "the type checker inferred `Int` for `x`") AND externally
(e.g., "the REPL prints `:Int 3` for `x`"). The internal observation
is more direct; the external observation is more durable.

**Default rule: prefer carry-forward when both are possible.** The
binary's observable surface is where the spec lives; if the property
shows up there, the e2e test is the right home. The internal version
is then redundant and quarantines or deletes.

**Quarantine only when e2e cannot observe the property.** If carrying
forward would require asserting on the absence of evidence (e.g.,
"the optimiser elided this allocation" — observable only via RC trace
output that the harness intentionally rejects, per `helpers.md`
§"What the harness does NOT provide"), quarantine it.

**Tie-breaker for "redundant"**: the test deletes only if a sibling
test in the carry-forward set already checks the same spec property
under at least one of the same input shapes. Otherwise carry forward.

#### `tests/legacy/` mechanism

Cargo's auto-discovery for integration tests scans `tests/*.rs` at
the top level only. Files under `tests/legacy/` are NOT compiled
into test binaries by `cargo test` / `cargo nextest run`. This is
the load-bearing property: quarantined files are preserved as source
archive without contributing to test runs.

**Per-file header comment** (every `tests/legacy/*.rs` opens with):

```rust
// QUARANTINED — Sprint 64 test-port. Not built or run by Cargo.
// FIXME: design/arch/fixmes/NNNN-harvest-tests-legacy-FILE.md
// Owning crate: cranelisp-{backend,runtime,frontend,typecheck} (or src/)
// Owning skill: /backend (or /runtime, /int, /typecheck, /frontend)
// Quarantined: 2026-MM-DD
//
// This file's assertions test Rust-internal state with no e2e
// equivalent. Harvest into `#[cfg(test)]` unit tests inside the
// owning crate per memory/feedback_unit_tests_with_dev.md and
// memory/project_test_strategy.md. Source preserved verbatim;
// translation may require dev-dependency adjustments and import
// rewrites against the post-FIXME-0109 internal surface.
```

**Index file** (`tests/legacy/README.md`):

```markdown
# tests/legacy/ — Quarantine archive

Source archive of test files moved out of the e2e tier during the
Sprint 64 test-port. Not built by Cargo (nested directory under
`tests/` is not auto-discovered). Each file is awaiting harvest
into the owning crate's `#[cfg(test)]` unit tests.

| File | LOC | Tests | Owning skill | FIXME | Quarantined |
|---|---:|---:|---|---|---|
| `cache.rs` | ~1500 | ~38 | /backend | 0NNN | 2026-MM-DD |
| `scheduler.rs` | 571 | 18 | /int | 0NNN | 2026-MM-DD |
| ... | | | | | |

## Discipline

- Files here are NOT modified after quarantine. They are read-only
  archive until the FIXME is actioned and the file is deleted.
- Each FIXME is filed against the owning crate's `/dev` skill with
  a `harvest:` prefix in the title (e.g.,
  "harvest: tests/legacy/cache.rs into cranelisp-backend unit tests").
- When a file is fully harvested, it is deleted (not blanked) and
  its row removed from this README. Git history preserves
  provenance.
```

#### FIXME format for harvest commitments

Every quarantined file requires a FIXME under
`design/arch/fixmes/NNNN-harvest-<file>.md`:

```yaml
---
number: NNNN
target: /backend         # or /runtime, /int, /typecheck, /frontend
filed_by: /qa
filed_at: 2026-MM-DD
sprint_filed: 64
refers_to: tests/legacy/<file>.rs
status: open
---

# Harvest tests/legacy/<file>.rs into <crate> unit tests

## Issue
The Sprint 64 test-port quarantined this file because its assertions
test Rust-internal state with no e2e equivalent (counter atomics,
direct cache::* API, scheduler observability, …). Per the two-tier
strategy (`memory/project_test_strategy.md`), these belong as
`#[cfg(test)]` unit tests inside the owning crate.

## Proposed resolution
- Read each test in `tests/legacy/<file>.rs`.
- Translate into `#[cfg(test)]` modules inside
  `crates/<crate>/src/<module>.rs` adjacent to the code under test.
- Use cranelisp-frontend's `parse` + `build_program` for AST input
  per `tests/CLAUDE.md §"Isolating Cross-Crate Failures"` — do NOT
  hand-construct AST.
- When complete, delete `tests/legacy/<file>.rs` and remove its row
  from `tests/legacy/README.md`. Git history preserves provenance.

## Operational implication / Context
This harvest is a coverage-preservation commitment from S64. Until
it lands, the assertions are inert (the file is not compiled). The
FIXME blocks no other work — but the longer it sits, the further
the post-FIXME-0109 internal surface drifts from the quarantined
shape and the more rewrite the harvest requires.
```

#### Per-file commit discipline

**Recommendation: per-file commit.** Each source file's audit + carry-forward
ports + quarantine + FIXME filing land as a single commit. Rationale:

- The audit is the load-bearing creative work; a per-file commit
  message is the audit trail (which assertions carried, which
  quarantined, which deleted, why).
- Failing tests landed during the audit pair with their `Ledger:`
  trailer (per the lockstep mechanism below) at file granularity —
  one commit, one ledger update, one diff to review.
- Reverting an audit decision is a clean revert.

Exception: trivial files with full carry-forward may batch by topic
(e.g., `examples.rs` + `examples_run.rs` together; the three
`sprint60_*.rs` cache files together). Default to per-file unless the
batch is clearly mechanical and < ~5 commits-worth.

### Phase 2 batches

Batches are organised by **destination file in the new shape** rather
than by source-file affinity. This makes the reorganisation visible at
the batch level: each batch produces (or extends) a discrete set of
target files, with the corresponding `tests/legacy/` quarantines and
FIXMEs.

Batch numbers are `/qa`'s proposal; Phase 4 finalises wave
organisation.

| Batch | Targets | Source files audited | Approx audited LOC | Notes |
|---:|---|---|---:|---|
| 1 | `cache.rs` + `legacy/cache.rs` (Phase 1 §2 seed) | `cache.rs`, `sprint59_cache_repro.rs`, `sprint60_cache_build_marker.rs` | 2,486 | Phase 1 §2 cache-isolation test seeds the new `cache.rs`. Cache-internals quarantine into `legacy/cache.rs`. Smallest batch by source-file count, large by audit volume — start here for momentum. |
| 2 | `spec_03_types.rs`, `spec_04_expressions.rs`, `spec_05_definitions.rs`, `spec_06_pattern_matching.rs`, `spec_07_traits.rs`, `spec_appendix_a_builtins.rs` | `e2e.rs`, `ring0.rs`, `ring1.rs`, `ring2.rs`, `lenient.rs`, `sketch_port.rs` (partial) | ~10,000 | The bulk of conformance carry-forward. Significant dedupe pressure between `e2e.rs` and the ring files. Large batch — sub-batch internally by spec-section file. The audit must dedupe before placing; otherwise Carry%×4 source files pile up against the same target. |
| 3 | `spec_08_modules.rs`, `spec_09_macros.rs` | `macros.rs`, `modules.rs`, `sprint59_neg.rs`, `ring1.rs` (partial), `e2e.rs` (partial), `sketch_port.rs` (partial) | ~1,300 (incremental) | Module + macro surface. `with_prelude(PrimitivesOnly)` + user-defined macros via `user.cl`. |
| 4 | `spec_10_io.rs` + `legacy/observability_io.rs` (partial) + `legacy/rc_alloc_trace.rs` (partial) | `io.rs`, `io_minimal.rs`, `sprint61_io_closure_regression.rs`, `sprint61_observability_io.rs` | 2,141 | IO surface. capture-return-inc residues + trampoline trace observability. Trace-channel parsing migrates to `legacy/`. |
| 5 | `spec_11_stdlib.rs` | `stdlib.rs` | 699 | Smallest batch. The `use_workspace_stdlib_for_stdlib_conformance_only()` named exception. |
| 6 | `spec_12_runtime.rs` + `legacy/v4_jit_reclaim.rs` + `legacy/observability_*.rs` + `legacy/rc_alloc_trace.rs` (rest) + `legacy/ring4_trace_taxonomy.rs` | `rc.rs`, `ring4_trace.rs`, `sprint60_observability.rs`, `sprint61_observability_scheduler.rs`, `sprint61_observability_shared.rs`, `v4_jit_reclaim.rs` | 3,375 | Heaviest quarantine batch. RC alloc/free balance, JIT reclaim counter atomics, scheduler observability all migrate to `legacy/`. Per-file commits because each FIXME targets a different owning skill. |
| 7 | `repl_introspection.rs`, `repl_lifecycle.rs`, `repl_negative.rs` | `repl_experience.rs`, `repl_negative.rs`, `ring3_repl.rs`, `v4_repl_eval.rs` | 5,429 | REPL experience surface. **Sub-batch `repl_experience.rs` to two commits** (introspection vs. lifecycle). Common defect risk: prompt stability + `/reset` cache-state. |
| 8 | `examples.rs`, `exemplar.rs`, `regression.rs` (defect cluster) | `examples.rs`, `examples_run.rs`, `exemplar.rs`, `exemplar_solver_correctness.rs`, `sprint23.rs`, `sprint59_defects456_repro.rs`, `sprint60_reduction.rs`, `sprint60_run_tests_reduction.rs`, `sprint61_bare_primitive.rs`, `wave6_demo_repros.rs`, `v4_pipeline.rs` (lifecycle bits) | ~9,000 | The defect-repro cohort + examples + exemplar. Largest source-file count; mostly mechanical. |
| 9 | `legacy/scheduler.rs`, `legacy/wave2_g6.rs`, `legacy/wave3_g8.rs`, `legacy/wave4_g9.rs` (full quarantine, no e2e carry) | `scheduler.rs`, `wave2_g6.rs`, `wave3_g8.rs`, `wave4_g9.rs` | 2,032 | Pure-quarantine batch. No e2e carry-forward. Files move under `legacy/` with header + FIXMEs. May land in parallel with earlier batches because the move is mechanical. |
| 10 | `build_confidence.rs` | (synthesised — no source file maps directly) | — | The release gate per `qa.md §"Working build requirement"`. Hand-authored from the smoke-set definition; not a port. |

**Volume estimate**: ~36,000 source LOC audited; ~57% carry-forward
becomes ~1,500–2,000 e2e tests in the reorganised suite (the audit
de-dupes against itself heavily for the ring/sketch/e2e overlap);
~25% quarantines as ~10 `legacy/*.rs` archive files; ~13% deletes
silently; ~80–110 failing tests land as ledger rows + FIXMEs.

### Sprint sizing assessment — recommend two-sprint split

**Honest read: the four-step pass per file is significantly more
work than the previous "mechanical port" framing.** The previous
plan estimated 8 batches as "one sprint of work" under
classify-then-port. Under audit-then-port-then-reorganise-then-quarantine:

- The audit step is creative work, not mechanical. Each file's tests
  must be read, classified, and the fate of each assertion decided
  against the threshold rule. For `repl_experience.rs` (190 tests),
  that is ~4–6 hours of careful reading at minimum.
- The reorganisation step routes carry-forward assertions across 16
  destination files. Each routing decision is small but they
  accumulate; for ~1,500 carried assertions, this is the long pole.
- The dedupe pressure between `e2e.rs`, `ring0/1/2.rs`,
  `sketch_port.rs`, and `v4_pipeline.rs` is real — these files
  overlap heavily and the dedup decisions are the hardest part of
  Batch 2. Mis-routing or under-dedup leaves the new suite with
  duplicated coverage that defeats the manageability goal.
- Failing tests landing during port consume ledger discipline budget;
  the lockstep mechanism (below) is sound but each ledger entry is
  ~10 minutes of authoring.

**Proposed split** (`/qa` recommendation; user/`/sprint` decide at
Phase 4 wave gate):

- **Sprint 64**: Phase 1 (harness build + helpers.md trim +
  cache-isolation seed test) + Phase 2 Batches 1, 5, 7, 9, 10.
  Targets the smaller, more independent batches + the heavy REPL
  surface + pure-quarantine cleanup + the build_confidence.rs gate.
  Phase 3 (legacy-helper deletion) does NOT close in S64 because
  Batches 2, 3, 4, 6, 8 are still on `ReplSession`.
- **Sprint 65**: Phase 2 Batches 2, 3, 4, 6, 8 + Phase 3 (delete
  `tests/helpers/mod.rs::ReplSession` and integration-tier helpers).
  Crate-refactor sprints (FIXME 0109) follow S65, not S64.

Alternative: **single-sprint compression** — accept that S64 is a
3–4 week sprint by calendar time rather than the usual cadence. The
user's framing ("the sprint is now bigger; that's accepted") reads
as openness to this; the recommendation above is `/qa`'s judgment
that the work decomposes cleanly at the natural midpoint of "REPL +
small surfaces" vs. "broad conformance + IO + runtime quarantine".

Either way, the test-port sprint precedes any crate-refactor sprint
that touches `session_v4`/`worker` (FIXME 0115 lock-in is preserved).

### Ledger lockstep mechanism

Per Sprint 64 §Phase 2 (parity rule + failing-not-ignored), every batch
that lands new failing tests MUST update `tests/plan/ledger.md` in the
same commit. The mechanism:

1. **Same-commit invariant.** Every PR landing one or more failing
   tests includes a diff to `tests/plan/ledger.md` in the same commit.
   Each newly-failing test is either added to the ledger as a new
   entry (with all six required fields per `ledger.md §Discipline`)
   or extends an existing entry's signature/SHA. Sprint 64 close
   verification grep: for each test marked `// FIXME(/skill)` in the
   batch's ported files, there exists a row in `ledger.md` whose test
   name matches.

2. **Commit-message citation.** Every Phase 2 commit message MUST
   include a `Ledger:` trailer naming the entries it touched, or
   `Ledger: no change` if all ports passed. Examples:

   ```
   port — Batch 5 RC + exemplar (commit 1/3)

   Ledger: extends sprint59_defects456_repro::d6_exemplar_propagate_only_does_not_segv
           (SHA refresh; signature unchanged)
   ```

   ```
   port — Batch 1 Ring 1 (commit 2/4)

   Ledger: no change
   ```

   The trailer is grep-able and forms the audit trail across the sprint.

3. **Inline FIXME ↔ ledger row pairing (grep invariant).** The
   discipline `memory/feedback_failing_not_ignored.md` requires
   un-ignored failing tests; the ledger is the inventory of those
   failures. For every `// FIXME(/skill)` annotation on a failing
   test (the spec-side traceability), there MUST be a corresponding
   ledger row naming the same skill as owner. Phase 4 may add a CI
   lint that greps both files and asserts the bijection; Phase 3
   specifies the discipline.

This mechanism is the closure for `/arch` Finding 4 (Phase 2 cliff
discipline). Phase 4's wave-gate check is a manual scan: for each
batch, `/sprint` confirms commit messages carry the `Ledger:` trailer
and that the `// FIXME(/skill)` ↔ ledger-row pairing holds for the
batch's diff.

### Open questions for Phase 4 wave organisation

1. **Single sprint vs. two-sprint split** (see §"Sprint sizing
   assessment" above). `/qa` recommends two-sprint split (S64 +
   S65); the user's earlier framing accepts the bigger scope but
   does not yet commit to either model. Phase 4 wave-gate is the
   decision point.

2. **Pure-quarantine Batch 9 sequencing.** The four files
   (`scheduler.rs`, `wave2_g6.rs`, `wave3_g8.rs`, `wave4_g9.rs`)
   move mechanically — they have zero carry-forward. Phase 4 decides
   whether Batch 9 lands at the front (so the FIXMEs are in queue
   ASAP for S65+ harvest planning) or at the end (so the e2e
   reorganisation is visible in PR history first).

3. **`rc.rs` trace-channel coverage shift.** Moving alloc/free-balance
   assertions from e2e into `cranelisp-runtime` unit tests is a
   real coverage shift, not a pure relocation — the unit tier
   cannot observe what a full subprocess invocation does (e.g.,
   no leak across `--run` + REPL boundary). The 30%/65%/5% split
   on `rc.rs` is `/qa`'s estimate; Phase 4 decides whether to
   coordinate a wider audit with `/runtime` `/dev` before
   committing the split, or accept the estimate and harvest in S65.

4. **Cache-isolation seed test** — placed in the new `cache.rs`
   (Batch 1) per Phase 1 §2. Confirmed; no longer open.

5. **Inline `// FIXME(/skill)` ↔ ledger row pairing** under the
   wave-gate manual scan: with ~80–110 expected failing tests
   across batches, the manual grep may not scale. Phase 4 decides
   whether the bijection check becomes a CI lint immediately
   (preferred) or a manual scan during S64/65 with a CI lint
   committed as a sprint-close FIXME against `/qa` itself.

6. **`spec_06_pattern_matching.rs` sourcing.** Pattern matching
   coverage is currently spread across `ring2.rs` + `e2e.rs` +
   `sketch_port.rs`. The audit's dedupe judgment is the load-bearing
   step. Phase 4 decides whether this file gets a dedicated audit
   sub-batch or piggybacks on Batch 2's sweep.

## What this plan deliberately does NOT do

- **Does not enumerate every spec section today.** That work is the
  active backlog; rows accrete sprint-by-sprint as `/qa` covers
  spec sections in scope. The plan's normative status is structural,
  not present-tense complete: it is the place rows go, not a claim
  that every row is already there.
- **Does not list per-crate unit tests.** Those are owned by `/dev`
  in each crate; `/qa` reviews coverage at sprint close via
  `coverage-gaps.md`, not by enumerating tests in this plan.
- **Does not replace the spec.** Rows cite the spec; the spec is
  normative on what the language does. This plan is normative on
  what `/qa` tests.

## Sprint 66 Phase 5 Wave 1 — failing-not-ignored bedrock (2026-05-09)

Per `tests/plan/implementation-slice-s66.md §5` inventory, `/qa` authored
35 failing-not-ignored e2e tests at Phase-5 Stage-1 open. The rows below
trace each test to its FIXME + spec section + resolving /dev workstream.
Status `[S66 W3]` until /dev wave lands the consumer-side API; flips to
`[Tested ...]` at FIXME closure.

### FIXME 0098 — process_form gap-orchestration (critical-path triad)

| Test | Spec | Status | Resolves at |
|---|---|---|---|
| `tests/process_form_dispatch.rs::process_form_dispatch_macro_after_import_succeeds_in_one_eval` | spec/08-modules.md §"REPL form sequencing"; spec/09-macros.md §"Macro resolution" | `[S66 W3a]` | frontend Phase 2 + int Phase 4 of FIXME 0098 |
| `tests/process_form_dispatch.rs::process_form_dispatch_begin_cluster_resolves_mutual_forward_ref` (positive — `(begin ...)` cluster atomicity per Decision 44 + /spec FIXME 0165 resolution + /arch FIXME 0166 resolution; renamed from `process_form_dispatch_typecheck_gap_completes_in_one_eval` 2026-05-10) | spec/05-definitions.md §5.13.2; design/arch/decisions/0044-cluster-atomic-typecheck-orchestrator-staging.md | `[S66 W3a]` | typecheck Phase 3 (`check_form_signatures` + `check_form_body` split per Decision 44) + int Phase 4 (`process_cluster` shape) of FIXME 0098 |
| `tests/process_form_dispatch.rs::process_form_dispatch_bare_forward_ref_errors_clearly` (negative — bare cross-input forward ref must surface clear typed error; staging drops, nothing commits) | spec/05-definitions.md §5.13.2 (non-clustered cross-input forward refs are an error) | `[S66 W3a]` | int Phase 4 of FIXME 0098 (typed Gap → user-visible diagnostic; cluster-atomic staging drop per Decision 44) |
| `tests/process_form_dispatch.rs::process_form_dispatch_function_gap_does_not_speculatively_jit` | spec/12-runtime.md §"Diagnostic logging" (CRANELISP_GOT_TRACE reservation) | `[S66 W3a]` | int Phase 4 of FIXME 0098 + backend Phase 1 of FIXME 0099 |

### FIXME 0099 — GotObserver

| Test | Spec | Status | Resolves at |
|---|---|---|---|
| `tests/got_trace.rs::got_trace_emits_jit_write_event` | spec/12-runtime.md §"Diagnostic logging" | `[S66 W3b]` | backend Phase 1 + int Phase 2 of FIXME 0099 |
| `tests/got_trace.rs::got_trace_emits_linker_write_event_on_cache_hit` | spec/12-runtime.md §"Diagnostic logging" | `[S66 W3b]` | backend Phase 1 + int Phase 2 of FIXME 0099 |
| `tests/got_trace.rs::got_trace_emits_redefinition_event_on_repl_redefn` | spec/12-runtime.md §"Diagnostic logging" | `[S66 W3b]` | backend Phase 1 + int Phase 2 of FIXME 0099 |
| `tests/got_trace.rs::got_trace_off_path_zero_overhead_neg` (negative) | spec/12-runtime.md §"Diagnostic logging" | `[S66 W3b]` | backend Phase 1 of FIXME 0099 |

### FIXME 0100 — single-consumer relocations

| Test | Spec | Status | Resolves at |
|---|---|---|---|
| `tests/public_api_relocations.rs::public_api_check_runs_against_all_eight_crates` | structural — `tests/CLAUDE.md §"Public-API enforcement"` | `[S66 W2-W4]` | All 8 per-crate baselines committed; FIXME 0100 Phase 1+2 relocations land |

### FIXME 0103 — IoObserver in intrinsics; trace.rs/io_trace.rs in int

| Test | Spec | Status | Resolves at |
|---|---|---|---|
| `tests/spec_10_io.rs::io_trace_snapshot_pre_post_relocation_byte_equivalent` | spec/10-io.md §"IO observation contract" + spec/12-runtime.md §"Diagnostic logging" | `[S66 W3b]` | intrinsics Phase 2 + int Phase 2 of FIXME 0103 |
| `tests/spec_10_io.rs::io_observer_registration_lives_in_intrinsics` | structural — facade-mediated | `[S66 W2-W3b]` | FIXME 0103 Phase 1 (intrinsics) + FIXME 0150 Phase 5 (runtime retire) |

### FIXME 0104 — PlatformError adoption

| Test | Spec | Status | Resolves at |
|---|---|---|---|
| `tests/platform_errors.rs::platform_load_failed_carries_form_span` | spec/11-platform.md §"Platform error reporting" | `[S66 W3a]` | types Wave 0 + platform Phase 2 + int Phase 3 of FIXME 0104 |
| `tests/platform_errors.rs::platform_manifest_not_found_carries_dll_path` | spec/11-platform.md §"Platform error reporting" | `[S66 W3a]` | types Wave 0 + platform Phase 2 of FIXME 0104 |
| `tests/platform_errors.rs::platform_abi_version_mismatch_emits_expected_vs_found` | spec/11-platform.md §"Platform error reporting" | `[S66 W3a]` | types Wave 0 + platform Phase 2 of FIXME 0104 + manifest-loader audit |
| `tests/platform_errors.rs::platform_dispatch_error_during_run_carries_fn_name` | spec/11-platform.md §"Platform error reporting" | `[S66 W3a]` | types Wave 0 + platform Phase 2 + int Phase 3 of FIXME 0104 |

### FIXME 0107 — `OwnedPlatformFnDescriptor` `#[non_exhaustive]`

Tracked at /dev-unit tier (compile_fail doc-test inside `cranelisp-platform`); no e2e row required per `tests/plan/implementation-slice-s66.md §5.6`.

### FIXME 0108 — display.rs backend → int

| Test | Spec | Status | Resolves at |
|---|---|---|---|
| `tests/repl_introspection.rs::display_format_eval_result_after_relocation_unchanged` | repl/spec.md §1.1 | `[S66 W3b]` | int FIXME 0108 |
| `tests/repl_introspection.rs::public_api_check_backend_display_absent_neg` (negative) | structural — facade-mediated | `[S66 W3b]` | int FIXME 0108 + backend baseline regenerated |

### FIXME 0150 — D43 runtime split (highest-risk reshape)

| Test | Spec | Status | Resolves at |
|---|---|---|---|
| `tests/stdlib_trait_impls.rs::stdlib_num_int_inline_path` | spec/appendix-a-builtins.md §"Num.Int" | `[S66 W3-W4]` | FIXME 0150 Phase 3 + 4 |
| `tests/stdlib_trait_impls.rs::stdlib_num_int_mappable_path` | spec/07-traits.md §"Operators as first-class values" | `[S66 W3-W4]` | FIXME 0150 Phase 3 + 4 |
| `tests/stdlib_trait_impls.rs::stdlib_num_float_inline_path` | spec/appendix-a-builtins.md §"Num.Float" | `[S66 W3-W4]` | FIXME 0150 Phase 3 + 4 |
| `tests/stdlib_trait_impls.rs::stdlib_num_float_mappable_path` | spec/07-traits.md §"Operators as first-class values" | `[S66 W3-W4]` | FIXME 0150 Phase 3 + 4 |
| `tests/stdlib_trait_impls.rs::stdlib_eq_int_inline_path` | spec/appendix-a-builtins.md §"Eq.Int" | `[S66 W3-W4]` | FIXME 0150 Phase 3 + 4 |
| `tests/stdlib_trait_impls.rs::stdlib_eq_int_mappable_path` | spec/07-traits.md §"Operators as first-class values" | `[S66 W3-W4]` | FIXME 0150 Phase 3 + 4 |
| `tests/stdlib_trait_impls.rs::stdlib_eq_float_inline_path` | spec/appendix-a-builtins.md §"Eq.Float" | `[S66 W3-W4]` | FIXME 0150 Phase 3 + 4 |
| `tests/stdlib_trait_impls.rs::stdlib_eq_float_mappable_path` | spec/07-traits.md §"Operators as first-class values" | `[S66 W3-W4]` | FIXME 0150 Phase 3 + 4 |
| `tests/stdlib_trait_impls.rs::stdlib_eq_bool_inline_path` | spec/appendix-a-builtins.md §"Eq.Bool" | `[S66 W3-W4]` | FIXME 0150 Phase 3 + 4 |
| `tests/stdlib_trait_impls.rs::stdlib_eq_bool_mappable_path` | spec/07-traits.md §"Operators as first-class values" | `[S66 W3-W4]` | FIXME 0150 Phase 3 + 4 |
| `tests/stdlib_trait_impls.rs::stdlib_eq_string_inline_path` | spec/appendix-a-builtins.md §"Eq.String" | `[S66 W3-W4]` | FIXME 0150 Phase 3 + 4 |
| `tests/stdlib_trait_impls.rs::stdlib_eq_string_mappable_path` | spec/07-traits.md §"Operators as first-class values" | `[S66 W3-W4]` | FIXME 0150 Phase 3 + 4 |
| `tests/stdlib_trait_impls.rs::stdlib_ord_int_inline_path` | spec/appendix-a-builtins.md §"Ord.Int" | `[S66 W3-W4]` | FIXME 0150 Phase 3 + 4 |
| `tests/stdlib_trait_impls.rs::stdlib_ord_int_mappable_path` | spec/07-traits.md §"Operators as first-class values" | `[S66 W3-W4]` | FIXME 0150 Phase 3 + 4 |
| `tests/stdlib_trait_impls.rs::stdlib_ord_float_inline_path` | spec/appendix-a-builtins.md §"Ord.Float" | `[S66 W3-W4]` | FIXME 0150 Phase 3 + 4 |
| `tests/stdlib_trait_impls.rs::stdlib_ord_float_mappable_path` | spec/07-traits.md §"Operators as first-class values" | `[S66 W3-W4]` | FIXME 0150 Phase 3 + 4 |
| `tests/stdlib_trait_impls.rs::stdlib_display_int_inline_path` | spec/appendix-a-builtins.md §"Display.Int" | `[S66 W3-W4]` | FIXME 0150 Phase 3 + 4 |
| `tests/stdlib_trait_impls.rs::stdlib_display_float_inline_path` | spec/appendix-a-builtins.md §"Display.Float" | `[S66 W3-W4]` | FIXME 0150 Phase 3 + 4 |
| `tests/stdlib_trait_impls.rs::stdlib_not_inline_path` | spec/appendix-a-builtins.md §"not" | `[S66 W3-W4]` | FIXME 0150 Phase 4 + primitives-side seeding |
| `tests/stdlib_trait_impls.rs::stdlib_not_mappable_path` | spec/appendix-a-builtins.md §"not" + spec/07-traits.md §"Operators as first-class values" | `[S66 W3-W4]` | FIXME 0150 Phase 4 + primitives-side seeding |
| `tests/stdlib_trait_impls.rs::stdlib_link_mode_against_intrinsics_archive` | structural — Phase 5 retirement | `[S66 W4]` | FIXME 0150 Phase 5 |
| `tests/stdlib_trait_impls.rs::cranelisp_runtime_crate_absent_post_phase_5_neg` (negative) | structural — Phase 5 retirement | `[S66 W4]` | FIXME 0150 Phase 5 |

## Sprint 68 Phase 5 Stage 1 — primitives-as-uniform-module failing tests (2026-05-17)

Per `sprints/SPRINT.md` Phase 4 Wave 1, `/qa` authored 16 failing-not-ignored
tests at S68 Phase 5 Stage 1 open. The rows below trace each test to its
spec / Decision anchor and resolving wave.

Decision anchors:
- 0048 — primitives' SymbolTable + GotTable statically constructed in
  the primitives crate; backend dep-ban (S68 Phase 3 amendment).
- 0047 — FQTypeName at resolved-stage cross-crate boundaries.
- 0040 — `(trace ...)` `--link`-mode link-time rejection (Path B1).

### S68 — primitives uniform module + facade lockdown + FQTypeName completion

| # | Test | Spec / Decision | Status | Resolves at |
|---|---|---|---|---|
| 1 | `tests/spec_appendix_a_builtins.rs::primitive_not_true` | spec/appendix-a-builtins.md §A.3 (not) + Decision 0048 §"The invariant" | `[Tested]` | pre-existing; passes today; remains green post-S68 via PRIMITIVES_TABLE GOT path |
| 2 | `tests/spec_appendix_a_builtins.rs::primitive_not_false` | spec/appendix-a-builtins.md §A.3 (not) + Decision 0048 §"The invariant" | `[Tested]` | pre-existing; passes today |
| 3 | `tests/s68_primitives_uniform.rs::s68_not_primitive_works_in_link_mode_sentinel` | spec/appendix-a-builtins.md §A.3 + Decision 0048 §"The invariant" | `[Tested]` (sentinel) | GREEN today via force-link; GREEN post-Wave-4 via cranelisp_init_primitives() |
| 4 | `crates/cranelisp-backend/tests/no_primitives_dep.rs::s68_backend_does_not_depend_on_primitives` | Decision 0048 §"Structural invariant — backend dep-ban"; Principle 18 | `[S68 W4]` | Wave 4 — atomic edit pair: delete backend's dep on primitives |
| 5 | `tests/s68_primitives_uniform.rs::s68_primitives_table_is_arc_symboltable_code_unit` | Decision 0048 §"Shape" | `[S68 W3]` | Wave 3 — primitives slice lands the typed shape |
| 6 | `tests/s68_primitives_uniform.rs::s68_facade_compliance_test_exists_for_s68_touched_crates` | design/arch/CLAUDE.md §"Baseline-diff discipline"; (deleted) FIXME 0218 | `[Tested]` (meta-sentinel) | **S75 W5c FLIPPED**: backend.md + backend-cache.md retired (S75 W5b) — the LAST two binding facades. All EIGHT facades now retired; `facade_pairs()` is an empty `vec![]` tombstone. Sentinel flips from present+absent guard to ALL-ABSENT guard (mirrors the S74 primitives/intrinsics flip): backend POSITIVE assertion REMOVED; absent-set extended to `["cranelisp-primitives", "cranelisp-intrinsics", "cranelisp-backend"]` — all three asserted absent from `facade_pairs()`. `split_once("fn facade_pairs()")` anchor preserved (empty tombstone retained). _Prior: S74 W4 narrowed to backend-only present + primitives/intrinsics absent._ BLOCKED-by-red-binary (links root `cranelisp`); validated by inspection + `std::fs` dry-run. |
| 6b | ~~`tests/facade_compliance.rs::rustdoc_coverage_for_retired_crates`~~ | (deleted) FIXME 0218 | **REMOVED** (S74 W4) | Over-built and deleted. A retired-facade crate's surface is DEFINED by its source (`public-api.txt` + the compiler are the guard); asserting "the crate documents itself" restates the code — not a contract check. Rustdoc carries rationale, not the surface. Retired crates have nothing for a facade-compliance test to check, so they are absent from the file rather than checked by a self-documentation assertion. |
| 7 | `tests/s68_primitives_uniform.rs::s68_ring0_jit_symbols_free_fn_is_retired` | FIXME 0182 + Decision 0048 §Consequences | `[S68 W3]` | Wave 3 — primitives slice deletes the free fn and its re-export |
| 8 | `tests/s68_primitives_uniform.rs::s68_exe_bundle_publishes_cranelisp_init_primitives_hook` | Decision 0048 §Cascade; SPRINT.md Phase 2 outcomes (/arch recommendation) | `[S68 W3]` | Wave 3 — int slice authors the hook in exe-bundle, called from cranelisp_init_platform |
| 9 | `tests/s68_primitives_uniform.rs::s68_backend_intrinsic_symbols_drops_primitives_paths` | FIXME 0191 + Decision 0048 §dep-ban | `[S68 W4]` | Wave 4 — backend slice deletes all `cranelisp_primitives::*` Rust-path refs (atomic with #4) |
| 10 | `tests/s68_primitives_uniform.rs::s68_code_enum_has_primitive_marker_variant` | Decision 0048 §"Shape" (S68 Phase 3 amendment) | `[S68 W2]` | Wave 2 — backend additive prep authors `Code::Primitive` |
| 11 | `tests/s68_primitives_uniform.rs::s68_primitives_entries_carry_code_primitive_marker` | Decision 0048 §"Shape" | `[S68 W3]` | Wave 3 — primitives slice constructs entries with `code = Some(Code::Primitive)` |
| 12 | ~~`tests/s68_primitives_uniform.rs::s68_fqtypename_int_exe_io_adt_boundary`~~ | Decision 0047 | REMOVED 2026-05-17 | Non-applicable target — `src/` is a binary (no `public-api.txt`); the flagged `TypeName::from("IO")` is a constructor argument inside `FQTypeName::new(...)`, exactly the lift-site pattern Decision 0047 permits. Test confused argument for free-standing violation. |
| 13 | ~~`tests/s68_primitives_uniform.rs::s68_fqtypename_int_pipeline_io_adt_boundary`~~ | Decision 0047 | REMOVED 2026-05-17 | Same as #12 — `src/pipeline.rs` site is a constructor argument inside `FQTypeName::new(...)`. |
| 14 | ~~`tests/s68_primitives_uniform.rs::s68_fqtypename_int_platform_io_adt_boundary`~~ | Decision 0047 | REMOVED 2026-05-17 | Same as #12 — `src/platform.rs` site is a constructor argument inside `FQTypeName::new(...)`. |
| 15 | `tests/s68_primitives_uniform.rs::s68_fqtypename_backend_uses_fqtypename_at_resolved_edges` | Decision 0047 + facades/types.md §"FQTypeName" | `[Tested]` | Shape A — scans `crates/cranelisp-backend/public-api.txt` for any `pub fn` signature using bare `TypeName` (FQTypeName masked first). Asserts zero occurrences. |
| 16 | `tests/s68_primitives_uniform.rs::s68_trace_in_link_mode_rejected_at_link_time` | spec/04-expressions.md §4.12.9 (post-S68 rework, FIXME 0209) + Decision 0040 Path B1 | `[S68 W3-W4]` | Wave 3/4 — trace runtime fully retired from staticlib; link-time failure becomes the architectural enforcement |
