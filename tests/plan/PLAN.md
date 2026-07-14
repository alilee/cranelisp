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
   defects. Each row cites the originating defect (sprint, FIXME, and
   the test's `// defect:` tag per `tests/CLAUDE.md` §"Defect-repro
   notation"). These exist forever per
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
- **Phase 6/7 (Assess/Close).** `/qa` updates row statuses to reflect
  what shipped, what didn't, and what was ignored with reason. The
  Phase 7 outcome cites plan-vs-tests integrity and RED-vs-known-defect
  integrity (every RED traces to an open defect naming its owner —
  root `CLAUDE.md` §Testing).

## Subordinate documents

- **`ledger.md`** — RETIRED S108 (tombstone only; history in git).
  Regression triage runs on the inline defect-comment/FIXME convention
  (root `CLAUDE.md` §Testing); defect frequency/locus/recurrence
  analysis runs on the `// defect:` notation (`tests/CLAUDE.md`
  §"Defect-repro notation"). The forbidden-disposition discipline
  (`flaky`, `pre-existing`, `documented race`, `timing-sensitive`)
  lives on in `tests/CLAUDE.md` §"Failing-test discipline".
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
| `lenient.rs` | 289 | 32 | 30 | 70 | 0 | 0 | `spec_04_expressions.rs` (S64 W5 ✓), `legacy/lenient.rs` (S64 W5 ✓ FIXME 0135) | /backend (with /runtime co-owner — sparkability analysis) | S64 Wave 5 Batch 2 landed: language-observable lenient-eval semantics (independent bindings produce correct sums; dependent bindings sequential) carried forward to `tests/spec_04_expressions.rs::lenient_*`. Sparkability heuristics + `CRANELISP_NO_LENIENT=1` opt-out + Par-node IR observations preserved in legacy for /backend harvest under FIXME 0135. **S85 Phase 6b** added the wall-clock *parallelism witness* (not just correctness): `spec_12_runtime.rs::lenient_vec_map_reduce_parallelizes` (positive — a free-standing index-range divide-and-conquer Vec map-reduce over `fib(35)`×8 runs >=1.43x faster lenient-ON vs `CRANELISP_NO_LENIENT=1`, same result) + `lenient_vec_map_reduce_prior_binding_stays_serial` (negative control — `mid` bound first in the SAME `let` block, referenced by both halves, so neither half is sparkable → ON≈OFF). Both `[Tested+Neg spec_12_runtime.rs]`, `// spec: §12.4.3`. Mirrors the `spec_10_io.rs` `prog_run_elapsed_ms` timing idiom (subprocess + `out.elapsed`, conservative one-sided margin). NOTE: the negative control's earlier binding MUST be in the SAME block as the two halves; placing `mid` in a separate *outer* `let` still parallelises (the sparkability rule keys on same-block predecessors only). |
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

## Sprint 76 Phase 5 Stage 1 — int alignment + the full e2e suite (2026-06-03)

S76 is the **final crate of the facade-retirement arc**: wash the cumulative
streamlined-crate changes through `int` (`src/`), collapse int's parallel JIT
pipeline into the single `compile_to_module` entry, and **enable the full
active e2e suite passing across run / REPL / `--link` / platform** (not merely
a compile-green workspace). Per `qa.md §Phase 5` this is QA-first: the failing
tests below scope what the per-crate D/D/R triads make pass.

The sprint's e2e completeness target is the **active suite (≈34 files), all
modes, plus the re-enabled s68 sentinels** — NOT the 42 quarantined
`tests/legacy/` files (legacy harvest is deferred to S77 per the SPRINT.md
scope decision).

### Spec anchors (the `[R4 S76 — tested-by /qa S76]` tags /spec placed)

- `spec/09-macros.md` §9.3.4 (Macro Availability and Definition Order),
  §9.3.6 (Qualified Macro References), §9.12 (three-pass Bootstrapping Order),
  §9.2.5 (Macro Body Capabilities), §9.14 #2 (define-before-use limitation).
- `spec/05-definitions.md` §5.13.2 (REPL ≡ batch cluster unification).
- `spec/08-modules.md` §8.5.4 (lazy-load for FQ macro references).
- LOCKED model: `design/arch/macro-availability-model.md §0`.

### W-Macro — the LOCKED macro-availability model (NEW; the headline)

`design/arch/macro-availability-model.md §0` is normative. The model: a macro's
**expansion** references only (a) **dependency-module** definitions
(typechecked-before, fetched just-in-time) and (b) **macros** (same-module
macros included); a **same-module non-macro definition is NOT available at
expansion** (round-trip safety, §0.3); **defmacro-before-use is normative**
(§0.2). The three-pass compile (§0.4) structurally enforces it (Pass-1 expand
precedes Pass-2/3 non-macro registration). NEW test file
`tests/s76_macro_availability.rs`.

| # | Test | Spec | New/Reg | Status | Resolves at |
|---|---|---|---|---|---|
| M1 | `tests/s76_macro_availability.rs::macro_used_before_defmacro_is_unresolved_neg` | §9.3.4 | NEW (neg) | `[S76 W-Macro]` | three-pass impl (typecheck recognition + int Pass-1) — INVERTS retired `spec_09_macros.rs::macro_used_before_defmacro_form_is_hoisted` |
| M2 | `tests/s76_macro_availability.rs::macro_defined_before_use_expands` | §9.3.4 | NEW (pos) | `[S76 W-Macro]` | three-pass impl — the always-reliable subset |
| M3 | `tests/s76_macro_availability.rs::macro_clause_calls_same_module_defn_helper_rejected_neg` | §9.3.4, §9.12, §0.8 | NEW (neg) | `[S76 W-Macro]` | three-pass impl — the `stdlib/defs.cl` real-world instance; a REJECTED PROGRAM with a clear diagnostic, NOT a defect. INVERTS retired `spec_09_macros.rs::macro_body_drives_three_level_call_graph` |
| M4 | `tests/s76_macro_availability.rs::macro_clause_reads_same_module_def_value_rejected_neg` | §9.3.4 | NEW (neg) | `[S76 W-Macro]` | three-pass impl — `def`/`const` value-read variant of M3 |
| M5 | `tests/s76_macro_availability.rs::macro_clause_calls_imported_helper_at_expansion_works` | §9.2.5 | NEW (pos) | `[Tested tests/s76_macro_availability.rs::macro_clause_calls_imported_helper_at_expansion_works]` | capability GREEN. S76 W3 (/qa, FIXME 0267): fixture retyped to the §9.2.2/§9.2.3 `Sexp -> Sexp` shape (`(defn bump [s] (SexpInt 42))`); just-in-time dependency compile + scheduler dep-order supply the typechecked-before guarantee. Was red on an ill-typed `Int -> Int` fixture, not the capability. |
| M5b | `tests/s76_macro_availability.rs::macro_clause_calls_imported_helper_ill_typed_rejected_neg` | §9.2.2, §9.2.3 | NEW (neg) | `[Tested tests/s76_macro_availability.rs::macro_clause_calls_imported_helper_ill_typed_rejected_neg]` | S76 W3 (/qa, FIXME 0267 _neg sibling): an `Int -> Int` helper called unquoted in a macro body is REJECTED with the §9.2.3 Sexp-expected type error. Upgrades M5 coverage to `+Neg`. |
| M6 | `tests/s76_macro_availability.rs::fq_macro_reference_expands_without_import` | §9.3.6, §8.5.4 | NEW (pos) | `[S76 W-Macro]` | Pass-1 FQ-macro lazy-load (FIXME 0007 folded in) |
| M7 | `tests/s76_macro_availability.rs::macro_generates_toplevel_defn` | §9.12 | NEW (pos) | `[S76 W-Macro]` | structural-form re-entry (typecheck re-classifies into same staging frame) |
| M8 | `tests/s76_macro_availability.rs::macro_generates_defmacro_available_to_later_use` | §9.12 | NEW (pos) | `[S76 W-Macro]` | recursive Pass-1 expand-to-fixpoint (macro-generated defmacro) |
| M9 | `tests/s76_macro_availability.rs::repl_begin_cluster_forward_macro_use_is_unresolved_neg` | §5.13.2 | NEW (neg) | `[S76 W-Macro]` | REPL ≡ batch — forward macro in begin-cluster fails identically |
| M10 | `tests/s76_macro_availability.rs::repl_macro_uses_earlier_macro_works` | §5.13.2, §0.1(b) | NEW (pos) | `[S76 W-Macro]` | macros may reference same-module macros (compile-time layer) |

**Existing-test inversions (CRITICAL — these now CONTRADICT the locked spec).**
Three tests in `tests/spec_09_macros.rs` encode the *retired* module-wide /
hoisting model. The `/dev` triad MUST resolve the discrepancy (not by reverting
the spec) — they are flagged here as the durable record:

| Existing test | Was | Now (locked) | Disposition |
|---|---|---|---|
| `spec_09_macros.rs::macro_used_before_defmacro_form_is_hoisted` (line 483) | asserts forward macro use SUCCEEDS (hoisted) | §9.3.4: forward use is a plain unresolved reference → MUST fail | INVERT — superseded by M1; `/spec`/`/qa` strike or rewrite the assertion + its `// spec:` comment ("v4 processes all defmacros before other forms" is now false) |
| `spec_09_macros.rs::macro_body_drives_three_level_call_graph` (line 498) | macro clause calls same-module `defn b`→`a` at expansion → asserts 21 | §9.3.4: same-module non-macro at expansion → REJECTED | INVERT — superseded by M3; rewrite to assert rejection OR move `a`/`b` into a dependency module (then it stays positive) |
| `spec_09_macros.rs::batch_macro_uses_earlier_macro` (line 260) | macro `inc2` calls earlier macro `inc` | §0.1(b): macros may reference same-module macros — STILL VALID | NO CHANGE — stays green; mirrored by M10 |

The cross-module macro tests (`spec_09_macros.rs::cross_module_macro_*`, lines
528–684) all reference helpers in **dependency modules** — they are the canonical
"expansion references a dependency" pattern and STAY GREEN under the lock (M5 is
the s76-locked-model companion asserting this). `cross_module_macro_emits_qualified_reference`
(line 577) overlaps M6's FQ-ref capability on the cross-module half.

### W-Enablement — constructor-as-value + single-JIT-setup (cross-crate, green-at-runtime)

| # | Test | Spec / FIXME | New/Reg | Status | Resolves at |
|---|---|---|---|---|---|
| E1 | `tests/spec_06_pattern_matching.rs` / `tests/spec_03_types.rs` — `(map Some xs)` constructor-as-value end-to-end | FIXME 0249; roadmap `(map Some xs)` item | NEW (pos) | `[S76 W-Enable]` | 0249-a typecheck got-slots ctor entries + 0249-b int enumerates synthesised ctor `Def`s into the compile batch |
| E2 | regression — primitives dispatch unbroken after `Jit::new(symbol_tables)` collapse (`spec_appendix_a_builtins.rs::primitive_*` stay green) | Decision 0048; BC §3 | REG | `[S76 W-Enable]` | single-JIT-setup must not regress primitive lookup |
| E3 | regression — intrinsics dispatch unbroken after `INTRINSICS_TABLE` publish (IO/print, RC ops via `spec_10_io.rs`, `spec_12_runtime.rs` stay green) | BC §4b inv 11 | REG | `[S76 W-Enable]` | `INTRINSICS_TABLE` flat catalog must not regress intrinsic Import-dispatch |

**Author note (E1):** `(map Some xs)` is free-standing language behaviour — author
it under the relevant spec file (pattern-matching / types) with
`PreludeVariant::TestStandard` for `map`/`Option`. The constructor-as-value
assertion is "a bare constructor name used as a first-class function value
compiles and runs"; keep it minimal so the CLIF is inspectable by eye if it fails.

### W-Integrate — full-suite mode coverage (run / REPL / `--link` / platform)

| # | Surface | Gated files | FIXME | Status | Resolves at |
|---|---|---|---|---|---|
| I1 | `--link` GOT-alignment | `tests/link.rs` (incl. the 0122 case) | 0122 | `[S76 W-Integrate]` | re-test once workspace builds; backend fixes in-sprint — failing-not-ignored repro is the durable record either way |
| I2 | Platform host-wiring round-trip | `tests/spec_platforms.rs`, `tests/platform_errors.rs`, `tests/spec_08_modules.rs` platform paths | 0229–0235 | `[S76 W3 — BLOCKED, no test authored]` | 0235 round-trip STILL blocked (NOT just on 0282): `/qa` probe (S76 W3) confirmed a CLAdt-typed platform fn sig `(Fn [Rectangle] Int)` fails at load with `unknown type 'Rectangle'` — `register_platform_in_tc` does not register schema-declared ADT type defs (open half of 0231/0233). `alloc_with_tag` (construction) landed but is necessary-not-sufficient. Item 4 (mismatch) additionally blocked on 0282. See 0235 progress note. |
| I3 | Conformance triad | `tests/facade_pif_rows.rs` + `crates/cranelisp-platform/tests/macro_full_arm_compile.rs` | 0224–0228 | `[Tested S76 W3]` ✓ | LANDED. 0224 `platform_clheap_inc_dec_rc_take_ref_self`, 0225 `platform_non_exhaustive_present_on_owned_descriptor_only`, 0227 `platform_repr_c_field_order_frozen`, 0228 `platform_send_sync_claims_match_invariants` (all in `facade_pif_rows.rs`, mechanical checks over `cranelisp-platform/public-api.txt`); 0226 `macro_full_arm_compile.rs::full_arm_invocation_compiles_and_emits_marker_types` (all-arms `declare_platform!` compile witness). FIXMEs 0224–0228 deleted. |
| I4 | Mode-equivalence | all language-behaviour suites via `run_through_all_modes` | — | REG | `[S76 W-Integrate]` | REPL ≡ `--run` ≡ `--link` for every language semantics test (Principle 11 guard, see W-Absorb below) |

**0235 round-trip DLL integration (`/qa` deliverable) — BLOCKED (S76 W3).** The
platform wave's witness is a round-trip: a Cranelisp program declares `(platform
<name>)`, the host `dlopen`s the DLL, a Cranelisp call marshals args host→DLL, the
DLL returns, the result marshals DLL→host. `/qa` attempted the unblocked half in
S76 W3 and found the **whole** round-trip still blocked. A throwaway `test-adt`
cdylib (built against workspace `cranelisp-platform`, `schema:` +
`schema_types: [Rectangle]`, `rectangle_area` reading `w`/`h`) loaded via
`CRANELISP_PLATFORM_PATH` + `--run` fails at platform-sig typecheck:
`type error in platform function 'rectangle-area' signature '(Fn [Rectangle]
Int)': unknown type 'Rectangle'`. Root cause: `src/platform.rs::register_platform_in_tc`
registers only function descriptors + a primitives glob into `platform.<name>`;
it does NOT consume the DLL `GetSchema`/`DLL_SCHEMA` to register the schema's ADT
type defs (the open half of FIXME 0231/0233 step 2; the rustdoc at
`src/platform.rs:355–357` names it a future seam). So a CLAdt-typed platform fn
cannot typecheck → no round-trip is expressible from cranelisp source. `alloc_with_tag`
(host construction) landed (0229 step 1) but is necessary-not-sufficient. Item 4
(schema-typo → `validate_schema` rejection) is additionally blocked on the
S-PLAT-1 schema-text-exposure seam (FIXME 0282, `/arch` ruling pending). NO test
authored — a `tests/spec_platforms_adt.rs` round-trip would fail upstream at sig
typecheck (not the round-trip under test), and the `platforms/test-adt/` DLL is
`/platform`'s artefact. 0235 kept open with a precise progress note. Will land in
`tests/spec_platforms.rs` (extend) using `Cranelisp::use_workspace_platforms()`
once the schema-type-registration seam lands.

### W-Absorb / W-Collapse — regression guard (the dual-pipeline defect, Principle 11)

The int cascade + `pipeline.rs` JIT-path deletion (the "parallel JIT pipeline"
collapse) must not regress existing behaviour. The guard is **mode-equivalence**:
the dual-pipeline defect (Principle 11; `archive/pipeline-convergence-review.md`)
manifested as REPL/`--run`/`--link` divergence — the same program producing
different results in different modes. The e2e tests that guard the collapse are
exactly the `run_through_all_modes` callers across the spec suites (and
`tests/regression.rs`). No NEW tests are required for the guard — it is the
**existing** mode-equivalence coverage staying green after the collapse. The
W-e2e→unit directive (below) catches any mode-specific regression the collapse
introduces and drives it to an int unit test.

| # | Guard | Status | Note |
|---|---|---|---|
| C1 | mode-equivalence across `spec_*.rs` via `run_through_all_modes` | REG | the Principle-11 dual-pipeline guard; must stay green through the collapse |
| C2 | `tests/regression.rs` mode-divergence cases | REG | known historical divergences; re-confirm green post-collapse |
| C3 | `tests/process_form_dispatch.rs` cluster-atomic dispatch | REG | Decision 44 atomicity over the Pass-2/3 layer; must survive the three-pass reshape |

### W-Green tail — re-enable the s68 sentinels

| # | Test | FIXME | Status | Resolves at |
|---|---|---|---|---|
| G1 | `tests/s68_primitives_uniform.rs::s68_backend_intrinsic_symbols_drops_primitives_paths` (line 319) | 0191 | `[S76 W-Green, currently #[ignore]]` | un-ignore once W-Green lands (int green) — IF the backend dep-ban cleanup is in S76 scope; ELSE keep ignored with the `FIXME 0191` reason and note the backend-sprint dependency |
| G2 | `tests/s68_primitives_uniform.rs::s68_code_enum_has_primitive_marker_variant` (line 357) | 0221 | `[S76 W-Green, currently #[ignore]]` | as G1 |

**Scope caveat on G1/G2 (flagged for `/sprint`).** SPRINT.md W-Green tail says
"re-enable the 2 s68 sentinels (0221/0191) once int green." But both sentinels'
`#[ignore]` reasons name the *backend* `Code::Primitive` deletion as a **deferred
backend sprint**, not int-green. If S76 does NOT include the backend
`Code::Primitive` deletion (per the SPRINT scope table, backend privacy items
"STAY private", and the explicit-deferral list), un-ignoring G1/G2 will fail —
they assert the deletion landed. **`/qa` reads "re-enable once int green" as: the
two sentinels that are gated on int-green, which may be a DIFFERENT pair than the
two `Code::Primitive` sentinels.** Resolution: `/sprint` confirms which two
sentinels are meant; if it is G1/G2, the backend deletion must be in scope or the
re-enable cannot pass. Filed here as a scope-arbitration item, not silently
assumed.

### W3 trace + lenient + 0279 reduction (FIXMEs 0258 / 0272 / 0276 / 0279 — /qa, 2026-06-07)

New active trace e2e home: `tests/trace.rs` (supersedes quarantined
`tests/legacy/ring4_trace.rs`; the 4 trace cases formerly in
`tests/spec_12_runtime.rs` are reconciled — `trace_returns_trace_value`
rewritten to match-based extraction, the stale `trace_nested_still_returns_trace`
"outermost wins" test RETIRED).

**FIXME 0258 — trace integration tests (`tests/trace.rs`).**

| # | Test | Spec | Status | Resolves at |
|---|---|---|---|---|
| T1 | `trace.rs::trace_nested_dynamic_raises_runtime_error` | §4.12.5 | `[Tested tests/trace.rs::trace_nested_dynamic_raises_runtime_error]` | GREEN — Wave-1.5 guard handles the dynamic case |
| T2 | `trace.rs::trace_nested_lexical_raises_runtime_error` | §4.12.5 | `[Tested tests/trace.rs::trace_nested_lexical_raises_runtime_error]` | GREEN (S81) — lexical-guard defect resolved (FIXME 0258); pure-lexical `(trace (trace e))` now raises a runtime error |
| T3 | `trace.rs::trace_panic_unwind_does_not_stick_guard` | §4.12.5 (NOTE-2) | `[Tested tests/trace.rs::trace_panic_unwind_does_not_stick_guard]` | GREEN — NOTE-2 worry does NOT reproduce in REPL (per-form panic recovery resets the flag); positive guard |
| T4 | `trace.rs::trace_linked_binary_match_consumption_runs` | §4.12.9 | `[Tested tests/trace.rs::trace_linked_binary_match_consumption_runs]` | GREEN — **FLIPPED (FIXME 0286)**: now asserts WITH extern-primitive children (0280 primitives-GOT static-backing landed; primitives group swapped in object mode). Traced `work` calls `str-concat`+`str-len`; the `user/work` node has 2 extern-primitive children; linked binary exits 42. (Was: WITHOUT children, 0280 interim disposition.) |
| T5 | `trace.rs::trace_extern_primitive_appears_as_child` | §4.12.3 | `[Tested tests/trace.rs::trace_extern_primitive_appears_as_child]` | GREEN — swap-all surfaces `primitives/str-concat` (REPL) |
| T6 | `trace.rs::trace_stdlib_fixture_fn_appears_as_child` | §4.12.3 | `[Tested tests/trace.rs::trace_stdlib_fixture_fn_appears_as_child]` | GREEN — prelude `helper` appears as a tree node |
| T7 | `trace.rs::trace_neg_inline_arithmetic_not_traced` (neg) | §4.12.3 | `[Tested+Neg]` | GREEN — inline `add-i64` produces no node |
| T8 | `trace.rs::trace_neg_anonymous_lambda_not_traced` (neg) | §4.12.3 | `[Tested+Neg]` | GREEN — anonymous `fn` lambda produces no named node |
| T9 | `trace.rs::trace_polymorphic_adt_result_renders` (NOTE-1) | §4.12.3 | `[Tested tests/trace.rs::trace_polymorphic_adt_result_renders]` | GREEN (S81) — ADT-render-overflow defect resolved (FIXME 0258); tracing a fn returning `(Option Int)` renders cleanly (production bake_adt round-trip no longer overflows) |
| T10 | `trace.rs::trace_adt_value_render_overflows_defect` | §4.12.3 | `[Tested tests/trace.rs::trace_adt_value_render_overflows_defect]` | GREEN (S81 render fix + S84 §3.11.1 realign) — nullary-ADT render-overflow resolved (FIXME 0258); the 1-ctor reduction of T9. S84/FIXME 0382: `mk`'s result pinned `:(Option Int) None` so the value is concrete at codegen (tightened §3.11.1 full-concreteness), reaching the intended `:primitives/String` render assertion. Positive regression guard, no longer a defect repro |
| T11 | `trace.rs::trace_trait_heavy_prelude_overflows_defect` | §4.12.3 | `[Tested tests/trace.rs::trace_trait_heavy_prelude_overflows_defect]` | GREEN (S81) — trait-prelude-overflow defect resolved (FIXME 0258); trace swap-all over a trait-heavy prelude (TestStandard) no longer stack-overflows on a `nice-worker` thread |

**FIXME 0276 — link-mode synthetic accessor (`tests/trace.rs`).**

| # | Test | Spec | Status | Resolves at |
|---|---|---|---|---|
| A1 | `trace.rs::trace_nanos_accessor_resolves_in_repl` | §4.12.4 | `[Tested]` GREEN (S77 W-Trace) | TEST-DESIGN fix — def order corrected (`id` before `work`) per §5.13.2 REPL no-forward-ref; positive guard: bare `nanos` accessor resolves + returns Int. |
| A2 | `trace.rs::trace_linked_accessor_consume_runs_clean` | §4.12.9 | `[Tested]` GREEN (S77 W-Trace) | TEST-DESIGN fix (renamed from `..._parks_defect`) — deterministic-return `main` (FIXME 0305); the park is gone, the consume path is sound; asserts linked binary builds + exits 0 (15s park guard retained). Backend 0292 + intrinsics consume verified. |
| A3 | `trace.rs::trace_run_mode_accessor_consume_runs_clean` | §4.12.4 | `[Tested]` GREEN (S77 W-Trace) | TEST-DESIGN fix (renamed from `..._crashes_defect`) — `--run` sibling; deterministic-return `main` (FIXME 0305); 4 iters all exit 0. The "mode-independent RC double-consume" was the nanos-as-exit-code artifact, not a crash. |

Mode note (FIXME 0280 RESOLVED / FIXME 0286): linked-binary tests now assert
WITH extern-primitive children. The 0280 primitives-GOT static-backing fix landed
(S76 W3); the primitives group is swapped in object mode, so `--link` trace trees
include extern primitives exactly as REPL/`--run` do (T5). The 0280 interim
WITHOUT-children disposition is retired. FIXME 0286 deleted.

**FIXME 0286 — extern-primitive `--link` e2e + linked-tree flip (`tests/link.rs` + `tests/trace.rs`, /qa S76 W3).**

| # | Test | Spec | Status | Note |
|---|---|---|---|---|
| LP1 | `link.rs::link_extern_primitive_str_ops_exits_with_computed_length` | appendix-A §A.3 | `[Tested]` ✓ | `(str-len (str-concat "ab" "cd"))` links + exits 4. Regression guard for the 0280 latent hole (link.rs had ZERO extern-primitive coverage). |
| LP2 | `link.rs::link_extern_primitive_str_len_of_literal_exits_with_length` | appendix-A §A.3 | `[Tested]` ✓ | `(str-len "hello")` links + exits 5; second extern-primitive `--link` shape. |
| LP3 | `link.rs::link_traced_extern_primitives_appear_as_children_exit_42` | §4.12.9 | `[Tested]` ✓ | traced `(greet "bob")` in `--link`; greet's 2 children (`str-concat`+`str-len`) prove extern primitives appear in linked trace trees; exits 42. Link-mode mirror of T5. |
| (flip) | `trace.rs::trace_linked_binary_match_consumption_runs` (T4) | §4.12.9 | `[Tested]` ✓ | linked-tree expectation flipped to WITH extern-primitive children — see T4. |

**FIXME 0272 Half A — lenient panic-swallow (`tests/spec_12_runtime.rs`). RESOLVED — ferry landed; repro green.**

| # | Test | Spec | Status | Resolves at |
|---|---|---|---|---|
| L1 | `spec_12_runtime.rs::lenient_binding_panic_not_swallowed_neg` (neg) | §12.4.3 | `[Tested]` ✓ | RESOLVED — the fork-join error-slot ferry obligation landed (IVar `ivar_force` worker-side `take_runtime_error()` → join-side `set_runtime_error` re-raise; S76 Wave 4, commits 9491ccc + e53ef13). A div-by-zero in a lenient `let` binding now correctly surfaces "division by zero" instead of yielding sentinel `:primitives/Int 0`. Durably green by the S80 close (verified at 48dcea3 + S81 aeff79d). Now a passing regression guard. FIXME 0272 closed S81. |
| L2 | `spec_12_runtime.rs::lenient_binding_panic_surfaces_with_no_lenient_control` | §12.4.3 | `[Tested]` | GREEN control — `CRANELISP_NO_LENIENT=1` DOES panic, proving the spark path is the trigger. Par/IO variant deferred (needs IO infra; cost-heuristic spark via `--run` with print) |

**FIXME 0279 — io.monad overflow reduction (`tests/regression.rs`).**

| # | Test | Spec | Status | Resolves at |
|---|---|---|---|---|
| R1 | `regression.rs::regression_0279_cross_module_polymorphic_import_monomorphisation` | spec/08-modules.md §8.3 | `[S77]` FAILING | FIXME(/typecheck) — reduced from io.monad to a 2-file/3-line repro: importing a polymorphic `(Fn [a] a)` fn cross-module and calling it overflows `cranelisp_types::types::apply` (types.rs:230) via a cyclic/occurs-violating Subst composed at cross-module scheme instantiation. NOT macro/`pure`/`Pure`-specific; the cross-module import of a polymorphic scheme is load-bearing. Likely also the root of the `d6_exemplar_*`/`wave6_*` exemplar overflow cluster |

### W-e2e→unit directive (the user's PRIMARY directive — frame for actionability)

Per SPRINT.md W-e2e→unit: **every e2e failure during Phase 5 gets two outputs** —
(a) a fix OR a tracked defect FIXME + failing-not-ignored repro per
`feedback_repros_join_suite`; AND (b) **an explicit assessment**: "would a unit
test inside `src/` (int) have caught this before e2e?" If no, the gap is closed
with a new `/dev (int)` unit test (`feedback_unit_tests_with_dev`). The
assessment is recorded PER FAILURE, not just the fix.

`/qa`'s framing so this is actionable in Phase 5:

1. Each failing e2e test above carries a `// FIXME(/dev …)` only when the failure
   path needs action `/dev` cannot infer from the test (per `qa.md §Defect
   protocol`). In normal operation the failing test IS the signal.
2. When an e2e failure is reduced to a minimal repro (per `tests/CLAUDE.md
   §"Isolating Cross-Crate Failures"`), the repro is committed to `tests/` as a
   durable record AND the per-crate `/dev` writes the isolating unit test inside
   `src/` (int) or the owning crate. `/qa` does not author the unit test — but
   `/qa` records, in the ledger, whether the e2e→unit assessment was done.
3. The assessment ledger lives in `tests/plan/ledger.md` (the failure ledger),
   one row per Phase-5 e2e failure: { failing test, root crate, fix-or-FIXME,
   "unit test would have caught? Y/N", "unit test added? (crate::name)" }.

### Free-standing discipline (root CLAUDE.md)

Every test above is free-standing — `PreludeVariant::None` for core-language /
macro-availability tests; `PreludeVariant::PrimitivesOnly` for tests needing bare
primitive names (`add-i64`); `PreludeVariant::TestStandard` ONLY where ADTs /
operators / `map` are required (E1). **Zero dependency on `stdlib/`** — the
`stdlib/defs.cl` instance is named in M3's rationale as the real-world case, but
the test reproduces the shape inline, it does not load stdlib.

## Sprint 108 Increment 2 — `/search` seeded-module scope + indexing lifecycle (2026-07-12)

Increment 2 extended `/search`'s reachable set to the bootstrap-seeded modules
(`primitives`, seeded `macros`) per the S108 user ruling (repl/spec.md §17.19
R10) and added the indexing-lifecycle messages (§17.19.3). Three e2e guards
landed in `tests/search.rs`; the two async lifecycle messages are unit-pinned
at the `IndicesInner`/`ReplInput` seams (deferral enumerated below).

| Spec citation | Test | Status | Polarity / provenance |
|---|---|---|---|
| repl/spec.md §17.19 R10 — reachable scope includes the built-in seeded modules; `(import [primitives [vec-len]])` is the actionable payoff | `tests/search::search_finds_seeded_primitive_offers_import` | [Tested] — GREEN; repro of the S108 E1 defect (`// defect: class=enumeration-miss`, locus `src/session_v4/index_worker.rs::resolve_module_file`) | positive; regression guard (Section 2) |
| repl/spec.md §17.19 R13 — a seeded exact match already bare-in-scope is shown-but-MARKED `already in scope — no import needed` and MUST NOT offer an import form | `tests/search::search_seeded_primitive_already_in_scope_marked_no_import` | [Tested+Neg] — GREEN | negative (asserts absence of the import form); R13 companion for the seeded feed |
| repl/spec.md §17.19.3 (+ §17.19 R10) — a user file whose module name collides with a seeded module (`primitives.cl`) MUST NOT wedge `pending_count`: seeded feed wins, no stuck `indexing N module(s)…` note, completion latch reachable | `tests/search::search_seeded_file_name_collision_does_not_wedge_pending_note` | [Tested+Neg] — GREEN; repro of the S108 I-1 review finding (`// defect: class=enumeration-miss`, locus `src/session_v4/index_worker.rs::arm_burndown`); deterministic via the SUT's own `wait_for_index_settled`, not a race | negative (asserts absence of the wedge note); arch-pre-flagged boundary |

**E2 lifecycle-message deferral — enumerated unit obligations (all landed, /dev,
same change-set; each confirmed fail-on-revert in the guard-closure wave):**

| Case | Unit guard |
|---|---|
| `record_preindexed` counts seeded modules in BOTH `enumerated_total` and `indexed` (no early note/completion) | `src/session_v4/index_worker.rs::record_preindexed_counts_seeded_in_both_tallies` (+ `record_preindexed_is_idempotent`) |
| completion latch is one-shot and gated on `note_shown` (timing (b)) | `src/session_v4/index_worker.rs::take_completion_notice_one_shot_gated_on_note_shown` |
| completion requires `pending_count == 0` | `src/session_v4/index_worker.rs::take_completion_notice_requires_pending_zero` |
| seeded-vs-file collision counts once and completes (I-1 seam) | `src/session_v4/index_worker.rs::seeded_name_file_collision_counts_once_and_completes` |
| seeded public symbols land in the index (R10 direct-read feed) | `src/session_v4/index_worker.rs::seeded_public_symbols_land_in_index` |
| empty-partial serves the note, NOT `no match` (I-2, §17.19.3 non-conflation MUST) | `src/repl.rs::empty_result_still_indexing_serves_only_the_note_not_no_match` |
| empty-complete serves `no match`, NOT the note (I-2 converse) | `src/repl.rs::empty_result_complete_index_serves_only_no_match_not_the_note` |
| note text present iff pending > 0 | `src/repl.rs::indexing_note_text_present_iff_pending` |
| non-TTY never emits the async completion notice (I-3, §10.8 byte-identical) | `src/repl_input.rs::piped_input_is_not_interactive_so_completion_notice_is_gated_off` |

Why no e2e for the messages themselves: the burn-down empirically beats the
first piped `/search` even at 30 reachable modules, so whether the note fires
is exactly the arm-vs-serve race — a racy e2e is forbidden. Full rationale in
`tests/search.rs` (the E2 deferral block) and SPRINT.md §Increment 2. If the
harness gains a burn-down hold (injectable delay/barrier), revisit.

## Sprint 108 Increment 3 — E3–E7 + candidate B + 0558 repros; the E4 styling byte-identity strategy (2026-07-12)

Whole-increment plan for `sprints/SPRINT.md` §Increment 3, authored at Phase 3
for `/testing`'s QA-first Stage 1. Design inputs: `design/arch/repl-styling-seam.md`
(E4), `design/arch/resolve-home-enumeration.md` (E3 + 0558), the locked
`repl/spec.md` §10.3 (styling roles R1–R15), §17.1 (classifier ruling), §17.19
(search R10/R13), §4.1.4 (trait sections), `design/int/agent.md` §5.5 (E5 harvest).

### Risk read (shapes the depth below)

- **E3/0558 — third and fourth sightings of one class.** The
  `enumeration-miss`/`wrong-scope-lookup` family has now recurred four times
  (Inc1 D1, Inc2 E1/E2, E3, 0558 — register in `resolve-home-enumeration.md` §1).
  Highest-depth coverage: every negative the arch doc §4 names gets a row or an
  enumerated unit obligation, because each prior fix was per-instance and missed
  the sibling. The class rule ("no source marked complete without contributing
  rows"; "formatters take `(entry, home)`") is what the negatives pin.
- **E4 — the largest surface, but mostly *equivalence* risk, not new-behaviour
  risk.** Wave D rewrites every token-styled render path. The load-bearing guard
  is colour-OFF byte-identity per output kind (the standing golden corpus — most
  kinds already have goldens); the *new* §10.3 colour-ON behaviour needs fresh
  per-kind byte-exact pins. The silent-failure mode is a producer that perturbs
  plain-text bytes while adding roles (§10.3 req 2) — that is what the golden
  corpus catches for free, so the corpus must be verified COMPLETE per kind
  before Wave D starts, not after.
- **E6/E7 — routing/eval seams with a deterministic unit surface.** No model in
  the loop anywhere: the classifier is a pure function, and E7 reproduces in the
  default build. Cheap, exact pins; the risk is under-enumerating the classifier
  input space (the reader-macro-in-prose trap has FOUR trigger chars: `'`,
  `` ` ``, `~`, `:`).
- **E5 — agent-lane only**; the testable seam is `harvest_context` (unit) plus
  an optional deterministic e2e through the `/context` dump (§17.11).

### A. Deterministic defect repros — Stage 1, RED-first

Proposed test names are canonical targets for `/testing`; adjust mechanics, keep
the polarity split (negatives get their own fns, `_neg_`/`_not_` naming). Every
repro carries `// spec:` + `// defect:` per `tests/CLAUDE.md`.

#### E3 — `/search` drops already-loaded modules' not-in-scope symbols

Fixture recipe (deterministic; from SPRINT.md §E3): `foo.cl` defines `count` +
`other`; the prelude variant imports `[foo [other]]` — so `foo` is
loaded/registered but `count` is NOT in scope. Serve determinism via the SUT's
own `wait_for_index_settled` (the Inc2 pattern; no new infra).

| Spec citation | Test (tests/search.rs) | Status | Polarity / provenance |
|---|---|---|---|
| repl/spec.md §17.19 R10 — importable-but-not-in-scope symbols of an already-LOADED module MUST surface with the `(import [foo [count]])` payoff | `search_finds_loaded_module_not_in_scope_symbol_offers_import` | [S108] — RED at authoring (the E3 defect); `// defect: class=enumeration-miss locus=src/session_v4/index_worker.rs::index_one_module (branch (a) mark_skipped) found=S108 owner=/dev` | positive; third `enumeration-miss` sighting |
| repl/spec.md §17.19 R13 — the in-scope exact match (`other`) is still shown-but-MARKED `already in scope — no import needed`, no import form offered | `search_loaded_module_in_scope_exact_match_still_marked_not_imported_neg` | [S108] — expected GREEN (control; guards R13 against the Wave-B fix) | negative (asserts absence of an import form for `other`) |
| repl/spec.md §17.19 R10 — an UNloaded reachable module still indexes via the file feed (branches b/c) alongside the new live-table feed | `search_unloaded_module_still_indexes_alongside_loaded_feed_neg` | [S108] — expected GREEN (control; guards the file path against the Wave-B rewrite of branch (a)) | negative (feed-union completeness) |

**E3 unit obligations (enumerated for `/dev` Wave B, same change-set,
fail-on-revert verified — the Inc2 E2 precedent; e2e is the wrong tier for the
arm-vs-load timing cases, per the Inc2 racy-e2e rationale):**

| Case (resolve-home-enumeration.md §4) | Unit guard (proposed seam) |
|---|---|
| arm-time sweep records already-terminal registered modules from the live table (`public_entries_from_table`) | `src/session_v4/index_worker.rs` |
| publication-edge hook records a module that reaches terminal typecheck AFTER arm (in-flight-at-arm case) — no polling, no respin | `src/session_v4/index_worker.rs` |
| late `/import`-loaded module's rows appear via the hook; no second completion note | `src/session_v4/index_worker.rs` |
| re-record REPLACES a module's rows (watcher reload / redefinition — no duplicates, no stale rows; idempotent tallies) | `src/session_v4/index_worker.rs` |
| accounting: `pending_count = enumerated_total − indexed.len()` ≥ 0, reaches 0, order-independent (arm-vs-hook — the S-1 property extended to the loaded feed) | `src/session_v4/index_worker.rs` |
| `mark_skipped`-with-zero-rows only for genuinely row-less outcomes (no file / empty / CF.2), never for "registered" | `src/session_v4/index_worker.rs` |

#### I-1 — private-prelude `/search`/display gate (fix+test co-landing ACCEPTED, /qa 2026-07-12)

The I-1 divergence ruling (`prelude-import-convergence.md` §3.5.2: a PRIVATE
prelude binding must not classify "in scope" for display/`/search`) was fixed
by `/dev` with two e2e authored INSIDE the same change-set (METHOD §2.2
fix+test-together). `/qa` reviewed them 2026-07-12 and **accepts them in place**
in `tests/search.rs` — a legitimate co-landing, no rehome needed: correct
`// spec:` anchors (repl/spec.md §17.19/§4.1.10 + spec/08-modules.md §8.8.1
importable=public), correct `// defect:` on the repro
(`class=enumeration-miss locus=src/repl.rs::exact_in_scope_hit`), placed in the
§17.19 in-scope/marked family sharing the `search_session_private_prelude`
fixture, no duplication with existing search or prelude-scope tests (verified
by sweep). Both verified GREEN by targeted run 2026-07-12.

| Spec citation | Test (tests/search.rs) | Status | Polarity / provenance |
|---|---|---|---|
| repl/spec.md §17.19 (R13) + spec/08-modules.md §8.8.1 — the prelude provides only its PUBLIC names: `/search` of a PRIVATE prelude binding MUST return the empty-set no-match note — no synthesized row, no `already in scope` mark, no import offer | `search_private_prelude_binding_returns_no_result_row_neg` | [Tested+Neg] — GREEN (repro; covers both the `exact_in_scope_hit` synthesis and `is_already_in_scope` mark paths at the shared `lookup_with_prelude_fallback` seam) | negative ×3 (empty set / no mark / no offer) |
| repl/spec.md §4.1.10 + §8.8.1 — a bare reference to a PRIVATE prelude binding takes the UNBOUND display path (display/enumeration seam agrees with resolution) | `bare_private_prelude_reference_is_unbound` | [Tested] — GREEN (companion pin, deliberately no `// defect:` — the repro above carries it) | negative (never displays as in-scope) |

One correction routed to `/testing` (comment-only, not blocking acceptance):
the repro's prose carries present-tense "RED on HEAD: `secret` appears as a
marked result row" — the gate landed and the test is GREEN, so per
`tests/CLAUDE.md` §"Defect-repro notation" convert to past tense (a GREEN repro
with present-tense open-defect framing lets a future regression pose as a known
guard). Fold into the §V stale-framing sweep above.

#### E6 + candidate B — classifier misroute (the §17.1 one-form rule)

Primary tier: **unit — `classify_for_agent` is a pure deterministic function,
no model** (`src/agent/mod.rs` `#[cfg(test)]`, the existing
request-content-test precedent; agent lane
`cargo nextest run --features agent --lib 'agent::'`). `/testing` drafts these
Stage 1 (they live beside the existing `"how do I define a function"` → Agent
pin); `/dev` Wave A owns keeping them green. Classifier input space to pin —
each its own test fn:

| §17.1 rule | Input | Expected | Status |
|---|---|---|---|
| ≥2 forms → Agent (the E6 repro — `'` contraction makes `doesn't` compound) | `why doesn't that typecheck?` | `Agent` | [S108] RED; `// defect: class=routing-misclassify locus=src/agent/mod.rs::classify_for_agent (any_compound arm) found=S108 owner=/dev` |
| ≥2 forms → Agent (the second transcript trap: `:` + `'` both) | prose containing `was:` and a contraction | `Agent` | [S108] RED |
| one FQ symbol → Repl, independent of `symbol_is_known` (candidate B) | `primitives/vec-len` | `Repl` (introspect) | [S108] RED (currently routes to agent per candidate B transcripts) |
| one bare unknown → Repl (§4.1.10 preserved) | `frobnicate` | `Repl` | [S108] expected GREEN control |
| one compound → Repl | `(+ 1 2)` | `Repl` | [S108] expected GREEN control |
| multi-form code → Agent when active | `foo bar` | `Agent` | [S108] RED (currently Repl via any_compound absence — verify at authoring) |

E2e companion (lane A, `tests/agent.rs`, stub provider — deterministic): ONE
routing pair, not the whole matrix: (a) NL sentence with active stub agent →
stub reply rendered in the `▌` frame, and NOT `:primitives/Int 0` (negative
assertion in the same fn); (b) single FQ symbol with active stub agent → §4
introspection line, and the stub's scripted reply ABSENT (the agent was not
consulted). Trace §17.1. [S108]

#### E7 — multi-form line swallows per-form errors (no-agent path)

Default build, `tests/repl_negative.rs` (or a sibling file) — reproduces
without the agent feature. Mechanism (per `/arch` P2): `src/eval.rs::eval`
~L185–208 wraps the per-form error as a fake `Val{0}` warning, then L207
clobbers the warning. `// defect: class=error-swallow
locus=src/eval.rs::eval (multi-form arm fake-Val + warning-clobber) found=S108
owner=/dev`.

| Spec citation | Test | Status | Polarity |
|---|---|---|---|
| repl/spec.md §17.1 (sequential-eval-abandon, no-agent path) + Design Principle "self-documenting REPL" — `foo bar` MUST surface `undefined variable: foo`, never `:Int 0` | `multi_form_line_surfaces_first_error_not_silent_zero` | [S108] — RED at authoring (the E7 defect) | positive (of the fix) + inline negative: stdout does NOT contain `:primitives/Int 0` |
| §17.1 abandon-on-FIRST: `2 foo` — the error surfaces even when a green form precedes it; no fake trailing value | `multi_form_error_after_green_form_still_surfaces_not_swallowed_neg` | [S108] — RED | negative (asserts absence of a fabricated result line) |
| §17.1 first-error selection: `foo bar` reports `foo` (first), not `bar` | `multi_form_abandons_on_first_error_reports_first_undefined` | [S108] — RED (currently `:Int 0`; post-fix pins WHICH error) | positive |
| §17.1 all-green multi-form control: `1 2 3` evaluates without error | `multi_form_all_green_line_evaluates_without_error` | [S108] — expected GREEN | control — see flag below |

**Flag to `/repl` (spec gap, non-blocking):** §17.1 pins the ERROR path
("abandons on the first error, surfacing it") but is silent on what an
all-green multi-form no-agent line DISPLAYS (today: the last value, `:Int 3`).
The control row asserts only "no error"; do not pin the display shape until
`/repl` scribes it. Filed as a note, not a FIXME — Wave C should not change the
green path, and the row will catch it if it does.

#### 0558 — prelude-globbed trait drops `; defn:`/`; impl:` sections

Same class family as E3 (resolve-home-then-enumerate; arch doc §1 register) but
the display-side mechanism — a lookup rooted at the asking scope instead of the
resolved home. **`class=wrong-scope-lookup`, NOT `enumeration-miss`** — the
controlled vocabulary already names FIXME 0558 under `wrong-scope-lookup`
(resolution-time mechanism), and the vocabulary note under `prelude-scope-miss`
draws exactly this line: census errors are `enumeration-miss`, wrong-root
resolution is not. One family, two classes; the `// defect:` lines keep them
distinct so the class-frequency analysis keeps working.

| Spec citation | Test (tests/repl_introspection.rs) | Status | Polarity |
|---|---|---|---|
| repl/spec.md §4.1.4 — a bare lookup of a prelude-globbed trait (reachable ONLY via the implicit outer-scope fallback bit, no `Import` edge) MUST show the primary line qualified to the trait's home PLUS the unconditional `; defn:` and `; impl:` sections | `bare_prelude_globbed_trait_lookup_shows_defn_and_impl_sections` | [S108] — **reproduce-or-record-close**: `/testing` authors the repro per the FIXME 0558 recipe (test-standard prelude's `Display`/`Num`, entered from `user`); if RED, it stands as the Wave-B guard (`// defect: class=wrong-scope-lookup locus=src/repl.rs::format_trait_display found=S108 owner=/dev`); if it does NOT reproduce, record that in the test comment as a GREEN pin and report to `/sprint` so 0558 closes on that finding | positive |
| repl/spec.md §4.1.4 — `; impl:` ordering: locally-defined types first, then imported; method names under `; defn:` unqualified | fold into the same fixture's assertions | [S108] | positive (byte-order assertion) |
| **Pattern-B sibling probe** (resolve-home-enumeration.md §5 note — the `/qa` repro decision): the TYPE-side `; impl:` view from a local type — does it include impls of a prelude-globbed trait on that type? | `local_type_impl_section_includes_prelude_globbed_trait_probe` | [S108] — probe: if it reproduces, it is a SEPARATE defect (the prelude hop missing from the VIEW walk, Decision-45 Pattern B) — do NOT fold into Wave B's home-rooting fix; report to `/sprint` for its own dispatch. If GREEN, keep as the Pattern-B regression pin | probe (either outcome commits) |

### B. E4 — the §10.3 byte-identity guard strategy (two tiers, by construction)

**Tier decision (load-bearing, from verified infra):** the e2e harness is
piped/non-TTY, `repl/spec.md` §10.1 explicitly rejects a `--color=force` flag,
and `src/style.rs::detect_color` has no env force-on — so **an e2e subprocess
can never produce colour-ON output**. The §10.3 contract therefore splits:

1. **Colour-OFF byte-identical goldens — e2e, `/testing`, Stage 1** (§10.3
   requirement 2, the non-TTY contract). These are GREEN regression guards, not
   REDs: their job is to hold every output kind's plain bytes fixed through the
   Wave-D producer rewrite. Stage-1 job = **verify the per-kind golden set is
   complete and add the missing kinds** (most exist — see matrix), plus one
   suite-wide negative: no `\x1b[` byte anywhere in non-TTY output for each
   kind's fixture (the `ESC_SGR` idiom from tests/agent.rs).
2. **Colour-ON byte-exact fixtures — unit tier, enumerated `/dev` Wave-D
   obligations** (§10.3 requirement 3 determinism, the §3.11 discipline extended
   to styling), via the `#[cfg(test)]`-only `style::test_support::ColorGuard`
   seam (nextest process isolation makes the process-global force safe). These
   cannot be drafted RED at Stage 1 — the `Role`/`StyledDoc`/`render` seam does
   not exist to compile against — so they land WITH Wave D, fail-on-revert
   verified, audited against this enumeration at Phase 6/7 (the Inc2 E2
   deferral precedent). Two layers:
   - **Per-role SGR pins** (migration step 1, arch doc §6): one unit pin per
     role R1–R14 on `role_style` asserting the exact SGR parameter string of
     the §10.3 table (`1`, `33`, `32`, `36`, `3`, `2`, `2`, `1;31`, `31`,
     `1;33`, `33`, `1`, `2`, `95`), plus the render invariants:
     `render(colour-off) == the doc's concatenated span text` (the golden/agent-
     membrane guarantee, §10.3 req 2) and every styled span terminated by
     `\033[0m` before newline/transition (§10.2).
   - **Per-output-kind colour-ON fixtures** (migration step 3): fixed input →
     full expected byte string with SGR spans at exact offsets, one per kind in
     the matrix below.

**Output-kind × role matrix** (the enumeration `/testing` completes colour-OFF
and `/dev` pins colour-ON; each kind lists the §10.3 roles it exercises — a
kind is DONE only when every listed role is byte-pinned in both tiers):

| # | Output kind | Fixture sketch | Roles pinned | Colour-OFF golden today |
|---|---|---|---|---|
| K1 | Result value — num/bool | `(+ 1 2)` → `:primitives/Int 3` | R4 (annotation cyan, single construct), R2 (literal yellow), R15 | exists (`display_exact.rs` §1 family) — verify per-kind |
| K2 | Result value — string | `"hi"` → `:primitives/String "hi"` | R4, R3 (whole quoted literal one green span; §10.2 no SGR inside content) | exists — verify |
| K3 | Introspection `/sig`/`/info`/bare symbol | defn with docstring → `:(Fn …) user/foo ; defn - doc` | R4, R7 (dim `user/` prefix on the FQ NAME — the NEW role), R15 (name part), R6 (dim `; defn - doc`) | exists (`repl_introspection.rs` §4.1 family) — verify. NOTE: §10.3 R1 does NOT apply here (Head is pretty-printed-code-only) — the sprint dispatch's "a `/sig` line pins R1" is corrected to R4/R7/R6/R15 per the locked table |
| K4 | Introspection drawers | bare trait/type lookup → `; defn:`/`; impl:`/`; match:` sections | R4, R6 (headers AND name bodies beneath), R7, R15 | shares the 0558/§4.1.4 fixtures above |
| K5 | Code — `/sexp`/`/source` | the §3.11 `rotate` fixture | R1 (head bold, incl. head-position delimiters), R2, R15 + §3.11 layout byte-exactness (colour-on adds SGR at the SAME columns — req 3 verbatim) | exists: `display_exact.rs::sexp_rotate_aligned_let_match_byte_exact` (colour-off byte-exact) |
| K6 | Code — source comment | a `/source` of a defn whose recorded source carries a `;` comment (the `rotate` fixture has none — R5 needs its own fixture) | R5 (italic — the 0561 resolution's source half), R1, R2 | gap — add colour-off golden Stage 1 |
| K7 | `/search` result row | Inc2 seeded fixture + a docstring-only hit | R4 (sig), R7 (module column), R6 (`; doc:` excerpt — §10.3 wins over §17.19.2's stale "italic" wording; R6 = dim), R15, import-snippet spans | exists (`search.rs`) — verify the docstring-excerpt row has a byte golden |
| K8 | Error line | `foo` → `Error: undefined variable: foo`; a `runtime error:` line | R8 (bold red keyword), R9 (red body) | exists (`repl_negative.rs`) — verify byte grain |
| K9 | Warning line | a warning-producing form → `; warning:` | R6 prefix + R10/R11 | verify; add if missing |
| K10 | Prompt + banner | startup + `user>` | R13 (dim) | exists (`non_tty_repl_line_editor_off` golden) |
| K11 | Category header | `/list` → `Fns:` etc. | R12 (bold; name bodies stay R15/layout — the scope boundary) | exists (`prelude_group_and_category_share_layout_body`) |
| K12 | Lifecycle note | `; search index complete.` | R6 | unit-only (the Inc2 racy-e2e rationale) — colour-ON unit pin only |
| K13 | Agent gutter + `agent>` composite | stub-agent prose; agent-typed line | R14; R13+R14 composite | exists (agent-lane goldens + the design-side §14.6 leaf guard) — re-baseline is NOT expected (gutter mechanism unchanged, arch doc §5 P9) |

**NEW-behaviour flag (result-value colouring).** §10.3 R2/R3/R4 on RESULT
VALUES is spec'd-but-unimplemented today (`format_result_value` emits zero SGR
— arch doc §1b): Wave D makes values styled for the FIRST time. Colour-OFF
goldens are unaffected by construction (req 2). But any existing test that
asserts colour-ON output for a value/introspection surface — or asserts "no
SGR" WITHOUT forcing colour off — encodes the old always-plain behaviour and
must be re-verified at Wave D: the no-SGR assertions in the corpus are valid
only because they run non-TTY/`--no-color`; none may be promoted to "values
are never styled." `/testing` sweeps for such assumptions Stage 1 and flags
any found (expected: none — the `ESC_SGR` checks all pin the colour-OFF mode
or well-formedness, which both survive).

**One-seam enforcement:** the "exactly one `styled()` call site" gate is
`/review`'s grep watch (arch doc §4, Principle 18), not a test — noted here so
the Phase-6 audit checks it happened.

### C. E5 — harvest omits errored turns (agent-feature-gated)

The harvest ring is `#[cfg(feature = "agent")]` end to end (design/int/agent.md
§5.5 (4)); feature-off there is NO testable surface by design (byte-identical
read loop). The plan therefore assigns:

- **Unit obligations (`/dev` Wave A, `src/agent/`, enumerated —
  fail-on-revert verified):** (1) `harvest_context` includes a recent errored
  turn's exact `input` + diagnostic string; (2) the single most-recent errored
  turn is PINNED to the budget floor (survives budget pressure that drops green
  turns); (3) errored-first newest-first ordering; (4) ring cap N=8 with
  errored-turn preference (an error survives 8 subsequent green turns is NOT
  promised — pin what §5.5 (1)/(3) actually says: scan-for-errors, most-recent
  error pinned); (5) `record_repl_turn` is a no-op when `agent == None`.
- **Optional e2e (lane A, deterministic, no model — `/testing` if cheap):**
  submit a failing `(defn …)` (type error), then `/ask …`, with `/context`
  dumping the assembled request (§17.11, existing
  `agent_on_context_dumps_request_to_file_dormant` precedent) → assert the
  failed form's source text AND its diagnostic appear in the dump. Trace
  design/int/agent.md §5.5 + repl/spec.md §17.11. [S108]

### D. `class=` assignments + vocabulary additions (this increment's repros)

| Finding | class | locus |
|---|---|---|
| E3 | `enumeration-miss` (third sighting) | `src/session_v4/index_worker.rs::index_one_module (branch (a))` |
| 0558 | `wrong-scope-lookup` (per the standing vocabulary row naming 0558) | `src/repl.rs::format_trait_display` |
| E6 + candidate B | `routing-misclassify` (NEW class — added to tests/CLAUDE.md) | `src/agent/mod.rs::classify_for_agent` |
| E7 | `error-swallow` (NEW class — added to tests/CLAUDE.md) | `src/eval.rs::eval (multi-form arm)` |
| E4 | no `// defect:` on the styling guards — they are spec-coverage/regression tests, not defect repros (the tagging rule: only defect-born tests carry the notation). The Inc1-D2-class drift E4 subsumes is already tagged on its D2 repro | — |
| E5 | no repro test carries it at e2e; if the optional `/context` e2e lands as the repro, tag `class=enumeration-miss`? NO — E5 is a missing SOURCE in context assembly, same census shape: tag `class=enumeration-miss locus=src/agent/harvest.rs::harvest_context` on whichever test (unit or e2e) is the designated repro | `src/agent/harvest.rs::harvest_context` |

### E. Test-infra notes for `/testing` (what exists / what does not)

- **No new harness infra is required for Stage 1.** E3 rides the Inc2 pattern
  (on-disk fixtures + prelude variants + `wait_for_index_settled`); E6 unit +
  stub-e2e ride the existing agent lane; E7 is plain piped REPL; 0558 rides the
  introspection fixtures.
- **Colour-ON e2e is structurally impossible today** (§10.1 forbids a force
  flag; harness is non-TTY) — hence the tier split in §B. If a future increment
  wants colour-ON at e2e grain, the options are a PTY harness helper or a §10.1
  spec change via `/repl` + user; NEITHER is requested for Inc3.
- **The colour-ON unit fixtures need the producers callable with fabricated
  session state** — `/dev` Wave D should keep `render`/`role_style` and the
  producer span-builders unit-reachable (pure over their inputs), or the
  per-kind pins degrade to render-layer-only. Flagged as a Wave-D design
  obligation, not new `/qa` infra.

## Prelude ≡ explicit import — resolution-site × polarity matrix (2026-07-12, /qa)

**The invariant (spec-settled; user-confirmed).** A prelude-provided name is in
a module's scope on EXACTLY the same terms as an explicit `import`, and is
resolved by a SINGLE lookup that consults the symbol table and transparently
falls back to the prelude. Materialised-vs-consulted-on-miss is an
implementation detail with ZERO semantic weight; there is no "outer scope" as a
language concept. Anchors: `spec/08-modules.md` §8.6.1 (peers, not precedence;
no def-over-prelude tier), §8.6.2 (chain-follow to terminal), §8.6.3 (ONLY
`let`/`fn`/`match` shadow), §8.6.4 (definition-over-name-in-scope is a
compile-time error INCLUDING over the implicit prelude; same-terminal dedup;
the S102/0484 pinning), §8.6.5 (distinct-terminal poison), §8.8.1 (implicit
prelude = `(import [prelude [*]])`; outer-scope realisation is
"a resolution-mechanism detail, not a normative exemption"), §8.8.3
(not-loading ≠ shadowing).

**Why a matrix.** The check path has grown SIX fallback-bolted resolver
variants (`cranelisp-types::resolve_with_fallback`,
`resolve_terminal_entry_or_prelude`, `resolve_terminal_fq_or_prelude`,
`resolve_current_or_prelude`, `probe_current_or_prelude`,
`lookup_trait_decl_or_prelude`) plus a `prelude_fallback` bit threaded through
~93 sites. Because the fallback is per-variant, not intrinsic to lookup, every
new resolution site can FORGET it — the mechanism behind the recurring
`enumeration-miss`/`wrong-scope-lookup`/`prelude-scope-miss` class (E3, E8,
0558, E9, and the live HKT-arity divergence below). This matrix enumerates
every resolution site with BOTH polarities so that any site lacking the
fallback — present or future — fails loudly. The RED set below is the driver
AND acceptance spec for the forthcoming `/arch` one-function convergence.

**Highest-signal test shape: the twin fixture.** One program, two provenances —
leg A brings name `X` via explicit `(import [prelude [X]])` (or an
explicit-module import), leg B relies on the implicit prelude — and the test
asserts the SAME outcome (same exit code, same diagnostic, same rejection).
Any site lacking the fallback diverges the twins. Author twins wherever the
matrix says "twin"; the divergence message names the site.

### I. Resolution-site enumeration (probed 2026-07-12 against HEAD)

Status legend: **GREEN** = prelude parity holds (probed and/or pinned);
**RED** = live divergence or missing enforcement, probe transcript in the /qa
report of 2026-07-12.

| # | Site | Seam | Parity status |
|---|---|---|---|
| S1 | Bare VALUE reference (call + value position) | `checker.rs::resolve_current_or_prelude` via `infer_var` | GREEN — pinned (`spec_08_prelude_outer_scope::bare_primitive_resolves_via_prelude_reexport`, `spec_08_modules::def1_prelude_provided_defn_called_bare_enters_codegen_batch` + explicit control) |
| S2 | Bare TYPE reference in annotation position (`:Zed` param/return) | `resolve_type` → `resolve_current_or_prelude` | GREEN — probed; **no pin** → row G2 |
| S3 | `deftype` FIELD type naming a prelude-provided type | same chokepoint at deftype registration | GREEN — probed; **no pin** → row G3 |
| S4 | Ctor reference, VALUE position | `resolve_current_or_prelude` ctor arm | GREEN — probed (`(ZedC 7)` via prelude) → row G4 |
| S5 | Ctor reference, PATTERN position (`match`) | `lookup_constructor_type_with_state` (0317 chokepoint) | GREEN — probed; unit-tier chokepoint pins exist → row G4 (e2e twin) |
| S6 | Trait reference at `impl` form (`(impl Trait Type …)`) | `lookup_trait_decl_or_prelude` (E9 fix) | GREEN — pinned (`repl_introspection::impl_of_prelude_globbed_trait_resolves_trait_name`) |
| S7 | `impl` TARGET-type resolution (`fq_impl_type`) | `resolve_type` at `impl_check.rs:113` | GREEN — probed (impl on prelude-provided `Zed` registers) |
| S8 | **`impl` HKT-ARITY gate type-def lookup** | `lookup_type_def_with_state` at `impl_check.rs:70` — **NO fallback** | **RED** — twin diverges: explicit-import target correctly rejected (`Zed has 0 type parameters, but trait Functor expects a constructor with arity 1`); implicit-prelude target **silently accepted** (arity check skipped) |
| S9 | Trait-method call dispatch / method→trait resolution | `resolve_terminal_entry_or_prelude` (checker.rs 2214/2259/2312) | GREEN — pinned (E9 test's `(show (Widget 5))` dispatch leg) |
| S10 | Macro RECOGNITION at expansion | `src/expander.rs` → `resolve_with_fallback` | GREEN — probed (prelude-provided `defmacro` expands bare); coverage verify → row G5 |
| S11 | Cross-module monomorphisation collection of a polymorphic callee | `resolve_terminal_fq_or_prelude` (program.rs 3629/3726/3785; 0488) | GREEN by code-read (fallback-aware); coverage verify → row G6 |
| S12 | Conflict check: `defn` (and private `defn-`) over name-in-scope | `reject_def_over_binding` (checker.rs:1013; 0514/0516) | GREEN — pinned all 3 modes (`spec_08_name_shadowing` §1–§5, all pass 2026-07-12) + `defn-` probed |
| S13 | Conflict check: `deftype` over name-in-scope | same seam (program.rs:911) | GREEN — probed (§8.6.4 diagnostic incl. prelude arm); **no pin** → row G7 |
| S14 | **Conflict check: `deftrait` over name-in-scope** | `register_trait_decl` → `lookup_trait_decl_with_state` — **current-module-only, and `TopLevel::TraitDecl` skips `reject_def_over_binding`** (program.rs:917) | **RED (prelude arm)** — twin diverges: `deftrait Show` over explicitly-imported `Show` rejected (`trait Show already defined`); over prelude-provided `Show` **silently accepted**, registers `user/Show` |
| S15 | **Conflict check: trait METHOD names** (a `deftrait` method contesting an in-scope name) | `register_trait_method` — no §8.6.4 seam | **RED (both arms)** — method `gulp` over prelude-provided AND over explicitly-imported `gulp` both silently accepted |
| S16 | **Conflict check: `defmacro` over name-in-scope** | macro registration in `src/expander.rs` — no §8.6.4 seam | **RED (both arms)** — `defmacro gulp` over prelude-provided AND over explicitly-imported `gulp` both silently accepted, and the macro WINS (bare `(gulp 3)` → 3) |
| S17 | Import-vs-prelude, DISTINCT terminals → poison | import installer + resolve | GREEN — pinned (`spec_08_prelude_outer_scope::explicit_{glob,specific}_import_over_prelude_distinct_terminal_poisons`) |
| S18 | Import-vs-prelude, SAME terminal → dedup (no false collision) | terminal-source comparison §8.6.4 | GREEN — probed (`(import [primitives [add-i64]])` under a primitives-re-exporting prelude resolves, exit 42); **no pin** → row G1 |
| S19 | Prelude refusal / selective import / FQ reach / lexical shadow | fallback-bit gate + §8.6.3/§8.6.6/§8.8.3 | GREEN — pinned (`spec_08_prelude_outer_scope` §3–4, `spec_08_name_shadowing` §6) |
| S20 | Display: bare symbol / trait sections / type `; impl:` view | `src/repl.rs` describe + format paths (D1/D2, E8, 0558, Pattern-B) | GREEN — pinned (`repl_introspection::bare_prelude_globbed_trait_lookup_shows_defn_and_impl_sections`, `type_impl_section_includes_prelude_globbed_trait_impls_probe`, all pass 2026-07-12) |
| S21 | Enumeration: `/imports` prelude group, `/search` index, `/list` boundaries | index worker + imports renderer (E1/E3) | GREEN — pinned (`repl_introspection` imports/prelude family, `search.rs` Inc2/Inc3 rows) |

Out-of-invariant finding recorded here for routing (NOT part of this matrix's
RED set — parity HOLDS): dotted constructor access `Type.Ctor` in value
position (`Zed.ZedC`, `Wed.WedC`) fails `undefined variable` in EVERY
provenance — same-module, explicit-import, and prelude alike — despite
§8.5.2's "Whenever `Option` is bound in the current scope, `Option.Some` …
accessible as dotted references". Field accessors (`Type.member`) are covered
(`spec_field_accessor.rs`); dotted CTOR references have no coverage and appear
unimplemented. **Triaged: attribution confirmed + row added — see §VI below**
(repro committed by `/testing` 2026-07-12:
`tests/spec_08_modules.rs::dotted_constructor_in_value_position_resolves`).

### II. RED rows — the acceptance spec for the one-function convergence [S109]

> **Status update (2026-07-12, /qa):** the convergence LANDED (both
> `prelude-import-convergence.md` §7 `/dev` change-sets, S108 Inc3) and **ALL
> R1–R8 tests are verified GREEN** by targeted `cargo nextest` run 2026-07-12 —
> including the R2/R5/R7 explicit-arm controls
> (`deftrait_over_explicitly_imported_trait_rejected_neg`,
> `defmacro_over_explicit_import_rejected_neg`,
> `deftrait_method_name_over_explicit_import_rejected_neg`) and both R8 fns.
> The per-row `[S109] — RED at authoring` statuses below are the authoring-time
> record; the rows now stand as `[Tested+Neg]` regression pins guarding the
> convergence.

QA-first: `/testing` authors these RED, failing-not-ignored; they flip GREEN
when the convergence (or per-site fixes) lands. Negatives get their own fns
per the `_neg_`/`_not_` convention. All conflict rows assert BOTH the §8.6.4
diagnostic (substring `conflict`/`ambiguous`/`already`) AND no-effect (the
shadow's exit/value never appears) — the `assert_batch_rejected` /
`assert_repl_rejected` idioms from `spec_08_name_shadowing.rs`.

| Row | Spec citation | Test (proposed) | File | Status | Polarity |
|---|---|---|---|---|---|
| R1 | spec/07-traits.md §7.2.3 (Kind Checking — "An implementation MUST validate that the impl target's type parameter count matches the expected constructor arity") + §7.3.4 (Higher-Kinded Implementation) + spec/08-modules.md §8.8.1 (prelude name in scope on identical terms) — an `(impl HktTrait Zed …)` whose target ADT is PRELUDE-provided MUST get the same arity validation as when `Zed` is explicitly imported; a wrong-arity target MUST be rejected, not silently accepted | `impl_hkt_arity_neg_prelude_provided_target_wrong_arity_rejected` (twin: leg A explicit `(import [prelude [Zed]])` — GREEN control; leg B implicit prelude — RED today) | tests/spec_07_traits.rs | [S109] — RED at authoring; citation corrected §7.5→§7.2.3/§7.3.4 per FIXME 0566 (2026-07-12, matches the test-side `// spec:`). `// defect: class=prelude-scope-miss locus=crates/cranelisp-typecheck/src/traits/impl_check.rs::register_trait_impl (HKT arity gate, lookup_type_def_with_state has no fallback) found=S108 owner=/dev` | negative (silent-accept) + twin positive parity |
| R2 | spec/08-modules.md §8.6.4 (definition-over-name-in-scope, deftrait listed) + §8.8.1 — a `(deftrait Show …)` whose name a loaded prelude provides MUST be the same compile-time error as over an explicit import; the rejected decl has no effect (`Show` keeps resolving to the prelude trait; introspection still describes it) | `deftrait_over_prelude_provided_trait_rejected_neg` (twin: `deftrait_over_explicitly_imported_trait_rejected_neg` — GREEN control, behaviourally rejects today) | tests/spec_08_name_shadowing.rs | [S109] — RED at authoring (silently registers `user/Show` today, probed in REPL + `--run`). `// defect: class=prelude-scope-miss locus=crates/cranelisp-typecheck/src/traits/registry.rs::register_trait_decl (lookup_trait_decl_with_state is current-module-only; TopLevel::TraitDecl skips reject_def_over_binding) found=S108 owner=/dev` | negative |
| R3 | spec/08-modules.md §8.6.4 — mode parity for R2: the deftrait-over-prelude rejection MUST be identical in REPL, `--run`, `--link` (the §8.6.4 all-modes MUST) | `deftrait_over_prelude_mode_parity_all_modes` (one binding set, three legs — the `mode_parity_def_over_import_same_rejection_all_modes` shape) | tests/spec_08_name_shadowing.rs | [S109] — RED (all three legs accept today; the gap is mode-uniform, so this pins parity through the fix) | negative |
| R4 | spec/08-modules.md §8.6.4 (defmacro listed as a definition form) + §8.8.1 — a `(defmacro gulp …)` over a PRELUDE-provided `gulp` MUST be rejected; today it is silently accepted and the macro WINS at expansion | `defmacro_over_prelude_provided_name_rejected_neg` | tests/spec_08_name_shadowing.rs | [S109] — RED. `// defect: class=silent-accept locus=src/expander.rs (macro registration never consults the §8.6.4 reject_def_over_binding seam) found=S108 owner=/dev` | negative |
| R5 | spec/08-modules.md §8.6.4 — same for the EXPLICIT-import arm: `(import [prelude [gulp]])` + `(defmacro gulp …)` MUST be rejected; today accepted (defmacro misses the seam on BOTH arms, not just the prelude one) | `defmacro_over_explicit_import_rejected_neg` | tests/spec_08_name_shadowing.rs | [S109] — RED. same `// defect:` line as R4 | negative |
| R6 | spec/08-modules.md §8.6.4 — a `deftrait` METHOD name contesting an in-scope name is a definition over a name in scope (a trait method is a fresh module-scope binding with a fresh terminal; it can never dedup): `(deftrait Zork (gulp …))` under a prelude providing `gulp` MUST be rejected | `deftrait_method_name_over_prelude_provided_name_rejected_neg` | tests/spec_08_name_shadowing.rs | [S109] — RED. `// defect: class=silent-accept locus=crates/cranelisp-typecheck/src/traits/registry.rs::register_trait_method (no §8.6.4 seam) found=S108 owner=/dev` | negative |
| R7 | spec/08-modules.md §8.6.4 — the explicit-import arm of R6: `(import [prelude [gulp]])` + `(deftrait Zork (gulp …))` MUST be rejected; today accepted (both arms miss) | `deftrait_method_name_over_explicit_import_rejected_neg` | tests/spec_08_name_shadowing.rs | [S109] — RED. same `// defect:` line as R6 | negative |
| R8 | spec/08-modules.md §8.6.4 (order-independence, symmetric direction) — an `import`/`export` whose bare name is already bound by a local `deftrait` or `defmacro` MUST be rejected symmetrically (the later-arriving form is the rejected one) | `import_over_local_deftrait_rejected_neg`, `import_over_local_defmacro_rejected_neg` | tests/spec_08_name_shadowing.rs | [S109] — probe at authoring; expected RED (the 0516 import-side predicate reads `Def` entries; trait/macro bindings likely invisible to it). If GREEN, keep as pins | negative |

**Diagnostic note (SHOULD-level, ride-along, not a row):** the R2 explicit-arm
control rejects with `trait Show already defined` — behaviourally correct but
the wrong diagnostic class (§8.6.4 SHOULD name the conflict's provenance and
remediations, as the landed `definition of 'gulp' conflicts with 'gulp' already
in scope via the implicit prelude …` wording does). Fold the wording into the
R2 fix; do not gate on it.

### III. GREEN rows — parity pins to author (thin, twin-shaped) [S109]

Expected GREEN at authoring (probed 2026-07-12); they exist to make the NEXT
forgotten-fallback site fail loudly and to guard the convergence refactor
(behaviour preservation). Cheapest shape: one twin fn per row.

| Row | Spec citation | Test (proposed) | File | Status |
|---|---|---|---|---|
| G1 | spec/08-modules.md §8.6.4 (same-terminal dedup) + §8.8.1 — an explicit `(import [primitives [add-i64]])` while the implicit prelude re-exports the SAME terminal `primitives/add-i64` MUST dedup silently (no false collision, name resolves) | `prelude_and_explicit_import_same_terminal_dedup` | tests/spec_08_prelude_outer_scope.rs | [S109] — expected GREEN |
| G2 | spec/08-modules.md §8.8.1 + §3 (annotations) — a `:Zed` param/return annotation naming a prelude-provided type typechecks identically to the explicit-import twin | `type_annotation_prelude_provided_type_twin` | tests/spec_08_prelude_outer_scope.rs | [S109] — expected GREEN |
| G3 | spec/08-modules.md §8.8.1 + §5.2 (deftype fields) — a deftype field `[:Zed z]` naming a prelude-provided type registers identically to the explicit-import twin | `deftype_field_type_prelude_provided_twin` | tests/spec_08_prelude_outer_scope.rs | [S109] — expected GREEN |
| G4 | spec/08-modules.md §8.8.1 + §6 (patterns) — a prelude-provided ctor works in VALUE and PATTERN position (`(match (ZedC 7) [(ZedC n) n])`) identically to the explicit-import twin | `ctor_value_and_pattern_position_prelude_provided_twin` | tests/spec_08_prelude_outer_scope.rs | [S109] — expected GREEN |
| G5 | spec/09-macros.md + spec/08-modules.md §8.8.1 — a prelude-DEFINED macro expands bare in a consuming module identically to the explicit-import twin (`/testing`: verify `s76_macro_availability.rs` first; add the twin only if the implicit-prelude leg is missing there) | `prelude_provided_macro_expands_bare_twin` | tests/s76_macro_availability.rs | [S109] — expected GREEN (verify-first) |
| G6 | spec/08-modules.md §8.8.1 + design/typecheck/monomorphisation.md — a POLYMORPHIC prelude-provided fn called at a concrete type from user code monomorphises through the fallback-aware mono-collection chokepoint (program.rs 0488 sites) identically to the explicit-import twin | `prelude_provided_polymorphic_fn_monomorphises_twin` | tests/generic_value_use_mono.rs | [S109] — expected GREEN (verify existing coverage first; the 0488 fix comment names an explicit-import control) |
| G7 | spec/08-modules.md §8.6.4 — the `deftype` leg of def-over-prelude: `(deftype Zed …)` over a prelude-provided TYPE name is rejected with the §8.6.4 diagnostic (only the `defn` leg is pinned today) | `deftype_over_prelude_provided_type_rejected_neg` | tests/spec_08_name_shadowing.rs | [S109] — expected GREEN (probed) |
| G8 | spec/08-modules.md §8.6.4 + §8.7.2 — the PRIVATE variant: `(defn- gulp …)` over a prelude-provided name is the same rejection (visibility of the definition does not exempt it) | `private_defn_over_prelude_provided_name_rejected_neg` | tests/spec_08_name_shadowing.rs | [S109] — expected GREEN (probed; exact §8.6.4 diagnostic observed) |

### IV. Structural acceptance criterion (for the `/arch` convergence ruling)

The RED set (R1–R8) flipping GREEN is the *behavioural* acceptance. The
*structural* acceptance is: **after the convergence, no `_or_prelude` variant
should be NEEDED** — one resolution primitive in which the prelude fallback is
intrinsic (applied inside the single lookup, not opted into per call site), so
a new resolution site CANNOT forget it. Corollaries the ruling must cover:

1. **Exactly two semantic operations exist**, and BOTH consult the prelude:
   *resolve-a-reference* (fallback intrinsic), and *may-this-name-be-defined*
   (the §8.6.4 seam — derived FROM the same resolution primitive, as
   `reject_def_over_binding` already does, with home==current ⇒ redefinition
   allowed). The rule of thumb currently recorded in
   `crates/cranelisp-typecheck/CLAUDE.md` ("pick the fallback variant for a
   *reference*, the non-fallback variant to decide whether a name is *free*" —
   the rationale defending the deftrait shadow) is WRONG under the settled
   spec and is exactly what produced S14: a name is NOT free merely because it
   is prelude-provided. The idempotent-retry duplicate check (same-module
   re-registration) is the only legitimate current-module-only probe, and it
   is a different question from name-freedom.
2. Every definition form — `defn`, `def`, `deftype`, `deftrait` (trait name
   AND method names), `defmacro`, private `-` variants — routes through the
   ONE §8.6.4 seam. S14/S15/S16 exist because three forms bypass it.
3. The ~93-site `prelude_fallback` bit threading collapses to the gate inside
   the primitive (`prelude_fallback_target` consulted once, in one place).
4. The I-1 public-only head filter and the terminal-source dedup/poison
   comparison live inside the primitive, not at call sites.
5. `lookup_type_def_with_state`-shaped non-fallback lookups are deleted or
   renamed so they cannot be mistaken for reference resolution (S8's cause).

Mechanical check for `/review` at convergence time: `grep -rn "_or_prelude\|prelude_fallback" crates/ src/`
should reduce to the primitive's own definition + the single gate + tests.

### V. Existing-pin upkeep (route to `/testing`, same change-set as authoring)

Stale framing found while verifying status (all named tests PASS on HEAD,
2026-07-12): `tests/spec_08_name_shadowing.rs` and
`tests/spec_08_prelude_outer_scope.rs` headers + per-test comments still carry
present-tense "RED signal (FIXME 0514/0515/0516) … fails today against
`e1fe4a8`" classifications and cite the retired `tests/plan/ledger.md` — the
0514/0516 fixes have landed and all 33 tests are GREEN. Per the `// defect:`
rules ("a GREEN repro carrying present-tense DEFECT framing lets a future
regression pose as a known guard"), strip the stale RED/ledger framing to past
tense and add the missing `// defect:` lines (class=`mode-divergence` for the
0514 batch-arm rows, class=`prelude-scope-miss` for the prelude-arm rows,
`owner=/dev found=S102`). Same cleanup for the three S108 introspection pins
(`bare_prelude_globbed_trait_lookup_shows_defn_and_impl_sections`,
`type_impl_section_includes_prelude_globbed_trait_impls_probe`,
`impl_of_prelude_globbed_trait_resolves_trait_name` — all GREEN; keep the
`// defect:` lines, convert prose to past tense). FIXME 0558 is dispositioned:
repro + fix both landed (deleted by /qa 2026-07-12, this section is the
durable record).

### VI. Out-of-invariant: dotted constructor in value position (§8.5.2) — attribution confirmed (2026-07-12, /qa)

| Spec citation | Test | File | Status | Polarity / provenance |
|---|---|---|---|---|
| spec/08-modules.md §8.5.2 (Dotted Names) — a dotted constructor reference `Type.Ctor` in VALUE position MUST resolve whenever the parent type is in bare scope, first-class like the dotted field accessor `Box.v` (which resolves; the bare ctor `Red` also resolves, and display already prints the canonical `Color.Red` form the resolver rejects as input) | `dotted_constructor_in_value_position_resolves` | tests/spec_08_modules.rs | [S109] — RED, failing-not-ignored known-defect guard (committed 2026-07-12). `// defect: class=enumeration-miss locus=crates/cranelisp-typecheck/src/checker.rs::resolve_dotted_field_accessor found=S108 owner=/dev` (locus corrected by /qa attribution — `/testing` to update the test-side line, which currently carries a free-text spaced locus that breaks the `grep -o "locus=[^ ]*"` recipe) | positive (mode-independent; nullary and applied ctors alike) |

**Attribution (confirmed by code-read, 2026-07-12): TYPECHECK — the alternate
frontend attribution is exonerated.** The reader
(`crates/cranelisp-frontend/src/reader.rs::read_dotted_symbol`) delivers
`Color.Red` and `Box.v` IDENTICALLY as a single dotted-symbol `Expr::Var` — no
desugaring, no ctor/field distinction, so the divergence cannot be frontend.
The split happens in `crates/cranelisp-typecheck/src/checker.rs::lookup` →
`resolve_dotted_field_accessor` (checker.rs ~1404): it probes the type's home
module for a **canonical `Type.member`-KEYED entry** and accepts it only when
`adt::committed_accessor_kind` classifies it `Concrete(fqtn)`. Field accessors
HAVE such an entry (adt.rs ~599 registers the canonical `Type.field`-keyed
accessor `Def` beside the bare alias); constructors register under the BARE
ctor name only (adt.rs ~382, `register_constructors`) — the probe misses, and
the accessor-kind gate would reject a `DefKind::Constructor` anyway. So the
dotted-member value resolver enumerates field accessors and OMITS constructors:
`enumeration-miss`, member-set edition.

**Fix shape (determined by the code-read; one crate, two seams):** (1) adt.rs
registers a canonical `Type.Ctor`-keyed entry per constructor (mirroring the
accessor canonical-key model; new entries are data, not a serde-shape change —
no `CACHE_SCHEMA_VERSION` bump expected); (2) `resolve_dotted_field_accessor`
(renamed to a dotted-MEMBER resolver) accepts a
`DefKind::Constructor { type_name == fqtn }` arm. **The registration half is
load-bearing, not optional**: backend GOT resolution
(`crates/cranelisp-backend/src/compiler/resolution.rs::resolve_driven`) is
entry-keyed by name — `Box.v` reaches codegen only because a `Box.v`-keyed Def
exists in the home module; a resolver-only typecheck fix would typecheck the
reference and then fail at codegen.

**Fix-now-vs-carry verdict (to `/sprint`): CARRY.** This is NOT a small
member-set enumeration extension — it is a registration-model extension (every
constructor of every deftype gains a second symbol-table entry) plus the
resolver arm, with enumeration/display ripple to sweep (`/list` boundaries,
`/search` index, importable sets now see `Type.Ctor` keys — exactly the
definition-variants lens). One narrow `/dev` (typecheck) dispatch, but wrong to
squeeze into increment close; schedule early S109 beside the matrix follow-ups.
The committed failing-not-ignored guard is the durable record meanwhile.
Follow-ups for `/testing` at fix time: CALL-position (`(Opt.Some 3)`) and
prelude/import-provenance twins for the dotted-ctor leg, per the
definition-variants lens.

### VII. Coverage-process lesson (S108 Inc3): "in-scope via prelude" controls derive from a PUBLIC re-export

During the `/search` I-1 visibility fix, the Wave-B control
`tests/search.rs::search_loaded_module_in_scope_exact_match_still_marked_not_imported_neg`
was found to have derived its "in-scope" symbol from a PRIVATE prelude
`(import [foo [other]])` — which per §8.8.1 does NOT put a name in downstream
scope (only the prelude's PUBLIC/exported names are provided). The control
passed only while the pre-fix private-prelude leak existed; the I-1 fix
(correctly stopping the leakage) turned it RED, and it was re-baselined to
`(export [foo [other]])`.

**Standing rule for control construction:** an "in-scope via prelude" test
control MUST derive its scope-membership from a PUBLIC prelude re-export
(`export`), never a private prelude `import` — the two provenances differ by
exactly the §8.4.0 visibility flag that governs downstream scope (§8.8.1), so
a control that conflates them passes only while a visibility leak exists.
This is a concrete cell in the standing "coverage by definition variants"
lens (`tests/CLAUDE.md`): provenance axis — explicit-import vs
implicit-prelude, × public vs private. The re-baselined test above is the
worked example. (The E3 fixture recipe in §"Sprint 108 Increment 3" describing
`(import [foo [other]])` is superseded by this re-baseline.)

## Sprint 109 — sprint-wide failing-test plan (Phase-3 exit gate, 2026-07-13, /qa)

The QA-first drafting spec for `/testing` (Phase 5 authors to THIS plan before
any per-crate D/D/R begins). Scope: `sprints/SPRINT.md` all six buckets. Spec
contracts: `spec/08-modules.md` §8.5.2/§8.5.4/§8.6.5/§8.2.3;
`spec/06-pattern-matching.md` §6.2.1/§6.2.2/§6.2.4; `spec/04-expressions.md`
§4.5; `spec/05-definitions.md` §5.1.2; `repl/spec.md` §1.1/§1.5/§17.2.1/
§17.19.2(+a,b)/§17.20.3a–c. Design contracts:
`design/typecheck/dotted-ctor-registration.md` (§4 blast radius),
`design/arch/dotted-ctor-canonical-keys.md` (Obligations A/B).

Discipline reminders binding on this plan: REDs are failing-not-ignored;
every fix pairs a `/dev` unit test in the same change-set (METHOD §2.2); every
deferral to unit tier below ENUMERATES its cases (S108 Inc2 lesson — a bare
"unit-pinned" is a hole); fixtures are stdlib-free (own modules composed into
the tmpdir via `.file()`; `PreludeVariant::None`/`PrimitivesOnly` unless a row
says otherwise); language-semantics rows run through all modes via
`run_through_all_modes`. Spec-side `[S109]` tags flip to `[Tested …]` by `/qa`
at Phase 6/7, never at drafting.

**Vocabulary addition (this pass, /qa):** `class=check-gate-leak` added to the
controlled `// defect:` vocabulary in `tests/CLAUDE.md` — a source-level fault
that typecheck must decide (resolve or reject check-side) leaks past the check
boundary and surfaces as a codegen/backend-layer error (the 0571 D1 shape).
Distinct from `silent-accept` (nothing raised) and `error-swallow` (raised then
dropped): here the wrong LAYER raises.

> **REVISED at the W1 re-ruling (2026-07-13, /qa; second vocabulary addition:
> `class=resolver-mirror`).** After the W1.1a landing/revert (73 regressions;
> `design/arch/dotted-ctor-canonical-keys.md` REVISED — user-ruled COORDINATE)
> and the landed §6.2.1/§6.2.2 **scrutinee-directed** bare-pattern rule:
> DC-11 added (determined-scrutinee bare pattern RESOLVES), DC-5 reframed
> (poison only on an indeterminate scrutinee), the §D fixture constraint added
> (no free-type-var param annotations — the live W6 defect), §D.1 acceptance
> negatives AN-1…AN-5 added (the 73-regression classes as guards; AN-2/AN-5
> are pre-existing-defect repros owed RED ahead of the wave), §D.2 records the
> two-commit acceptance structure (commit-1 reader-widening holds the 25-fail
> baseline; commit-2 writer-flip + cache 16→17 flips the DC/BR REDs), and §L
> adds the W6 annotation-resolution matrix.
>
> **REVISED again at W1.2 (arch §10 Blocker ruling, commit `d45e2cee`):** §D.3
> adds the tag-order class — DC-12 (differing-layout twins, both source
> orders), DC-13 (the `xmod.cl` cross-module nondeterminism guard, exit 1/7/7
> today), BU-1/BU-2 (`/dev` backend unit pins: loud-miss + I-1 spark
> exclusion), DC-14 (cache 17→18). The committed DC-11/DC-6 greens are
> tag-layout coincidences; `/review` re-checks them against DC-12, not the
> coincident fixtures.

### Risk read (summary; full entries in `risks.md` §"S109 risk read")

Highest-silent-failure changes this sprint, in order: (1) the **C-class
in-flight race** (auto-load member-probe against a non-terminal module) —
nondeterministic, invisible to single runs, and the forbidden-disposition rules
make any intermittent RED a real bug by definition; (2) the **two blast-radius
sites** `/design` pre-flagged (exhaustiveness `.`-strip; IO-internal-ctor
exclusion) — both fail SILENTLY on revert (false non-exhaustive blocks valid
code; internal-exclusion loss forces users to match `Bind`/`Pure`/`Effect`),
so both get fail-on-revert guards in the registration change-set; (3) the
**cache-schema 16→17** key-meaning change — a stale `.meta.json` read by the
canonical-key resolver silently misses ctor `Def`s and mis-classifies heap
categories (a UAF class per the arch note); (4) **0573 product persistence** —
silent data loss, observable only at reload. Arch-pre-flagged boundaries and
spec MUSTs are authored FIRST (before happy paths), per the S108 Inc2 rule.

### A. §8.5.4 Auto-loading — the ten-edge MUST list (file: `tests/spec_08_modules.rs` unless noted)

Every edge is a row; every row carries its negative. Edge 1 (all modes ×
positions × kinds) is expanded as matrix M2 (§H); rows AL-2…AL-10 cover edges
2–10. Arch's 0571 A/B rows fold in where they coincide (noted).

| Row | Edge / arch id | Spec citation | Test (proposed) | Status | Polarity |
|---|---|---|---|---|---|
| AL-1 | 1 / A1–A4 | §8.5.4 edge 1 — all modes, positions, kinds | matrix M2 cells (§H): `fq_call_position_autoloads_all_modes` (A1, `run_through_all_modes`), `fq_value_position_ref_call_through_let` (A2), `fq_macro_ref_expands_at_qualified_site` (A3, §9.3.6), `fq_type_annotation_triggers_autoload` (A4) | [S109] — A1/A3 mostly GREEN today per arch verification; A2/A4 verify-first | pos + M2 neg column |
| AL-2 | 2 | §8.5.4 edge 2 — absolute path, same resolution as `import` | `fq_ref_autoloads_absolute_module_path` (file-backed fixture module, no import); neg `autoload_neg_no_phantom_child_from_bare_qualifier` (undeclared child dir `main/util.cl` NOT invented from bare `util/helper`; error at reference site) | [S109] | pos+neg |
| AL-3 | 3 / B1 | §8.5.4 edge 3 — file not found ⇒ compile error AT REFERENCE SITE, names both modules, resolution-layer | `fq_ref_missing_module_errors_at_reference_site` — **span-pinned** (reference-site span, not `0..0`; RED until the span fix); neg facet: output does NOT contain `undefined variable` or a codegen-layer frame | [S109] — RED (span + wrapping today) | pos+neg |
| AL-4 | 4 / B2 | §8.5.4 edge 4 — "module *X* has no member *Y*", order-independent | `fq_ref_member_absent_names_module_and_member`; neg `fq_ref_member_absent_error_identical_when_preloaded_neg` (twin: auto-loaded leg vs explicitly-imported-first leg, byte-same error class) | [S109] | pos+neg |
| AL-5 | 5 / B3 | §8.5.4 edge 5 — dep compile failure ⇒ chained diagnostic; REPL survives | `fq_ref_dep_compile_error_chained_diagnostic` (names failed module + underlying error); neg `fq_ref_dep_compile_error_repl_survives_to_next_prompt_neg` (follow-on `(add-i64 1 2)` still evaluates) | [S109] — RED expected (chaining) | pos+neg |
| AL-6 | 6 / B4+B5 | §8.5.4 edge 6 — cycle ⇒ circular-dependency error NAMING THE PATH; no deadlock; never "undefined variable" | `fq_ref_cycle_reports_circular_dependency_path` (**B4 — RED today**, misattribution); `fq_ref_mixed_cycle_import_plus_fq_reports_cycle` (B5: A imports B, B FQ-refs A); neg facets: harness timeout = deadlock failure; assert NOT `undefined variable` | [S109] — B4 RED | pos+neg |
| AL-7 | 7 / C1 | §8.5.4 edge 7 — in-flight atomicity | §C below (the e2e-vs-unit enumeration) | [S109] | pos+neg |
| AL-8 | 8 / A7 | §8.5.4 edge 8 — idempotence, at-most-once load, cache MAY satisfy | `fq_ref_second_reference_no_reload` (`CRANELISP_MODULE_TRACE=1`: one load event); `fq_ref_resolves_from_warm_cache` (cache.rs — cache-hit leg) | [S109] | pos+neg (`_no_reload` IS the neg) |
| AL-9 | 9 | §8.5.4 edge 9 — visibility unchanged; private member via FQ ref is a compile error (§8.6.6) | `fq_ref_private_member_rejected_neg` (`defn-` in target); pos twin `fq_ref_public_member_resolves` | [S109] | pos+neg |
| AL-10 | 10 | §8.5.4 edge 10 — no scope pollution: no bare bindings, no §8.6.5 ambiguity introduced | `autoload_neg_installs_no_bare_bindings` (after `(mathx/square 3)`, bare `square` unresolved); `autoload_neg_no_ambiguity_with_local_def` (local `(defn square …)` after the FQ ref is NOT a conflict) | [S109] | neg (two fns) |
| AL-11 | (chain) / A5 | §8.5.4 edges 1+8 composed — chain depth ≥3 parks/resumes | `fq_ref_chain_depth_three_resumes` (A FQ-refs B, B FQ-refs C; correct value) | [S109] | pos |
| AL-12 | (diamond) / A6 | §8.5.4 edges 7+8 composed — diamond, C loads once, both resume | `fq_ref_diamond_loads_once_both_resume` (root refs A and B, both FQ-ref C; module trace: C loaded once) | [S109] | pos+neg (load-count) |

### B. 0571 failure-mode + defect-class rows (arch A/B/C/D fold-in)

A-capability rows are AL-1/AL-11/AL-12 above; B-failure rows are AL-3/4/5/6.
The D rows below are the actual 0571 defect class:

| Row | Arch id | Citation | Test (proposed) | File | Status | Polarity |
|---|---|---|---|---|---|---|
| FQ-D1 | D1 | §8.5.4 edge 1 + spec/03-types.md §3.11 — value-position FQ ref to a GENERIC fn concretely used (`(let [f mathx/gcount] (f [1 2 3]))`) MUST either resolve check-side (mono minted at the inferred concrete type) or die check-side with an actionable §3.11-style annotation-required error — NEVER a codegen-layer error | `fq_value_ref_generic_fn_concrete_use_never_reaches_codegen` | tests/spec_08_modules.rs | **[S109] — RED, THE failing-not-ignored repro `/testing` owes.** `// defect: class=check-gate-leak locus=crates/cranelisp-typecheck (value-position ref to slot-less Polymorphic template never mints a mono; leaks to backend/literals.rs) found=S108 owner=/dev` | pos-or-error + neg (no codegen frame) |
| FQ-D2 | D2 | repl/spec.md §1.5/§1.5.1 + §8.5.4 — bare REPL FQ ref displays via the SAME introspection path a bare imported name uses; no codegen forced | `fq_bare_display_parity_with_imported_introspection` (twin: `mathx/gcount` bare vs `(import …)` + `gcount` bare — same envelope) | tests/repl_introspection.rs | [S109] | pos (twin parity) |
| FQ-D3 | D3 | §8.5.4 edge 3 ("MUST NOT surface as a codegen-layer leak") — NEGATIVE sweep | `fq_ref_neg_no_doubly_wrapped_codegen_error` — dedicated fn PLUS a shared assertion helper applied across every AL/FQ fixture: output NEVER matches the doubly-wrapped `codegen error … codegen failed for /` shape | tests/spec_08_modules.rs | [S109] | neg |
| FQ-D4 | D4 | §8.5.4 edge 10 + §8.6.4 order-independence — import-invariance | `fq_ref_import_invariance_twin` — same program ± a prior `(import …)` behaves identically (value AND diagnostic legs) | tests/spec_08_modules.rs | [S109] | pos (twin) + neg (diagnostic leg) |

### C. C-class — the in-flight race: e2e-vs-unit enumerated per case (edge 7)

Deterministic e2e forcing of the "member-probe arrives while the module is
in-flight" interleaving is **unattainable** today (no scheduler-pause test
hook; adding one is not warranted while the unit arms below hold). The split,
per case — neither tier substitutes for the other:

1. **C1-e2e (owner `/testing`, e2e tier — the confidence sweep, probabilistic
   detection, deterministic guard value under repetition):**
   `autoload_diamond_race_under_load_repeated` — `--run` with
   `--priority-workers 4`; root imports A and B (the import wave puts both
   in-flight); A FQ-refs B in a top-level form. **Repeat ≥25 process spawns in
   one test fn**; EVERY iteration asserts exit 0 + the correct value, and
   NEVER `has no member` (the racy misclassification). File:
   `tests/spec_08_modules.rs`. A single failing iteration is a real bug —
   forbidden dispositions (`flaky`/`timing-sensitive`) apply in full.
2. **C1-unit (owner `/dev` int/`src`, the deterministic guard — arch's
   scheduler-seam fallback, ENUMERATED):** the int gap-arm decision logic gets
   four unit pins, each failing on revert of its arm:
   (i) module ABSENT from map → load + park;
   (ii) module PRESENT but NON-TERMINAL → **PARK, not err** (the race cure);
   (iii) TERMINAL + member present → resolve;
   (iv) TERMINAL + member absent → "module X has no member Y".
3. **C1-tc-unit (owner `/dev` typecheck):** `resolve_qualified`'s
   member-absent arm yields the gap **unconditionally** (typecheck stays
   scheduler-free; INT decides) — one unit pin: a present-but-non-terminal
   module's member probe emits a gap, never the member-absent diagnostic.
4. **C2 (deterministic e2e):** the mixed cycle AL-6 `…mixed_cycle…` row — the
   import edge forces the ordering, so this cycle leg IS deterministic.

`/dev` + `/review` confirm each enumerated unit case has a fail-on-revert
guard (S108 Inc2 enumerated-deferral rule).

### D. Dotted-`Type.Ctor` capability — twins + blast-radius fail-on-revert guards

| Row | Citation | Test (proposed) | File | Status | Polarity |
|---|---|---|---|---|---|
| DC-1 | §8.5.2 | `dotted_constructor_in_value_position_resolves` — the committed RED (§VI above) **flips GREEN** at the registration change; row then reads `[Tested]` | tests/spec_08_modules.rs | [S109] — RED today (committed 2026-07-12) | pos |
| DC-2 | §8.5.2/§8.6.5 | `same_named_ctors_dotted_value_position_both_resolve` — two in-scope types sharing `Some`; `Maybe.Some`/`Option.Some` both resolve (applied) + `Maybe.None`/`Option.None` (nullary) | tests/spec_08_modules.rs | [S109] — RED | pos |
| DC-3 | §8.6.5 + §6.2.1 unifying rule ("in **value** position there is no context, so a contested bare constructor always poisons") | `same_named_ctors_bare_value_poisoned_lists_alternatives_neg` — bare `Some` in VALUE position is a compile error LISTING `Maybe.Some` and `Option.Some`; **0568 facet: the diagnostic MUST NOT contain the internal `__expr` binder**. This is the "no context" arm of the DC-3/DC-11 unifying-rule pair | tests/spec_08_modules.rs | [S109] — RED | neg |
| DC-4 | §6.2.1/§6.2.2 ("the dotted form **always resolves regardless of scrutinee type**") | `same_named_ctors_dotted_pattern_position_disambiguates` — `(Maybe.Some x)` binds positionally; dotted nullary `Maybe.None` arm matches; exhaustiveness + field-binding arity computed against the type the dotted ctor names. Dotted is never contingent on the scrutinee | tests/spec_06_pattern_matching.rs | [S109] — RED | pos |
| DC-11 | §6.2.1/§6.2.2 **scrutinee-directed (W1 re-ruling, landed)** — a contested BARE constructor pattern RESOLVES against a determined scrutinee type | `contested_bare_pattern_resolves_against_determined_scrutinee` — `(match m [(Some x) …])` with `m : Maybe` determined (concretely constructed, or concrete-annotated — NO free-var annotation, see fixture constraint below) resolves bare `(Some x)` to `Maybe.Some`; nullary leg: a bare `None` arm resolves to `Maybe.None`. **REPLACES the pre-re-ruling expectation that a contested bare pattern requires the dotted form.** DC-3 (value: always poisons) + DC-11 (pattern: resolves when determined) pin the one-rule-two-contexts framing together | tests/spec_06_pattern_matching.rs | [S109] — RED | pos |
| DC-5 | §6.2.1 + §8.6.5 — poisoned **ONLY when the scrutinee type cannot disambiguate** | **REFRAMED (W1 re-ruling):** `contested_bare_pattern_indeterminate_scrutinee_poisoned_neg` — an INDETERMINATE scrutinee (per the landed §6.2.1 wording: an unannotated-lambda-parameter scrutinee with no other constraint) with a contested bare `(Some x)` is a compile error listing the canonical alternatives; in-test control: the same match written dotted compiles. The negative targets the indeterminate-scrutinee case ONLY — a determined-scrutinee bare pattern is DC-11's positive, never a poison | tests/spec_06_pattern_matching.rs | [S109] — RED | neg |
| DC-6 | §8.5.2 + §8.6.5 (import shapes) | `same_named_ctors_define_plus_import_twin`, `same_named_ctors_import_plus_import_twin` — SAME assertions as DC-2/DC-3 with provenance varied (local `deftype` + imported type; two imported types). The twin fixture: a provenance that grew its own codepath diverges the twins | tests/spec_08_modules.rs | [S109] — RED | pos+neg per twin |
| DC-7 | §8.5.2 product corner | `product_ctor_dotted_form_does_not_resolve_neg` — `Point.Point` does not resolve; bare `Point` does; NO spurious poison (bare `Point` stays usable) | tests/spec_08_modules.rs | [S109] | neg+pos |
| DC-8 | §8.5.2 first-class MAY | `dotted_ctor_passed_as_argument_and_let_bound` — `(let [f Maybe.Some] (f 3))` | tests/spec_08_modules.rs | [S109] | pos |
| DC-9 | Obligations A/B (`dotted-ctor-canonical-keys.md`) | `dotted_ctor_resolves_from_warm_cache` — cold run then warm run, identical result (guards the canonical-key/`type_ctor_names` round-trip through `.meta.json`); neg: a pre-bump cache is invalidated, not silently mis-read (version-bump behaviour) | tests/cache.rs | [S109] | pos+neg |
| **BR-1** | §6.5 exhaustiveness × the `.`-strip (design §4.1 — **arch-pre-flagged, author FIRST**) | `match_over_dotted_covered_ctor_not_false_nonexhaustive_neg` — a TOTAL match written with dotted arms (`(Maybe.Some x)` / `Maybe.None`) compiles with NO "non-exhaustive" diagnostic. **FAILS if the covered-set normalizer's `.`-strip regresses** | tests/spec_06_pattern_matching.rs | [S109] — RED until the change-set lands (dotted patterns don't resolve yet); permanent fail-on-revert guard after | neg |
| **BR-2** | §6.5 × internal-ctor exclusion (design §4.2 — **arch-pre-flagged, author FIRST**) | e2e: a user `match` over an IO-typed value covering only its public surface compiles WITHOUT "non-exhaustive: missing `Bind`/`Pure`/`Effect`" (`io_internal_ctors_stay_excluded_from_exhaustiveness_neg`, tests/spec_10_io.rs — `/testing` verifies the IO-match idiom is expressible e2e). **Enumerated unit fallback if not** (`/dev` typecheck, fail-on-revert): the per-ctor `internal` flag read chain-follows the bare alias to the terminal ctor `Def` — asserts `internal == true` for `Bind`/`Pure`/`Effect` AFTER the bare key becomes an alias | tests/spec_10_io.rs (or enumerated unit) | [S109] | neg |
| DC-10 | repl/spec.md §17.19.2b (+§3.3/§3.5) | `search_lists_constructor_once_canonical_form` + `search_neg_no_bare_duplicate_ctor_row`; `/list` + `/exports` twins (`list_shows_ctor_once_canonical`, `exports_show_ctor_once_canonical`) — the bare alias is never a second row | tests/search.rs, tests/repl_introspection.rs | [S109] — `/testing` twin owed (design §6 display row; couples 0572/E4) | pos+neg |

**Fixture constraint (W1 re-ruling; unblocks DC-2/DC-5/BR-1 from the W6
defect).** Fixtures for the DC/BR rows MUST NOT use a **free type variable in a
`defn`/`fn` parameter annotation** (`:(Maybe a) m`, `:a x`) — that hits the
separate, live W6 poly-annotation defect (`unknown type 'a'`, verified live)
and would make these rows RED for the WRONG reason. Use **concrete types or
inference** instead: `deftype` type parameters are fine (`(deftype (Maybe a)
MNone (MSome [:a v]))` works), so determine the scrutinee/value by concrete
construction (`(Maybe.Some 5)` / `(MSome 5)`), by a concrete-application
annotation (`:(Maybe Int) m`), or by inference from a constructed value.
Dotted-ctor coverage is unchanged by this constraint — resolution is about
ctor-name keying, not type parameters. The poly-annotation defect gets its OWN
coverage in §L (the W6 matrix).

#### D.1 W1 coordinate acceptance negatives (arch re-ruling §5 — the 73-regression classes as guards)

`design/arch/dotted-ctor-canonical-keys.md` §3/§5: the first W1.1a landing
flipped the writers without the readers — 73 regressions, classes empirically
pinned. Each class below becomes a permanent guard. AN-1/3/4 are
**behaviour-invariance pins** (GREEN today, authored BEFORE the wave; they must
still pass after commit-1 AND commit-2 — they are the writer-flip's acceptance
negatives). AN-2/AN-5 are **pre-existing defects W1 incidentally fixes** —
failing-not-ignored repros owed AHEAD of the wave, flipping GREEN at commit-1.

| Row | Regression class (arch §5) | Citation | Test (proposed) | File | Status | Polarity |
|---|---|---|---|---|---|---|
| AN-1 | (B) prelude cascade — the `collections.list.test` one-hop miss took down `do`/`pure`/`cond`/`when`/`case`/`vec`/`list`/`def` | spec/08 §8.6.2 (chain-follow to terminal) + root CLAUDE.md stdlib-separation exception | Two guards: (a) free-standing ROOT-CAUSE twin — a fixture prelude module with a `(mod test)` submodule whose test file `match`es an imported bare nullary ctor, then the prelude's LATER export lines must still install (`prelude_module_with_ctor_matching_submodule_still_exports_all`); (b) stdlib-prelude availability smoke via the gated `use_workspace_stdlib_for_stdlib_conformance_only()` entry — each of `do`/`pure`/`cond`/`when`/`case`/`vec`/`list`/`def` evaluates (`workspace_prelude_core_names_all_available`) | (a) tests/spec_08_modules.rs, (b) tests/spec_11_stdlib.rs | [S109] — GREEN today; invariance pin + commit-2 acceptance | neg (cascade absence) |
| AN-2 | (D) cross-module nullary-ctor SOUNDNESS — the silent wrong-value class: `lookup_constructor`'s one-hop miss falls through to the fn-as-value closure wrap; tag comparison against a heap pointer → runtime "match failed" | spec/06 §6.3 + spec/08 §8.6.2; arch §3.1 (two backend resolvers disagreeing on one name) | `imported_bare_nullary_ctor_match_compiles_to_tag_not_closure` — import a bare nullary ctor (`Red`) cross-module (include a re-export hop so the chain is ≥2 hops), `match` on it, assert the CORRECT arm value (the wrong-value/`match failed` shape is the neg facet). **The failing-not-ignored repro arch found is OWED** | tests/spec_08_modules.rs | **[S109] — RED ahead of the wave (pre-existing, silent); flips GREEN at commit-1** (`lookup_constructor` collapses onto `resolve_driven`). `// defect: class=resolver-mirror locus=cranelisp-backend/src/compiler/context.rs::lookup_constructor (one-hop copy vs resolve_driven multi-hop — two resolvers, one name) found=S109 owner=/dev` | pos+neg (soundness) |
| AN-3 | (C) display — data ctor values rendered with fields DROPPED (`(Cons 2 …)` → bare `Lst.Cons`) | repl/spec.md §1.5 (data ctor display row) | `data_ctor_value_displays_with_fields_not_bare_name_neg` — a user `(Cons 5 Nil)`-shaped value renders `(Lst.Cons 5 Lst.Nil)`-form WITH fields; assert the bare-ctor-name-only render is ABSENT | tests/repl_introspection.rs | [S109] — GREEN today; invariance pin + commit-2 acceptance (guards `display.rs::ctor_field_types` canonical-aware probe) | neg |
| AN-4 | (B/§3.3) member-glob import loses bare ctor refs (canonical names collected, alias edges skipped) | spec/08 §8.4 import shapes + §8.6.2 | `glob_import_bare_ctor_still_resolves` — after `(import [m [*]])` a bare imported ctor constructs and pattern-matches; `/testing` twins the member-glob shape (`(import [m [(Lst *)]])`-style) per the import-shapes variant family | tests/spec_08_modules.rs | [S109] — GREEN today; invariance pin + commit-2 acceptance (guards `imports.rs::collect_member_glob` alias installation) | pos (its absence post-flip is the guarded regression) |
| AN-5 | (arch §6) latent field-accessor same-cluster `--run` defect — bare accessor `v` NEVER resolved same-cluster under `--run` (live-only chain-follow misses the same-module staged alias) | spec/08 §8.5.2 field-accessor alias + §8.6.2 | `bare_field_accessor_same_cluster_run_mode` — one `--run` file defining `(deftype Box [:Int v])` and using bare `(v (Box 7))` in the SAME cluster. **Failing-not-ignored repro owed ahead of the wave** (pre-existing); the `/dev` types-level unit pin (staging-view alias hop in `chain_follow_committed`) is arch-directed, same change-set | tests/spec_08_modules.rs (or spec_05 accessor family) | **[S109] — RED ahead of the wave; flips GREEN at commit-1** (the §3.5 primitive amendment). `// defect: class=wrong-scope-lookup locus=cranelisp-types/src/resolve.rs::chain_follow_committed (same-module Import hop reads LIVE table, misses the caller's staging view) found=S109 owner=/dev` | pos |

#### D.2 Two-commit acceptance structure (arch §4 — how the RED/GREEN arithmetic works)

W1 lands as ONE `/dev` deployment, TWO commits; the plan's acceptance is
staged accordingly:

1. **Commit 1 — reader widening (behaviour-invariant).** All readers become
   canonical-aware with bare fallback. **MUST hold the S109 baseline (25
   fails)** — plus the deliberate adds: AN-2 and AN-5 (authored RED ahead of
   the wave as pre-existing-defect repros) flip GREEN **here**; AN-1/AN-3/AN-4
   and the whole existing suite must be byte-level undisturbed. Commit 1 is
   independently revertable; the AN guards are what make a revert loud.
2. **Commit 2 — writer flip + `CACHE_SCHEMA_VERSION` 16→17 + RED flips.** All
   ctor writers (user `deftype`, `bootstrap.rs` seeds incl. `IO.Bind`,
   typecheck fixture seeds — the uniform keying rule, arch §1) mint
   canonical+alias. The DC/BR REDs (DC-1…DC-11, BR-1/BR-2) flip GREEN here;
   AN-1/AN-3/AN-4 MUST STAY GREEN (they are the §5 regression classes as
   acceptance negatives); DC-9's cache legs bind to this commit (the bump is
   part of commit-2's definition of done, never a follow-up).

The reader-side bare fallback is NOT a Principle-8 interim — it permanently
serves the product facet (arch §4). `/review` checks both commits are present
in the one deployment and that no writer keeps bare-keyed sum-ctor `Def`s.

#### D.3 W1.2 DC-11-Blocker acceptance rows (arch §10.9, commit `d45e2cee` — the tag-order class)

**Why these rows exist (the missing definition-variants cells, named).** The
committed DC-11/DC-6 greens are **tag-layout coincidences**: the twin fixtures
gave both candidate types the same tag order/arity, so a wrong-ctor resolution
produced the right answer anyway — masking a silent wrong-ctor soundness
Blocker. Typecheck records the scrutinee-directed resolution in
`MethodResolutions.pattern_ctors`, but **no backend code consumes it**:
`compile_constructor_pattern` re-resolves the source-written bare name
context-free, falling to `resolve_driven`'s global fallback — a **DashMap
iteration in arbitrary order** → wrong module's same-named ctor, wrong tag,
runtime `match failed`, run-to-run nondeterminism. The missing variant axis is
**ctor declaration order across candidate types/modules**; the decisive cells
are the tag-order-DIFFERING twins. Cure: arch §10.1–10.3 (sidecar carries the
STORAGE key; transported on `MonoMatchArm.resolved_ctor` via a required
`MonoExpr::from_expr` parameter; backend does a direct keyed read and
HARD-ERRORS on a miss — no fallback).

**`/review` obligation (recorded):** DC-11 and DC-6 MUST be re-checked against
the differing-layout twins below, NOT the coincident fixtures — a green on
same-layout twins is no evidence for this class.

| Row | Citation | Test (proposed) | File | Status | Polarity |
|---|---|---|---|---|---|
| **DC-12** | §6.2.1 scrutinee-directed + arch §10.9 (**the decisive rows — differing-layout twins**) | `contested_bare_pattern_differing_layout_twins_both_orders` — two in-scope types sharing a ctor name with **DIFFERENT tags AND different arities**: `(deftype (Maybe a) None (Some [:a v]))` (`Some` = tag 1, arity 1) vs `(deftype Opt2 (Some [:Int a :Int b]) None2)` (`Some` = tag 0, arity 2). Scrutinee-directed bare `(Some …)` matched over BOTH types in ONE program (`(Some x)` on the `Maybe` scrutinee, `(Some x y)` on the `Opt2` scrutinee), **both directions asserted** (each match returns its own type's correct arm value). Authored with the two `deftype`s in **BOTH source orders** — two fixture legs, identical assertions: the DashMap-arbitrary-iteration failure mode means both orders MUST give the correct, identical result. **REPL + `--run` parity** | tests/spec_06_pattern_matching.rs | **[S109] — RED** (the Blocker made flesh; flips at the §10 sidecar-transport change-set) | pos ×2 source orders (order-invariance IS the neg) |
| **DC-13** | arch §10.9 + §6.3 — cross-module nondeterminism regression guard | `xmod_same_named_ctor_pattern_deterministic_across_runs` — commit the `/review` `xmod.cl` repro (same ctor name across two IMPORTED modules, differing tag orders): **three consecutive `--run` invocations MUST give the SAME correct value** (observed today: exit 1/7/7). `// defect: class=resolver-mirror locus=cranelisp-backend/src/compiler/match_codegen.rs::compile_constructor_pattern (context-free re-resolution; the pattern_ctors sidecar never consumed — typecheck and backend disagree, one seam up from AN-2) found=S109 owner=/dev` | tests/spec_06_pattern_matching.rs | **[S109] — RED, failing-not-ignored** (nondeterministic today; the three-run shape makes it loud — forbidden dispositions apply in full: 1-in-3 wrong is a real bug) | pos (determinism + correct value) + neg (no `match failed`) |
| BU-1 | arch §10.3 loud-miss (Principle 18) | **`/dev`-owned backend in-crate unit pin (enumerated, fail-on-revert):** a hand-built codegen view whose ctor arm lacks `resolved_ctor` yields the §10.3 `CodegenError` ("pattern constructor '{name}' has no typecheck resolution"), **NEVER a silent fallback** to context-free re-resolution | cranelisp-backend unit | [S109] — lands with the §10 change-set | neg |
| BU-2 | arch §10.4 — I-1 sparkability exclusion via `bare_member_name` (landed) | **`/dev`-owned backend in-crate unit pin (enumerated):** with a canonically-keyed table, a sum-ctor call is EXCLUDED by `find_sparkable_bindings`/`find_sparkable_args` — asserted via the exclusion SET, not wall-clock | cranelisp-backend unit | [S109] — lands with the §10 change-set | neg |
| **DC-14** | arch §10.2/§10.8 — `CACHE_SCHEMA_VERSION` **17→18** (`MonoMatchArm.resolved_ctor` serializes into the cached `codegen_view`; fresh-build value `Some` on ctor arms ≠ serde default `None`, so the exempt-class rule does not apply) | `pre_schema_18_cache_rejected_and_warm_18_green` — a pre-18 `.meta.json` is **rejected wholesale** (never silently read into a `None`-armed view that would hard-error at the backend); a warm schema-18 rerun of the DC-12 differing-layout twin stays green | tests/cache.rs | [S109] — the 17→18 bump rides the §10 change-set. NOTE: this is the sprint's SECOND schema step (16→17 at D.2 commit-2 — DC-9's legs; 17→18 here — this row) | pos+neg |

### E. 0573 — deftype-shape × persistence matrix (the "coverage by definition variants" category made flesh; file: `tests/repl_lifecycle.rs`)

| Shape | backing `.cl` contains the def | reload retains type + accessor | Status |
|---|---|---|---|
| sum (`deftype (Opt a) None (Some [:a v])`) | `sum_deftype_persisted_to_backing_file` | `sum_deftype_reload_retains_type_and_ctors` | [S109] — expected GREEN (pins; verify-first against existing persistence coverage) |
| product (`deftype Point [:Int x :Int y]`) | `product_deftype_persisted_to_backing_file` | `product_deftype_reload_retains_type_and_accessor` | **[S109] — RED, the 0573 defect (silent data loss); repro owed.** `// defect: class=enumeration-miss locus=src/…/save.rs::generate_types (matches ModuleEntry::TypeDef only; product facet is Def{Constructor{type_def:Some}}) found=S108 owner=/dev` |
| neg (post-fix guard) | `sum_deftype_not_double_emitted_neg` — the `type_def_info()`-keyed fix must NOT emit sum types twice (sum ctor `Def`s carry `type_def: None`) | — | [S109] | 

### F. Observability — §17.20.3a field→metric acceptance + §17.2.1 probe channel (file: `tests/agent.rs`, agent-feature build; feature-off negs ride the existing family)

Each field row cites the `agent-context-tuning.md §4` metric it feeds — the
two-sided match `/qa` checks at review. **Metric-side reconciliation resolved
this pass (the `/repl` flag): F6 folds into the two existing metrics as named
facets — no standalone step-accounting metric is minted.** §4 amended
accordingly (see that doc); the repl-side mapping table (§17.20.3a) is exactly
accurate as landed.

| Row | Field / MUST | Metric fed (§4) | Test (proposed) | Tier | Polarity |
|---|---|---|---|---|---|
| OB-1 | F1 `question` on `pull`, verbatim | Unresolved-question list | `agent_log_pull_records_question` | e2e | pos |
| OB-2 | §17.20.3b — `question` REQUIRED on every probe tool (schema non-conformance without) | (enabler for F1) | enumerated unit deferral (`/dev` `src/agent`): every probe-tool definition in the §17.2.1 set declares required `question`; harness records it | unit (enumerated: one assertion per probe tool in the set) | neg |
| OB-3 | F2 `error_class` on failed `pull` result | Error-class histogram; First-submit-typecheck rate | `agent_log_failed_pull_carries_error_class` | e2e | pos |
| OB-4 | F3 `give_up` cause + dominant class | Give-up rate + cause histogram | `agent_log_give_up_records_cause_and_dominant_class` — e2e IF the step budget is externally configurable (verify-first, `/testing`); else enumerated unit at the give_up emission seam (cases: `step_budget` cause; `model_declined` cause; dominant-class computation) | e2e-or-enumerated-unit | pos |
| OB-5 | F4 `primer_hash`+`harvest_len` at session start | Comparable-runs discipline (§5) | `agent_log_session_start_stamps_context_version` | e2e | pos |
| OB-6 | F5 `scenario` on EVERY record; absent/neutral when env unset | Per-scenario slicing | `agent_log_scenario_env_stamped_on_every_record` + `agent_log_neg_no_scenario_field_when_env_unset` | e2e | pos+neg |
| OB-7 | F6 `step`/`steps_at_submit`/`steps_at_give_up` | Probes-per-submit (step facet); Give-up histogram (step facet) | `agent_log_submit_carries_step_accounting` | e2e | pos |
| OB-8 | §17.20.3 contract preserved — metadata-only, NO content; silent; fields absent on non-agent build | (guards every metric's substrate) | `agent_log_neg_carries_no_content_fields` (no form text / error message / model prose keys); feature-off absence rides the existing `*_feature_off_*` family | e2e | neg |
| OB-9 | §17.2.1 — probe traffic MUST NOT echo `agent> {cmd}` + result into the user session | (experience MUST, thread B) | `agent_probe_traffic_not_echoed_to_session_neg` | e2e | neg |
| OB-10 | §17.2.1 — user DOES see conclusions (`▌` gutter prose) + the finished definition | (experience MUST) | `agent_probe_conclusions_and_definition_still_shown` | e2e | pos |

### G. Display/envelope MUSTs — 0572/0569 + the `[S109 — repro owed]` items `/repl` annotated

| Row | Citation | Test (proposed) | File | Status | Polarity |
|---|---|---|---|---|---|
| EV-1 | §1.5 "named function value carries its qualified name, not `<closure>`" (0572) | `named_function_value_displays_fq_name_not_closure` — bare `primitives/vec-len` (and a user fn) shows the FQ name in the value slot; neg facet: NOT `<closure>` | tests/repl_introspection.rs | **[S109] — RED, repro owed** (`/repl` annotated) | pos+neg |
| EV-2 | §1.5 — `<closure>` reserved for genuinely anonymous values | existing `closure_value_display_shows_closure_token` stays GREEN (the counter-guard: the fix must not qualify anonymous lambdas) | tests/repl_introspection.rs | [Tested …] — keep | neg-control |
| EV-3 | §17.19.2a — macro `/search` row shows `; defmacro`, NEVER a placeholder scalar (0569) | `search_macro_row_shows_defmacro_not_scalar_type_neg` — user-defined fixture `defmacro`; colour-off byte assertions: primary line is the macro envelope (`:{mod}/{name} ; defmacro …`), NOT `:primitives/Int {name}` | tests/search.rs | **[S109] — RED, repro owed** | pos+neg |
| EV-4 | §1.1 one-envelope + §17.19.2 (0572) | `search_row_primary_line_byte_identical_to_bare_lookup` — same symbol: `/search` primary line == bare-lookup primary line (colour off, byte compare); sibling cells `/sig`/`/info` in matrix M3 | tests/search.rs | [S109] | pos (byte-identity IS the neg) |
| EV-5 | §17.19.2b | DC-10 rows (§D) | — | [S109] | — |

### H. The variant × {pos, neg} matrices (standing definition-variants lens — explicit tables; a missing cell is where a variant silently diverges)

**M1 — dotted-ctor position/provenance family** (one codepath pressure: every
cell must be served by the ONE `resolve_dotted_member_entry` core, design §3):

| Variant | Positive (dotted resolves / correct behaviour) | Negative (bare poisoned / wrong thing absent) |
|---|---|---|
| value position, single type | DC-1 | (no contest — n/a by construction) |
| value position, two types | DC-2 | DC-3 (bare ALWAYS poisons — no context) |
| call position (applied ctor) | DC-2 (applied leg) | DC-3 |
| pattern, dotted (any scrutinee) | DC-4 (data + nullary — never scrutinee-contingent) | BR-1 (no false non-exhaustive) |
| pattern, bare contested, DETERMINED scrutinee | **DC-11 (bare RESOLVES — scrutinee-directed, W1 re-ruling)** | — (resolution IS the cell; wrong-type dotted vs scrutinee is an ordinary type error, §6.4.1) |
| pattern, bare contested, INDETERMINATE scrutinee | (dotted control inside DC-5) | **DC-5 (poison listing canonical alternatives — the ONLY pattern-position poison)** |
| **tag order: differing layouts (tags AND arities), both source orders** | **DC-12 (both directions correct, both orders identical — the decisive cells; DC-11/DC-6 alone are tag-layout coincidences)** | DC-12 order-invariance leg + BU-1 (loud-miss, never fallback) |
| **tag order: cross-module (imported candidates)** | **DC-13 (three-run determinism)** | DC-13 (no `match failed`) |
| sidecar transport: warm cache (schema 18) | DC-14 (warm-18 twin green) | DC-14 (pre-18 cache rejected wholesale) |
| first-class (let-bound / arg) | DC-8 | — (covered by DC-3's poison) |
| provenance: define+define | DC-2/3/11/5 | same |
| provenance: define+import | DC-6 twin A | DC-6 twin A neg |
| provenance: import+import | DC-6 twin B | DC-6 twin B neg |
| provenance: imported bare nullary, chain ≥2 hops (re-export) | **AN-2 (tag, not closure — soundness)** | AN-2 neg facet (no wrong-value / "match failed") |
| provenance: glob + member-glob import, bare ctor | **AN-4** | AN-4 post-flip regression guard |
| product degenerate | DC-7 (bare `Point` works) | DC-7 (`Point.Point` does not; no spurious poison) |
| warm cache | DC-9 | DC-9 (stale-cache invalidation; binds to commit-2) |
| display: value with fields | **AN-3 (fields rendered)** | AN-3 (bare-name-only render absent) |
| display `/search`/`/list`/`/exports` | DC-10 canonical listing | DC-10 no-bare-duplicate |
| exhaustiveness | BR-1 (dotted-covered total match) | BR-1 (no false non-exhaustive) + BR-2 (internal exclusion) |
| sibling family: field accessor, same-cluster `--run` | **AN-5** | — (the `/dev` types unit pin is the deterministic revert guard) |
| prelude cascade (writer-flip acceptance) | AN-1 (a+b) | AN-1 (cascade absence) |

**M2 — §8.5.4 auto-load: kind×position × mode** (language-semantics rows use
`run_through_all_modes`, so one fn covers the three mode columns; the NEG
column is the FQ-D3 no-codegen-leak sweep + the row's own edge negative):

| Kind × position | REPL | `--run` | `--link` | Negative |
|---|---|---|---|---|
| fn, call position | AL-1/A1 | AL-1/A1 | AL-1/A1 | FQ-D3 sweep |
| fn, value position | AL-1/A2 + FQ-D2 (display) | AL-1/A2 | AL-1/A2 | FQ-D1 (generic template — check-side, never codegen) |
| generic fn, value position | FQ-D1 | FQ-D1 | FQ-D1 | FQ-D1 neg facet |
| macro, call position | AL-1/A3 | AL-1/A3 | AL-1/A3 | FQ-D3 sweep |
| type, annotation position | AL-1/A4 | AL-1/A4 | AL-1/A4 | AL-3 (unresolvable FQ type = resolution-layer error) |
| ctor, pattern position (qualified) | M2-P: `fq_ctor_pattern_position_autoloads` (edge-1 "pattern position" leg — NEW fn, tests/spec_06_pattern_matching.rs) | same fn | same fn | DC-5-style bare contest unaffected by auto-load (edge 10) |

**M3 — envelope surfaces × symbol kinds** (§1.1 one-envelope; extends the S108
Inc3 §B byte-identity strategy):

| Surface | defn | defmacro | ctor | 
|---|---|---|---|
| bare lookup | existing §1.1 pins | existing §4.1 macro pins | DC-10/§1.5 canonical form |
| `/sig` / `/info` | EV-4 sibling cells | EV-4 sibling cells | EV-4 sibling cells |
| `/search` row | EV-4 | EV-3 | DC-10 |

### I. Settled-semantics rows — 0575 (§4.5) + 0576 (§5.1.2)

| Row | Citation | Test (proposed) | File | Status | Polarity |
|---|---|---|---|---|---|
| SS-1 | §4.5 "`fn` is single-arity … compile-time (parse) error" | `fn_multi_arity_clause_form_parse_error_neg` — `(fn ([x] x) ([x y] x))` rejected in REPL + `--run`; error-quality facet: names `fn` as single-arity and points at `defn` (the 0575 `/dev` tail) | tests/spec_04_expressions.rs | [S109] — behaviour may already reject; the ERROR-QUALITY assertion is the RED | neg |
| SS-2 | §4.5 (control) | existing `lambda_immediate_call` — single-clause `fn` stays GREEN | tests/spec_04_expressions.rs | [Tested …] — cite | pos-control |
| SS-3 | §5.1.2 "each variant type-checked independently … ambiguous-type compile-time error" | `defn_multi_arity_unpinned_clause_ambiguous_error_names_clause_neg` — the spec's ERROR example (unannotated 2-arg delegating clause); diagnostic NAMES the offending param/clause (0576 `/dev` diagnostic tail) and does NOT contain `__expr` (0568) | tests/spec_05_definitions.rs | [S109] — RED on the diagnostic-quality facet | neg |
| SS-4 | §5.1.2 (control) | `defn_multi_arity_annotated_clauses_compile` — the spec's CORRECT example; delegating call returns the right value | tests/spec_05_definitions.rs | [S109] | pos |
| SS-5 | §5.1.2 dispatch | existing `defn_multi_clause_arity` stays GREEN | tests/spec_05_definitions.rs | [Tested …] — cite | pos-control |

### J. 0570 — `mod-` twin (§8.2.3 tested-neg extended to search-surfacing)

| Row | Citation | Test (proposed) | File | Status | Polarity |
|---|---|---|---|---|---|
| MV-1 | §8.2.3 ("Surfacing a private submodule's symbol as an importable result … MUST NOT occur") + §17.19.2 | `mod_dash_submodule_symbols_absent_from_search_neg` — a `(mod- internal)` submodule's symbol NEVER appears as a `/search` row (wait for `indexing…` note to clear or assert on completed index); no `(import …)` hint anywhere | tests/search.rs | [S109] — RED expected (the 0570 surfacing gap) | neg |
| MV-2 | §8.2.3 import leg | existing `mod_dash_private_submodule_not_importable_from_peer_neg` stays GREEN | tests/spec_08_modules.rs | [Tested+Neg …] — cite | neg-control |
| MV-3 | §8.2.3 (control) | `bare_mod_submodule_symbols_present_in_search` — a public `(mod test)` sibling's symbol DOES appear (proves MV-1 asserts privacy, not a dead index) | tests/search.rs | [S109] | pos-control |
| MV-4 | §8.2.5 × `mod-` (the `/stdlib` precondition) | `mod_dash_child_file_pattern_loads` — `(mod- test)` with `<module>/test.cl` child file loads and is usable from the parent subtree | tests/spec_08_modules.rs | [S109] — verify-first (the bare-`mod` stdlib convention was deliberate) | pos |

### K. Cross-skill citation churn (0580 `program.rs` split) — disposition

- `tests/plan/s101-coverage-postmortem.md` (**mine**): line citations frozen
  with a provenance note added this pass (historical post-mortem; do not chase
  the 0580 relocation). No further action.
- `crates/cranelisp-typecheck/CLAUDE.md` + any `// spec:`-anchored
  `program/tests.rs` references: **`/dev`'s to sweep in the 0580 move
  change-set** (as SPRINT.md already assigns; `design/typecheck/check-form-api.md`
  is the `// spec:` anchor and is `/design`'s).
- `/qa` reruns both structural verifiers (`plan/spec_link_check.py`,
  `plan/spec_coverage_reconcile.py`) after the 0580 wave lands and repairs any
  annotation-band citation the move breaks (annotation band is `/qa`'s, edited
  in place).

### L. W6/W6.2 — annotation-resolution variant × {pos, neg} matrix (the poly-annotation defect's own coverage; rigid model as of 2026-07-14)

The coverage-gap finding from the W1 re-ruling pass: a **free type variable in
a `defn`/`fn` parameter annotation** fails `unknown type 'a'` (verified live)
— and no cell in the suite would have caught it, because annotation-resolution
coverage grew per whichever position an implementer exercised. The matrix
below is the missing family. **Re-examined W6.2 (2026-07-14)** after the user
ruled written vars RIGID/definition-scoped — the reclassifications and the
skolem-escape rows the first pass lacked are marked inline.

**Spec stance RESOLVED (2026-07-14; SPRINT.md §"W6 spec-stance gate") —
REVISED W6.2 (2026-07-14, user ruling; SPRINT.md §"W6.2 RIGID/DEFINITION-SCOPED
RULING").** The W6 `/dev` pass (`e401cce9`) shipped the FLEXIBLE/acquire model
— a written var minted an ordinary inference variable, so an in-body ascription
or use silently SET it (`:a "hello"` → `(Fn [a] String)`; F1/0588). The user
ruled the opposite: a written type variable is **definition-scoped and RIGID**
— annotations ASSERT, they do not acquire. `/spec` rescribed §3.3; this matrix
was re-examined against it 2026-07-14 (reclassifications marked per-row). Every
row cites the §3.3 MUST band:

> **MUST-1 (type variable, boundary-quantified, call-site-instantiated):** "a
> lowercase identifier appearing free in an annotation — whether standing alone
> (`(defn id [:a x] :a x)`) or nested inside an applied type (`:(Maybe a)`) —
> is a type variable in exactly the sense above" + §3.3 property 1: "MUST be
> treated as implicitly universally quantified at the definition boundary …
> Which concrete type it becomes is chosen by the **caller** at each use site
> (instantiation-at-use, §3.10) — **never** by the definition's own body."
>
> **MUST-2 (not-unknown-type):** "A written free lowercase variable MUST NOT
> be treated as a reference to an unknown named type; it is a genuine type
> variable."
>
> **MUST-3 (rigid; assert-not-acquire; skolem-escape):** §3.3 property 2: "an
> annotation `:a e` **asserts, it does not acquire**: it is a *checking
> obligation* that MUST be discharged by `e` **already** having type `a` (e.g.
> `e` is a parameter declared `:a`…). Ascribing a **concrete-typed** expression
> — or one carrying a *distinct* rigid variable — to a bare quantified variable
> MUST be rejected as a type error (**skolem-escape**); it MUST NOT silently
> acquire the concrete type."
>
> **MUST-4 (unification asymmetry):** "a **flexible** inference variable (for
> example, the type of an unannotated parameter) MAY unify with a rigid written
> variable — this is precisely how a parameter *acquires* a written type — but
> a **rigid** written variable MUST NOT be unified with a concrete type, nor
> with a *distinct* rigid variable."
>
> **SCOPE-5 (definition-scoped = lexical co-reference; CORRECTED 2026-07-14
> within W6.2 — the earlier "nested shadow" reading was ruled the OPPOSITE):**
> a written var "is introduced at the **outermost binder where its name first
> appears** in a definition, universally quantified at that enclosing
> definition's boundary … and every occurrence of the same name within that
> lexical scope — **including inside nested `fn` closures** — MUST co-refer
> to that same one rigid variable. A nested `fn`/`defn` does **NOT** open a
> fresh quantification boundary: a name becomes a *distinct* rigid variable
> only when it is not already in scope, and a fresh identifier first appearing
> in an inner `fn` is still quantified at the enclosing definition's
> boundary." At the **top level**, a `def` binding is itself the
> generalization boundary (bare `:a 5` / `(def y :a 5)` → skolem-escape).
> Worked (normative): `(defn id [:a x] :a x)` → `∀a.(Fn [a] a)` checks;
> `(defn g [:a x] (fn [:a y] y))` → `∀a. (Fn [a] (Fn [a] a))` — `x` and `y`
> the **SAME** rigid `a` (the inner `:a` co-refers, it does NOT shadow);
> `(defn f [:a x] :a "hello")` → **type error** (skolem-escape), it does NOT
> yield `(Fn [a] String)`.

Rigidity binds ALL unification with the var inside its definition, not only
explicit ascriptions: a body *use* that would force the rigid var concrete
(`(add-i64 x 1)` on `x : a`) is the same skolem-escape rejection (MUST-4 has
no by-use exemption). This is what reclassifies FV-11.

The family sweep table stays as the position × shape map — its free-var cells
are REALIZED by the FV rows (pointers in the cells).

**Fixture syntax notes (binding for `/testing`):**

- **Annotation precedes the parameter name** — `[:a x]`, `[:(Box a) b]` — per
  §5.1.1 EBNF (`annotated_param = colon_prefix symbol`) and §3.9 (`:Type form`
  binds the immediately-following form in ALL positions). The 0587 example-order
  typo was RESOLVED in the W6.2 `/spec` rescribe — §3.3's worked examples now
  read `(defn id [:a x] :a x)`, matching the EBNF order fixtures already use.
- **Body-annotation parse gaps (F4/0591, CARRIED):** annotations do not parse
  in four body positions (multi-arity clause body, `fn`/match-arm/`if` bodies)
  — a pre-existing frontend limitation, FIXME 0591 open. New W6.2 fixtures
  place body annotations ONLY in the single-arity `defn` body position (which
  parses — the 0588 live repro is exactly that shape); cells whose natural
  fixture needs a gapped position route to the unit tier (noted per-row).
- **There is no return-annotation syntax** (§5.1.1: "The return type is always
  inferred"). The "return position" cells are realized as the BODY expression
  annotation (`:Type form`, §3.9/§4.9): `(defn id [:a x] :a x)`'s second `:a`
  annotates the body `x`.
- Free-standing fixtures only (no stdlib): `(deftype (Box a) [:a v])`,
  `(deftype (Pair2 a b) [:a x :b y])`, primitives `add-i64`/`str-concat`.

Annotation shape × position (the family map; free-type-var cells realized by
§L.1 FV rows):

| Position \ annotation shape | concrete app (`:(Box Int)`) | free type var (`:(Box a)`) | bare var (`:a`) |
|---|---|---|---|
| `defn` param | pos pin (`defn_param_concrete_app_annotation`) | **FV-4/FV-5**; rigid-by-use neg **FV-19** | **FV-1/FV-2/FV-3**; distinct-rigid neg **FV-17** |
| `fn` (lambda) param | pos pin | FV-15 (nested facet) | **FV-15**; nested co-reference **FV-20** |
| `deftype` field | pos pin (likely existing — verify-first) | GREEN control (works today: `(deftype (Box a) [:a v])` is the language's bread and butter — cite existing; the header BINDS `a`, so it is not free — unaffected by W6.2) | GREEN control |
| body/return expression annotation (`:Type form`) | pos pin (§4.9 existing) | FV-6 (co-reference facet); applied skolem-escape **FV-18** | **FV-6**; assert-not-acquire neg **FV-16**; boundary: **FV-10** (§3.11 discrimination) |
| `let` binding annotation | pos pin | sweep item (verify-first: may share the defn-param seam) | sweep item — rigid re-read: a concrete initializer under a free `:a` is now a skolem-escape NEGATIVE (see sweep) |

Name-discrimination guards sit beside the map (they are not shape cells):
uppercase unknown **FV-13** (PIN), trait path **FV-14** (PIN), qualified
lowercase `:user/int` **FV-21** (F2/0589 — a qualified name is a named-type
reference, never a var).

#### L.1 W6/W6.2 — written free-var annotation resolution: acceptance rows (rigid model)

Every row cites the §3.3 MUST band (MUST-1..MUST-4/SCOPE-5, quoted above) plus
the listed section. **Two defect generations run through this matrix:**

- **W6 (`unknown type 'a'`, fixed):** the original defect — a free lowercase
  annotation ident took the named-type lookup path. Fixed at `e401cce9`; the
  13 W6 REDs are GREEN there (SPRINT.md §W6.2). Their `// defect:` line
  (already on the authored tests, past-tense once W6.2 confirms no wording
  churn): `class=wrong-scope-lookup locus=crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr (free lowercase annotation var absent from var_map fell to TypeNotFound instead of minting a quantified var) found=S109 owner=/dev`
- **W6.2 (flexible-acquire, OPEN — the current REDs):** `e401cce9` minted
  FLEXIBLE vars, so ascription/use silently acquires (F1/0588) and qualified
  lowercase names mint (F2/0589). `// defect:` lines for the new REDs:
  - FV-11/FV-16..FV-19 (+FV-20 both facets — same 0588 per-Annotate/non-threaded var_map seam): `class=silent-accept locus=crates/cranelisp-typecheck/src/infer.rs::infer_annotate + resolve.rs::resolve_type_expr (W6 minted FLEXIBLE inference vars for written annotation vars — ascription/use ACQUIRES instead of asserting; no rigid skolem, per-Annotate fresh var_map instead of definition-scoped — F1/0588) found=S109 owner=/dev`
  - FV-21: `class=silent-accept locus=crates/cranelisp-typecheck (type-var minting keyed on lowercase-ness without excluding QUALIFIED names; four mirror mint sites per 0590 — traits/type_resolve.rs ×3 + form.rs — F2/0589) found=S109 owner=/dev`

**Status legend:** "PIN (W6)" = authored in W6, GREEN at `e401cce9`, and MUST
HOLD through the W6.2 rigid re-fix — the rigid model changes none of these
verdicts, so a W6.2 regression on any of them is over-broadening. "RED (W6.2)"
= expected failing-not-ignored at authoring against `e401cce9` (the flexible
model accepts what MUST-3/MUST-4 reject); flips green at the `/dev` rigid pass.
**RECLASSIFIED W6.2** rows are explicitly marked with what moved and why.

| Row | Citation + fixture → expected verdict | Test (proposed) | File | Tier | Status | Polarity |
|---|---|---|---|---|---|---|
| FV-1 | §3.3 MUST-1, standalone bare var — `(defn id [:a x] x)` → scheme `(Fn [a] a)`; genuine quantification proven by use at TWO types in one program: `(id 3)` → `:primitives/Int 3` AND `(id "s")` → `:primitives/String "s"`. Rigid re-read: unchanged — the body never constrains `a`; the two-type use is MUST-1's caller-side instantiation made observable | `defn_param_bare_free_var_quantifies_and_uses_at_two_types` | tests/spec_03_types.rs | e2e all-modes | [S109] — PIN (W6) | pos |
| FV-2 | §3.3 MUST-2, same fixture as FV-1 — output MUST NOT contain `unknown type`; MUST NOT contain a codegen-layer frame (the error class, if the fix regresses, must never be a named-type miss) | `defn_param_bare_free_var_not_unknown_type_neg` | tests/spec_03_types.rs | e2e | [S109] — PIN (W6) | neg |
| FV-3 | §3.3 MUST-1 (written quantifies exactly as inference-generated) — TWIN: `(defn idw [:a x] x)` vs `(defn idi [x] x)` — introspection displays the SAME scheme for both; both evaluate at the same two types. W6.2 SCOPE NOTE: the parity claim is SCHEME/display + call-site only — under the rigid model the two are NOT interchangeable in-body (idw's `a` is rigid, idi's param var flexible); the in-body contrast is FV-16/FV-19's, and this twin must not be read (or extended) as licensing body-behaviour parity | `written_var_vs_inferred_var_identical_scheme_twin` | tests/spec_03_types.rs | e2e (REPL introspection + all-modes call) | [S109] — PIN (W6) | pos (parity) |
| FV-4 | §3.3 MUST-1, nested in applied type — `(deftype (Box a) [:a v])` + `(defn unbox [:(Box a) b] (v b))` → `(Fn [(Box a)] a)`; `(unbox (Box 7))` → 7 and a String leg. The verified-live W6 failing shape. Neg facet: no `unknown type 'a'`. Rigid re-read: checks via MUST-4's allowed direction — the accessor's instantiated FLEXIBLE var unifies with rigid `a`; the body never forces `a` concrete | `defn_param_free_var_nested_in_applied_type` | tests/spec_03_types.rs | e2e all-modes | [S109] — PIN (W6) | pos + neg facet |
| FV-5 | §3.3 MUST-1, multi-var applied + deeper nesting — `(deftype (Pair2 a b) [:a x :b y])` + `(defn get-x [:(Pair2 k v) p] (x p))` → `(Fn [(Pair2 k v)] k)`; deeper facet `:(Box (Pair2 k v))` | `defn_param_multi_var_applied_annotation` | tests/spec_03_types.rs | e2e | [S109] — PIN (W6) | pos |
| FV-6 | §3.3 MUST-1/MUST-3/MUST-4 + §3.9/§4.9 (body/"return" position — no return syntax exists per §5.1.1) — (a) the §3.3 worked POSITIVE `(defn id [:a x] :a x)`: the SAME written var in param annotation and body annotation co-refer within one definition boundary → `(Fn [a] a)`, not `(Fn [a] b)`. Rigid re-read: this is MUST-3's discharge case — the assertion `:a x` checks because the annotated expr IS the param already typed `a`; (b) var only in the body annotation `(defn id2 [x] :a x)` → `(Fn [a] a)` — discharges via MUST-4's allowed direction (the unannotated param's FLEXIBLE var unifies with rigid `a`: acquisition by the flexible side, never by the rigid one). Co-reference NOT rescued by incidental unification (0588's per-`Annotate` fresh-map seam) is **unit u2** | `written_var_param_and_body_annotation_corefer` | tests/spec_03_types.rs | e2e + **unit u2** | [S109] — PIN (W6) | pos |
| FV-7 | §3.3 MUST-1, multiple distinct vars — `(defn fst2 [:a x :b y] x)` → `(Fn [a b] a)`; `(fst2 1 "s")` → 1. The success at MIXED argument types IS the guard that `a`/`b` are independent (not wrongly unified). The in-body face of the same property — ascribing a `b`-typed param to `:a` MUST error — is FV-17 (MUST-4's distinct-rigid clause) | `defn_param_two_distinct_free_vars_independent` | tests/spec_03_types.rs | e2e all-modes | [S109] — PIN (W6) | pos + neg (no cross-var unify) |
| FV-8 | §3.3 SCOPE-5 (one definition boundary = one rigid var per identifier; within-signature co-reference) — `(defn eq2 [:a x :a y] x)` → `(Fn [a a] a)`; pos: `(eq2 1 2)` → 1; neg: `(eq2 1 "two")` → TYPE-MISMATCH error (both args instantiate ONE quantified `a`), and the error is a CALL-SITE instantiation/unification failure — not skolem-escape (the definition itself is well-typed), never `unknown type` | `defn_param_same_free_var_reused_unifies` (+ `_neg` sibling) | tests/spec_03_types.rs | e2e + **unit u2** | [S109] — PIN (W6) | pos + neg |
| FV-9 | §3.3 + §3.9.1, free + concrete mixed — `(defn tag [:a x :Int n] x)` → `(Fn [a Int] a)`; `(tag "s" 3)` → "s"; neg facet: `(tag "s" "t")` rejected (the concrete cell still constrains) | `defn_param_free_var_and_concrete_mixed` | tests/spec_03_types.rs | e2e | [S109] — PIN (W6) | pos + neg |
| FV-10 | §3.11 boundary discrimination — a free-var annotation on a CODEGEN-REACHING bare value (`:(Vec a) []` consumed at runtime in `--run`/`--link`) is the §3.11 AMBIGUOUS-type error ("add an annotation"), and at the REPL a bare polymorphic value is disposition-3 introspection display (§3.11.4) — in NO mode is the verdict `unknown type 'a'`. Rigid re-read: verdict unchanged — `[]`'s flexible elem var unifies with the written var (MUST-4 allowed direction) and the value stays polymorphic into the §3.11 machinery; what "the definition boundary" is for a TOP-LEVEL written var stays the sweep's verify-first item | `free_var_annotation_codegen_reaching_is_ambiguity_not_unknown_type_neg` | tests/spec_03_types.rs | e2e per-mode verdicts | [S109] — PIN (W6) | neg |
| FV-11 | **RECLASSIFIED W6.2: was positive-acquire, now negative-skolem-escape.** The W6 row (and its authored GREEN test) expected each clause's BODY to pin its own `:a` concretely — `(defn h ([:a x] (add-i64 x 1)) ([:a x :Int n] (str-concat x x)))` compiling with `(h 5)` → 6, `(h "ab" 0)` → "abab". That is the flexible/acquire model §3.3 now REJECTS: MUST-1 ("never by the definition's own body") + MUST-4 (a rigid var MUST NOT unify with a concrete type — by use just as by ascription). SAME fixture, INVERTED verdict: each clause is a TYPE ERROR (its body forces its rigid `a` concrete — skolem-escape). Facets: (i) the error is skolem-escape/type-mismatch, never `unknown type` (MUST-2); (ii) cross-clause independence (§5.1.2, UNCHANGED property, now observed in the error shape): each clause errors against ITS OWN rigid var (`a` vs Int in clause 1, `a` vs String in clause 2) — the diagnostic MUST NOT be an Int-vs-String CROSS-CLAUSE conflict, which would betray a shared var. `/testing`: REWRITE the authored test (its success assertions now assert spec-violating behaviour); per-clause freshness beyond the error-shape observable is **unit u3** | `multi_arity_written_var_body_pin_skolem_escape_per_clause_neg` (replaces `multi_arity_same_written_var_independent_per_clause`) | tests/spec_05_definitions.rs | e2e + **unit u3** | [S109] — RED (W6.2): GREEN-as-positive at `e401cce9`, which is the F1/0588 defect visible | neg (was pos) |
| FV-12 | §5.1.2 (polymorphic variant = ambiguous error) × §3.3 — a free-var annotation does NOT rescue multi-arity ambiguity: the delegating clause `([:a p :a rot] (rp p rot 0))` errors NAMING the clause (couples SS-3's diagnostic row), never `unknown type 'a'`, and the sibling's `:Int` types never back-flow. **W6.2 re-read (verdict UNCHANGED — not a reclassification):** under the rigid model the rejection is doubly grounded — the body could not pin the rigid `a` even in principle (MUST-3/MUST-4: the delegating call unifying `a` with the sibling's `:Int` params is itself skolem-escape), and an unpinned variant is §5.1.2's poly-variant error. Error-CLASS facet stays soft: ambiguous-variant OR skolem-escape/no-matching-variant are both conforming classes; `unknown type` and silent acquisition are not. `/testing`: comment wording update only | `multi_arity_unpinned_free_var_variant_ambiguous_not_unknown_type_neg` | tests/spec_05_definitions.rs | e2e | [S109] — PIN (W6); wording re-read W6.2 | neg |
| FV-13 | §3.9.3 (neither type nor trait ⇒ error) — the critical over-broadening guard: UPPERCASE unknowns still error. (a) `(defn f [:Foo x] x)` → `unknown type` naming `Foo`; (b) nested `(defn g [:(Box Foo) b] b)` (Box defined) → same. The fix MUST key on the §3.3 bare-lowercase rule, not swallow real unknown-type errors. Qualified-lowercase sibling: FV-21 (F2/0589) | `unknown_uppercase_type_annotation_still_errors_neg` (+ nested sibling) | tests/spec_03_types.rs | e2e + **unit u4** | [S109] — **PIN** (GREEN today; MUST HOLD through W6.2) | neg (invariance) |
| FV-14 | §3.9.2 invariance — `(defn show2 [:Num x] x)`-shape trait-constraint annotation still yields the CONSTRAINED polymorphic scheme (§3.4.1 display), not a free var, not unknown-type. Cite existing coverage if a `[Tested …]` row exists; else thin pin | `trait_constraint_annotation_unaffected_by_free_var_rule` | tests/spec_03_types.rs (or cite spec_07) | e2e cite-or-pin + **unit u5** | [S109] — **PIN** (GREEN today; MUST HOLD through W6.2) | pos (invariance) |
| FV-15 | §3.3 MUST-1 × §4.5 (`fn` param position) — `((fn [:a x] x) 3)` → 3; parity facet: `(let [f (fn [:a x] x)] …)` behaves identically to the unannotated `let_polymorphism_identity_two_types` twin. Rigid re-read (corrected SCOPE-5): with NO enclosing definition, the standalone `fn` is itself the outermost binder — the written var is quantified at that (sole) definition boundary and instantiated at each application (the immediate call chooses `a := Int`); the annotation adds NO new generalization boundary beyond that. Nested facet `(fn [:(Box a) b] …)`. The nested CO-REFERENCE cell (inner `:a` under an enclosing defn's `:a` = the SAME rigid var) is FV-20 | `fn_lambda_param_free_var_annotation` | tests/spec_04_expressions.rs | e2e all-modes | [S109] — PIN (W6) | pos + parity |

**W6.2 additions — the rigid/skolem-escape rows the first pass lacked
(ADDED 2026-07-14):**

| Row | Citation + fixture → expected verdict | Test (proposed) | File | Tier | Status | Polarity |
|---|---|---|---|---|---|---|
| FV-16 | §3.3 MUST-3 — THE worked negative, verbatim from the spec: `(defn f [:a x] :a "hello")` → **type error** (skolem-escape: `"hello"` is concrete `String`, the assertion `:a "hello"` cannot be discharged); it MUST NOT yield `(Fn [a] String)` (silent acquisition). Facets: (i) a follow-on `(f 3)` errors as undefined/unresolved — the defn was REJECTED, so the acquired-type world never arises; (ii) the error class is a type error, never `unknown type` (MUST-2), never a codegen frame. Body-annotation position parses (0588's live-repro shape) | `written_var_concrete_ascription_skolem_escape_neg` | tests/spec_03_types.rs | e2e all-modes + **unit u6** | [S109] — RED (W6.2): `e401cce9` silently acquires (F1/0588) | neg |
| FV-17 | §3.3 MUST-3/MUST-4 (distinct-rigid clause) — ascribing a `b`-typed value to `:a` errors: `(defn g [:a x :b y] :a y)` → type error (rigid `b` is a *distinct* rigid variable; the assertion cannot be discharged); MUST NOT unify the two vars (which would collapse `(Fn [a b] …)` to `(Fn [a a] …)`); never `unknown type`. FV-7's in-body negative face | `written_var_distinct_rigid_ascription_skolem_escape_neg` | tests/spec_03_types.rs | e2e + **unit u6** | [S109] — RED (W6.2) expected: flexible model unifies the two silently | neg |
| FV-18 | §3.3 MUST-3 nested in an applied type — TWIN pair (free-standing `Box` per fixture notes; the ruling's `(Maybe a)` shape): (neg) `(defn h [:(Box Int) b] :(Box a) b)` → type error (rigid `a` ≠ `Int` under the constructor — skolem-escape reaches through applied types); (pos control) `(defn h2 [:(Box a) b] :(Box a) b)` → checks, `(Fn [(Box a)] (Box a))` — the annotated expr already HAS the asserted type via its param (MUST-3's discharge case, applied form) | `applied_annotation_rigid_var_concrete_mismatch_neg` + `applied_annotation_rigid_var_corefers_param` | tests/spec_03_types.rs | e2e | [S109] — neg RED (W6.2; flexible model acquires `a := Int`); pos GREEN today (control) | pos + neg twin |
| FV-19 | §3.3 MUST-1 ("never by the definition's own body") + MUST-4 — rigidity binds unification BY USE, not only by explicit ascription: `(defn f2 [:a x] (add-i64 x 1))` → type error (the body forces rigid `a` ~ `Int`); MUST NOT compile as `(Fn [Int] Int)` (the flexible model's silent narrowing — the defn would then LIE about its written polymorphism). Never `unknown type`. FV-11's single-clause core | `written_var_body_use_cannot_pin_rigid_neg` | tests/spec_03_types.rs | e2e + **unit u6** | [S109] — RED (W6.2): compiles-as-narrowed at `e401cce9` | neg |
| FV-20 | §3.3 SCOPE-5 (lexical CO-REFERENCE — a nested `fn` does NOT open a fresh quantification boundary; **CORRECTED 2026-07-14**: this row previously specced the OPPOSITE, shadow) — pos (e2e), the §3.3 worked example verbatim: `(defn g [:a x] (fn [:a y] y))` → `∀a. (Fn [a] (Fn [a] a))` — `x` and `y` are the SAME rigid `a`, quantified once at `g`'s boundary (introspection shows the scheme). Call facet proves co-reference observably: `(g 3)` instantiates `a := Int` for BOTH layers, so `((g 3) 4)` → `:primitives/Int 4` and `((g 3) "t")` MUST error — under the superseded shadow reading `(g 3)` would stay polymorphic in `y` and accept `"t"`. Companion pos facet: `(defn g2 [:a x] ((fn [:a y] y) x))` checks trivially (same rigid `a` both sides). Neg facet (e2e — the discriminating cell, INVERTED from this row's previous pos fixture): `(defn outer [:a x] ((fn [:a y] y) "s"))` MUST be a skolem-escape type error — the inner `:a` co-refers to outer's rigid `a`, so the application forces rigid `a` ~ `String` (MUST-4); the shadow reading expected this to COMPILE to `"s"`. Both facets parse (param annotations + application only). Annotation-form neg (inner-body assertion `:a "hello"` inside the `fn` body) still cannot parse (0591) — that facet stays UNIT-ONLY — **u7** | `nested_fn_written_var_corefers_enclosing_rigid` (+ `_neg` sibling; replaces the never-authored `nested_fn_written_var_is_fresh_rigid_shadow`) | tests/spec_04_expressions.rs | e2e (pos+neg) + **unit u7** | [S109] — RED-or-GREEN verify-first at `e401cce9` (co-reference needs the definition-scoped var_map to THREAD into nested `fn`; the W6 per-Annotate fresh-map seam — F1/0588 — predicts RED on both facets); expected verdict per corrected SCOPE-5 regardless | pos + neg |
| FV-21 | §3.3 ¶[S109] (the var rule is for a BARE lowercase identifier) + §3.9.3 (neither type nor trait ⇒ error) — F2/0589: a QUALIFIED lowercase annotation is a named-type reference, never a var: `(defn f [:user/int x] x)` → `unknown type` error naming `user/int`; MUST NOT mint a type variable (today it mints silently and the defn typechecks polymorphic). The qualified sibling of FV-13's uppercase guard — together they fence the minting rule to exactly bare-lowercase | `qualified_lowercase_annotation_unknown_type_not_minted_neg` | tests/spec_03_types.rs | e2e + **unit u8** | [S109] — RED (W6.2): F2/0589 verified live by `/review` | neg |

**Row count: 21** (was 15). Polarity: 6 positive (FV-1/3/5/6/14/15), 9 negative
(FV-2/10/11/12/13/16/17/19/21), 6 dual pos+neg (FV-4/7/8/9/18/20).
**W6.2 disposition of the 15 W6 rows:** 1 RECLASSIFIED positive→negative
(FV-11 — the acquire expectation inverted to skolem-escape; test rewrite);
1 verdict-unchanged re-read (FV-12 — wording only); 13 carried as PINs
(FV-1..FV-10/FV-13/FV-14/FV-15 — GREEN at `e401cce9`, MUST HOLD through the
rigid re-fix; FV-3 gains an explicit scheme-parity-only scope note).
**W6.2 additions: 6 rows** (FV-16..FV-21): 5 RED-expected negatives + 1
verify-first pos/neg pair — the assert-not-acquire (FV-16), distinct-rigid
(FV-17), applied-type skolem-escape twin (FV-18), rigid-by-use (FV-19),
nested co-reference (FV-20; corrected 2026-07-14 from its initial shadow
spec), and qualified-lowercase mint-guard (FV-21) cells.

**Unit-tier enumeration (the S108-Inc2 deferral discipline — `/dev` pins these
at the annotation-resolution seam in the SAME change-set as the fix; a bare
"unit-pinned" without these named cases is a hole):**

- **u1** — a free BARE-lowercase identifier in an annotation mints a fresh
  **RIGID (skolem)** type variable — never the named-type/trait lookup of
  §3.9.3, and never a FLEXIBLE inference variable (the F1/0588 regression:
  flexible minting is exactly what made ascription acquire);
- **u2** — same identifier within ONE definition boundary ⇒ SAME rigid
  variable, definition-scoped, not per-occurrence (param↔param FV-8,
  param↔body FV-6, and body↔body — two `Annotate` nodes in one body share the
  var; body↔body is unit-only within 0591's parse limits. The 0588 seam:
  `infer_annotate`'s per-`Annotate` fresh `var_map` vs the definition-scoped
  map the fix must install);
- **u3** — fresh identifier scope per multi-arity clause (FV-11's seam):
  clause 1's rigid `a` and clause 2's rigid `a` are distinct skolems.
  (UNAFFECTED by the 2026-07-14 co-reference correction: sibling clauses are
  DISJOINT lexical scopes — neither clause's `a` is "already in scope" in the
  other — the corrected SCOPE-5 merges NESTED scopes only, per §5.1.2
  clause independence);
- **u4** — case discrimination: uppercase unknown still takes the §3.9.3
  error path (FV-13's seam);
- **u5** — a known TRAIT name annotation still takes the §3.9.2 constraint
  path (FV-14's seam);
- **u6** — the MUST-4 unification asymmetry, ALL THREE arms at the unify
  seam: (a) flexible ~ rigid SUCCEEDS (the param-acquisition direction);
  (b) rigid ~ concrete FAILS as skolem-escape (FV-16/FV-19's seam — by
  ascription AND by use); (c) rigid ~ distinct-rigid FAILS (FV-17's seam).
  A unify that is symmetric in flexibility is the defect;
- **u7** — nested CO-REFERENCE (corrected 2026-07-14; was "nested shadow +
  restore"): the same `var_map` threads INTO the nested `fn` — the enclosing
  definition's var scope is SHARED into `infer_lambda`, not freshly allocated
  and NOT reset at the lambda boundary; an inner `:a` resolves to the SAME
  rigid TypeId as the enclosing `defn`'s `:a`, and a fresh identifier first
  appearing in the inner `fn` still registers in (and is quantified at) the
  enclosing definition's scope (corrected §3.3 SCOPE-5 co-reference MUST).
  FV-20's seam; includes the e2e-unreachable neg — an inner-body ASSERTION
  forcing the co-referring rigid concrete (`:a "hello"` inside the `fn` body)
  errors as skolem-escape — which 0591's parse gap keeps out of the e2e tier;
- **u8** — a QUALIFIED lowercase annotation (`:user/int`) takes the §3.9.3
  unknown-type error path, never mints (FV-21's seam; F2/0589 — the guard
  must land at ALL FOUR mirror mint sites per 0590, or the discrimination
  diverges per-site).

Sweep for further cells in the family (enumerated so none falls through;
`/testing` probes each and adds the cell with its observed polarity):

- `let` binding annotation with a free var (verify-first: may share the
  defn-param seam — if a distinct codepath, it gets its own FV row). **W6.2
  re-read:** the polarity flips with the model — a CONCRETE initializer under
  a free `:a` let annotation (`(let [:a x 5] …)` inside a defn) is now a
  skolem-escape NEGATIVE per MUST-3 (under the old flexible reading it would
  have acquired); the positive is an `a`-typed initializer (a param);
- higher-order param (`:(Fn [a] a) f`) — free vars inside an `Fn` annotation.
  **W6.2 re-read:** a body use that concretizes the var (`(f 3)` with
  `f : (Fn [a] a)`) is now skolem-escape (MUST-4); the usable pattern is the
  `a`-generic pass-through, and the CALL SITE instantiates `a` per MUST-1.
  Verify-first, then row it with both polarities;
- top-level expression annotation `:a form` / `:(Box a) form` outside any
  definition (§1.4.5/§2.3.8/§4.9) — FV-10 covers the codegen-reaching arm.
  **W6.2 re-read:** the old pinned-by-context arm ("`:a 5` → unifies to
  Int?") is now expected to be the MUST-3 REJECTION (a concrete literal
  cannot discharge a bare quantified var); the top-level boundary question is
  SETTLED by the 2026-07-14 §3.3 co-reference rescribe — "a top-level `def`
  binding is itself the generalization boundary", so bare `:a 5` and
  `(def y :a 5)` are normatively skolem-escape errors (no `/spec` FIXME
  needed); verify-first is now only the observed-vs-spec probe;
- `deftrait` method signature (GREEN control — type vars are normative there)
  and `impl` target/method sigs;
- written CONSTRAINED-var display syntax as input (`[:Num a]` parses as a
  param NAMED `a` constrained by Num per §5.1.1 EBNF — confirm no fixture
  accidentally relies on it reading as "var a with constraint").

Consistency negative (the uniformity lens this matrix exists for): the SAME
annotation shape must behave identically across positions (`defn` param vs
`fn` param vs body annotation vs `let`) — a per-position divergence is the
codepath-duplication smell; FV-3/FV-15's twin-parity facets are its guards.
**W6.2 extends the lens to the model itself:** assert-not-acquire (MUST-3)
and the MUST-4 asymmetry must hold UNIFORMLY at every annotation position
and every mint site (the 0590 four-way mirror is the standing risk — a site
that keeps minting flexible, or keeps minting for qualified names, diverges
exactly where the matrix has no cell; FV-16..FV-21 are the cells).

#### L.2 W6 in-scope `/testing` execution items (recorded for wave-gate accounting)

Not plan rows — `/testing` execution work scheduled INSIDE W6, recorded here
so the wave gate accounts for them:

1. **FIXME 0586** — invert/delete/regen the 5 superseded pre-§17.2.1
   "pull-visible-command" agent-lane e2e tests per the FIXME's own per-test
   action table (probe channel landed in W2; the five now assert removed
   behaviour). Includes the golden regen. The separate pre-existing `set-doc`
   resolution defect flagged in that FIXME is NOT folded in — it needs its
   own triage row (`/qa` to attribute when the repro lands).
2. **vec-assoc nondeterministic garbage** (W1 finding, `/stdlib`,
   stash-confirmed PRE-EXISTING; SPRINT.md §Notes) — commit the narrow
   FREE-STANDING failing repro (stdlib-free per root CLAUDE.md
   §Stdlib-separation; `vec-assoc` shape reduced to primitives).
   Nondeterministic wrong value ⇒ likely uninitialized-memory/RC class;
   lands failing-not-ignored with `// defect:` (class per observed evidence —
   `rc-miscount` or `uaf` candidates; `/testing` records what reduction
   shows), owner attribution to backend expected but confirmed at reduction.
   Out of S109 theme → carries ACROSS sprint close as a committed RED guard.

### Phase-5 sequencing note for `/testing`

Author order: (1) the pre-existing-defect REDs + arch-pre-flagged boundaries
FIRST — **DC-12 + DC-13 (the tag-order Blocker rows — decisive, currently
masked by coincident fixtures)**, BR-1/BR-2, FQ-D1, AN-2, AN-5, the AL-6 cycle
row, PM product rows; (1b) the AN-1/AN-3/AN-4 invariance pins (GREEN today —
they must exist BEFORE W1 commit-1 lands to make the two-commit acceptance
checkable); (2) the DC twins (incl. DC-11 and the reframed DC-5, under the
fixture constraint — no free-var param annotations; note DC-12's differing
arities keep it clear of the W6 defect by construction — concrete `:Int`
fields) + AL edge set + DC-14; (3) observability + display rows
(these depend on the `/repl`-specced surfaces and the agent harness;
verify-first items marked above); (4) the §L.1 W6 matrix — W6.2 state: the
15 W6 rows are AUTHORED (GREEN at `e401cce9`); the W6.2 work is (a) author
the FV-16..FV-21 REDs FIRST (they pin the rigid model the `/dev` pass must
implement), (b) REWRITE FV-11's test per its reclassified row (its current
success assertions assert F1/0588's defect behaviour), (c) FV-12 comment
wording only, then the L.2 execution items; (5) remaining GREEN
pins/controls.
Every RED lands failing-not-ignored with `// spec:` + (for defect rows) the
`// defect:` line given in its row.
