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
