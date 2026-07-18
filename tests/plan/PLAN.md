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

### L. W6/W6.3 — written-type-var semantics acceptance matrix (spec §3.3 rows 1–19, SETTLED 2026-07-14 + W6.3.1 rank-model reversal 2026-07-15; supersedes the W6.2 rigid-everywhere matrix)

**Four generations run through this matrix** (kept because each generation's
tests are in the tree and carry `// defect:` records):

- **W6 (`unknown type 'a'`, FIXED at `e401cce9`):** a free lowercase annotation
  identifier took the named-type lookup path. The original FV-1..FV-15 rows
  were authored GREEN at `e401cce9` under the flexible model.
- **W6.2 (rigid-everywhere, IMPLEMENTED at `b2bfb760` = current HEAD, now
  SUPERSEDED):** the user first ruled written vars rigid/definition-scoped;
  `/testing` authored the FV-16..FV-21 REDs + the FV-11 rewrite (`fb6e84c6`)
  and `/dev` landed rigid bare vars + lexical co-reference (`b2bfb760`).
- **W6.3 (SETTLED — user-ruled rows 1–17, empirically grounded; SPRINT.md
  §"W6.3 SETTLED PRINCIPLE"; scribed as spec §3.3.1–3.3.5 + the §3.10
  poly-as-value clause):** REVERSES the rigid-BARE half of W6.2 while KEEPING
  lexical co-reference; rigidity moves onto the CONSTRAINT path. This matrix.
- **W6.3.1 (rank-model REVERSAL, user-ruled 2026-07-15; SPRINT.md §"W6.3
  POLY-AS-VALUE REVERSAL"; scribed as the rewritten spec §3.3.4 + §3.3.5
  rows 10/18/19 + the §3.10 bullet; `/dev` `eb6c94e6`):** REVERSES the
  W6.3 eager poly-as-value rejection — **rank-1 polymorphic function
  RETURNS are legitimate** (written ≡ unwritten); only rank-2 *use* is
  unsupported, and it is rejected **at the use** by mechanisms that already
  exist (value restriction, rank-2-argument unification, §3.11 ambiguity).
  The D-matrix below (Table 1b) is this generation's row set.

**The settled model (one line):** bare `:a` = a named inference variable — it
relates same-named occurrences (incl. into nested `fn`, lexically) and
documents; the body MAY pin it, never an error. A constraint `:C x` is a
checkable claim ONLY at a quantified (parameter / generalizable) position —
held abstract over `C` for the body-check; body-narrowing = skolem escape
(body-only; caller instantiation is always sound). A value-position constraint
is a satisfaction check; a concrete-type value annotation resolves ambiguity
including return-type-polymorphic trait dispatch; an unresolved return-type
poly in a codegen-reaching position is the §3.11 ambiguity error; a rank-1
polymorphic function value may be RETURNED or contained (written ≡ unwritten)
— only rank-2 *use* is unsupported, rejected at the use, never at the
returning definition (W6.3.1; spec §3.3.4).

**The §3.3 MUST band (a)–(k)** — every row below cites it (the retired W6.2
MUST-1..MUST-4/SCOPE-5 band is superseded; `// spec:` comments citing it are
swept in the same `/testing` pass):

- **(a)** §3.3.1 — a bare written variable pins freely; body narrowing is
  never an error (rows 2, 4, 11)
- **(b)** §3.3.2 — a constraint at a quantified position is held abstract;
  body narrowing is a skolem escape, arising from the body ONLY (rows 5–7)
- **(c)** §3.3.3 — a value-position constraint is a satisfaction check (row 12)
- **(d)** §3.3.3 — a concrete-type ascription resolves ambiguity, including
  return-type-polymorphic dispatch; context resolves the same way (rows 13–15)
- **(e)** §3.3.3 — an unresolved return-type polymorphism is the §3.11
  ambiguity error; a value-position constraint does NOT disambiguate
  (rows 16–17)
- **(f)** §3.3.4 + §3.10 — **REVERSED (W6.3.1, 2026-07-15):** a rank-1
  polymorphic function value may be RETURNED or contained, written ≡
  unwritten — `(defn mk [] (fn [:b y] y))` MUST be accepted as
  `∀a. (Fn [] (Fn [a] a))`; a written `:b` MUST NOT be treated differently
  from an unwritten parameter (row 10). The earlier reading of (f) —
  "poly-as-value rejected at the definition" — is superseded; only rank-2
  *use* is unsupported, rejected at the use per (i)/(j)/(k)
- **(g)** §3.3.1 — lexical co-reference, including into nested `fn`; no fresh
  quantification boundary at a nested `fn` (rows 3, 8)
- **(h)** §3.3.1 — caller instantiation is never an error; a lambda-owned var
  applied in place is instantiation-at-use (row 9)
- **(i)** §3.3.4 — a single polymorphic instance used at two types is
  rejected (value restriction): an application result bound by `let` is NOT
  generalized; `(let [f (mkid)] (pair (f "x") (f 5)))` MUST error (row 18)
- **(j)** §3.3.4 — a polymorphic value applied at two types inside a callee
  is rejected (rank-2 argument): a parameter carries ONE monotype for the
  body-check; `(defn apply2 [f] (pair (f "x") (f 5)))` MUST error (row 19)
- **(k)** §3.3.4 + §3.11.3 — a result-only variable left unresolved at a
  codegen-reaching use is the §3.11 ambiguity error, NOT a rank-1 rejection:
  the returning definition IS admitted (sound, code-less until instantiated);
  only an unpinned codegen-reaching *use* errors — `(defn g [] (constf 5))`
  surfaces the §3.11 "pin the type" ambiguity, the R16 monomorphisation
  family

**Empirical grounding at `b2bfb760`** (SPRINT.md, 2026-07-14 REPL probes):
rows 13/14/15 PASS; row 16 leaks `codegen error … __expr entry has no GOT
slot` instead of the §3.11 message; row 2 ERRORS (bare rigid) while row 6
PASSES (trait constraint not rigid) — the current implementation is exactly
INVERTED from the settled model on the rigidity axis.

**Coverage-by-definition-variants axis family** (the standing lens this matrix
realizes; root `CLAUDE.md` §Testing, `tests/CLAUDE.md` §Coverage by definition
variants): **{bare var, trait constraint, concrete type} × {quantified/parameter
position, value position} × {body pins it, body uses only the interface, left
unresolved}** — ONE uniform rule per cell, holding across every annotation
position (`defn` param / `fn` param / body ascription / `let` / `deftype`
field / trait & impl sigs) and every mint site (the 0590 four-way mirror). A
missing cell is where a variant grows its own codepath.

The family map (shape × position; cells point at realizing rows):

| Shape \ position | quantified (param / generalizable binding) | value position (concrete expression) |
|---|---|---|
| bare `:a` | names + relates (R1/R3/R8, FV-4..FV-7 applied forms); body MAY pin (R2, C-1..C-4) | pins to the expression's type (R4/R11); a still-unresolved var stays §3.11-governed (FV-10) |
| constraint `:C` | held abstract; body-narrow = skolem escape (R5 pos / R6 neg); inferred-from-use is NOT asserted (R7) | satisfaction check only (R12 pos+neg); does NOT disambiguate (R17) |
| concrete type | pins the param (§3.9.1; existing concrete-app coverage) | resolves ambiguity incl. return-type dispatch (R13/R14/R15); mismatch still rejected (FV-9 neg) |

Boundary rows outside the 3×2 grid: R16 (unresolved return-type poly = §3.11
error, mode-uniform), the rank-model D-matrix rows R10/D-1/D-2/R18/R19/D-3
(Table 1b — rank-1 poly-return ACCEPTED; rank-2 use / unpinned
codegen-reaching var rejected at the use; W6.3.1 + FIXME 0602), R9
(caller instantiation), the name-discrimination guards FV-13 (uppercase) /
FV-21 (qualified lowercase), and the two review-found cells B-1/B-2
(Table 2b, added 2026-07-14).

**The rank-model discriminator (W6.3.1; SUPERSEDES the 0596
applied/held-as-value axis):** the 0596-era axis — {applied-in-place,
held-as-value} × {concrete-arg, generic-arg}, with held-as-value rejected at
the definition — is retired along with the eager check it calibrated
(`eb6c94e6` removed the discriminator wholesale; B-1's history below records
why it was unbuildable). The settled axis is NOT "written vs unwritten"
either — the written `:b` is irrelevant (written ≡ unwritten parity, §3.3.1).
It is:

- **{define a rank-1 poly-return} → ACCEPT** — every `∀` at the defining
  definition's own boundary (prenex); returned or let-stored-and-returned
  both included (MUST (f); rows 10, D-1 below). Passing uninstantiated is
  not itself a rank-2 *use*, but it is an ACCEPT only when the flow pins
  the var (callee applies it) or returns the closure (making the definition
  a poly-return); a passed closure the callee IGNORES leaves the var
  unpinned at codegen → the §3.11 arm below (D-2; FIXME 0602 correction);
- **{use a poly *instance* at >1 type / pass as a rank-2 argument / hold a
  result-only var unresolved at a codegen-reaching use} → REJECT at the
  use** — by value restriction (MUST (i), row 18), rank-2-argument
  unification (MUST (j), row 19), and §3.11 ambiguity (MUST (k))
  respectively. These three mechanisms were the *real* enforcement of "no
  first-class polymorphism" all along; the eager definition-time check was
  redundant where they fire and wrong where they don't.

**Fixture notes (binding for `/testing`):**

- Annotation precedes the parameter name — `[:a x]`, `[:(Box a) b]` — per
  §5.1.1 EBNF and §3.9 (`:Type form` binds the following form).
- **Trait fixtures are free-standing** (no stdlib; `PreludeVariant::None` or
  `PrimitivesOnly`): `zed : ∀a. Zeroable a => (Fn [] a)` — a `Zeroable`
  deftrait with nullary method `zed`, `Int` impl → `0`, `Float` impl → `0.0`
  (the SPRINT.md empirical fixture, so the syntax is known-good); and
  `nadd : (Fn [a a] a)` — a `Num`-style deftrait (pick a non-colliding name,
  e.g. `Num2`, if the prelude variant binds `Num`) with an `Int` impl via
  `add-i64`. Exact `deftrait`/`impl` syntax per §7 is `/testing`'s.
- **Body-annotation parse gaps (F4/0591) still bind:** body ascriptions parse
  only in the single-arity `defn` body position; cells whose natural fixture
  needs a gapped position route to the unit tier (noted per-row). C-4's
  multi-arity fixture uses PARAM annotations only, which parse.
- There is no return-annotation syntax (§5.1.1); "return position" cells are
  realized as the body ascription.
- Free-standing ADTs as before: `(deftype (Box a) [:a v])`,
  `(deftype (Pair2 a b) [:a x :b y])`, primitives `add-i64`/`str-concat`.

#### L.1 W6.3 acceptance rows (R1–R19 = spec rows 1–19 — R10 reversed + R18/R19 added at W6.3.1, Table 1b; + derived corollaries C-1..C-4, + retained guards)

**Status legend** (all verdicts read against HEAD `b2bfb760`, the rigid-bare
tree): **PIN** = GREEN today, verdict unchanged under W6.3, MUST HOLD through
the `/dev` pass (a regression is over-broadening). **RED** = expected
failing-not-ignored at authoring; flips green at the W6.3 `/dev` pass.
**REWRITE→RED** = an authored W6.2 test currently GREEN whose assertions pin
the SUPERSEDED rigid model — `/testing` inverts it per its row, after which it
is RED until `/dev` lands. **verify-first** = expected verdict stated; observed
state at `b2bfb760` recorded at authoring.

**`// defect:` lines for the REDs:**

- **The six rewritten flips (R2, R4, C-1..C-4) + R11:**
  `class=wrong-reject locus=crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr + unify.rs::unify_with_rigid (W6.2 minted RIGID vars for BARE written names — spec-valid body pins rejected as skolem-escape; §3.3.1 puts rigidity on the constraint path only) found=S109 owner=/dev`
  (vocabulary addition `wrong-reject` recorded in `tests/CLAUDE.md` §Defect-repro
  notation, /qa 2026-07-14)
- **R6:** `class=silent-accept locus=crates/cranelisp-typecheck constraint path (0590 mirror sites: traits/type_resolve.rs x3 + form.rs — a :C x parameter is never held abstract, so the body narrows the claimed-abstract type silently) found=S109 owner=/dev`
- **R10:** RETIRED (W6.3.1) — the "silent accept" this line attributed was the
  CORRECT behaviour; the acceptance is spec (MUST (f)). The `/testing`
  rewrite of `returned_polymorphic_fn_rejected_neg` DROPS its `// defect:`
  line (no defect existed at this cell; the W6.3 eager check that briefly
  enforced the rejection was itself the wrong-reject, removed at `eb6c94e6`).
- **R16/R17:** `class=check-gate-leak locus=crates/cranelisp-typecheck §3.11 finalization gate (unresolved return-type-poly trait dispatch reaches the backend as an __expr-has-no-GOT-slot codegen error instead of the check-side ambiguous-type rejection; message-quality sibling FIXME 0568) found=S109 owner=/dev`
- **B-1:** `class=wrong-reject locus=crates/cranelisp-typecheck/src/program.rs::check_defn_body (escaped_poly_fn) + infer.rs::infer_lambda (lambda_written_vars) (the landed W6.3 discriminator flags any written lambda var still Type::Var after body inference, conflating held-as-value with applied-in-place-at-a-GENERIC-type — §3.3.4's operative "held as a value" condition does not hold, §3.10 makes instantiation-at-use sound; FIXME 0596) found=S109 owner=/dev`

**Table 1 — the seventeen settled rows:**

| Row | Spec row + MUST | Fixture → expected verdict | Test (proposed) | File | Tier | Status | Polarity |
|---|---|---|---|---|---|---|---|
| R1 | row 1, (a) | `(defn id [:a x] x)` → `∀a.(Fn [a] a)`, used at Int AND String in one program | existing `defn_param_bare_free_var_quantifies_and_uses_at_two_types` (ex-FV-1) | tests/spec_03_types.rs | e2e all-modes | PIN | pos |
| R2 | row 2, (a) | `(defn f [:a x] (add-i64 1 x))` → `(Fn [Int] Int)`, `(f 5)` → 6 — the body pin is NOT an error; the scheme reflects the pinned type | REWRITE of `written_var_body_use_cannot_pin_rigid_neg` (ex-FV-19) → `written_var_body_use_pins_freely` | tests/spec_03_types.rs | e2e all-modes + unit U1 | **REWRITE→RED** (b2bfb760 rejects) | pos (was neg) |
| R3 | row 3, (a)/(g) | `[:a x :a y]` ties the two params — realized by the existing eq2 pair: pos `(eq2 1 2)` → 1; neg `(eq2 1 "two")` = call-site unification error | existing `defn_param_same_free_var_reused_unifies` + `_neg_mismatch` (ex-FV-8) | tests/spec_03_types.rs | e2e + unit U2 | PIN | pos+neg |
| R4 | row 4, (a) | `(defn f [:a x] :a "hello")` → `(Fn [String] String)`; `(f "x")` → "x" — the value-position bare ascription relates `a` → String, never an error | REWRITE of `written_var_concrete_ascription_skolem_escape_neg` (ex-FV-16) → `written_var_concrete_ascription_pins` | tests/spec_03_types.rs | e2e all-modes + unit U1 | **REWRITE→RED** | pos (was neg) |
| R5 | row 5, (b) | free-standing `Num2`/`nadd` fixture; `(defn f [:Num2 x] (nadd x x))` → `∀a. Num2 a => (Fn [a] a)` (constrained scheme per §3.4.1 display; result is `self` = `a`, NOT Int) + `(f 3)` → 6 — interface-only use keeps the constrained polymorphic scheme | NEW `constraint_param_interface_use_keeps_constrained_scheme` (absorbs ex-FV-14's substance; FV-14's thin pin retained as control) | tests/spec_03_types.rs | e2e | verify-first PIN (constraint path is non-rigid today → expected GREEN) | pos |
| R6 | row 6, (b) | `(defn f [:Num2 x] (add-i64 1 x))` → **skolem-escape type error** (the body narrows the held-abstract var to Int). Facets: (i) the error is a type error — never `unknown type`, never a codegen frame; (ii) the defn is REJECTED, so a follow-on `(f 3)` errors unresolved | NEW `constraint_param_body_narrow_skolem_escape_neg` | tests/spec_03_types.rs | e2e all-modes + unit U3 | **RED** (t4 evidence: PASSES today — the 0590-mirror-class gap) | neg |
| R7 | row 7, (b) | `(defn f [:a x] (nadd x x))` → `∀a. Num2 a => (Fn [a] a)`, no error — the constraint is INFERRED from use, not asserted; nothing is held abstract | NEW `bare_var_inferred_constraint_not_held_abstract` | tests/spec_03_types.rs | e2e | verify-first pos (b2bfb760's rigid bare may reject constraint accrual → possibly RED today; record observed) | pos |
| R8 | row 8, (g) | `(defn g [:a x] (fn [:a y] y))` → `∀a.(Fn [a] (Fn [a] a))` — inner `:a` co-refers, one var both layers. Call facet: `((g 3) 4)` → 4 AND `((g 3) "t")` errors (co-reference observable) | existing `nested_fn_written_var_corefers_enclosing_rigid` (ex-FV-20 pos facet) — KEEP; co-reference survives W6.3 (name-sweep of the `_rigid` suffix optional) | tests/spec_04_expressions.rs | e2e + unit U2 | PIN | pos |
| R9 | row 9, (h) | (i) `((fn [:a x] x) 3)` → 3 — standalone lambda applied in place (existing ex-FV-15); (ii) NEW in-defn shape: `(defn h [x] ((fn [:b y] y) 3))` accepted — `b` is lambda-owned, quantified at `h`'s boundary, and `3` is caller-instantiation, never an error | existing `fn_lambda_param_free_var_annotation` + NEW `lambda_owned_var_instantiated_in_place` | tests/spec_04_expressions.rs | e2e | (i) PIN; (ii) verify-first pos (the rigid tree may reject the in-place instantiation) | pos |
| R10 | row 10, (f)/§3.10 — **REVERSED (W6.3.1, 2026-07-15)** | `(defn mk [] (fn [:b y] y))` → **ACCEPTED** as `∀a. (Fn [] (Fn [a] a))` — a rank-1 poly-return is legitimate; written `:b` ≡ unwritten (the unwritten twin `mkid` is the same scheme); each `(mk)` instantiates fresh. Twin facets: `weird` `(defn weird [x] (fn [:b y] x))` accepted (`const`'s written twin); the W6.3-era rejection verdict this row carried is SUPERSEDED | REWRITE of `returned_polymorphic_fn_rejected_neg` → `returned_rank1_polymorphic_fn_accepted` (drop the `// defect:` line; add the mkid written≡unwritten twin facet) | tests/spec_03_types.rs | e2e + unit U7 (repurposed) | **REWRITE→GREEN** — behaviour landed at `eb6c94e6`; the CURRENT test is RED pinning the superseded rejection until `/testing` flips it | pos (was neg) |
| R11 | row 11, (a) | `(defn f [] :a 5)` → `(Fn [] Int)`; `(f)` → 5 — a bare value-position ascription pins to the concrete type, no error | NEW `bare_var_value_position_pins_to_concrete` | tests/spec_03_types.rs | e2e all-modes | **RED** (b2bfb760 rejects as skolem-escape — the wrong-reject flip-to-pass) | pos |
| R12 | row 12, (c) | `(defn f [] :Num2 5)` → no error, `(f)` → 5 — Int satisfies Num2; the check changes nothing. NEG twin: `:Num2 "s"` with no String impl → satisfaction-check error naming the trait (accepted IFF the type implements the trait) | NEW `value_position_constraint_satisfaction_check` + `_neg` sibling | tests/spec_03_types.rs | e2e + unit U4 | verify-first (pos expected GREEN today; neg verdict recorded at authoring) | pos+neg |
| R13 | row 13, (d) | Zeroable fixture; `:Int (zed)` → `:primitives/Int 0` — the concrete-type ascription selects the Int impl of return-type-polymorphic dispatch | NEW `concrete_ascription_resolves_return_type_dispatch_int` | tests/spec_03_types.rs (cross-cite §7) | e2e all-modes | PIN (empirically GREEN 2026-07-14) | pos |
| R14 | row 14, (d) | `:Float (zed)` → `:primitives/Float 0.0` — same method, other impl, chosen by the annotation | NEW `concrete_ascription_resolves_return_type_dispatch_float` | tests/spec_03_types.rs | e2e all-modes | PIN (empirically GREEN) | pos |
| R15 | row 15, (d) | `(add-i64 (zed) 5)` → `:primitives/Int 5` — surrounding CONTEXT resolves the dispatch, no annotation needed | NEW `context_resolves_return_type_dispatch` | tests/spec_03_types.rs | e2e all-modes | PIN (empirically GREEN) | pos |
| R16 | row 16, (e) | bare `(zed)` in a codegen-reaching position → the **§3.11 ambiguous-type error** ("ambiguous … add an annotation" class), **MODE-UNIFORM across REPL/`--run`/`--link`** — the sibling disposition of unpinned `[]`. Output MUST NOT contain `GOT slot` / `codegen error` / the `__expr` internal binder (0568). Discrimination facet: bare `zed` (the NAME, no call) at the REPL is disposition-3 introspection display (§3.11.4), not an error | NEW `unresolved_return_type_dispatch_ambiguity_error_neg` (per-mode assertions) | tests/spec_03_types.rs | e2e per-mode | **RED** (leaks `codegen error … __expr has no GOT slot` today — check-gate-leak) | neg |
| R17 | row 17, (e) | `:Zeroable (zed)` → STILL the §3.11 ambiguous-type error — a value-position CONSTRAINT does not disambiguate; only a concrete type does | NEW `value_position_constraint_does_not_disambiguate_neg` | tests/spec_03_types.rs | e2e | **RED** (verify today's shape at authoring — expected the same codegen leak) | neg |

**Table 1b — the rank-model D-matrix (W6.3.1 REVERSAL, user-ruled
2026-07-15):** verdicts read against **`eb6c94e6`** (the `/dev` commit that
removed the eager poly-as-value escape check), NOT `b2bfb760`/`c3008d1f`.
Spec ground: rewritten §3.3.4 ("rank-1 polymorphic function values are
returnable; only rank-2 use is unsupported"), §3.3.5 rows 10 (flipped to
accept), 18, 19, the corrected §3.10 first bullet, and MUSTs (f)/(i)/(j)/(k).
Empirical ground truth verified at `eb6c94e6` (`mk4` leg CORRECTED per FIXME
0602, `/testing` verification): `mk`/`weird`/`mkid`/`const`/`mk3` ACCEPT;
**`mk4` does NOT** — its fixture callee `(defn takes [g] 0)` IGNORES its
argument, so `mk4` returns `0` (not the closure) and is no rank-1 poly-return;
the closure's type var is never pinned and reaches codegen → the clean
**§3.11 ambiguous-type error** ("add an annotation to pin the type of the
polymorphic value bound in `mk4`"; MUST (k), the D-3/R16 family). The framing
is decisive: a passed-and-RETURNED variant (`(defn hold [g] g)` +
`(defn mk4r [] (hold (fn [:b y] y)))`) IS a rank-1 poly-return and ACCEPTS,
and a callee that APPLIES `g` (`(g 5)`) pins the var and also accepts. The
multi-type-use `let`, `apply2`, and `(defn g [] (constf 5))` fixtures reject
by their real mechanisms (value restriction / unification / §3.11 ambiguity).
Fixture note: `constf` = `(defn constf [x] (fn [y] x))` (the unwritten
`const` shape, named to avoid prelude collision).

| Row | Spec + MUST | Fixture → expected verdict | Test (proposed) | File | Tier | Status | Polarity |
|---|---|---|---|---|---|---|---|
| D-1 | §3.3.4, (f) — **REVERSED**: let-stored-and-RETURNED ACCEPTS | `(defn mk3 [] (let [g (fn [:b y] y)] g))` (let-stored-and-returned) → **ACCEPTED** as `∀a. (Fn [] (Fn [a] a))` — `let` bindings are monomorphic (§3.4 — no generalization at `let`); `g` is used once and flows to the enclosing `defn` boundary, where generalization happens (§3.3.4 ¶1), and the closure IS the return value (rank-1 poly-return, same scheme as `mk`). The W6.3-era "stays rejected" fence verdict is SUPERSEDED. (The former blanket "held-as-value trio ACCEPTS" claim grouped `mk4` here — WRONG for the ignored-closure framing; `mk4` moved to D-2 per FIXME 0602) | `let_stored_rank1_fn_returned_accepted` (the accept half of the 0602 split of the retired `held_as_value_polymorphic_fn_variants_stay_rejected_neg`) | tests/spec_03_types.rs | e2e + unit U7 (repurposed) | **LANDED GREEN (W6.3.1)** — behaviour landed at `eb6c94e6`; split test authored + green | pos (was neg) |
| D-2 | §3.3.4 mech. 3 + §3.11/§3.11.1, (k) — **the D-3/R16 FAMILY** (0602 correction: NOT an accept, and NOT a rank-1 rejection) | `(defn takes [g] 0)` + `(defn mk4 [] (takes (fn [:b y] y)))` (passed-and-IGNORED) → the **§3.11 ambiguous-type error** — `takes` never applies `g` and `mk4` returns `0`, not the closure, so the closure's type var is never pinned and reaches codegen unpinned (§3.11.1: "an argument passed to a function that is itself evaluated"). Facets: (i) the message is the clean §3.11 class ("ambiguous type; add an annotation to pin the type of the polymorphic value bound in `mk4`") — no GOT-slot/`__expr`/codegen leak — and `mk4` MUST NOT be silently defined; (ii) mode-uniform (`--run` exit 1, same message); (iii) contrast controls verified by `/testing`: a callee that APPLIES `g` (`(g 5)`) pins the var → `mk4 : (Fn [] Int)` accepts; a callee that RETURNS `g` is a D-1-class poly-return → accepts | `passed_uninstantiated_poly_fn_unpinned_ambiguity_neg` (the neg half of the 0602 split) | tests/spec_03_types.rs | e2e | **LANDED GREEN (W6.3.1)** — spec-correct rejection verified at `eb6c94e6` (clean §3.11 message, both modes) | neg |
| R18 | row 18, (i) | `(defn mkid [] (fn [y] y))` then `(let [f (mkid)] (pair (f "x") (f 5)))` → **error** — value restriction: the application result `(mkid)` is ONE monomorphic instance, not generalized; using it at `String` AND `Int` is a unification conflict. Facet: the error is a type error, never a codegen frame. This is a *retained genuine restriction* — it was the real enforcement all along, not the eager check | NEW `single_poly_instance_used_at_two_types_value_restriction_neg` (free-standing `pair` via `(deftype (Pair2 a b) [:a x :b y])`) | tests/spec_03_types.rs | e2e + unit U7 (repurposed) | **GREEN PIN** (verified rejecting at `eb6c94e6`) | neg |
| R19 | row 19, (j) | `(defn apply2 [f] (pair (f "x") (f 5)))` → **error** — rank-2 argument: the param `f` carries a single monotype for the body-check, so it cannot serve both `String` and `Int`; the §3.10 "no rank-2 polymorphism" restriction. *Retained genuine restriction* | NEW `rank2_argument_applied_at_two_types_neg` | tests/spec_03_types.rs | e2e + unit U7 (repurposed) | **GREEN PIN** (verified rejecting at `eb6c94e6`) | neg |
| D-3 | §3.3.4 mech. 3 + §3.11/§3.11.3, (k) — **the R16 FAMILY** (monomorphisation of not-arg-determined result vars), NOT a rank-1 rejection | `(defn constf [x] (fn [y] x))` then `(defn g [] (constf 5))` → the **§3.11 ambiguous-type error** at the codegen-reaching unpinned use — `g`'s result var is nobody's argument-carried quantifier (contrast `weird`, which DEFINES the template and accepts), so no use can pin it and codegen has nothing to mint. Facets: (i) the error is the §3.11 "pin the type" class, never `rank-2`/`cannot be returned`, never a codegen frame; (ii) per MUST (k) the *returning-definition admission* is the requirement to watch — a future fix must move the error to the codegen-reaching use, not re-reject definitions. CARRIED alongside R16 (same §3.11 error-quality seam; R16's check-gate-leak caveat applies here too — verify the observed error shape at authoring) | NEW `result_only_var_unresolved_use_ambiguity_not_rank1_neg` | tests/spec_03_types.rs | e2e | **verify-first** — rejection confirmed at `eb6c94e6`; record whether the surfaced message is the §3.11 class or the R16-style codegen leak (if leak: same `check-gate-leak` defect line as R16, same owner) | neg |

**W6.3.1 `/testing` reclassification (in-scope for the wave gate — the two
`spec_03_types.rs` tests `/dev` named at `eb6c94e6`):**

1. `returned_polymorphic_fn_rejected_neg` → **rewrite to accept `mk`**
   (R10 row above): assert `:(Fn [] (Fn [a] a)) user/mk` present, `--run`
   leg succeeds; drop the `// defect:` line (retired above); re-ground the
   `// spec:` comment on §3.3.4 MUST (f) row 10.
2. `held_as_value_polymorphic_fn_variants_stay_rejected_neg` → **SPLIT per
   FIXME 0602** (supersedes this item's original "rewrite to accept
   `mk3`/`mk4`" instruction — `mk4` does not accept):
   `let_stored_rank1_fn_returned_accepted` (`mk3` accepts — D-1, MUST (f))
   + `passed_uninstantiated_poly_fn_unpinned_ambiguity_neg` (`mk4` is the
   §3.11 ambiguity — D-2, MUST (k), the D-3/R16 family).

Both were RED at `eb6c94e6` pinning the superseded rejection; the R10
rewrite and the D-1/D-2 split landed GREEN. Adjacent legs that MUST NOT move in the same pass:
B-1's `lambda_applied_in_place_at_generic_arg_accepted` (GREEN at
`eb6c94e6` — the eager check whose over-fire it pinned is gone) and
`let_stored_polymorphic_fn_applied_in_place_accepted` (GREEN; its
"contrast mk3 rejected" comment prose needs the same re-grounding sweep).
The R18/R19/D-2/D-3 rows land as NEW guards in the same batch so the retained
restrictions are pinned before anyone "simplifies" them away.

**Table 2 — derived corollaries** (rewrites of W6.2 negatives whose fixtures
are NOT verbatim rows 1–17; each verdict DERIVES from MUST (a) — a bare
variable imposes no checking obligation — plus (g) where noted. If `/dev`
finds a contrary reading, escalate via `/spec`, do not improvise):

| Row | MUST | Fixture → expected verdict | Test (rewrite) | File | Tier | Status | Polarity |
|---|---|---|---|---|---|---|---|
| C-1 | (a) | ex-FV-17: `(defn g [:a x :b y] :a y)` — two bare names TIED by the body MERGE (ordinary HM unification of two inference vars): accepted; scheme collapses to `(Fn [a a] a)` | REWRITE of `written_var_distinct_rigid_ascription_skolem_escape_neg` → `bare_vars_tied_by_body_merge` | tests/spec_03_types.rs | e2e | **REWRITE→RED** | pos (was neg) |
| C-2 | (a), applied form | ex-FV-18 neg leg: `(defn h [:(Box Int) b] :(Box a) b)` — accepted; `a := Int` pins through the constructor → `(Fn [(Box Int)] (Box Int))`. The pos control `applied_annotation_rigid_var_corefers_param` is UNCHANGED (name/comment sweep only) | REWRITE of `applied_annotation_rigid_var_concrete_mismatch_neg` → `applied_annotation_bare_var_pins_through_ctor` | tests/spec_03_types.rs | e2e | **REWRITE→RED** | pos (was neg) |
| C-3 | (a)+(g) | ex-FV-20 neg leg: `(defn outer [:a x] ((fn [:a y] y) "s"))` — the inner `:a` CO-REFERS (one var, per (g)) AND the body application pins it (per (a)): accepted, `(Fn [String] String)`, `(outer "x")` → "s". Co-reference stays observable via R8's `((g 3) "t")` error facet | REWRITE of `nested_fn_written_var_corefers_enclosing_rigid_neg` → `nested_fn_corefering_var_pinned_by_body` | tests/spec_04_expressions.rs | e2e + unit U2 | **REWRITE→RED** | pos (was neg) |
| C-4 | (a) per clause + §5.1.2 clause independence | ex-FV-11 — RESTORES the original W6 positive: `(defn h ([:a x] (add-i64 x 1)) ([:a x :Int n] (str-concat x x)))` — each clause's bare `:a` is pinned by ITS OWN body: `(h 5)` → 6, `(h "ab" 0)` → "abab"; the two different pins ARE the observable clause-independence guard | REWRITE of `multi_arity_written_var_body_pin_skolem_escape_per_clause_neg` → restore `multi_arity_same_written_var_independent_per_clause` | tests/spec_05_definitions.rs | e2e + unit U9 | **REWRITE→RED** | pos (was neg) |

**Table 2b — review-found boundary cells** (added 2026-07-14 from the W6.3
change-set review of `c3008d1f`; FIXMEs 0596 + 0600 — both cells were absent
from the matrix, and their absence is where the landed discriminator grew its
over-fire unobserved. Unlike Tables 1–2, verdicts here read against
`c3008d1f`, the landed W6.3 tree):

| Row | Spec + MUST | Fixture → expected verdict | Test (proposed) | File | Tier | Status | Polarity |
|---|---|---|---|---|---|---|---|
| B-1 | §3.3.4 + §3.10, (f)/(h) — applied-in-place × GENERIC-arg: the "held as a value" condition does NOT hold | `(defn f1 [x] ((fn [:b y] y) x))` AND `(defn f2 [:a x] ((fn [:b y] y) x))` — the annotated inner lambda is APPLIED IN PLACE to a generic-typed argument (the enclosing defn's own quantified var); application binds `b` to it and NO function value stays polymorphic anywhere (the returned value is `y`'s value, not a `fn`) → both ACCEPTED, `f1 : ∀a. (Fn [a] a)` (instantiation-at-use, always sound per §3.10) | NEW `lambda_applied_in_place_at_generic_arg_accepted` (both f1/f2 facets — bare-enclosing and co-annotated-enclosing) | tests/spec_03_types.rs | e2e + unit U7 (the two repros join the unit tier beside the existing U7 pair) | **GREEN** — was RED at `c3008d1f` (wrong-reject, 0596 Blocker), flipped by the 0596 fix (`750471ac`) and moot since `eb6c94e6` removed the eager check wholesale. **Fence framing REVERSED by W6.3.1:** the original "adjacent legs stay put" clause required the held-as-value trio (mk/mk3/mk4) to stay REJECTED — under the settled rank model `mk`/`mk3` ACCEPT (Table 1b R10/D-1) while `mk4` — passed to an IGNORING callee — is the §3.11 ambiguity (D-2; FIXME 0602 correction); R9's legs + the pinned-by-use `(let [g (fn [:b y] y)] (g 3))` stay accepted as before. The retained-restriction fence is now R18/R19/D-3 | pos |
| B-2 | §3.3.2 × the **fn-param position** — a lambda param is a quantified position (quantified at the enclosing definition's boundary), so §3.3.2's "a parameter" reading naturally covers it | free-standing trait fixture; `(fn [:NumT y] (nadd y y))` → **CURRENT behaviour** at `c3008d1f`: `unknown type 'NumT' (from module '')` — the §3.9.3 try-type-then-trait fallback exists at the defn-param seam (`register_defn_signature` → `resolve_bound_param`) but NOT at `infer_lambda`'s param resolution; a trait constraint is inexpressible at the fn-param position. PRE-EXISTING (not introduced by `c3008d1f`) | none authored — recorded cell; test rows land when the closing effort picks it up | — | (unit-tier candidate at pickup) | **KNOWN-LIMITATION / scope caveat** — closing it is OUT of the W6.3 landed scope; it rides the open 0590 convergence (constraint rigidity reaches `defn` params ONLY today; fn params / let / trait-impl sigs untouched — `infer_lambda` is exactly a 0590 mirror site missing the ONE mint/fallback capability) or a future constraint-position-uniformity pass. NO fix verdict asserted here. **Desired end-state for the future record:** fn-param constraints behave IDENTICALLY to defn-param — held abstract for the enclosing body-check, R5/R6 logic per cell; if that derivation is contested at pickup, escalate via `/spec` (per the Table-2 note), do not improvise. Error-shape note: independent of when support lands, the R6/R12 band's "never `unknown type` for a recognised constraint shape" applies to this seam | n/a (recorded, no polarity until a verdict is owned) |

(Related but NOT folded in: FIXME 0597's value-position satisfaction-check
{non-nominal concrete} neg is a separate `/dev`-targeted defect in R12's neg
family — it keeps its own FIXME and joins the matrix when triaged.)

**Table 3 — retained guards** (verdicts UNCHANGED under W6.3; GREEN at
`b2bfb760` unless noted; `// spec:` comment-band sweep to (a)–(k) only):

| Row | Test | W6.3 disposition |
|---|---|---|
| FV-2 | `defn_param_bare_free_var_not_unknown_type_neg` | PIN — §3.3 ¶[S109]: a written free lowercase var is never a named-type miss |
| FV-3 | `written_var_vs_inferred_var_identical_scheme_twin` | PIN — and the W6.2 "scheme-parity ONLY" scope note is DELETED: under W6.3 a bare written var IS an ordinary inference var + name, so written/inferred parity is TOTAL (in-body too). Optional extension facet once R2 lands: `(defn fw [:a x] (add-i64 1 x))` and `(defn fi [x] (add-i64 1 x))` both → `(Fn [Int] Int)` |
| FV-4 | `defn_param_free_var_nested_in_applied_type` | PIN (unbox; MUST (a) discharge via ordinary unification) |
| FV-5 | `defn_param_multi_var_applied_annotation` | PIN |
| FV-6 | `written_var_param_and_body_annotation_corefer` | PIN — `(defn id [:a x] :a x)` → `(Fn [a] a)`; discharge is now trivial co-reference unification; (g)-adjacent |
| FV-7 | `defn_param_two_distinct_free_vars_independent` | PIN — call-site mixed types prove independence when the body does NOT tie the vars; the in-body tie case moved to C-1 (merge, not error) |
| FV-9 | `defn_param_free_var_and_concrete_mixed` + `_neg` | PIN — concrete param cells still constrain |
| FV-10 | `free_var_annotation_codegen_reaching_is_ambiguity_not_unknown_type_neg` | PIN — the §3.11 per-mode dispositions; now also R16's sibling under MUST (e) |
| FV-12 | `multi_arity_unpinned_free_var_variant_ambiguous_not_unknown_type_neg` | PIN with RE-GROUNDING: the W6.2 skolem-escape grounding is REMOVED — the row stands on §5.1.2's poly-variant rule alone. Under W6.3 the delegating clause's `:a` is in-principle pinnable by delegation (R2 logic + arity-unique dispatch); whether cross-clause delegation MUST pin (making the fixture compile) is FIXME 0576's open question. HARD assertions kept: never `unknown type`, never silent acquisition of the sibling's `:Int`s; the accept-vs-ambiguous-variant disposition stays SOFT pending 0576 |
| FV-13 | `unknown_uppercase_type_annotation_still_errors_neg` + `_nested_` sibling | PIN — the minting rule keys on bare-LOWERCASE exactly; uppercase unknowns still error (§3.9.3) |
| FV-14 | `trait_constraint_annotation_unaffected_by_free_var_rule` | PIN as thin control; substance upgraded by R5 (pos) + R6 (neg) |
| FV-21 | `qualified_lowercase_annotation_unknown_type_not_minted_neg` | Verdict unchanged under W6.3 (a QUALIFIED lowercase name is a named-type reference, never a var — F2/0589). Verify-first at `b2bfb760`: the W6.2 `/dev` pass may have closed the mint sites; record observed state |

**Row accounting: 40 rows** (was 35; **+4 at W6.3.1**: R18, R19, D-1, D-3;
**+1 at the FIXME 0602 correction**: D-2 split off D-1) —
19 settled spec rows (R1–R19; R1/R3/R8/R9(i) realized by existing ex-FV
tests; R10 REVERSED to accept; R18/R19 added with the rewritten §3.3.5),
3 rank-model D-rows (D-1 `mk3` reversed-to-accept, D-2 the `mk4`
ignored-closure §3.11 ambiguity per 0602, D-3 the R16-family carry),
4 derived corollaries (C-1..C-4), 2 review-found boundary cells (B-1 now
GREEN, B-2 recorded known-limitation), 12 retained guards.

**W6.2 → W6.3 reclassification summary (what `/testing` flips):**

- **6 authored tests INVERT** (currently GREEN pinning the superseded rigid
  model; each rewrite lands RED until `/dev`): ex-FV-19 → R2 (`(Fn [Int] Int)`,
  was skolem-escape); ex-FV-16 → R4 (`(Fn [String] String)`, was skolem-escape);
  ex-FV-17 → C-1 (vars merge, was distinct-rigid error); ex-FV-18 neg leg → C-2
  (`a := Int` pins through the ctor, was error); ex-FV-20 neg leg → C-3
  (co-referring var pinned by body, was skolem-escape); ex-FV-11 → C-4
  (per-clause body pins restored, was per-clause skolem-escape).
- **4 NEW REDs fail on the current tree:** R6 (constraint not held abstract —
  passes today, MUST error), R10 (returned poly fn — **SUPERSEDED by W6.3.1**:
  the rejection this RED demanded was landed at `c3008d1f` and then REVERSED;
  see the W6.3.1 block below), R16 (bare `(zed)` leaks a
  codegen GOT-slot error, MUST be the §3.11 message, mode-uniform), R17
  (value-position constraint does not disambiguate).
- **1 flip-to-pass RED:** R11 (bare value-position `:a 5` — rejected today,
  MUST be accepted).
- **New positives:** R5, R7, R9(ii), R12(+neg), R13, R14, R15 (R13/R14/R15
  empirically GREEN — land as PINs).
- **PINs carried:** R1, R3, R8, R9(i) + the 12 Table-3 guards.
- **1 post-landing RED (W6.3 review, reads against `c3008d1f`):** B-1 —
  applied-in-place at a GENERIC arg wrong-rejected by the landed
  discriminator (0596 Blocker); flipped green at the 0596 `/dev` fix
  (`750471ac`) and moot since `eb6c94e6`.
- **1 recorded known-limitation (no RED authored):** B-2 — {constraint ×
  fn-param} inexpressible today (`unknown type`); rides 0590.

**W6.3 → W6.3.1 reclassification summary (rank-model reversal, 2026-07-15;
reads against `eb6c94e6`; what `/testing` flips — enumerated in full in
Table 1b's trailing note):**

- **2 authored tests flip** (were RED pinning the superseded
  poly-as-value rejection; the rewrites landed GREEN):
  `returned_polymorphic_fn_rejected_neg` → R10 accept (`mk`, MUST (f));
  `held_as_value_polymorphic_fn_variants_stay_rejected_neg` → SPLIT per
  FIXME 0602: `let_stored_rank1_fn_returned_accepted` (D-1 accept — `mk3`,
  MUST (f)) + `passed_uninstantiated_poly_fn_unpinned_ambiguity_neg`
  (D-2 §3.11-ambiguity neg — `mk4`, MUST (k); the plan's original blanket
  "mk4 accepts" instruction was a plan error, corrected here).
- **2 NEW GREEN PINs** guard the retained genuine restrictions: R18 (value
  restriction, MUST (i)), R19 (rank-2 argument, MUST (j)).
- **1 NEW verify-first neg:** D-3 (result-only var → §3.11 ambiguity,
  MUST (k)) — the R16 monomorphisation family, carried, NOT a rank-1
  rejection; error-shape recorded at authoring.
- **PINs carried unchanged:** B-1, `let_stored_polymorphic_fn_applied_in_place_accepted`
  (comment-prose re-grounding only), R9's legs.

**Unit-tier enumeration for `/dev`** (the S108-Inc2 deferral discipline: each
named cell gets a guard that FAILS on revert of its fix, in the SAME change-set;
a bare "unit-pinned" without these is a hole):

- **U1 — bare mints an ORDINARY inference variable carrying a display name** —
  NOT rigid (the `b2bfb760` rigid flag comes OFF the bare path), NOT the §3.9.3
  named-type lookup. Seam: `crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr`
  (the mint site). Guards R1/R2/R4.
- **U2 — co-reference threading SURVIVES:** the definition-scoped `var_map`
  threads into `infer_lambda` and across param/body `Annotate` nodes — same
  name ⇒ same TypeId within one definition boundary; a lambda-first-minted name
  later ascribed outside is STILL the same var (0592's keying seam — under
  W6.3 the acquire itself is correct behaviour; the per-mint-site keying
  consistency is what to pin). Guards R3/R8/C-3, FV-6.
- **U3 — a constraint at a quantified position enters the held-abstract
  (skolem) set for the body-check:** unify(held-abstract var, concrete) FAILS
  as skolem escape — by ascription AND by use; unify(flexible, held-abstract)
  succeeds (param acquisition); the caller-instantiation path is untouched.
  Seam: `unify.rs::unify_with_rigid` REPURPOSED (rigid set = constraint-annotated
  vars, not bare) + the 0590 four mirror mint sites (`traits/type_resolve.rs`
  ×3, `form.rs`) MUST route through the ONE mint capability so the
  constraint-rigid rule lands at every site at once — this IS the 0590
  convergence. Guards R5/R6/R7.
- **U4 — a value-position constraint is a satisfaction check only:**
  impl-exists check against the expression's already-known type; NO unification
  into the type, NO skolem, NO type change. Seam:
  `infer.rs::infer_annotate` constraint arm. Guards R12/R17 (R17: satisfaction
  alone must NOT count as disambiguation for §3.11).
- **U5 — a concrete-type value ascription resolves return-type dispatch:** the
  ascribed type flows into trait-method instance selection / mono collection
  (§3.6.3). Seam: `infer_annotate` + the dispatch/mono-collection seam. Guards
  R13/R14/R15.
- **U6 — the §3.11 gate catches unresolved return-type poly:** the residual-var
  detector at the post-inference finalization boundary fires for a
  `(zed)`-shaped codegen-reaching application with no pinning context; the
  error is raised CHECK-side ("ambiguous type; add an annotation"), never
  reaches the backend GOT path, and carries no `__expr` internal binder (0568).
  Seam: the §3.11.1 enforcement seam (program finalization). Guards R16.
- **U7 — rank-model enforcement at the use (REPURPOSED, W6.3.1):** the
  original U7 charge — an eager poly-as-value rejection at the
  generalization boundary — is RETIRED with the check (`eb6c94e6`); do not
  reintroduce it. The unit set inverts to pin the settled model: (i) a
  returned or stored-and-returned rank-1-polymorphic `fn` generalizes at the
  enclosing definition's boundary and is ACCEPTED, written ≡ unwritten
  (guards R10/D-1 — a regression here is the eager check creeping back;
  a passed-and-IGNORED closure is NOT in this set — its unpinned var is the
  §3.11 ambiguity, D-2/FIXME 0602);
  (ii) an application result is NOT generalized at `let`, so one instance
  unified at two types FAILS (value restriction; guards R18); (iii) a
  parameter carries one monotype for the body-check, so applying it at two
  types FAILS (guards R19); (iv) applied-in-place instantiation stays sound
  at concrete AND generic args (guards R9/B-1 — the `eb6c94e6` unit-test
  rework in `program/tests.rs` seeded this set; audit it covers all four
  cells). Seams: the §3.4 generalization boundary + `unify.rs`.
- **U8 — name-discrimination guards retained:** uppercase unknown → §3.9.3
  error path (FV-13); qualified lowercase NEVER mints, at ALL 0590 mirror
  sites (FV-21).
- **U9 — multi-arity clause scoping:** sibling clauses are DISJOINT lexical
  scopes — clause-local bare vars pin independently (C-4's seam; unchanged by
  co-reference, which merges NESTED scopes only).

**Open-FIXME interactions** (dispositions are the owners'/`/sprint`'s; recorded
so the wave gate sees them): 0590 becomes the CARRIER of the constraint-rigid
path (R6's fix = the convergence); 0588's co-reference half landed at
`b2bfb760` and survives, its rigid-bare half is reversed; 0592's
ascription-acquire face STOPS being a defect under W6.3 (bare acquire is
correct) — its residual is per-mint-site keying consistency (U2); 0593
(`suppress_rigid_annotations`) re-scopes to the constraint-skolem model; 0595's
`unify_with_rigid` hardening survives repurposed (U3); 0568 is R16's
message-quality sibling; 0576 governs FV-12's soft disposition; 0591 keeps the
body-ascription parse gaps that route cells to the unit tier; 0596 (Blocker,
`target: /dev`) was B-1's carrier — resolved + deleted at `750471ac`, then the
whole eager check it calibrated was removed at `eb6c94e6` (W6.3.1); 0600
(`target: /qa`) is ACTIONED into B-2 and deleted — its implementation half
rides 0590 (the `infer_lambda` mint/fallback seam is a 0590 mirror site), and
its verdict-derivation half is recorded on B-2 as the non-asserted desired
end-state with the `/spec` escalation route; 0597 stays its own `/dev` FIXME
(see the Table-2b trailing note).

**Sweep items re-read under W6.3** (`/testing` probes each; polarity per the
settled model):

- `let` binding bare-var annotation + CONCRETE initializer → now POSITIVE
  (bare pins freely; the W6.2 skolem-escape reading is superseded).
  Verify-first whether `let` shares the defn-param seam; if distinct, it gets
  its own row (0591 may gate the parse position → unit tier).
- A CONSTRAINT on a GENERALIZABLE `let` binding → a quantified position per
  §3.3.2 ("any binding generalized … so that a caller chooses") → held
  abstract, R6 logic applies. Unit-tier if the position doesn't parse.
- Higher-order param `:(Fn [a] a) f` with body `(f 3)` → now POSITIVE (pins
  `a := Int` per MUST (a)); the pass-through-generic shape stays polymorphic.
- Top-level `:a 5` / `(def y :a 5)` → now POSITIVE (`y : Int` — R11's logic;
  the W6.2 "top-level def is a skolem boundary" reading is superseded).
- `deftrait` method sigs / `impl` sigs → now part of the constraint-rigid path
  PROPER (R5/R6's seam; 0590/0593) — a trait method's own vars are quantified
  positions held abstract during impl-body checks.
- Written constrained-var display syntax as input (`[:Num a]` parses as a
  param NAMED `a` per §5.1.1) — confirm no fixture relies on a contrary
  reading (unchanged item).

**Consistency lens (what this matrix exists to force):** the SAME annotation
shape must behave identically at every position (defn param / fn param / body
ascription / let / trait & impl sigs) and every mint site — {bare, constraint,
concrete} × {quantified, value} × {pins, uses-interface, unresolved} is ONE
rule per cell, everywhere. A per-position or per-mint-site divergence (a site
that keeps bare rigid, or holds a value-position constraint abstract, or lets
a constraint disambiguate) is the codepath-duplication smell; the 0590 four-way
mirror is the standing risk and U3's one-mint-capability convergence is the
structural cure.

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
verify-first items marked above); (4) the §L.1 matrix — W6.3 state: (a)
author the four NEW REDs + the flip-to-pass RED FIRST (R6, R10 [SUPERSEDED
by W6.3.1 — R10 is now an accept row; the Table 1b reclassification + the
R18/R19/D-2/D-3 batch replace this item], R16, R17,
R11 — they pin the settled model the `/dev` pass must implement; add B-1 to
this batch — it pins the 0596 over-fire the follow-on `/dev` fix removes,
RED against the landed `c3008d1f` tree), (b)
REWRITE the six inverted W6.2 tests (R2, R4, C-1..C-4 — their current GREEN
assertions pin `b2bfb760`'s superseded rigid model; each lands RED until
`/dev`), (c) author the new positives (R5, R7, R9(ii), R12, R13, R14, R15 —
the zed/Num2 free-standing trait fixtures; R13/R14/R15 land as GREEN PINs),
(d) sweep `// spec:`/`// defect:` comments from the retired
MUST-1..MUST-4/SCOPE-5 band to the §3.3 (a)–(k) band + FV-12's re-grounding
comment, then the L.2 execution items; (5) remaining GREEN pins/controls.
Every RED lands failing-not-ignored with `// spec:` + (for defect rows) the
`// defect:` line given in its row.

## Sprint 110 — sprint-wide failing-test plan (Phase-3 exit gate, 2026-07-15, /qa)

The QA-first drafting spec for `/testing` (Phase 5 authors to THIS plan before
per-crate D/D/R begins). Scope: `sprints/SPRINT.md` all five buckets. Design
contracts: `design/arch/backend-keyed-consumer.md` (§1 carrier contract, §1.1
hard-miss families, §1.2 REJECT criterion, §3 S1–S24 inventory + W3 grep gate,
§4 wave briefs, §5 W0.b totalization, §6 R-2, §7 0585 guard);
`design/typecheck/type-expr-resolver-convergence.md` (0590);
`design/typecheck/return-poly-dispatch-signal.md` + FIXME 0611 (R16/R17);
`design/int/index-worker-isolation.md` (0604 — attribution CORRECTED, see
`s109-attribution-index-feed-race.md` §2); FIXMEs 0583/0585/0604/0605/0609.
Spec contracts: `spec/03-types.md` §3.3.3 MUST (e)/§3.11;
`spec/05-definitions.md` §5.1.2; `spec/07-traits.md` (trait/HKT sig
resolution); `spec/08-modules.md` §8.5 (type refs resolve in scope);
`spec/12-runtime.md` §12.1.

Discipline reminders binding on this plan: REDs are failing-not-ignored; every
fix pairs a `/dev` unit test in the same change-set (METHOD §2.2); every
deferral to the unit tier ENUMERATES its cases (S108 Inc2); fixtures are
stdlib-free except the §E gate (the ONE sanctioned
`use_workspace_stdlib_for_stdlib_conformance_only()` exception);
language-semantics rows run all modes. A large share of S110 is
**behaviour-invariant plumbing** (0583 W0–W3, R-2, 0606/0608), so this plan
leans harder than usual on (a) invariance gates (suite-green + CLIF
byte-identity + zero library-baseline movement), (b) unit-tier hard-miss
negatives (loud-failure pins that e2e structurally cannot reach — a
well-formed program never produces a missing carrier), and (c) structural
grep gates executed by `/review`. Where a family is unit-tier, its cases are
enumerated here — a bare "unit-pinned" is a hole.

**Vocabulary addition (this pass, /qa):** `class=shared-state-write-race`
added to the controlled `// defect:` vocabulary in `tests/CLAUDE.md`
(requested by FIXME 0604 §Acceptance 4) — a background/concurrent actor
writes substrate a foreground consumer reads, correctness previously resting
on undo/cleanup or scheduling luck. `/testing` retro-tags the 0604 repro
family with it when the fix lands.

### Risk read (summary; full entries in `risks.md` §"S110 risk read")

Highest-silent-failure changes, in order: (1) **W0/W0.b behaviour-invariance**
— the producer change-set touches every mono view and relocates the lenient
builder; a semantic drift ships silently unless byte-identity is gated, and a
**stale cache** (schema 18→19) deserialising `None` carriers post-W1 is a
hard-fail-at-a-distance class; (2) **the soft-fallback hybrid** — one
keyed-read-else-`resolve_driven` arm silently masks every producer gap and
voids the whole initiative (Rev-2 makes it a `/review` REJECT; no test can
see it from outside); (3) **W1 harness red** — backend unit fixtures that
don't populate sidecars flip the whole backend unit suite RED mid-wave
(pinned as a `/dev`+`/testing` W0 obligation); (4) **0590 tightening blast
radius** — the deleted never-error `Named` fabrication may have been
load-bearing (a program that compiled via a fabricated ADT now errors) —
scout BEFORE the flip; (5) **0604 false-green** — a scheduling-perturbation
"fix" that quiets the phantom under one interleaving; the locate-first sweep
is the gate; (6) **R16/R17 false-positive regression** — the S109 revert
class: an outcome-grounded gate that drifts back to surface-type concreteness
re-flags `(add2 3 4)`.

### A. 0583 — backend pure keyed-lookup consumer: per-wave acceptance

The per-site flip sets are `backend-keyed-consumer.md` §3 (S1–S24) — each
wave brief enumerates its sites and `/review` checks carrier coverage per
site. The e2e suite's job per wave is **invariance** (the flips are
behaviour-preserving); the NEW authored guards are the **hard-miss negative
families**, which are **unit-tier by construction**: post-W0 a well-formed
program always carries its resolutions, so carrier-miss/entry-miss states are
only constructible by fixture (the backend unit harness builds both tables
and exprs). The S109 §10.9 BU-1 loud-miss pin is the worked precedent.

#### A.1 W0 (producer) — behaviour-invariance + totalization pins

| Row | Contract | Guard | Tier / owner | Status |
|---|---|---|---|---|
| KC-W0-1 | §4 W0 shippability — carriers ride unread | Full suite green at W0 close; **zero new REDs** vs the S110-entry RED set | e2e (existing suite) / `/dev` runs, `/qa` verifies | [S110] |
| KC-W0-2 | §4 W0.b — CLIF byte-identity: the typecheck-built lenient view lowers identically to the deleted backend-built one | `CRANELISP_CODEGEN_TRACE=1` capture over a fixture set spanning the lenient entry classes (ctor `Def`, synthesised accessor, `f$Var` multi-sig variant, generic template, `__expr` disposition-3 body, non-concretized macro-clause body) — byte-compare pre/post W0.b | e2e-shaped verification harness, run in the W0 change-set / `/dev` + `/testing` | [S110] |
| KC-W0-3 | §8 cache `CACHE_SCHEMA_VERSION` 18→19 | Warm-cache row: cold run then warm run identical result post-W0; stale-cache neg: a pre-bump cache is INVALIDATED wholesale, never deserialised into `None`-carrier views (`tests/cache.rs`, the DC-9/DC-14 template) | e2e / `/testing` | [S110] — author with W0 |
| KC-W0-4 | §5 pin 1 — every synthesised accessor view's ctor arm carries `resolved_ctor` = the owner type's canonical ctor key | typecheck unit (enumerated: product accessor; sum-with-fields accessor; parameterised-type accessor) | unit / `/dev` (typecheck) | [S110] |
| KC-W0-5 | §5 pin 2 — totalization: every codegen-reached `defined_symbols()` entry carries a view after check | typecheck unit + the backend view-absent hard error (`lib.rs:905` flip) as the runtime twin | unit / `/dev` | [S110] |
| KC-W0-6 | **W1 harness pin** (arch §4 W0.a) — backend unit-test fixtures populate `resolved_targets`/mono sidecars | `/testing`+`/dev` obligation recorded HERE so W1 does not red the backend unit suite: `test_support.rs:327/692` callers updated IN W0, fixture sidecars computed from the fixture tables. Acceptance: backend unit tier green at W0 close AND at W1 close | unit-infra / `/dev` (backend) | [S110] — blocking for W1 |

#### A.2 W1 (call seam, flips S1–S9) + W2 (value seam, flips S10–S18)

Positive kind-flip coverage: for each reference kind below, `/testing`
VERIFIES an existing e2e exercises it through the keyed path (all modes where
marked) and authors only the missing cells — the flip is behaviour-invariant,
so pre-existing green tests ARE the flip guards; a kind with no e2e exercising
it is a coverage gap to fill BEFORE its wave lands.

| Row | Kind (wave) | Existing-coverage verification target / new cell | Status |
|---|---|---|---|
| KC-K1 | Concrete user fn call, cross-module + mangled variant (W1) | multi-module call suites (`spec_08`, `mono_mangle_home_collision.rs`) — verify; modes | [S110] — verify-first |
| KC-K2 | Primitive call, GOT-slot (W1) | ubiquitous (`add-i64` everywhere) — verify | [S110] |
| KC-K3 | Ctor `Apply` incl. dotted + colliding names (W1) | DC-1/DC-2/DC-6/DC-12/DC-13 (§S109 D) stay green — these ARE the W1 ctor guards | [S110] |
| KC-K4 | Platform effect + poll shape (W1) | `concurrency_*`/platform suites — verify | [S110] |
| KC-K5 | Extern (`discover-tests`) (W1) | `/run-tests` + discover-tests e2e — verify | [S110] |
| KC-K6 | Callee mode-summary / borrow elision (W1→W2) | `ownership_fences.rs`, `projection_elision_guard.rs` stay green | [S110] |
| KC-K7 | fn-as-value gate + closure-wrapper arity (W2) | `generic_value_use_mono.rs`, HOF suites — verify | [S110] |
| KC-K8 | vec-query primitive as value, both curry legs (W2) | vec-query value-use family (null-got-slot repros, S100–101) stays green | [S110] |
| KC-K9 | Nullary-ctor `Var` + ctor-as-value (W2) | the S109 AN-2 nullary-as-closure class guards stay green; `dotted_ctor_passed_as_argument_and_let_bound` (DC-8) | [S110] |
| KC-K10 | Operator-as-value (backend-synthesized name, §1.4) (W2) | verify an e2e passes a bare operator as a value (e.g. `(map + …)`-shape with prelude ops or primitives-only `(let [f +] …)`); author if missing | [S110] — likely new cell |

Hard-miss negative families (unit tier, backend harness — **enumerated**, per
wave; each asserts a `CodegenError` whose message names the reference and the
miss, and asserts the output is NOT `undefined variable` and NOT a silent
wrong value):

| Row | §1.1 family | Fixture shape (unit) | Wave |
|---|---|---|---|
| KC-N1 | Carrier-`None` on a table-reference kind at the CALL seam | mono `Apply` whose callee `Var` carries `resolved_target: None` but names a table-resident fn | W1 |
| KC-N2 | `Some(fq)` that fetches nothing (entry-miss) at the call seam | carrier names `m/ghost` absent from the fixture tables | W1 |
| KC-N3 | Carrier-`None` at the VALUE seam | value-position `Var`, `resolved_target: None`, table-resident target | W2 |
| KC-N4 | Entry-miss at the value seam | value-position carrier → absent entry | W2 |
| KC-N5 | Slot-less `Polymorphic` template at a value read (the 0585 backstop) | carrier resolves to a `UserFnState::Polymorphic` slot-less template entry → the pinned message "generic value reference '<name>' reached codegen without a mono instance" — release builds included | W2 |
| KC-N6 | Local-variable `None` is NOT a miss | local/lambda param `Var` with `resolved_target: None` compiles (the backend local-`variables` check precedes the keyed read) — the false-positive fence for KC-N1/N3 | W1 |

Structural acceptance (not test rows; `/review` executes, `/qa` audits at
Phase 6/7): **Rev-2 REJECT** — any keyed-read-else-resolver hybrid in a wave
change-set is a Blocker; kinds flip atomically (every §3 site of a kind in
its wave).

#### A.3 W3 (deletion + residue)

| Row | Contract | Guard | Tier / owner |
|---|---|---|---|
| KC-W3-1 | §3 grep gate: zero `resolve_driven\|resolve_chain\|resolve_got_target\|…\|lookup_constructor\|lenient_mono_from_expr` in `crates/cranelisp-backend/src/`; `resolution.rs` retains exactly `got_data_symbol_name` + `inner_fn_discriminator_for` | `/review` structural criterion at the W3 change-set + the post-W3 backend audit's boundary lens; recorded here as the wave's definition of done | structural / `/review` + `/audit` |
| KC-W3-2 | §5 pin 3 — no live caller of `compile_defn` / `lenient_mono_from_expr` (delete or `#[cfg(test)]`) | compile-time (deletion) + `/review` confirms | structural / `/dev` |
| KC-W3-3 | S20 fold onto `ctor_meta_at(arm.resolved_ctor)` is behaviour-invariant | the S109 pattern-position suite (DC-4/DC-11/DC-12/DC-13, BR-1/BR-2) stays green — no new rows | e2e (existing) |
| KC-W3-4 | S19 `None`-arm deletion — a `None` on any ctor arm post-W0.b is keying drift | unit: a mono match arm with `resolved_ctor: None` hard-errors (supersedes the §10.3 fold-in note) | unit / `/dev` (backend) |

### B. 0585 — value-position × {mint, die} matrix (lands under W2)

The class record: MINT (a generic value ref at a concretely-determined type
mints a mono and RUNS) and DIE (an indeterminate generic value ref dies
check-side with the §3.11 message — never a codegen frame, never `undefined
variable`) must hold at EVERY value position. S109 0571.2 fixed the
if/match/vec instances via the uniform `for_each_child_expr` collect; these
rows pin the CLASS so a 4th position cannot silently leak. File:
`tests/generic_value_use_mono.rs` (dedupe against its existing FQ-call /
HOF-arg / control cells and spec_08 FQ-D1). All mint rows
`run_through_all_modes`; die rows assert the §3.11 message + the FQ-D3
no-codegen-frame negative.

| Row | Position | Mint cell (proposed test) | Die cell (proposed test) | Status |
|---|---|---|---|---|
| VP-1 | Apply arg (HOF) | existing `imported_generic_in_value_position_monomorphises` — verify green post-W2 | `generic_value_hof_arg_indeterminate_dies_check_side_neg` (no concrete use anywhere) | [S110] — mint exists |
| VP-2 | Let / ParBind binding value | existing FQ-D1 (`fq_value_ref_generic_fn_concrete_use_never_reaches_codegen`) + S109 0571.2 cells — verify | covered by FQ-D1's error leg | [S110] — verify |
| VP-3 | **if-branch** | `generic_value_in_if_branch_mints_and_runs` — `((if c gcount gother) [1 2])` with concrete use | `generic_value_in_if_branch_indeterminate_neg` | **[S110] — the missing RED (mint leg pins 0571.2's fix; die leg new)** |
| VP-4 | **match-arm value** | `generic_value_in_match_arm_mints_and_runs` | `generic_value_in_match_arm_indeterminate_neg` | **[S110] — missing RED** |
| VP-5 | **vector element** | `generic_value_as_vec_element_mints_and_runs` (`(vec-get [gcount] 0)` applied concretely) | `generic_value_as_vec_element_indeterminate_neg` | **[S110] — missing RED** |
| VP-6 | Return position | `generic_value_returned_then_concretely_used_mints` (rank-1 poly-return legitimacy fence — must NOT regress the S109 W6.3 reversal: `mk`/`weird` shapes stay accepted) | result-only-var case is R16's family (§D) — no duplicate die row | [S110] |

Leg 3 of the arch ruling (the structural guard) is KC-N5 above — one shared
enumeration + the loud W2 backstop + this matrix. `/review` verifies the
`collect_parametric_fn_value_args` whitelist is DELETED in the wave that
touches it. FIXME 0585 closes when W2 + this matrix land.

### C. 0590 — TypeExpr resolver convergence: behaviour-tightening matrix + fence

The convergence deletes the never-error `Named` fabrication arms (mirrors
2/3) and routes trait-sig bare user types through the symbol table (mirror 1
errored on them). Two behaviour changes, each a matrix axis; the fence rows
pin what must NOT broaden. File: `tests/spec_07_traits.rs` (+ typecheck unit
tier for the co-reference pins). Blast-radius scout precedes the flip.

| Row | Cell: head shape × context | Expected post-convergence | Today | Status |
|---|---|---|---|---|
| TX-1 | bare in-scope user type × trait-method sig — `(deftrait T (m [MyType] Self))`, `MyType` a local `deftype` | RESOLVES (spec §8.5: bare ≡ qualified-in-scope); impl + call runs | mirror-1 "unknown type" error | **[S110] — RED (behaviour-tightening positive)** |
| TX-2 | bare in-scope user type × HKT trait sig | RESOLVES against the table (not fabricated) — pin via a working HKT trait whose sig names a user ADT; assert the resolved type behaves nominally (impl dispatch works) | fabricates empty-module ADT (accidentally "works" or silently mis-keys) | [S110] |
| TX-3 | bare in-scope user type × HKT impl method | RESOLVES against the table | fabricates target-module ADT | [S110] |
| TX-4 | unknown uppercase Named × trait-method sig | ERRORS "unknown type" (unchanged — mirror 1 already errored) — GREEN pin | errors | [S110] — pin |
| TX-5 | unknown uppercase Named × HKT trait sig | **ERRORS** — the fabrication deletion made loud | silently fabricates | **[S110] — RED neg** |
| TX-6 | unknown uppercase Named × HKT impl method | **ERRORS** | silently fabricates | **[S110] — RED neg** |
| TX-7 | qualified type × each of the three contexts | RESOLVES via module ref (the FIXME-0436 arm) — GREEN pins | works | [S110] — pin |
| TX-8 | **FV-13 fence** — uppercase-unknown-in-annotation still errors | stays GREEN (over-broadening guard: the mint capability must not swallow unknown TYPES) | green | [S110] — must-hold |
| TX-9 | **FV-14 fence** — trait-path resolution unaffected by the annotation mint | stays GREEN | green | [S110] — must-hold |
| TX-10 | Step-A co-reference pin — platform-sig multi-occurrence free var shares one id (mint-on-miss ≡ the deleted pre-walk) | typecheck unit at `check_type_expr`'s caller (enumerated: two occurrences of `a` in one sig unify; `a` vs `b` stay distinct) | — | [S110] — unit, `/dev` |

**Blast-radius scout (BEFORE the TX-5/TX-6 flip; `/dev` (typecheck) executes,
`/qa` reads the report):** grep every HKT trait/impl sig in tests/, stdlib/,
examples/, exemplar/ for non-intrinsic bare `Named` heads that today resolve
only via fabrication — each hit is either (a) genuinely in scope (TX-2/TX-3
covers it), or (b) a latent mis-key the flip converts to a loud error
(enumerate; fix the source or file the finding). A fabrication that proves
LOAD-BEARING (forward reference inside a cluster) is a staging question
routed through `scope_resolve_in`, never a reason to keep silence
(convergence note §3). Structural criterion for `/review`: zero
`fresh_var`/`fresh_var_id` inside any `TypeExpr`-matching function other than
`resolve_type_expr`'s `mint_free_var` closures; the three free-function
mirrors + their unit suite deleted (cases re-homed onto the canonical
resolver's tests, now covering the `Self` and con-var arms — enumerated in
convergence note §4 step B).

### D. R16/R17 — unresolved-return-poly dispatch signal (coordinated typecheck+int)

The committed REDs are the acceptance spec — they flip GREEN at the fix:

| Row | Committed guard | What flips it | Status |
|---|---|---|---|
| RD-1 | `tests/spec_03_types.rs::unresolved_return_type_dispatch_ambiguity_error_neg` (R16) — bare `(zed)`: §3.11 "ambiguous" message, MODE-UNIFORM (REPL + `--run` + `--link`), NO `GOT slot`/`__expr`/`codegen error`/`has no \`main\`` leak; bare-name `zed` stays disposition-3 introspection | the typecheck finalize gate (class (a)) + the int entry/eval consult (class (b): `validate_main` + `__expr` eval path via the 0611 carrier) | RED today — flips at the wave |
| RD-2 | `tests/spec_03_types.rs::value_position_constraint_does_not_disambiguate_neg` (R17) — `:Zeroable (zed)`: NOT `unknown type`, NOT a GOT-slot leak, IS the §3.11 ambiguity | same change-set | RED today — flips |

False-positive fence (the S109-revert class — **the load-bearing negatives**,
authored/verified BEFORE the wave lands so the two-commit acceptance is
checkable):

| Row | Fence | Test | Status |
|---|---|---|---|
| RD-3 | Arg-directed dispatch stays computable and unflagged | existing `spec_07_traits.rs` `(add2 3 4)` rows stay GREEN; plus NEW explicit cell `arg_directed_dispatch_result_in_value_position_not_flagged` — `(let [r (add2 3 4)] r)` evaluates (an arg-resolved dispatch whose recorded span type is a residual var sits in an ORDINARY VALUE POSITION and must NOT be flagged by the outcome-grounded scan — the exact cell the surface-concreteness gate false-fired on) | [S110] — new GREEN pin, author FIRST |
| RD-4 | Context-pinned return-dispatch stays green | rows 13–15 pins (`:Int (zed)` → 0; `(add-i64 (zed) 5)` → 5) stay GREEN | existing — must-hold |
| RD-5 | Rank-1 poly-return legitimacy unaffected | the W6.3 reversal set (`mk`/`weird`/`mk3` accept) stays GREEN; the result-only-var case (`(defn g [] (constf 5))`) stays the §3.11 ambiguity (same family as R16, same message) | existing — must-hold |

Unit tier (enumerated, `/dev` typecheck): (i) the finalize signal set contains
the bare-`(zed)` span and is EMPTY for `(add2 3 4)`, `(add-i64 (zed) 5)`,
`:Int (zed)`; (ii) `find_ambiguous_value_position`'s dispatch-position verdict
consults the outcome signal, not `!is_concrete()`; (iii) int side: a non-empty
`unresolved_dispatch` at the `main`/`__expr` result span produces the §3.11
error pre-backend (`src/exe.rs::validate_main` + the eval path). Gate:
`/arch` ratifies the 0611 carrier BEFORE the Phase-5 wave.

### E. 0605 — stdlib-compile smoke gate: design CONFIRMED (with two refinements)

Confirming the §6 tier-1 shape with these pins (`/testing` builds):

1. **Enumeration is RECURSIVE, not top-level-only.** The top-level `.cl` set
   (13 modules after skipping `prelude.cl`) would NOT reach `num.bits` — the
   0604 blast radius itself. The gate enumerates every `stdlib/**/*.cl` at
   test time, skipping `prelude.cl` and every subtree declared private by its
   parent (`(mod- name)` — which covers ALL `.test` submodules per the S109
   P5-S2 `(mod- test)` conversion). Enumeration = walk + a light scan of each
   parent `.cl` for `(mod- ` declarations; no hand-list anywhere.
2. **Shape: ONE enumerating test fn, per-module `--run` subprocess loop,
   aggregated failure report.** Per-module discrimination comes from the loop
   (each module compiles in its own subprocess + tmpdir), not from nextest
   binaries: a generated test-per-module would need codegen or a hand-list
   (which rots — the exact blindness this gate cures). The test collects ALL
   failing modules and panics naming each (module + first error line), so one
   run reports the full breakage set, not the first. Generous `.timeout`;
   cache ON within the test's own tmpdir (transitive deps compile once);
   behind `use_workspace_stdlib_for_stdlib_conformance_only()`.
3. **Determinism note:** the gate runs `--run` (batch) — the background index
   feed is REPL-only (R17), so the gate is deterministic by construction and
   is NOT a race guard; the 0604 race is guarded by the ≥25× sweep landing
   with the fix (§F). The gate's job is the CLASS (stdlib-breaking compiler
   regressions cannot ship invisibly).

| Row | Guard | Status |
|---|---|---|
| SG-1 | `stdlib_all_public_modules_compile_and_run` (file: `tests/stdlib_conformance.rs`, new) — every enumerated public module `--run`s a `(import [<mod> [*]])`-shaped probe cleanly, exit 0; failing MODULES named | [S110] — AUTHORED (`c31b6050`); **RED-attributed 2026-07-15: real defect, layered** — 36/37 clean, `derive` fails a compiler defect (quote/quasiquote never desugared outside macro clauses, FIXME 0613 → `/dev`) with a §9.3.4 same-module-helper violation behind it (FIXME 0614 → `/stdlib`). NOT an enumeration refinement; gate stays RED tracing to 0613+0614; both carried S111. Attribution: `s110-attribution-sg1-sg2.md` §1 |
| SG-2 | `agent_flag_errors_on_non_agent_build` build-interleave race (same infra wave, separate root) — nextest setup-script/profile fix so the `--features agent` build cannot clobber the non-agent binary mid-suite; acceptance = the agent e2e family passes in a full-suite run 3× consecutively, no isolation retry | [S110] — `/testing` infra; **attributed 2026-07-15: build-artifact provenance race** (harness hardcodes `target/debug/cranelisp`; agent lane rebuilds the same path). Fix = agent-lane `CARGO_TARGET_DIR` isolation + lane-aware harness resolution, NOT setup-script ordering (FIXME 0615 → `/testing`, rides W-GATE, in-sprint). Risk row S110-11. Attribution: `s110-attribution-sg1-sg2.md` §2 |

Tier-2 (stdlib self-test execution) stays sized-separately, not S110.

### F. 0604 — index-feed write-race: locate-first acceptance (attribution CORRECTED)

The attribution correction is recorded in
`s109-attribution-index-feed-race.md` §2 (this pass): the mutate-live-then-undo
seam was S91-cured (`9ba2ca91`); the prime suspect is the **shared-cache §25.5
write channel** (`write_index_meta` → `record_source_hash`/`record_compiled`),
with the live `&shared.prelude_fallback` thread as the tightening item. The
Phase-5 `/dev` brief targets the cache channel, NOT the cured live-write.

| Row | Acceptance item | Owner | Status |
|---|---|---|---|
| IF-1 | **LOCATE before patching**: ≥25-iteration `CRANELISP_MODULE_TRACE=1` sweep of the deterministic recipe (attribution §3) against the full real stdlib, run FIRST; it must implicate the residual writer (confirm/refute the cache channel per `index-worker-isolation.md` §4, incl. whether `--no-cache` gates the index `.meta` writes). If the phantom persists with all three private snapshots + the §3.3 severance, attribution moves to the foreground import path — STOP and re-scope (flag `/qa`/`/sprint`), do not force the patch | `/dev` + `/testing` | [S110] — gate on the fix |
| IF-2 | Unit test at the located write seam (fail-on-revert), same change-set as the fix (METHOD §2.2) | `/dev` (src/int) | [S110] |
| IF-3 | ≥25-iteration e2e repetition sweep of the deterministic recipe lands WITH the fix (the C1-e2e precedent, §S109 C); every iteration exit 0, never the ambiguity signature | `/testing` | [S110] |
| IF-4 | Twin guards stay GREEN — `spec_08_prelude_outer_scope.rs::super_import_wrapper_over_specific_prelude_compiles_clean` + `…_collides_when_prelude_globs_primitive_neg`. **Do NOT weaken the poison** (the consumer is spec-correct) | standing | must-hold |
| IF-5 | §5 greppable invariant (no live SharedState map into install/typecheck/register calls; zero `shared.cache` writes on any index branch; sole write target `importable_indices`) | `/review` structural criterion | [S110] |
| IF-6 | `concurrency_capacity::same_token_capacity_n_blocking_admits_n_concurrent_nplus1_parks` verify-after-fix: re-run ≥25× post-fix; still flaking ⇒ its OWN defect, attribute separately | `/testing` | [S110] |
| IF-7 | `// defect:` retro-tag of the family with `class=shared-state-write-race` (vocabulary added this pass) | `/testing` | [S110] |

### G. vec-assoc UAF ×2 — repro EXISTS; fix-wave acceptance

The dispatch-time "repro owed" is DISCHARGED: `/testing` committed the reduced
free-standing repro at S109 W6
(`tests/vec_assoc_param_mutate_return_uaf.rs` — 2-line shape, stdlib-free,
`// defect: class=rc-miscount locus=crates/cranelisp-backend … owner=/backend`,
RC-trace-evidenced premature free; REPL garbage-value + `--link` SIGABRT are
the two deterministic surfaces). No further reduction owed. S110 rows:

| Row | Guard | Status |
|---|---|---|
| VA-1 | `vec_set_on_param_returned_and_consumed_repl_yields_correct_value` flips GREEN at the backend RC fix | RED today — the acceptance |
| VA-2 | `vec_set_on_param_returned_link_does_not_corrupt_heap` flips GREEN (exit 99) | RED today |
| VA-3 | Unit test at the RC-emission seam the fix lands on (the param-aliased-return last-use/ownership decision), same change-set; enumerated minimum: (i) `vec-set` on param, returned — no dec before caller use; (ii) `vec-push` sibling; (iii) the identity-fn control stays undamaged (no over-count introduced) | `/dev` (backend) with the fix |
| VA-4 | **Inversion fence**: the OPPOSITE-polarity sibling `tests/vec_cow_value_use_leak.rs` (COW copy-branch LEAK) stays GREEN — an RC fix that flips an under-count into an over-count is the named risk | must-hold |
| VA-5 | Triage aid: the 2-line repro's CLIF (`/clif` or `CRANELISP_CODEGEN_TRACE=1`) makes the early `emit_rc_dec` visible in IR — triage BEFORE patching; scheduling: against the 0583 wave holding `apply.rs`/`heap.rs` open, not interleaved (SPRINT §8) | `/dev` |

### H. C-4 — multi-arity-call-from-`main` "no main" misdirect: repro EXISTS; triage note

Repro DISCHARGED at S109 W6.3:
`tests/spec_05_definitions.rs::multi_arity_call_from_main_batch_no_main_neg`
(RED; `// defect: class=mode-divergence
locus=src/session_v4/lifecycle.rs::lookup_main_code_ptr … owner=/dev`), with
the reduction facts recorded on the test (concrete `:Int` params — W6.3
independent; needs 2+ clauses; trigger = calling it from `main`'s body;
REPL evaluates the identical program fine).

**Attribution triage note (`/qa`):** the evidenced candidate is the int-side
batch-entry path — `main`'s GOT slot/code-ptr lookup
(`lifecycle.rs::lookup_main_code_ptr`) failing only when the batch contains a
multi-arity (overloaded-base + mangled-variant) defn that `main` references.
Triage order for the fixing `/dev` (src/int): (1) `CRANELISP_MODULE_TRACE=1` +
got-trace over the repro — is `main` registered but slot-less, or absent from
the table the lookup reads? (2) discriminate "overload batch derailed main's
codegen" vs "lookup reads the wrong entry kind for the overloaded callee and
aborts the batch" — the misleading message suggests the lookup, the
mode-divergence suggests the batch deriving differently from the REPL's
per-form path (Principle 11: any divergence here is itself the defect). If
the seam lands in typecheck (mangled-variant registration) rather than int,
re-attribute via `/qa` before patching — do not fix at the symptom layer.

| Row | Guard | Status |
|---|---|---|
| C4-1 | The committed RED flips GREEN (exit 7, no bogus no-`main` error) | RED today — the acceptance |
| C4-2 | Unit pin at the seam the fix identifies (batch-entry lookup or overload-batch codegen), same change-set | `/dev` with the fix |
| C4-3 | Mode-parity facet: the REPL control (same defn + `(h 7)`) stays green; post-fix, `run_through_all_modes` on the repro program | `/testing` post-fix |

### I. 0609 — phantom-shim reachability VERDICT: UNREACHABLE → DELETE (with pins)

**Verdict (`/qa`, this pass): the `phantom_member_diagnostic` shim
(`src/process_form.rs:535`, consult at `:450`) is UNREACHABLE post-0571 in
every producible gap shape. `/dev` deletes it in 0609** (with its
now-orphaned `find_named_var_span_in_toplevel`/`find_named_var_span` reach —
note `find_var_span_matching` and `module_has_no_member_error` STAY: they
serve the live FQ-gap arm). Basis, recorded:

1. **Gap-variant reachability.** The shim matches
   `SymbolTypechecked`/`MacroInMem`/`Type` gaps. Workspace-wide, the ONLY live
   constructors of `ResolutionGap::MacroInMem` and `ResolutionGap::Type` are
   unit-test fixtures (`src/process_form/tests.rs`) — no production code
   builds them. The only live variant is `SymbolTypechecked`, built at exactly
   two sites, both inside `checker.rs::resolve_qualified` (typecheck).
2. **Child-shape producibility.** The phantom shape (`<current>.<qualifier>`
   with `<qualifier>` a loaded module) requires a child-path gap. The sole
   synthesis of a `{current}.{qualifier}` module path in the crate is
   `lookup`'s child probe (`checker.rs:1281`). Post-0571 the gap selection
   (`checker.rs:1303–1329`) surfaces the ABS probe's gap in every `Ok` arm —
   including the member-absent case, which now gaps UNCONDITIONALLY
   (`resolve_qualified`, checker.rs:1840–1848) — so the original 0490 shape
   (loaded abs module, missing member) yields the ABS gap and the honest
   diagnostic via the FQ-gap arm, never the child gap. Verified empirically
   on HEAD: `(m/nonexistent x)` with `m.cl` present → `module 'm' has no
   member 'nonexistent'` at the reference span.
3. **The one theoretical residual arm** — abs probe HARD-errors
   (`PrivateInaccessible`, checker.rs:1859) and the fall-through returns the
   child probe's gap (checker.rs:1325) — was probed empirically in all four
   shapes (call/value position × autoloaded/pre-imported module): every one
   surfaces the honest `` `secret` is private to module `m` `` §8.7.3 error at
   the real reference span; the phantom-shaped diagnostic never appears. (The
   exact raise seam producing that real-span visibility error was not located
   in this analysis — an earlier pass raises before the gap path can surface —
   so this leg is empirical, not structural; hence pin D-3 below.)

Deletion-change-set pins (`/dev` src/ + `/dev` typecheck unit; enumerated):

| Pin | Guard |
|---|---|
| D-1 | e2e stays green: member-absent (`module 'X' has no member 'Y'` at ref span — the AL-4 row) + private-member (`… is private to module …`) + missing-module (AL-3) — verify existing S109 rows cover all three; author any missing cell BEFORE the deletion |
| D-2 | typecheck unit at the `lookup` gap-selection seam: (i) loaded-abs-module member-absent surfaces the ABS gap, never a `<current>.<qualifier>` gap; (ii) the abs-Err (private) arm does NOT surface a child gap that reaches the caller as a phantom module reference (pin whatever the located raise seam is) |
| D-3 | **Recommended structural closure (small, same change-set or 0609 follow-up):** flip `checker.rs:1325` to PROPAGATE the abs probe's hard error instead of falling through to the child gap — the §8.6.6 visibility diagnostic is the honest cause, and the child-shaped gap becomes structurally unproducible, converting verdict leg 3 from empirical to structural. This is the "deeper probe-order cure" the shim's comment deferred; with it, deletion is safe against future `ResolveError` variants |

### J. R-2 — `build_adt_entries` caller wiring: behaviour-invariance rows

The builder landed additively (S110 Phase 3, 4 unit tests, cache-neutral).
The Phase-5 caller wiring (typecheck `adt.rs` + `src/bootstrap.rs` become thin
callers) is behaviour-invariant; the acceptance leans on the existing suites
plus twin checks targeting the S109 hand-apply-to-BOTH defect class:

| Row | Guard | Tier |
|---|---|---|
| AB-1 | Entry-shape invariance: existing adt + bootstrap unit suites green; NO cache bump (entry shapes unchanged) — a schema-affecting drift here is a REJECT | unit (existing) |
| AB-2 | **Writer-twin check** (the defect class this cures): a user `deftype` sum and the bootstrap-seeded `IO`/`Option` produce identical entry STRUCTURE per ctor — canonical `member_key` `Def` + bare-alias `Import` edge + internal flags + product dual-facet — asserted through the S109 DC suite (DC-1/2/4/6/7/9, BR-2) + IO-match internal-exclusion staying green; no new e2e needed, the twins already exist BECAUSE S109 keyed both writers | e2e (existing — must-hold set named) |
| AB-3 | `/review` verifies the mirror is DELETED — both writers thin, zero residual entry-construction logic in either caller (the 0585-leg-1 precedent); §8.6.5 contest classification arms keep their semantics, operating on the RETURNED alias | structural |
| AB-4 | Slot allocation stays caller-side: unit pin that builder output carries the pre-allocated `got_slot`s unchanged (no builder-side allocation) | unit (`/dev`) |

### K. src/-hygiene track (0606/0608/0610) — invariance gates only

Pure-decomposition claims are gated per Phase-2 Rev-3: (a) ZERO movement on
any library crate's `public-api.txt` (none should be touched — do not invent
a binary baseline); (b) e2e byte-identity — the golden REPL suite
(`display_exact.rs`, goldens) + full suite green; (c) unit tier green. 0606
additionally: the `fq_arg_tests` three-way split lands with the move
(`repl-decomposition.md` §2) and no `repl/` file exceeds ~1,500 lines
(`/review`). No new test rows — the gates are the acceptance. 0610: no test
surface (hygiene).

### Phase-5 sequencing note for `/testing`

Author order: (1) **RD-3 (the `(add2 3 4)` value-position fence) + KC-W0-6
harness prep + the TX blast-radius scout request** — the fences must exist
BEFORE their waves land; (2) the VP-3/4/5 matrix REDs + TX-1/TX-5/TX-6 REDs
(behaviour-tightening rows, RED-for-the-right-reason against HEAD); (3)
KC-W0-3 cache rows + KC-N1..N6 unit-family handoff enumeration to `/dev`
(backend) — `/testing` verifies the drafted unit set matches the rows at the
wave gate; (4) SG-1 gate + SG-2 infra (low-collision; serialize with other
tests/-touching work); (5) kind-coverage verification sweep (KC-K1..K10) —
verify-first, author only missing cells (KC-K10 likely new); (6) D-1
verification for the 0609 deletion; (7) post-fix items (IF-3 sweep, C4-3
mode-parity, VA flips) ride their fixing waves. Standing REDs (RD-1/RD-2,
C4-1, VA-1/VA-2) are already committed — no re-authoring; they are the
acceptance criteria their waves flip.

## Sprint 111 — sprint-wide failing-test plan (Phase-3 exit gate, 2026-07-17, /qa)

The QA-first drafting spec for `/testing` (Phase 5 authors to THIS plan before
per-crate D/D/R begins). Scope: `sprints/SPRINT.md` §§1–5 (archived at close
as `sprints/archive/sprint-111.md`). Design contracts:
`design/arch/ownership-inference.md` §3.7 (the 3-layer COW ownership root —
`ResultMode::MayAliasOf` + truthful COW facts + prelude-fallback-aware envs,
schema 19→20, ONE coordinated change-set); SPRINT.md §"Architecture review"
§5 (the four carrier-completeness axes — binding input to this plan);
`design/arch/backend-keyed-consumer.md` §1.1/§1.2/§9 (hard-miss families);
`design/arch/principles/24-resolve-once.md` (the battery source);
`audits/cranelisp-backend-s110.md` §2.1 + R2/R7 (backend P24 classification —
cited, not redone; the R2 zero-hit finding; the GOT R7 seam). Spec contracts:
`spec/09-macros.md` §9.4 (incl. §9.4.4 "Legal Wherever an Expression Is
Legal" — the user's 0613 ruling, scribed); `spec/12-runtime.md` §12.1 +
§12.3.1; `spec/03-types.md` §3.11 + §2.3.8/§3.9; `spec/05-definitions.md`
§5.1.2; `spec/08-modules.md` §8.6.4 (prelude ≡ explicit import — the
reachability axis's spec ground).

FIXME dispositions this pass: **0623 ACTIONED → §A below, file deleted**;
**0591 ACTIONED → §G.4 below (the §L-addendum position map + the
spec-conformance judgment), file deleted**. Both per the FIXME-file lifecycle
(the plan rows + the Phase-5 committed REDs are the durable record and
trigger; no FIXME needed alongside a failing-not-ignored repro).

Discipline reminders binding on this plan: REDs are failing-not-ignored;
every fix pairs a `/dev` unit test in the same change-set (METHOD §2.2);
every deferral to the unit tier ENUMERATES its cases (S108 Inc2); fixtures
are stdlib-free (SG-1 is the ONE sanctioned exception, already committed);
language-semantics rows run all modes; RC-trace rows run serially. Wave-order
constraints from the Phase-2 review are load-bearing for authoring order:
**§E (R2 keyed-miss negatives) exists FIRST** (they guard everything after),
then the R4/R5 byte-identity gates (§H), then the schema-20 ownership wave
(§A/§B) with its scoped re-baseline as the wave's last act; the quasiquote
int shield lands ≤ the frontend fold (§C's interaction negatives are the
guard for fold-without-shield).

### Risk read (summary; full entries in `risks.md` §"S111 risk read")

Highest-silent-failure changes, in order: (1) **schema-20 window discipline**
— 0621's `callees` meaning-flip and the COW-fact meaning-flip must sit inside
the ONE bump window; a cache written between two separate bumps carries
schema-20 with alias edges (arch §1 — same CHANGE-SET, not same sprint);
(2) **RC polarity inversion** — fixing the vec-COW under-count (UAF) by
widening converts it into an over-count (leak) the flipped-GREEN repros
cannot see (the S110-8 successor; §A fences); (3) **partial landing of the
3-layer root** — facts (a2) without reachability (a3) leaves declared facts
silently dead in production, the exact gap §3.7 names (§A CW-F3 twins);
(4) **quasiquote fold-without-shield** — macro expansion silently corrupting
quoted literals (§C interaction negatives); (5) **GOT fallible-refactor
caller misses** — one of the 10 enumerated callers keeps `unwrap`/
`unreachable!` and the diagnosed error is UB again on that path (§D);
(6) **P24 mis-classification** — an identity-scan waved through as
"enumeration" (register discipline: grounds per row, acid test verbatim).

### A. CENTREPIECE — vec-COW ownership root: body-shape × branch × face matrix + fences (0623 actioned)

File: `tests/vec_assoc_param_mutate_return_uaf.rs` (+ the leak sibling
`tests/vec_cow_value_use_leak.rs` for shared-source/leak polarity). Spec:
`spec/12-runtime.md` §12.1 (value representation & RC), §12.3.1 (heap free).
Design: `ownership-inference.md` §3.7. This is the standing
coverage-by-definition-variants category made flesh: COW-in-return-position
must behave UNIFORMLY across the body-shape family; the S110 W2 review found
the direct-body cell fixed while let/match siblings still UAF'd.

#### A.1 Acceptance — the 4 committed REDs flip GREEN at the schema-20 wave

| Row | Committed guard (RED today) | Flips at |
|---|---|---|
| CW-1 | `vec_set_let_wrapped_param_returned_and_consumed_repl_yields_correct_value` | the §3.7 change-set |
| CW-2 | `vec_set_let_wrapped_param_returned_link_does_not_corrupt_heap` | same |
| CW-3 | `vec_set_match_arm_param_returned_and_consumed_repl_yields_correct_value` | same |
| CW-4 | `vec_set_match_arm_param_returned_link_does_not_corrupt_heap` | same |

Must-holds: the direct-body pair (`vec_set_on_param_returned_*`, GREEN —
S110's fix) and ALL THREE `vec_cow_value_use_leak.rs` negatives (the
opposite-polarity leak fences — an RC fix that flips under-count into
over-count is the named risk).

#### A.2 The matrix — new cells (variant × {pos, neg}; pin load-bearing cells, don't re-probe all 60)

Axes: body shape {direct [pinned], let-wrapped [RED above], match-arm [RED
above], **if-branch [new]**, **chained COW [new]**} × source branch {rc==1
in-place, rc>1 shared → copy} × face {REPL, `--run`, `--link`} × op
{`vec-set`, `vec-push`}. Positive = correct value + clean exit; negative =
no premature free (RC-trace balanced), no SIGABRT, source unchanged on the
copy branch. The W2 probe list named chained/lambda-captured/nested-double
cells probed SAFE — pin the load-bearing ones:

| Row | Cell | Proposed test (all `// spec: spec/12-runtime.md §12.1`) | Status |
|---|---|---|---|
| CW-5 | if-branch × rc==1 × all modes | `vec_set_if_branch_param_returned_yields_correct_value` — `(defn f [v i x] (if (lt i 0) v (vec-set v i x)))`, returned + consumed; `run_through_all_modes` | [S111] — expected RED with CW-1..4 (same class) — verify against HEAD |
| CW-6 | chained COW × rc==1 × all modes | `vec_push_chained_cow_returns_correct_vec` — `(defn g [v] (vec-push (vec-push v 4) 5))` (inner Fresh result consumed by outer MayAliasOf) | [S111] — probed SAFE at W2; pin as GREEN control |
| CW-7 | vec-push × let-wrapped × REPL + `--link` | `vec_push_let_wrapped_param_returned_*` twins of CW-1/CW-2 (op-uniformity: the SECOND truthful-COW row must not grow its own codepath) | [S111] — expected RED |
| CW-8 | shared-source (rc>1) × let-wrapped × REPL | `vec_set_let_wrapped_shared_source_copies_neg` — source bound twice, COW through the let shape; assert result correct AND source still reads its ORIGINAL element (the copy-branch "wrong thing absent" negative) + clean exit | [S111] |
| CW-9 | shared-source × match-arm × REPL | match-arm twin of CW-8 | [S111] |
| CW-10 | `--run` face for the two RED shapes | convert CW-1/CW-3 programs through `--run` (or fold into `run_through_all_modes` at flip time) — the matrix names three faces; the committed pairs cover only REPL + `--link` | [S111] |
| CW-11 | lambda-captured source | `vec_set_lambda_captured_source_safe` — GREEN control (probed SAFE at W2 review) | [S111] — pin |

#### A.3 Fence 2 — return-position copy-arm residual magnitude (RED → flips at the fix → deliberately re-flips at exactness)

| Row | Guard | Status |
|---|---|---|
| CW-F2 | `vec_set_shared_source_nondirect_return_copy_residual_exactly_one_per_call` (file: `vec_cow_value_use_leak.rs` harness — RC-trace, serial): K-call loop, shared source, COW returned through a NON-direct shape; assert (i) correct values, (ii) NO UAF/SIGABRT, (iii) alloc/free imbalance == EXACTLY K (the §3.7 retain-side conservative over-inc: one count per call — never more). Against HEAD the shape UAFs → RED; flips at the §3.7 fix; **goes RED again when the per-site-fact exactness generalization lands** (imbalance → 0) — at that flip `/testing` updates the assertion to 0 and the `return_cow_source` recognizer deletes (its named deletion trigger). An accidental WIDENING (imbalance > K) fails immediately — that is the fence's job | [S111] — RED |

#### A.4 Fence 3 — declared-fact reachability twins (the a3 leg, e2e face)

The gap §3.7 names: `ClusterEnv` resolves via the fallback-less
`resolve_terminal_entry_and_home`, so §3.1(a) declared-fact precision is
silently dead for prelude-fallback modules. Twin fixture (highest-signal
shape — one invariant, two provenances, SAME assertion):

| Row | Guard | Status |
|---|---|---|
| CW-F3a | `borrowed_declared_primitive_explicit_import_no_percall_rc` — explicit `(import [primitives [vec-len]])`, K-iteration loop over `vec-len` on one vec; RC-trace: inc/dec count on the vec is O(1), NOT O(K) | [S111] — expected GREEN control (explicit chain reaches facts today); **verify against HEAD — if RED, the gap is wider than §3.7 states: report to `/arch` before the wave** |
| CW-F3b | `borrowed_declared_primitive_prelude_fallback_no_percall_rc` — IDENTICAL program, provenance = prelude fallback (`spec/08-modules.md` §8.6.4) | [S111] — **RED** (the fence that would have caught "declared facts silently dead"); flips at a3 |

#### A.5 Schema-20 window + 0621 rider

| Row | Guard | Tier / owner |
|---|---|---|
| CW-S1 | Cache 19→20: warm-cache row (cold then warm identical result) + stale-cache neg (a pre-bump cache INVALIDATED wholesale — never deserialised into mixed-meaning views: alias `callees` edges or false-`Fresh` COW facts). `tests/cache.rs`, the KC-W0-3/DC-9 template | e2e / `/testing` — author with the wave |
| CW-S2 | 0621 rider unit pins, SAME change-set as the bump: `program::tests::callees_renamed_import_records_storage_key` (`[(foo bar)]` → edge `{m, foo}`, never `{m, bar}`) + `callees_bare_accessor_records_member_key` (edge `{m, Box.v}`, never `{m, v}`) | unit / `/dev` (typecheck) |
| CW-S3 | 0621 landing cross-check: `extract_call_graph_edges`' ResolvedCall channel already storage-keyed (post-W0.1b) — verify, record in the change-set | `/dev` verify |
| CW-S4 | ONE-window structural check: both meaning changes (COW facts + `callees`) inside the single commit window that flips `CACHE_SCHEMA_VERSION` | `/review` structural criterion |

### B. Carrier-completeness matrix (arch §5 axes 1–3 — binding input)

The S110 lesson generalized: a carrier whose SEMANTICS are extended needs its
axis×path matrix enumerated before `/dev` writes a line. Axis 4 (behavioural)
is §A above.

#### B.1 Reachability axis — 5 fact-lookup sites × 3 reach paths (unit tier, enumerated)

Sites (from §3.7; `/design` typecheck re-verifies completeness by grepping
`resolve_terminal_entry_and_home`/`probe_module_entry_owned` under
`ownership/` — no sixth site): `ClusterEnv::summary_of` +
`ClusterEnv::terminal_kind` (`ownership/fixpoint.rs:72–93`), the
`UniqClusterEnv` twins (`:388–415`), confinement's read
(`confinement.rs:162`). Paths: {same-module def, explicit-import chain,
prelude fallback}.

| Row | Guard | Tier |
|---|---|---|
| CC-R1..R5 | Per site, a three-path unit: a declared fact (e.g. `vec-len` → `Borrowed` param) reached through EACH path yields the declared summary, not the conservative default — 15 cells, one test fn per site with three-path fixtures | unit / `/dev` (typecheck), enumerated here per the S108 Inc2 rule |
| CC-R6 | Structural (Principle 7): ONE shared prelude-hop helper routed through the existing scope-resolve machinery — zero hand-rolled hops at the five sites | `/review` grep criterion |
| CC-R7 | The `transfer.rs:590` `Fresh` default STAYS for genuinely-unresolvable callees (co-sound with ⊤-`Owned` under the consuming convention — the §3.7 ruling): unit pin that an unknown callee still defaults `Fresh` — the reachability fix must not "cure" the default | unit / `/dev` |
| CC-R8 | E2e face of this axis = CW-F3a/CW-F3b (§A.4) | — |

#### B.2 Variant axis — exhaustive `ResultMode` consumption (structural + two safe-direction pins)

`ResultMode` deliberately carries no `#[non_exhaustive]` (arch §2 note) — the
compiler forces every exhaustive match to be revisited. Test obligations are
the two known BINARY consumers (each collapses the enum to a bool — the
escape hatch exhaustiveness cannot see):

| Row | Guard | Tier |
|---|---|---|
| CC-V1 | `return_is_fresh_by_summary(MayAliasOf(k)) == false` — protect kept (safe direction) | unit / `/dev` (typecheck) |
| CC-V2 | `is_abi_conservative` classifies `MayAliasOf` non-conservative | unit / `/dev` |
| CC-V3 | `/review` greps `_ =>` / `== Fresh` binaries over `ResultMode` consumers — NO third binary beyond the two above; any new one needs its own safe-direction pin | structural |
| CC-V4 | Transfer-join arms unit-enumerated (minimum): `MayAliasOf ⊔ Fresh`, `MayAliasOf(0) ⊔ MayAliasOf(1)`, the widening-toward-Owned direction (monotone soundness — widening always legal) | unit / `/dev`, per `/design`'s arm table |

#### B.3 Producer axis — publish arms + the whole-table `ownership_facts.rs` sweep

| Row | Guard | Tier |
|---|---|---|
| CC-P1 | `origin_to_result_mode` publish arms (`transfer.rs:240–252`): `MayParam{projection:false}` → `MayAliasOf`; `projection:true` NOT; hard `AliasOf`/`ProjectionOf` reserved for unconditional claims — one unit per arm | unit / `/dev` (typecheck) |
| CC-P2 | **Whole-table sweep pin**: a `cranelisp-primitives` unit enumerating the COMPLETE `ownership_facts.rs` table and asserting the `MayAliasOf` row set == exactly {`vec-set`, `vec-push`} at landing — the ask is "no other `Borrowed`-emission primitive declares `Fresh` for a result that can alias an argument", and the pin is the unforgettable form: any new COW-shaped row forces an explicit classification edit to this test. The one-time classification of every existing row (Fresh-legit vs COW-shaped) is executed by `/dev`(primitives) with `/design` input at Phase 5 and recorded in the table rustdoc | unit / `/dev` (primitives) |
| CC-P3 | Fail-on-revert: `vec-set`/`vec-push` no longer declare `Fresh` (the false declaration §3.7 kills) | unit / `/dev` (primitives) |
| CC-P4 | The `cranelisp-primitives/CLAUDE.md` declared-facts contract sentence (§3.7's durable form) lands with the wave — `/qa` verifies presence at Phase 6 | doc, not a test row |

### C. Quasiquote 0613 — form × position × mode matrix + macro-interaction rows

Spec: `spec/09-macros.md` §9.4 (esp. §9.4.4). File: `tests/spec_09_macros.rs`.
Modes {REPL, `--run`} per the FIXME (mode-uniform defect); use
`run_through_all_modes` where the fixture has a `main` (adds `--link` free).
`// defect: class=wrong-reject locus=crates/cranelisp-frontend (missing
pre-build_form desugar wiring) found=S110 owner=/dev` on the repro rows.

Core matrix — form {quote / quasiquote+unquote / unquote-splicing} ×
position {defmacro clause body [GREEN control] / `defn`+`defn-` body /
top-level expr}:

| Row | Cell | Proposed test | Status |
|---|---|---|---|
| QQ-1 | quasiquote+unquote × defn body | `quasiquote_in_defn_body_desugars` — `(defn helper [x] `(if ~x 1 0))` + use; result is the Sexp | **[S111] — RED** (the 0613 one-liner) |
| QQ-2 | quote × defn body | `quote_in_defn_body_desugars` — `(defn f [] '(1 2))` | **[S111] — RED** |
| QQ-3 | unquote-splicing × defn- body | `unquote_splicing_in_private_defn_body_desugars` — `(defn- g [xs] `(begin ~@xs))` via a public caller | **[S111] — RED** |
| QQ-4 | all three forms × top-level expr | `'(1 2)` / `` `(a ~x) `` / splice at top level — three cells, REPL + `--run` | **[S111] — RED ×3** |
| QQ-5 | GREEN control — all three forms × defmacro clause body keep working (the `macro_clause.rs` caller becomes idempotent; the desugar is a fixpoint) | existing defmacro suite + one explicit idempotence pin | [S111] — must-hold |
| QQ-6 | 0614 rider | `stdlib_conformance.rs::stdlib_all_public_modules_compile_and_run` (SG-1) flips GREEN — `derive` compiles with NO stdlib rewrite (confirms 0614 = `/stdlib` no-op) | RED today — the acceptance |

Interaction rows (arch §3 — the fold-without-shield guard; these are the
NEGATIVES that make the int quote-shield's absence loud). Fixture: a
registered macro `m` whose expansion is observably distinct from the literal
(e.g. `(defmacro m [x] 999)`):

| Row | Cell: macro-call shape × context | Must | Status |
|---|---|---|---|
| QQ-I1 | `(m x)` under quote × {defn body, top level} — `(defn f [] '(m x))` | **NOT expand**: the quoted literal survives as the 2-element Sexp list `(m x)` — assert the DATUM (e.g. via `shead`), never `999` | **[S111] — RED-class negative** (fires if fold lands without shield) |
| QQ-I2 | `(m x)` under quasiquote OUTSIDE unquote × both contexts — `` `(m x) `` | **NOT expand** — datum preserved | [S111] — same class |
| QQ-I3 | `(m 1)` under unquote — `` `(a ~(m 1)) `` | **MUST expand** (ordinary expression position): element is `999` | [S111] |
| QQ-I4 | `(m 1)` under unquote-splicing — `` `(a ~@(m2 1)) `` with `m2` expanding to a list-producing expr | **MUST expand** and splice | [S111] |
| QQ-I5 | Nested quasiquote depth — `` `(a `(b ~(m 1))) ``: the inner unquote belongs to the INNER quasiquote | inner `(m 1)` **NOT expanded** at outer processing (shield tracks nesting depth) | [S111] — negative |
| QQ-I6 | Macro-ARGUMENT representation (the arch ruling "macro arguments stay raw"): a macro receiving `'(1 2)` as an argument sees the `(quote …)` sexp the user wrote (desugar-at-build, i.e. AFTER expansion dispatch) | pin via a macro that inspects its arg's head | [S111] — pin |
| QQ-B1 | Backstop invariant stays: a synthetic surviving `quasiquote` symbol still rejected at `ast_builder.rs:1160+` ("should have been expanded") | unit / `/dev` (frontend) | [S111] |

Structural (not test rows): `lib.rs:48`'s claim ("desugaring runs before
`build_form`") becomes TRUE — `/review` cites the currency fix;
`frontend.md:127` likewise (the `/audit` frontend rotation sanity-checks
both, arch §7).

### D. GOT slot exhaustion (R7) — diagnosed error, not release-mode UB

Seam: `cranelisp-types` `allocate_got_slot` → `Result` (arch-approved shape);
10 production callers enumerated in the arch §2 table (9 typecheck + backend
`extern_call.rs:151`; bootstrap `unreachable!` by convention — a fresh table
cannot exhaust). Provenance: audit R7 (3rd consecutive naming; Phase-H
release-critical) + the self-documenting-errors principle. No spec section
constrains the limit — design-doc provenance.

| Row | Guard | Tier |
|---|---|---|
| GE-1 | Boundary unit in `cranelisp-types/src/module/tests.rs`: slots 0..1023 allocate; the 1024th (`next_got_slot == GOT_TABLE_SIZE`) returns the exhaustion `Err` — never a wrap, never a panic, release-mode semantics (a `Result`, not a `debug_assert!`) | unit / `/dev` (types) |
| GE-2 | The exhaustion error names the module and the capacity (actionable diagnostic) | unit, same fn |
| GE-3 | Caller-side session-surfaced pin: representative typecheck caller (`adt.rs` or `program/body.rs`) with a nearly-full fixture table → a diagnosed `CheckError` (not `unwrap`/`unreachable!`); + the backend `extern_call.rs:151` → `CodegenError` arm pin | unit / `/dev` (typecheck + backend) |
| GE-4 | E2e (author IF cheap, `/testing` sizes the runtime cost): generated source exceeding 1024 slots in one module `--run`s to the diagnosed error, clean exit, no SIGSEGV. If skipped, the deferral is already enumerated: GE-3 + the `/review` caller sweep (all 10 callers map the `Err` to a diagnosed error) cover the surface | e2e / `/testing` |

### E. Backend hard-miss negatives (s110 R2) — author the three §9 families FIRST

Carried verbatim from §"Sprint 110" A.2's KC-N1..N6 enumeration (planned
S110, **not authored** — audit R2 confirms zero test hits on the §9
families). Unit tier, backend harness; each family asserts a DISTINCT pinned
`CodegenError` message (names the reference + the miss), NOT `undefined
variable`, and never a silent wrong value: **KC-N1/N3** carrier-`None` on a
table-reference kind (call + value seams), **KC-N2/N4** `Some(fq)` fetching
nothing (both seams), **KC-N5** slot-less `Polymorphic` template at a value
read (the pinned "generic value reference … reached codegen without a mono
instance" message, release builds included), **KC-N6** the false-positive
fence (local/lambda-param `None` is NOT a miss). Provenance:
`backend-keyed-consumer.md` §1.1/§9. **Ordering: first wave of the backend
drain track — these guard the R4/R5 refactors and the ownership wave's
backend touches.** Owner: `/dev` (backend) unit tier per audit R2; `/testing`
verifies presence at Phase-5 close.

### F. Principle-24 classification battery + compiler-wide register

The battery, the criteria transcription (acid test + both carve-outs
verbatim from `principles/24-resolve-once.md`), the leg protocol, the grep
classes, and the register itself live in
**`tests/plan/s111-principle24-register.md`** (this pass, /qa-owned). Plan
rows:

| Row | Item | Status |
|---|---|---|
| P24-1 | Register discipline: every row = site → verdict ∈ {chain, enumeration (carve-out 1), `/search` (carve-out 2), **identity-scan (defect)**} → GROUNDS (why order-independent / complete-set-consumed / tie = error). A verdict without grounds is not a classification | standing |
| P24-2 | Leg closures: primitives/intrinsics/platform CLOSED this pass (grep zero — evidence in the register); backend CITED (audit s110 §2.1, four legit enumerations); typecheck leg (priority 1) + int leg (11 `symbol_tables.iter()` sites pre-listed in the register) classified during S111; frontend leg rides the `/audit` rotation (post-quasuote-landing, arch §7) | [S111] |
| P24-3 | Pre-seeded row `jit.rs:117` (`register_platform_effect_symbols`): enumeration whose tie-discipline is convention-only (platform names globally unique today; two same-named effects would be last-write-wins by DashMap order) — the sweep decides structural tie-error vs documented uniqueness invariant | [S111] — decision owed |
| P24-4 | Outcome rule (the defect rule): any identity-scan found ⇒ a failing-not-ignored test (when a divergence is constructible) or a FIXME naming the owner (when not); findings land as plan-row addenda at Phase 6 | standing |

### G. Adjacent carries

#### G.1 0604 — index-race, re-attributed FOREGROUND: the failing repro is the deliverable

The S110 `/dev` disposition PROVED the index feed inert under the recipe
(`--run` never arms the index; instrumented 0×) — the phantom
`bit-and → primitives/bit-and` write is on the **foreground concurrent-compile
path** (eval thread + priority/nice workers building `num.bits` + prelude +
~13 re-exported domain modules concurrently). S110 §F's IF-1 gate did its job
(locate-first prevented patching the wrong seam).

| Row | Item | Owner | Status |
|---|---|---|---|
| IR-1 | **Foreground repro production**: run the deterministic recipe (`0604` §recipe) in the environment where it fires 16/16, `CRANELISP_MODULE_TRACE=1`, and catch the phantom write's origin on the foreground path (`src/process_form/`, `src/imports.rs`, `src/worker.rs`). Deliverable = a DETERMINISTIC committed repro at the located write seam — an intermittent RED is its own defect; if determinism is not achievable free-standing, the deliverable is the located seam + attribution record update (`s109-attribution-index-feed-race.md` §3) naming the writer, and the fail-on-revert guard rides the fix | `/testing` (reduction) + `/qa` (attribution) | [S111] |
| IR-2 | Fix acceptance (carried from §S110 F): unit at the located write seam (METHOD §2.2) + ≥25-iteration recipe sweep landing WITH the fix + the twin guards stay GREEN (`super_import_wrapper_*` — do NOT weaken the §8.6.5 poison; the consumer is spec-correct) | `/dev` (int) + `/testing` | gate on the fix |
| IR-3 | `concurrency_capacity::same_token_capacity_n_blocking_admits_n_concurrent_nplus1_parks` — its OWN defect (fails CONSISTENTLY ~151–156ms vs the 150ms overlap threshold on the `/dev` VM; not interleaving-dependent): triage row, effect-concurrency track; threshold-vs-mechanism call is the triage question. NOT folded into 0604 | `/qa` triage | [S111] |

#### G.2 0590 R1 (+ M2) — the 0349-class 3rd-instance wrong-reject

Spec: `spec/03-types.md` §3.11 + `spec/05-definitions.md` §5.1.2. File:
`tests/spec_03_types.rs`. The S110 tc-rereview named the repro; the class:
multi-arity bodies are verdicted PRE-drain (correct per the C-4 constraint),
where a deferred-overload ret var is still fresh.

| Row | Guard | Status |
|---|---|---|
| OA-1 | `multi_clause_body_let_bound_resolved_overload_call_compiles` — `(defn h ([:Int x] x) ([:Int x :Int y] x))` + `(defn g ([:Int a] (let [r (h 7)] a)) ([:Int a :Int b] a))` MUST compile (today: spurious `ambiguous type …` at the `(h 7)` span); mode-uniform (REPL + `--run`); BOTH let-bound-dropped and let-bound-returned variants. `// defect: class=wrong-reject locus=crates/cranelisp-typecheck/src/program/finalize.rs (AmbiguityScanPhase pre-drain multi-arity leg) found=S110 owner=/dev` | **[S111] — RED ×2** |
| OA-2 | Must-holds around the fix (it re-touches the same pass ordering): the single-clause twin (LEG-2-fixed) + B1/B2's S110 guards + RD-3 + rows 13–15 + VP-3/4/5 stay GREEN | must-hold set |
| OA-3 | M2 asymmetry pins (GREEN, documenting INTENDED §5.1.2 behaviour): `(defn p ([x] x) ([x y] x))` accepted; `(defn q ([x] (let [v x] v)) ([x y] x))` rejected with the purpose-built per-clause message | [S111] — pins |

Note for `/sprint`/`/design`: I2 (converge the regeneralize family; give
"drained/settled" a representational carrier — Principles 18/20) is the
durable cure and `/design`(typecheck) territory. If the OA-1 fix is a FOURTH
positional patch of the 0349 class, `/qa` escalates to `/arch` per the
recurrence rule.

#### G.3 0595 — rigid-unify structural hardening (unit tier, enumerated; rides a typecheck wave)

| Row | Guard | Tier |
|---|---|---|
| RU-1 | TyConApp head-bind guard: both head binds (`unify_with_rigid` ~:109/:131) route through `unify_var` (or minimum: `debug_assert!(!rigid.contains(&f_id))`); unit fixture = a kind-confused sig smuggling a rigid id into head position via `cranelisp_types::apply`'s head rewrite — the silent acquire is refused | unit / `/dev` (typecheck) |
| RU-2 | Teardown symmetry: `rigid_vars`/`written_var_scope` restored on the ERROR path at `check_defn_body`, `infer_annotate`, `infer_lambda` (match `impl_check.rs`'s save/restore discipline); unit induces an inference error and asserts restoration | unit / `/dev` |

#### G.4 0591 ACTIONED — §L addendum: the annotation-position parse-gap map

**Spec-conformance judgment (`/qa`, the call the FIXME asks for): these four
positions are §2.3.8/§3.9 VIOLATIONS to schedule, not carve-out candidates.**
Spec ground: `:Type` binds the immediately-following form in ALL positions
(§§1.4.5/2.3.8/4.9 — user-settled, scribed). The W6 uniformity claim is
bounded by parseability, not violated — but parseability itself is the
non-uniform operation: the SAME body shape `[:a x] :a x` parses in
single-arity `defn` (FV-6, GREEN) and dies at parse in a multi-arity clause
and in `fn` — the definition-variants class. Owner of the fix: `/dev`
(frontend); fix shape: adopt `build_one_expr_at`/`build_args_with_annotations`
at the four builders (`build_defn_variant`, `build_fn`, `build_match_arms`,
`build_if`). The frontend is already open this sprint (quasiquote wave) —
ride-candidate; `/sprint` decides the wave. The REDs are authored Phase 5
regardless (the durable record + trigger; FIXME file deleted this pass).

§L position-map extension — current verdict at HEAD: parse error (never
`unknown type 'a'`):

| Row | Position (new §L rows) | RED repro | Free-var cell | Status |
|---|---|---|---|---|
| AP-1 | multi-arity defn clause (params + body ascription) | `(defn g ([:a x] :a x) ([:a x :Int n] x))` parses + typechecks; call both arities | same fixture IS the `:a` cell | **[S111] — RED** |
| AP-2 | `fn` params + body ascription | `(fn [:a x] :a x)` applied; concrete twin `(fn [:Int x] :Int x)` | `:a` pins via use | **[S111] — RED** |
| AP-3 | match-arm BODY ascription | `(match 5 [n :Int n])` | `:a` variant once parsing lands | **[S111] — RED** |
| AP-4 | `if` branch ascription | `(if true :Int 1 2)` | `:a` variant | **[S111] — RED** |

Each position, once parsing, exercises the typecheck seam for free
(`Expr::Annotate` → `infer_annotate` — the §L consistency lens: ONE rule per
cell, everywhere); the free-var cells are the proof. `// spec:
spec/03-types.md §3.9` (+ §2.3.8); `// defect: class=wrong-reject
locus=crates/cranelisp-frontend/src/ast_builder.rs (four builders never
adopted the annotation-pairing primitive) found=S109 owner=/dev`.

### H. Backend drain invariance gates (R4 hygiene batch + R5 funnel splits) — no new failing tests

Pure-refactor claims are gated, not test-authored (the §S110 K template):
(a) **CLIF byte-identity** over the golden corpus (`golden_clif_w0b` + the
S102 §6.2 classifier — these change-sets are emission-affecting NEVER);
(b) full suite green, zero new REDs vs the S111-entry RED set; (c) backend
`public-api.txt` regen for the `module_aliases`/`compile_to_module` signature
move, in the same change-set (baseline-diff discipline); (d) `/review`
confirms the R4 items actually land (the `module_aliases` field is
threaded-but-UNREAD since W3 — a 5th audit carrying it is a Principle-8
failure, arch §5 watch item). Ordering: AFTER §E's negatives exist, BEFORE
the emission-affecting ownership wave (arch constraint 1) — golden
attribution stays clean.

### I. In-sprint additions (S111 P5 — rows added at the CS-0.5 /qa touch)

#### I.1 §5.1.2 multi-arity clause-param pinning matrix (CS-4/CS-4.1 B-1 vectors 1–2 FIXED + /review B-2 vector 3 CARRIED; committed `03b8bf30`)

File: `tests/multi_arity_clause_param_51_2.rs`. Spec: `spec/05-definitions.md`
§5.1.2 — per-clause independent type-checking (a written clause var must be
pinned by its own clause, never acquired from a sibling). `// defect:
class=wrong-accept` (vocabulary ratified this touch). Fix for the B-2 rows is
CS-4.2, evidence-gated + coupled to the pending I-C user ruling.

| Row | Test | Status |
|---|---|---|
| MA-G1 | `rp4_delegating_let_body_multi_arity_param_not_pinned_rejected` — B-1 vector 1 (delegating self-call `let` body) rejection guard | [Tested+Neg tests/multi_arity_clause_param_51_2.rs::rp4_delegating_let_body_multi_arity_param_not_pinned_rejected] — GREEN; protects the CS-4.1 revert |
| MA-G2 | `rp2_body_ascription_self_call_multi_arity_param_not_pinned_rejected` — B-1 vector 2 (body-ascription unifies self-call ret var with a param var) rejection guard | [Tested+Neg tests/multi_arity_clause_param_51_2.rs::rp2_body_ascription_self_call_multi_arity_param_not_pinned_rejected] — GREEN; protects the param-subtraction close |
| MA-R1 | `lf1_leaf_literal_body_unused_free_var_param_should_reject` — B-2: leaf literal body escapes `find_ambiguous_value_position` (child-positions-only scan) | [S111] — RED wrong-accept guard (B-2, CS-4.2) |
| MA-R2 | `lf2_leaf_body_returns_free_var_param_should_reject` — B-2: leaf `Var` body returning the free-var param | [S111] — RED wrong-accept guard (B-2, CS-4.2) |
| MA-R3 | `rp15_leaf_body_var_clause_escapes_param_scan_defn_accepted_should_reject` — B-2 all-mode DEFN-accept marker (heap-ptr read narrated, not asserted — no-flaky rule) | [S111] — RED wrong-accept guard (B-2, CS-4.2) |
| MA-R4 | `rp19_mirror_int_read_as_string_cross_batch_should_reject` — B-2 REPL cross-batch unsafe READ face (stable `<invalid:1>` Int-as-String observable; `refresh_multi_sig_variant_ret_types` refreshes ret only) | [S111] — RED wrong-accept guard (B-2, CS-4.2) |

#### I.2 0633 ADT drop-glue under-key (FIXME 0633 REACHABLE verdict; committed `9371f9f2`; fix = CS-1.1)

File: `tests/adt_drop_glue_underkey.rs`. Spec: `spec/12-runtime.md` §12.3.1.
Attribution record: `tests/plan/s111-0633-adt-drop-glue-underkey.md` (two
under-keyed layers: `resolution.rs::adt_drop_glue_name` +
`vec_codegen.rs::build_elem_dec_fn`, both bare-`fqtn.name` first-build-wins).
`// defect: class=drop-glue-underkey` (vocabulary ratified this touch).
Collision scope differs per mode (batch cardinality) — hence the 3-mode split;
CS-1.1 must flip all three + R2.

| Row | Test | Status |
|---|---|---|
| DG-R1a | `adt_vec_drop_glue_concrete_args_axis_repl_r1` — `(Vec (Pair Int Str))` + `(Vec (Pair Str Int))` dropped in one batch; wrong glue → corruption (REPL face) | [S111] — RED guard (CS-1.1) |
| DG-R1b | `adt_vec_drop_glue_concrete_args_axis_run_r1` — same, `--run` face | [S111] — RED guard (CS-1.1) |
| DG-R1c | `adt_vec_drop_glue_concrete_args_axis_link_r1` — same, `--link` face | [S111] — RED guard (CS-1.1) |
| DG-R2 | `adt_vec_drop_glue_module_axis_leak_r2` — module axis: alloc/free imbalance (Str leak) under RC stats | [S111] — RED guard (CS-1.1) |

#### I.3 CS-0.5 L-B1 golden-lane certification (this touch — verdict record)

The 10-frame drift (S103 baseline → HEAD) certified sound by `/qa`:
R7 differential oracle (`CRANELISP_NO_OWNERSHIP=1` all-Owned lowering)
MATCH 13/13 frames (exit + stdout); RC balance allocs==deallocs equal-or-
better ownership-ON vs the conservative oracle on every frame;
`CRANELISP_RC_DEC_CHECK=1` zero stale decs 13/13; counts deterministic ×3.
Reshape attributed: (1) S104 M-static spark admission (`3804e425` +
default-flip `4924c26c`) — non-recursive call sites lose the runtime-guarded
spark leg (the RC/fence/call/block reductions); (2) S109 W1c2 canonical
`Type.Ctor` keying + S110 keyed-consumer resolver deletion (`be06f6cb`) —
ctor frame renames, GOT renumbering, single keyed `call_indirect` leg;
(3) S102–S107 ownership increments — non-atomic RC on confined temporaries,
consumer-driven vec-get projection elision, borrow elision (f1 rc_inc 528→17
vs oracle). GREEN-LIGHT → `/testing` re-baselines via `clif_golden.sh
capture` (all 13 entries, this attribution cited in the commit body).
Corpus scope caveat: certification covers the green-by-construction corpus;
open §3.7/0633/0638 defect shapes are corpus-excluded (`EXCLUSIONS.md`) and
are guarded by their own REDs, not this lane.

#### I.4 Phase-5-close attribution addendum (`/qa`, 2026-07-17 — the conclusion-prep dispatch)

Attribution verdicts for the open-defect REDs at P5 close (16 RED / 1 skip at
HEAD `dd914241`; every RED traces below — zero genuine regressions). Full
evidence in the P5-close `/qa` report to `/sprint`.

**DG-R2 4th re-attribution (supersedes I.2's row note AND the CS-5 /review
"vec-element-drop" verdict).** `/qa` reduction (executed): the imbalance
survives with ONE ADT / ONE module / no vec (`(defn main [] (let [s "hi"]
(Pure 9)))` → 2 allocs / 1 free), is ownership-independent (toggle-off
identical), absent for non-heap lets, absent in non-`main` fns (balanced
2/2), and the leaked allocation is always the chronologically-LAST (the IO
result box), while the let-bound heap values ARE freed. Verdict: an
**entry-`main` teardown leak of the final IO/result allocation, triggered by
any heap-valued let in `main`'s body** — not drop-glue (CS-1.1 proved), not
§3.7 (CS-5 proved), not vec-element-drop (this reduction). Owner `/dev`
(backend main-epilogue / int IO-trampoline result-dec seam — Step-2 CLIF
look decides the crate). `/testing`: re-annotate `// defect:` →
`class=rc-miscount locus=entry-main IO-teardown seam`; the 2-line repro
supersedes the R2 fixture as the narrow guard.

**0641 false-Fresh residual rows (committed `dd914241`,
`tests/false_fresh_provenance_residual.rs` — 8 RED: B-1/B-2/I-1/I-2 ×
REPL/`--link`).** Owner split CONFIRMED by toggle-off probes: B-1 (container-
element laundering) + I-1 (capture) are inference-half (`/dev` typecheck,
under the 0641 `/design`(typecheck) increment); **B-2 + I-2 carry the stacked
ownership-INDEPENDENT factor** — toggle-off yields WRONG VALUES (B-2: 55 for
99; I-2: 190 for 9; no crash, no error), so beneath the provenance miss sits
a backend consume/RC defect on the `vec-set`-RESULT path (result flowing
through a match var-binding / stored as a vec-literal element under the
all-Owned convention). Class `rc-miscount`/`uaf` at the backend vec-set
result-consume seam. The 0641 increment therefore needs the PAIRED
`/dev`(backend) fix — the typecheck provenance axis alone cannot flip B-2/I-2.

**0638 (macro-clause invocation corruption).** Re-checked at HEAD post-CS-5:
NOT cured, and NOT §3.7/0633 — distinct defect, attribution CONFIRMED to the
macro-clause JIT invocation path (`src/expander.rs` invoke core +
`src/marshal.rs` Sexp marshalling; intrinsics alloc adjacent). Evidence: the
preserved repro SIGSEGVs plain, surfaces `macro … aborted: runtime panic:
match failed` under `CRANELISP_RC_TRACE=1` (perturbation-sensitive), and the
RC trace shows frees with GARBAGE header tags (corrupt heap headers) plus
same-address alloc/free ping-pong — heap corruption, symptom polymorphic
(double-free → match-failed → SIGSEGV). The identical helper logic through
plain cross-module calls exits correctly (twin executed, exit 3). Owner
`/dev` (int marshal/invoke seam first; intrinsics if the corruption is in
the Sexp unmarshal alloc discipline). Class `uaf`. **No committed repro yet**
— `/testing` owes the narrow test from FIXME 0638's preserved files.

**I-3 renamed-import wrong-reject.** Confirmed: `(import [m [(src local)]])`
→ `expected symbol for import name` from
`crates/cranelisp-frontend/src/module_extract.rs::parse_names_list` (:337) —
the §8.3.5 grammar has NO parser arm and `cranelisp_types::ImportNames`
(module.rs:2387) has NO Renamed variant. **Pre-existing since Sprint 9**
(git -L blame `32dff6e4`, 2026-03-07) — never implemented, not
S111-introduced. Fix spans frontend parser + the types carrier (+ installer
`collect_specific`) → `/arch` interface approval; carry as its own
increment. Class `wrong-reject`. Until it lands, the a3 renamed-import reach
path + the 0621 rider stay unit-pinned only (e2e-untestable).

**0604 seam verdict: NOT-YET-LOCATABLE → CS-6 carries evidence-gated** (the
CS-6 gate). (1) Zero fires in ~99 fresh iterations this dispatch across four
scheduling regimes — single-shot ×5, 8-way parallel ×40, taskset 1–4-CPU
×16, 12-way busy-load ×30 — plus the committed IR-1 lane passing UNDER
full-suite concurrent load; cumulative with S110/S111 history: ~320
no-fires; the only firing environment remains the S109-era `/sprint` one.
(2) `CRANELISP_MODULE_TRACE` CANNOT locate the seam — its only emit sites
are `process_form/cache_restore.rs:122` + `index_worker.rs:1008/:1051`;
the foreground install path has zero trace instrumentation, so the FIXME's
trace recipe is inoperable for seam location. (3) Static narrowing landed:
the poison consumer (`imports.rs::insert_detecting_ambiguity` :548 branch,
exact error shape) proves the phantom is a PUBLIC `bit-and` head in
prelude's LIVE table at `num.bits.test` super-import install time; the
enumerable live-table writer set (install_imports/exports — destination is
the explicitly-passed `current_module`; the staging commit gate +
`insert_cluster` — destination is the cluster's own module; the Code-install
sites — mutate existing entries only; cache-restore — off under
`--no-cache`; typecheck has NO prelude materialization write) contains no
textual path to `prelude ← bit-and`, so the writer hides in concurrency
plumbing invisible to enumeration — or was already removed by S110/S111
restructurings (unprovable; verify-fix-not-symptom-absence). **Carry
package:** IR-1 stays the guard; the missing observability is the concrete
next step — a `/dev`(int)-sized change adding a MODULE_TRACE emit (or
debug_assert) at live-table insertion, minimally a prelude-table invariant
("prelude gains no entry outside its export list post-compile"), so the
NEXT firing anywhere names the writer instead of needing this hunt again.

#### I.5 Standing memory-safety coverage strategy adopted (this touch — user directive)

The S111 pattern §I.1–§I.4 record — memory-safety defects found only
incidentally (adversarial review, new language exercise), never by the
suite — is now managed as a **standing strategy**:
`tests/plan/memory-safety-coverage.md`. Normative content there, not here:
the differential-oracle nextest gate (four signals: toggle-equivalence,
`RC_STATS` balance, `RC_DEC_CHECK` zero, `--link` face), the generative
flow-space harness, refute-instructed review as standing practice for
safety surfaces, the rolling audit category "safety operation elided by a
static analysis, verified by example", and the exposure quantification
(oracle reach ≈0.6% of suite; `RC_DEC_CHECK` asserted nowhere). Binding
sequencing: **the oracle lane gates the 0641 instance-fix** (user
directive — the false-`Fresh` class closes by gate, not instance-by-
instance). From S112 Phase 3, ownership/RC-affected plan rows carry the
`[oracle]` mark and MUST be authored through the safety-matrix combinator.

### Phase-5 sequencing note for `/testing`

Author order: (1) **§E KC-N1..N6** (handoff enumeration to `/dev` backend —
they exist before any backend-drain change-set) + **QQ-I1/I2/I5** (the
fold-without-shield negatives — must exist before the quasiquote wave) +
**CW-F3a verification probe** (if the explicit-import control is RED at HEAD,
escalate to `/arch` before the ownership wave); (2) the new REDs: QQ-1..4 +
QQ-6 verification, CW-5/CW-7/CW-10 + CW-F2 + CW-F3b, OA-1, AP-1..4, GE-1..3
handoff to `/dev`; (3) GREEN pins/controls (CW-6/CW-8/CW-9/CW-11, QQ-5,
QQ-I3/I4/I6, OA-3) + CW-S1 cache rows authored with the schema wave; (4) the
B-section unit enumerations are `/dev` handoffs recorded per-crate at wave
dispatch (CC-R1..R7, CC-V1/V2/V4, CC-P1..P3) — `/review` verifies each
enumerated case has a fail-on-revert guard; (5) IR-1 reduction runs as its
own lane (environment-bound — coordinate with `/sprint` for the firing
environment). Standing REDs (CW-1..4, SG-1/QQ-6, RD-1/RD-2, C4-1) are already
committed — no re-authoring; they are their waves' acceptance criteria.

## Sprint 112 — the 0628/I-C compiler wave (Phase-3 exit gate, 2026-07-18, /qa)

**The full S112 plan lives in `plan/s112-0628-ic-wave.md`** (kept separate:
the sprint is dominated by an UNWIND — rewriting superseded rejection assets
to the S111-settled spec — and the per-asset disposition/preservation tables
are working detail). This section is the durable index:

- **Row families**: MS-1..10 (leg (a) §5.1.2 back-flow: rp4 anchor, poly+
  concrete positive, boundary twins, §5.1.1 definition-site RED MS-6);
  UW-1..12 (the unwind checklist — includes the 0432 Face-B trio 0642's list
  missed); TB-1..19 (leg (b) declaration-reject + 3-valued echo × kind +
  §7.3.5 slot-2 matrix + parse-diagnostic rows); AG-1..6 (arch gates: stale-
  cache wholesale refusal, per-class mode-uniformity, `.meta.json`
  byte-identity, return-type dispatch ×3 modes ×2 contexts, before/after
  corpus run, prelude-fixture cleanliness); CP-1..4 (constrained-poly ×
  multi-sig cell, user-ruled in-scope); RT-1..3 (new-form round-trip:
  `/sexp`, `/source`, `user.cl` regeneration).
- **Flag rulings** (s112 plan §7): §5.1.1 definition-site unifiable-overlap
  check is OWED (spec MUST; MS-6 is the record); con_var lowercase row added
  NOW (single-seam fix at the b0 shared helper); `program/tests.rs`
  message-pin updates ride the same change-set; **FIXME 0644 position: the
  leg-(a) no-bump rationale is falsified by the B-2 wrong-accept persisted
  state — recommend leg (a) rides the 20→21 window** (/arch rules).
- **Risk read**: `risks.md` §"S112 risk read" (S112-1..7). Ownership/RC-
  affected rows MS-1b/CP-1b carry the `[oracle]` mark — they graduate into
  the S113 oracle lane; this sprint they run on established observables only.
- **Traceability**: no spec band cites a retired-name asset; §5.1.2 heading
  and §7.3.5 carry `[S112]` markers; Phase-6 re-runs
  `spec_coverage_reconcile.py` after the migrations and re-points bands
  directly.
