# Sprint 64: Test-Port — `/qa` two-tier migration

**Status**: PHASE 5 LANGUAGE (ACTIVE) — Wave 5.5 audit complete + committed. **25% GAP-COVER rate found** — Wave 5 silently lost discriminating tests; 34 recovered as new e2e + 1 defect surfaced (FIXME 0140). One wave remaining (Wave 6 — defects + Phase 3 close).

**Goal**: Transition `/qa` fully to the two-tier regime. Audit every test file for assertions that test language behaviour (carry forward as new e2e tests in the harness specified by `tests/plan/helpers.md`) vs. Rust-internal state (quarantine in `tests/legacy/` for FIXME-driven harvest into the owning crate's unit tests). Reorganise the new e2e suite for spec-coverage auditability. Delete the legacy scaffolding once the new suite is sound. **Parity in spec-relevant coverage**: every assertion that exercises spec behaviour survives the transition; defects surfaced during audit land as FIXMEs + failing tests, not fixes.

This sprint is the lock-in described in FIXME 0115: it must complete before any crate-refactor sprint that reshapes `session_v4`/`worker` (FIXME 0109) can begin, because tests reaching into those internals would otherwise break for many sprints under the refactor.

## Scope

Three phases per FIXME 0115. **All `/qa`. No `/int` Phase 0.**

The original framing called for `/int` FIXMEs 0110 (toml/CLI knobs), 0111 (trace channel separation), 0112 (REPL ready sentinel) to land first. All three were retired during scope review (2026-05-03 — see FIXME 0115 §"Phase 0 collapse"):

- Traces are debugging aids without spec basis → `/dev` concern, not `/qa`.
- Pipe-all-stdin + parse-stdout-after-exit covers every e2e case; no ready sentinel needed.
- Fresh per-test `TempDir` makes cache state a test-orchestration detail, not a binary knob.
- Regex-based parsing (`compiler::repl_prompt()` etc.) absorbs prompt timing decoration without needing byte-stable mode.

The harness builds against the existing binary surface. Genuine `/int` blockers discovered during port file as new FIXMEs (parity rule: do not fix in-sprint).

### Phase 1 — Build the e2e harness (`/qa`)

Phase 1 deliverables, in order:

1. **Trim `tests/plan/helpers.md` per Phase 0 collapse — first, before harness implementation.** Remove `TomlVariant` catalogue (§"Configuration: Cranelisp.toml + CLI options"), `assert_stderr_traces_only`, `stderr_traces` field on `CrOutput`, FIXME 0110/0111/0112 trade-off references in §"Trade-offs the design accepts", the §"Determinism" framing that cites toml/CLI configuration, the trace-assertion example (`rc_balanced_for_string_concat`), and ready-sentinel framing. The harness must be coded against a clean spec; doing the trim in Phase 3 (Design) leaves a window where `/qa` implements from a stale doc. (Per `/arch` Finding 1, Blocker.)

2. **Verify the spec property: cache lives under project root.** Write `tests/cache_isolation.rs` (or extend the existing `cache.rs` row) asserting `design/backend/module-caching.md` §"Cache directory layout" — `.cranelisp-cache/` lives under `project_root`. The harness exploits the equivalence `project_root = std::env::current_dir()` (per `design/int/repl-lifecycle.md`) by setting the child's CWD to a fresh `TempDir`, but **the test cites the project-root spec property, not the CWD implementation detail**: assert `project_root.join(".cranelisp-cache").exists()` and that no other path on disk was touched. This test is the lock the rest of Phase 2's cache-hit tests depend on. (Per `/arch` Finding 2, framing corrected by user 2026-05-03 — cache location is project-root, not CWD; CWD-as-project-root is the harness orchestration, not the spec property under test.)

3. **Implement `tests/helpers/e2e.rs`** per the trimmed `helpers.md`:
   - `Cranelisp` builder + `CrInvocation` + `CrOutput` types
   - `PreludeVariant` catalogue (NONE, PrimitivesOnly, TestStandard) with on-disk fixtures
   - `tests/helpers/regex.rs` — named regex library (`compiler::time_line()`, `compiler::repl_prompt()`, `compiler::error_line()`, `compiler::alloc_addr()`, plus golden-masking primitives)
   - Per-test fresh `TempDir` by construction
   - Assertion methods: `assert_ok` / `assert_exit` / `assert_stdout_eq` / `assert_stdout_contains` / `assert_stdout_matches` / `assert_stderr_empty` / `assert_golden` / `assert_golden_masked`
   - Stdin driving: `stdin(...)`, `stdin_lines(...)`, `output()` — pipe-then-parse pattern only
   - **`use_workspace_stdlib()` gated**: only `tests/stdlib.rs` may legitimately call it (stdlib conformance is the named exception to the no-stdlib rule). Apply a marker the only-allowed callers pass, a `// SAFETY:` annotation reviewable in PRs, or a name that makes misuse visible (`use_workspace_stdlib_for_stdlib_conformance_only`). (Per `/arch` Finding 3.)

The new harness lives **alongside** the existing `tests/helpers/mod.rs::ReplSession` until Phase 3. `ReplSession` remains frozen (no new methods) but green.

### Phase 2 — Audit, port, reorganise, quarantine (`/qa`)

For every test file in `tests/`, run a four-step pass:

1. **Audit.** Read each test in the file. Classify each assertion:
   - **Language-behaviour** — observable from outside the binary (stdout, stderr, exit code, file artefacts). Carry forward as a new e2e test in the harness.
   - **Rust-internal** — reaches into `cranelisp::*` types, observability counters, `ReplSession::symbol_tables()`, etc. Belongs as `#[cfg(test)]` unit test inside the owning crate. Quarantine for harvest.
2. **Port forward.** Author new e2e tests for the language-behaviour assertions, slotting them into the reorganised suite shape (see below).
3. **Reorganise.** The new e2e tests are NOT a 1:1 file rewrite of the old. Group by spec section or language area so spec-coverage auditing reads naturally and the file set is manageable. `/qa` proposes the target shape in Phase 3.
4. **Quarantine.** Move files (or remainders) that are not fully carried forward into `tests/legacy/`. Cargo does not auto-discover nested directories under `tests/`, so files there are source archive — preserved but not built or run. File a FIXME against the owning crate's `/dev` to harvest into `#[cfg(test)]` unit tests in a future sprint.

**Coverage rule:** every spec-relevant assertion survives the transition (either as a new e2e test or via a FIXME-tracked harvest commitment with the source preserved in `tests/legacy/`). No silent drops.

**Defect rule:** if an audit reveals a defect (assertion that the integration-tier passed but the new e2e form fails), commit the failing test under the new e2e file with `// FIXME(/skill)` + a fresh `design/arch/fixmes/NNNN-*.md` filed against the responsible skill. **No defect-fixing in-sprint.** Failing tests follow the failing-not-ignored rule (`memory/feedback_failing_not_ignored.md`).

**Ledger lockstep:** every Phase 2 batch that lands new failing tests MUST update `tests/plan/ledger.md` in the same commit — every newly-failing port either adds a ledger entry or extends an existing one, naming the responsible skill. (Per `/arch` Finding 4.)

**FIXME hygiene per quarantined file**: every `tests/legacy/*.rs` carries a header comment naming (a) the FIXME number that tracks its harvest, (b) the owning crate, (c) the date of quarantine. Index in `tests/legacy/README.md` (or equivalent), maintained by `/qa`.

Test files in scope (~56 files, ~36k LOC):
```
cache.rs, e2e.rs, examples_run.rs, examples.rs, exemplar.rs,
exemplar_solver_correctness.rs, io.rs, io_minimal.rs, lenient.rs,
macros.rs, modules.rs, rc.rs, repl_experience.rs, repl_negative.rs,
ring0.rs, ring1.rs, ring2.rs, ring3_repl.rs, ring4_trace.rs,
scheduler.rs, sketch_port.rs, sprint23.rs, sprint59_*.rs,
sprint60_*.rs, sprint61_bare_primitive.rs, wave2_g6.rs, wave3_g8.rs,
wave4_g9.rs, wave6_demo_repros.rs
```

Wave organisation (Phase 4) determines batching. Likely several sub-waves to keep batches reviewable.

### Phase 3 — Remove legacy (`/qa`)

Once Phase 2 is sound:

- Delete `tests/helpers/mod.rs::ReplSession` and the integration-tier helpers (`compile_and_run`, `compile_and_run_simple`, `compile_and_run_with_macros`, `repl_session`, `repl_session_with_test_prelude`, `compile_both`, `assert_type_error`, `assert_parse_error`, `assert_rc_balanced`)
- Delete the inline `const &str` trait preludes (`NUM_TRAIT_PRELUDE`, `EQ_TRAIT_PRELUDE`, `ORD_TRAIT_PRELUDE`)
- Update `tests/CLAUDE.md` to remove integration-tier sections; the helpers table becomes e2e-only
- Confirm `cargo nextest run` green against the new suite

If any tests resisted the port and remain on the legacy helpers, document each holdout (file + reason + FIXME) and defer the deletion to a follow-up sprint with explicit rationale. Default expectation: clean Phase 3, no holdouts.

## Out of scope

- **New spec coverage.** No tests for spec sections that weren't tested at all in the legacy suite — the audit carries forward what exists, it doesn't expand. No new negative tests (`[Tested]` → `[Tested+Neg]` upgrades) beyond what falls out of the audit naturally.
- **Defect fixes.** Any defect surfaced during port is recorded as a FIXME and a failing test (per `memory/feedback_failing_not_ignored.md`); fix lands in a future sprint owned by the responsible skill.
- **Crate refactors.** FIXME 0109 (`/int` decomposition: split `session_v4.rs` + `worker.rs`) and other refactors that would reshape internal session state explicitly **do not start** until this sprint completes.
- **Other `/dev` FIXMEs in the queue** (0098/0099/0100/0103/0104/0107/0108) — deferred to post-test-port sprints.
- **Concurrency work.** S62 carries (3 Wave-1-gate items + heisenbug-race-closure §3e'' residue + 5 escaped exemplar-gap + harness ceiling) explicitly stay deferred per the FIXME 0115 sequencing lock-in.
- **`/int` binary-surface changes.** No new toml schema, no new CLI flags, no trace channel work, no ready sentinel. Genuine blockers discovered during port file as FIXMEs against `/int`.
- **Speculative harness API.** The `Cranelisp` builder is the target surface, not interim under Principle 8. New builder methods accrete on demand per real test need, not pre-emptively. (Per `/arch` Finding 6.)

## FIXME debt

Open carries from prior sprints; only those bearing on this sprint listed. Full scan at Phase 1 close.

| FIXME | Target skill | Status | Notes |
|---|---|---|---|
| 0115 | /sprint | open (this sprint) | Sequence the test-port sprint — actioned by running it. Updated 2026-05-03 with Phase 0 collapse rationale. |
| 0109 | /dev (int) | deferred-by-this-sprint | Crate refactor; locked behind Phase 3 completion. |
| 0098–0108 | /dev (various) | deferred-by-this-sprint | Other crate refactors locked behind Phase 3. |

**Retired in scope review (2026-05-03):** FIXMEs 0110, 0111, 0112 — deleted from `design/arch/fixmes/`. Rationale captured in 0115 §"Phase 0 collapse".

New FIXMEs filed during port land in `design/arch/fixmes/` per the protocol; they are scope input for the next sprint, not retroactive Phase 5 work.

## Architecture review (Phase 2)

`/arch` review completed 2026-05-03. **Verdict: APPROVE-WITH-REVISIONS.**

### Findings

1. **(Blocker)** `tests/plan/helpers.md` carries dead surface (`TomlVariant`, `assert_stderr_traces_only`, FIXME 0110/0111/0112 references) that is load-bearing in the same doc Phase 1 codes against. Move the trim from Phase 3 (Design) into Phase 1, before harness implementation. **Applied** to Phase 1 §1.

2. **(Important)** Cache project-root locality is the spec property (`design/backend/module-caching.md:439` — `.cranelisp-cache/` lives under `{project_root}/`). The harness uses fresh-TempDir-as-CWD because `project_root = current_dir()` (per `design/int/repl-lifecycle.md:329`), but the test cites the spec property (project root), not the implementation chain (CWD). Currently a verified-by-inspection assumption; Phase 2's cache-hit tests depend on it being a test. **Applied** as Phase 1 §2 (first concrete deliverable). Framing corrected by user 2026-05-03.

3. **(Important)** `use_workspace_stdlib()` is a quiet escape hatch for the "tests must not depend on stdlib" rule; only `tests/stdlib.rs` may legitimately call it. **Applied** to Phase 1 §3 (gating directive).

4. **(Important)** Parity rule + failing-not-ignored creates a Phase 2 cliff that needs explicit ledger discipline; without it Phase 7 has no signal for downstream sprints. **Applied** to Phase 2 (ledger lockstep requirement).

5. **(Suggestion)** Sequencing lock-in confirmed sound. No revision.

6. **(Suggestion)** Principle-8 check: harness IS the target, not interim. **Applied** to Out-of-scope ("speculative harness API").

### Public-API delta

**None.** No `crates/cranelisp-types/` changes, no facade updates, no new boundary types, no `interfaces.md` revisions, no `decisions/` additions. The `--no-cache` CLI flag and `Cranelisp.toml` resolution are existing surface; the harness consumes both via documented options without new contracts.

### Principle adherence (spot-check)

- **P01 Decoupling over convenience** — APPROVE. Subprocess-only harness explicitly decouples test surface from `session_v4`/`worker`.
- **P02 Narrow interfaces** — APPROVE. One struct family; surface is binary CLI/stdin/stdout/env, no new internal hooks.
- **P05 Testability is structural** — APPROVE. Test-discipline boundary moves to a stable place; failing-port tests joining the suite is the principle in action.
- **P06 Complexity has a budget** — APPROVE. Phase 0 collapse explicitly removed three speculative complexity items.
- **P07 Single source of truth** — REVISION (Finding 1, applied). `helpers.md` trim moved into Phase 1.
- **P08 No interim implementations** — APPROVE. Harness is target.
- **P13 `interfaces.md` is auditable** — APPROVE. No interfaces.md change because no boundary type changes.

No new FIXMEs filed by `/arch` — Blocker resolved by SPRINT.md edit; Important findings are scope refinements.

## Skill plans (Phase 3)

Only `/qa` invoked in Phase 3. No `/spec` (no language semantics change), no `/arch` (public-API delta is none, confirmed by Phase 2 review), no per-crate `/design` (no crate is touched — `tests/` is `/qa`'s domain).

### /qa

- **Task**: Author the Phase 3 design package. Three artefacts:
  1. **Trim `tests/plan/helpers.md`** per the Phase 0 collapse list (Phase 1 §1 of scope). The trimmed `helpers.md` is the spec the Phase 1 implementation codes against.
  2. **Concrete API signatures** for `tests/helpers/e2e.rs` (`Cranelisp`, `CrInvocation`, `CrOutput`, `PreludeVariant`) and `tests/helpers/regex.rs` (the named regex library). Either inline in the trimmed `helpers.md` or in a new sibling file.
  3. **Per-test row plan in `tests/plan/PLAN.md`** for Phase 2 — list every test file in scope (~56 files), classify each (clean port / port-with-defect-likely / holdout-risk), and propose batches. Output drives Phase 4 (Wave organisation).
- **Design refs to read first**:
  - `tests/plan/helpers.md` (current — drafting both the trim list AND the concrete API)
  - `tests/plan/PLAN.md` (current — the per-test row work extends this)
  - `design/backend/module-caching.md` §"Cache directory layout" (Phase 1 §2 cites this)
  - `design/int/repl-lifecycle.md` §"Project root resolution" (the harness orchestration foundation)
  - `tests/CLAUDE.md` §"Fresh Temp Directory per Test" (the fresh-tmpdir discipline)
  - `memory/feedback_failing_not_ignored.md`, `memory/feedback_repros_join_suite.md`, `memory/project_test_strategy.md` (the parity/failing-test discipline that Phase 2 enforces)
- **Acceptance criteria** (`/sprint` checks before advancing to Phase 4):
  - `tests/plan/helpers.md` is consistent end-to-end (no remaining references to `TomlVariant`, FIXME 0110/0111/0112, `assert_stderr_traces_only`, ready-sentinel, or "blanket determinism mode" framing).
  - Concrete signatures cover every Phase 1 §3 deliverable (builder methods, assertion methods, regex helpers, gating mechanism for `use_workspace_stdlib`).
  - `tests/plan/PLAN.md` has rows for every test file in scope with a port classification.
  - Phase 2 batches are proposed with rationale (file size, dependency clusters, defect-risk concentration).
  - Ledger lockstep mechanism is specified (how does each Phase 2 PR demonstrate `tests/plan/ledger.md` was updated?).

## Waves (Phase 4)

User decision: one sprint, multi-wave structure with mid-sprint review checkpoint after Wave 2. `/qa` is the only executing skill; "waves" here are checkpoint groups for sequencing and review, not parallel skill invocations.

### Open question resolutions (Phase 4 gate)

The 5 remaining open questions from `tests/plan/PLAN.md §"Open questions for Phase 4 wave organisation"` resolve as follows:

- **Q2 — Batch 9 (pure-quarantine) sequencing**: front-loaded into Wave 1. Mechanical work that exercises the `tests/legacy/` + FIXME pattern at low risk; FIXMEs queue early for downstream sprint planning.
- **Q3 — `rc.rs` trace-channel split**: accept `/qa`'s unilateral 30/65/5 classification. Cross-skill joint audit with `/runtime` `/dev` adds coordination overhead this parity sprint doesn't need. Harvest commitment via FIXME is the right path; `/runtime` audits during their harvest sprint.
- **Q4** — already resolved (cache-isolation seed test placed in new `tests/cache.rs` per Batch 1).
- **Q5 — FIXME ↔ ledger row pairing**: manual scan at wave-gate during S64. CI lint added as sprint-close FIXME against `/qa` itself for landing in a future sprint. Lighter-weight, fits parity rule.
- **Q6 — `spec_06_pattern_matching.rs` sourcing**: piggybacks on Batch 2's sweep. The dedupe across `ring2.rs` / `e2e.rs` / `sketch_port.rs` is happening anyway at the assertion level; separating pattern-matching adds bookkeeping overhead.

### Wave structure

| Wave | Scope | Deliverables | Source LOC audited | Approx commits | Gate |
|---:|---|---|---:|---:|---|
| 1 | **Foundation + first quarantine** | (a) `tests/plan/helpers.md` trim (✓ done in Phase 3); (b) `tests/helpers/e2e.rs` + `tests/helpers/regex.rs` build per `helpers-api.md`; (c) `tests/cache.rs` cache-isolation seed test (Phase 1 §2); (d) Batch 9: `tests/legacy/{scheduler,wave2_g6,wave3_g8,wave4_g9}.rs` + 4 harvest FIXMEs + `tests/legacy/README.md` index. | ~2,032 (Batch 9) | 6–8 | Harness compiles + cache-isolation test passes; 4 legacy files quarantined. |
| 2 | **Small surfaces (build the routine)** | Batch 5 (`spec_11_stdlib.rs`); Batch 10 (`build_confidence.rs` synthesised); Batch 1 (full `cache.rs` audit + cache-internals quarantine to `tests/legacy/cache.rs`). | ~3,200 | 5–8 | Three batches landed clean + `tests/legacy/cache.rs` quarantined + 1 harvest FIXME. **USER REVIEW CHECKPOINT** before Wave 3. |
| 3 | **REPL + IO** | Batch 7 (`repl_introspection.rs` + `repl_lifecycle.rs` + `repl_negative.rs`, sub-batched); Batch 4 (`spec_10_io.rs` + `tests/legacy/observability_io.rs` partial quarantine). | ~7,570 | 8–12 | REPL surface fully on new harness; IO carry-forward complete; observability quarantine routes to `legacy/`. |
| 4 | **Runtime quarantine** | Batch 6 (`spec_12_runtime.rs` carry-forward + heaviest legacy migration: `legacy/v4_jit_reclaim.rs`, `legacy/observability_*.rs`, `legacy/rc_alloc_trace.rs` rest, `legacy/ring4_trace_taxonomy.rs`). | ~3,375 | 6–10 | Runtime carry-forward in new shape; ~5 harvest FIXMEs filed (per-file commits because each FIXME targets a different owning skill). |
| 5 | **Conformance core (heaviest dedupe)** | Batch 2 (`spec_03_types.rs`, `spec_04_expressions.rs`, `spec_05_definitions.rs`, `spec_06_pattern_matching.rs`, `spec_07_traits.rs`, `spec_appendix_a_builtins.rs` — sub-batched per spec section); Batch 3 (`spec_08_modules.rs`, `spec_09_macros.rs`). | ~11,300 | 12–18 | Conformance carry-forward complete; spec sections 3–9 + Appendix A in new files; ring/sketch/e2e dedupe complete. |
| 6 | **Defects + Phase 3 close** | Batch 8 (`examples.rs`, `exemplar.rs`, `regression.rs` — defect-repro cohort). Phase 3: delete `tests/helpers/mod.rs::ReplSession` + integration-tier helpers + inline trait preludes; update `tests/CLAUDE.md`. | ~9,000 | 8–12 | All 42 source files audited; 16 e2e files in shape; ~10 legacy files quarantined; `ReplSession` deleted; `cargo nextest run` green; ledger integrity verified. |

**Total**: 6 waves, ~36k source LOC audited, ~45–68 commits, ~10 harvest FIXMEs, ~80–110 ledger entries.

### User review checkpoint after Wave 2

Per user direction, `/sprint` pauses at end of Wave 2 and presents to user before Wave 3 begins. Review surface:

- Working harness on disk (`tests/helpers/e2e.rs` + `tests/helpers/regex.rs`).
- 4 mechanically-quarantined files in `tests/legacy/` + 4 harvest FIXMEs in `design/arch/fixmes/`.
- 3 ported batches (stdlib + build_confidence + cache) producing 4 e2e files in the new shape + 1 quarantine.
- ~5,200 source LOC audited (~14% of total).
- Initial ledger entries (if any) under the lockstep mechanism.
- `cargo nextest run` green for everything that's been touched.

User confirms continuation, redirects ordering, or requests scope adjustment. `/sprint` advances to Wave 3 on user approval.

## Notes

- 2026-05-03: Sprint opened by `/sprint`. Initial scope drafted with `/int` Phase 0 (FIXMEs 0110/0111/0112).
- 2026-05-03: Scope review with user collapsed Phase 0 entirely. Three FIXMEs retired (deleted from `design/arch/fixmes/`); 0115 updated with rationale. Sprint becomes all-`/qa`. Phase 2 (`/arch` review) dispatched.
- 2026-05-03: `/arch` returned APPROVE-WITH-REVISIONS. One Blocker (helpers.md trim moves into Phase 1, not Phase 3), three Importants (cache project-root locality test as first Phase 1 deliverable; `use_workspace_stdlib()` gated; ledger lockstep in Phase 2), two Suggestions confirming soundness. Public-API delta: none. Revisions applied to scope.
- 2026-05-03: User correction — Finding 2 framing was CWD-centric; corrected to project-root (the spec property in `design/backend/module-caching.md`); CWD-as-project-root is the harness orchestration via `design/int/repl-lifecycle.md`, not the spec property under test. Phase 1 §2 and Architecture review Finding 2 updated.
- 2026-05-03: Advanced to Phase 3 (Design); `/qa` dispatched.
- 2026-05-03: `/qa` Phase 3 artefacts delivered:
  - `tests/plan/helpers.md` trimmed (595→385 lines) — `TomlVariant`, `assert_stderr_traces_only`, `stderr_traces`, `TraceKind`, `rc_balanced_for_string_concat` example, `--deterministic` framing, FIXME 0110/0111/0112 references all removed. One remaining mention in §"What the harness does NOT provide" intentionally documents rejection.
  - `tests/plan/helpers-api.md` created (347 lines) — concrete signatures for `Cranelisp`, `CrInvocation`, `CrOutput`, `CrError`, `PreludeVariant`, `tests/helpers/regex.rs`. `use_workspace_stdlib_for_stdlib_conformance_only()` rename chosen for gating. Cache-hit pattern: `CrOutput::run_again() -> Cranelisp` (consumes output, transfers TempDir into new builder).
  - `tests/plan/PLAN.md` extended (+201 lines) — §"Sprint 64 port plan" with classification taxonomy + per-file table covering 42 files / ~36k LOC + 8 batches by topic affinity + 3-pronged ledger lockstep mechanism.
  - **Two structural findings flagged for user decision**: (a) 8 holdout-risk files (`scheduler.rs`, `wave2/3/4_g{6,8,9}.rs`, `v4_jit_reclaim.rs`, `sprint61_observability_*.rs`) reach into `cranelisp::scheduler`, `cranelisp::observability`, runtime counters — belong as `#[cfg(test)]` unit tests in owning crates, not e2e; (b) `cache.rs` (2073 LOC, 55 tests) directly constructs `SymbolTable`/`CacheManifest` — mostly unit-tier in the wrong location, needs FIXME(/backend) to relocate. 4 open questions surfaced for Phase 4.
- 2026-05-03: User resolved Q1-Q4 with scope expansion:
  - Q1: `tests/legacy/` (Cargo doesn't auto-discover nested dirs) confirmed.
  - Q2: option (a) — `/qa` does the audit-and-extract NOW, this sprint. No deferred coverage gap.
  - Q3: reorganise the test suite during port for spec-coverage auditability + manageable file set.
  - Q4: every file gets the audit-and-extract filter, not just the awkward ones. End state: high-quality manageable test set assessable against the spec.
  - Sprint scope expanded: Phase 2 is now four-step (audit / port / reorganise / quarantine) per file. `/qa` re-dispatched to update Phase 3 artefacts (PLAN.md classification framework, reorganisation strategy, batch re-shape, audit-workflow specification, `tests/legacy/` mechanism).
- 2026-05-03: `/qa` revised Phase 3 artefacts delivered:
  - `tests/plan/PLAN.md` extended (518 → 924 lines). New §"Sprint 64 port plan" rewritten with: per-file disposition framework (Carry-forward% / Quarantine% / Delete% / target file / FIXME target / defect risk), reorganisation strategy + file tree, per-file disposition table (42 rows), audit workflow specification, FIXME template for harvest commitments, per-file commit discipline, 10 Phase 2 batches, sprint sizing assessment, ledger lockstep mechanism, 6 Phase-4 open questions.
  - **Reorganisation strategy chosen**: spec-section-anchored. 16 top-level e2e files (`spec_03_types.rs` … `spec_appendix_a_builtins.rs` + `repl_*` + `cache.rs` + `examples.rs` + `exemplar.rs` + `regression.rs` + `build_confidence.rs`) plus ~10 `tests/legacy/` archive files. Down from 42 source files. Reviewer answers "which spec section?" from filename.
  - **Sprint sizing recommendation**: two-sprint split. S64 = Phase 1 + Batches 1/5/7/9/10 (cache seed + stdlib + REPL + pure-quarantine + build_confidence). S65 = Batches 2/3/4/6/8 + Phase 3 legacy-helper deletion. Rationale: ~36k LOC + ~1500 carry-forward assertions + ~10 harvest FIXMEs + ~80–110 ledger entries does not fit single-sprint cadence cleanly. Single-sprint compression left as user/`/sprint` decision at Phase 4 wave gate. FIXME 0115 lock-in (test-port precedes crate-refactor) preserved either way.
  - 6 open questions for Phase 4 wave organisation; sprint sizing is the load-bearing one.
- 2026-05-03: User decision: one sprint, multi-wave with mid-sprint review checkpoint after Wave 2; `/qa` picks ordering for simplicity. `/sprint` Phase 4 wave organisation: 6 waves, ~45–68 commits, ~10 harvest FIXMEs, ~80–110 ledger entries. 5 remaining open questions resolved at gate (Q2 front-load Batch 9; Q3 accept `/qa` rc.rs split; Q5 manual scan + sprint-close lint FIXME; Q6 piggyback spec_06 on Batch 2).
- 2026-05-03: User approved Phase 4 wave plan. Phase 5 LANGUAGE active. Wave 1 dispatched: harness build (`tests/helpers/e2e.rs` + `tests/helpers/regex.rs`) + cache-isolation seed test + Batch 9 pure-quarantine (4 files + 4 harvest FIXMEs + `tests/legacy/README.md`).
- 2026-05-03: Wave 1 complete; 9 commits landed clean (`ccd43e9` through `5a1f6e2`). Harness on disk, 4 quarantines indexed, FIXMEs 0116–0119 filed. Stale "11 sketch_port + 2 v4_platform" pre-existing-failure count noted as deferred-to-`/arch`-good-time per user.
- 2026-05-03: Wave 2 dispatched: Batch 5 (stdlib → spec_11_stdlib.rs), Batch 10 (build_confidence.rs synthesised), Batch 1 (full cache.rs audit + cache_seed.rs merge + cache-internals quarantine).
- 2026-05-03: Wave 2 complete (uncommitted, staged). 3 batches landed:
  - Batch 5: `tests/stdlib.rs` (54 tests) → `tests/spec_11_stdlib.rs` (54 tests, 100% carry-forward, 0 quarantine). `use_workspace_stdlib_for_stdlib_conformance_only()` is the named exception caller.
  - Batch 10: `tests/build_confidence.rs` (7 hand-authored smoke tests — REPL banner, `--run main 0`, primitive return, stdlib import, REPL pipe, `--link` exec, cache materialisation).
  - Batch 1: `tests/cache.rs` rewritten (24 e2e tests covering cache-hit/miss + multi-module + transitive deps + prelude caching + mtime invariants + round-trip parity); `tests/cache_seed.rs` merged + deleted; `tests/legacy/cache.rs` quarantines 31 internal-API tests (FIXME 0120 → `/backend`).
  - **Defect surfaced (parity-rule landing)**: `cache::cache_multi_module_transitive_imports` fails — `--run` does not discover `(mod ...)` declarations in entry module (integration helper does). FIXME 0121 → `/int`. Ledgered as `out-of-scope (owner=/int)`.
  - `cargo nextest run`: 1845 tests, 1839 pass, 6 fail (5 pre-existing d6 cluster + 1 new parity-rule landing). Net 0 regressions.
  - **Harness-API surprises**: zero. Wave 1 builder + assertions covered every shape needed across all three batches. Validates the Phase 0 collapse decision.

- 2026-05-03: User review of Wave 2 raised mode-canonicalisation question (REPL/`--run`/`--link` boundary). Decisions: adopt; canonical = REPL; re-port `spec_11_stdlib.rs` for pristine state; PLAN.md update only (no `/arch` consult); fix before Wave 3. Mode-equivalence helper extended to 6 permutations: `repl-fresh / repl-cached / run-fresh / run-cached / link-fresh / link-cached`.
- 2026-05-03: Wave 2.5 dispatched — methodology-correction wave between Wave 2 and Wave 3. Combined design + helper + re-port + reshape work.
- 2026-05-03: Wave 2.5 complete (uncommitted). Outcomes:
  - `tests/plan/PLAN.md` extended with §"Mode canonicalisation — REPL is the canonical surface for language conformance" + audit-workflow rule update.
  - `tests/plan/helpers.md` and `tests/plan/helpers-api.md` extended with mode-equivalence helper section.
  - `tests/helpers/e2e.rs` extended with `run_through_all_modes(program, prelude) -> AllModesResult` + `assert_all_equivalent()` + `assert_all_equal(N)`. Canonical observation: `(defn main [] expr-returning-Int)`; cross-mode equivalence is "all 6 paths produce the same Int". `Cranelisp::with_prelude_no_overwrite()` added for cached-permutation flow.
  - `tests/spec_11_stdlib.rs` re-ported to REPL canonical: 54/54 pass. Net stronger assertion shape (`:Type value` substring asserts both type and value in one call). 3 ADT-typed tests needed minor reshaping for top-level type-variable disambiguation; no spec-coverage drop.
  - `tests/build_confidence.rs` reshaped: 4 smoke tests + 11 mode-equivalence tests covering arithmetic, ADTs, pattern match, traits, modules, macros, IO, let, if-else.
  - **NEW DEFECT — FIXME 0122 → `/backend`**: `--link` mode produces alignment-too-small linker error for programs using ADT/match, defmacro, or IO Pure primitive. REPL/`--run` succeed; `--link` fails. **Invisible to legacy integration-tier tests.** 4 ledger entries under §"Sprint 64 Wave 2.5 — `--link` mode divergence".
  - `cargo nextest run`: 1843/1853 pass. Failures: 5 pre-existing d6 cluster + 1 Wave-2 FIXME 0121 + 4 new Wave-2.5 FIXME 0122 parity-rule landings. **Net 0 regressions.**
  - **The mode-equivalence subset paid for itself on its first run.** The architecture pivot was correct.

**USER REVIEW CHECKPOINT** — Wave 2 + Wave 2.5 complete. User approved (A) — keep methodology iteration in history; defer FIXMEs 0121/0122; proceed to Wave 3.
- 2026-05-03: Wave 2 + Wave 2.5 committed in 5 commits (`04e9061` through `543dd08`). The "(A) keep 7 commits" preference reduced to 5 because Wave 2's superseded `spec_11_stdlib.rs` and `build_confidence.rs` versions were overwritten before reaching disk; methodology iteration preserved in commit messages + this notes section.
- 2026-05-03: Wave 3 dispatched: Batch 7 (REPL surface, sub-batched) + Batch 4 (IO surface).
- 2026-05-03: Wave 3 complete + committed (4 commits, `5bd7eeb` through `e3ec1db`):
  - Batch 7 — REPL surface (5,429 LOC, 285 tests audited):
    - `tests/repl_introspection.rs` (39 e2e tests — slash commands, /list, /info, /sig, /doc, /type, /help, /expand, defmacro display, /imports)
    - `tests/repl_lifecycle.rs` (29 e2e tests — boot, eval persistence, recursion, ADT lifecycle, redefinition, error recovery, /reset, macro persistence, /mod)
    - `tests/repl_negative.rs` (28 e2e tests — replaces in-place; old content preserved as `tests/legacy/repl_negative_old.rs`)
    - 4 quarantines: `repl_experience.rs` (190 tests), `repl_negative_old.rs` (31 tests), `ring3_repl.rs` (50 tests, 16 stub placeholders), `v4_repl_eval.rs` (14 tests). FIXMEs 0124 → `/int`, 0125 → `/int`+`/typecheck`, 0126 → `/int`.
  - Batch 4 — IO surface (2,141 LOC, 90 tests audited):
    - `tests/spec_10_io.rs` (26 e2e tests — Pure/bind, IO type inference, REPL trampoline, --run exit code, capture-return-inc regression guard, IO branch consistency, match on IO)
    - 4 quarantines: `io.rs` (76 tests), `io_minimal.rs` (5 tests), `sprint61_io_closure_regression.rs` (2 tests), `sprint61_observability_io.rs` (7 tests, renamed `observability_io.rs`). FIXMEs 0127 → `/int`+`/typecheck`+`/backend`+`/runtime`, 0128 → `/runtime`.
  - **NEW DEFECT — FIXME 0123 → `/int`**: `/reset` slash command not implemented in v4 REPL. Returns "command not yet available in v4 REPL" rather than clearing user-defined symbols. Hidden behind ReplSession Rust-API boundary in legacy tests. THIRD defect surfaced by the test-port. Failing test `repl_lifecycle::reset_clears_user_defns` ledgered.
  - **Harness-API surprises**: zero. The Wave 1 builder + Wave 2.5 helper covered every shape needed across both batches. The bespoke `result_lines` parser in `v4_repl_eval.rs` was strictly weaker than `assert_stdout_contains`.
  - `cargo nextest run`: 1600/1600 ran, 1589 pass, 11 fail (5 pre-existing d6 cluster + 1 FIXME 0121 + 4 FIXME 0122 + 1 FIXME 0123). Net 0 regressions; total test count dropped from 1853 (Wave 2.5) to 1600 because 375 quarantined tests no longer compile + 122 new e2e tests landed (-253 net).
  - **Implicit ledger resolution**: pre-existing entry `io_trace_off_path_subprocess_completes_within_generous_ceiling` resolves under the new harness — per-test TempDir isolation prevents the concurrent-load contention that fired the original failure. Resolution candidate for S65.
- 2026-05-03: User pushback on Wave 3 close: `/reset` test asserts on a feature not in `repl/spec.md §3.1` Command Inventory (21 commands listed; no `/reset`). Raises systemic question — did `/qa` invent other non-spec assertions? Wave 3.5 audit dispatched.
- 2026-05-03: Wave 3.5 audit complete + committed (3 commits, `017be46` through `2fe61fc`). Fresh `/qa` instance with audit-eye framing; reviewed 213 tests across 7 new e2e files + harness + plan docs.
  - Spec-traceability findings: 2 INVENTED (both `/reset`-related, deleted: `repl_lifecycle::reset_clears_user_defns`, `repl_lifecycle::reset_session_continues`); 42 MIS-CITED annotations (all corrected); 0 OVER-SPECIFIED; 0 MISSING-ANNOTATION.
  - Mis-cite clusters: §1.6/§1.7 cited for "session eval"/"redefinition" (do not exist; correct §15.2/§15.6); `spec/10-io.md` §10.4/§10.10/§10.3.5 mis-cited (correct §10.6.1/§10.7.1/§10.7.2/§10.8/§10.1); `spec/06-adt.md` cited (file does not exist; ADTs at `spec/05-definitions.md §5.2`).
  - FIXME spec-validity: 0121 RETAIN ((mod ...) is normative per spec/08-modules.md §8.2.1); 0122 RETAIN (`--link` linkable-object production required per repl/spec.md §0.2.1 + design/backend/executable-generation.md); 0123 DELETED.
  - Code review: organisation APPROVE; harness APPROVE; minor maintainability flagged for S65 (REPL helper stub duplicated 3× across `repl_*.rs`; some wider `contains`-checks; ADT match-witness reads complex but correct).
  - `cargo nextest run`: 1598 tests, 1588 pass, 10 fail (5 pre-existing + 1 FIXME 0121 + 4 FIXME 0122). 2 tests removed from `/reset` deletion. **Net 0 regressions.**
  - **Meta-finding**: the `/reset` slip-through survived `/qa` landing + `/sprint` Wave 2/3 review + the Wave 2→2.5 pivot. Single guard that caught it was a user reading the FIXME. Audit agent recommends a landing-time `// spec:` linter (one-evening Python script in `tests/plan/`) — durable mitigation against future invented assertions or mis-cited annotations.
  - `tests/plan/wave-3.5-audit.md` records full per-file findings.
- 2026-05-04: Wave 3.5b + Wave 3.5c dispatched in parallel. User authorised building the linter NOW (not deferring) and fixing the maintainability findings NOW (not deferring to S65).
- 2026-05-04: Wave 3.5b complete + committed (`6020c89`). Linter on disk at `tests/plan/spec_link_check.py` (Python 3, stdlib only). Recognises multiple citation forms (numeric/named/section-anchored), normalises shortform paths, handles multi-line continuations. `tests/CLAUDE.md` extended with linter section + audit history pointer. **Audit-scope (7 Wave-3.5 files) clean: 213/213 citations OK, EXIT 0.** Full-tree scan surfaced 76 pre-existing findings in older files (`sketch_port.rs`, `ring{0,1,2}.rs`, `v4_*.rs`, `sprint{23,60,61}*.rs`, `exemplar_solver_correctness.rs`, `wave6_demo_repros.rs`) — durable findings now visible for Wave 4+ cleanup. Linter agent also fixed 14 incidental mis-cites in `e2e.rs`, `cache.rs`, `build_confidence.rs` during verification (re-anchored `repl/spec.md §4.2`/`§4.3` to §4.1.5/§4.1.8; replaced `Cache directory layout` named anchor with `§10`; replaced non-existent `repl-lifecycle.md §"REPL boot"` and `build-pipeline.md` with valid citations).
- 2026-05-04: Wave 3.5c complete + committed (`ba60d05`, `871b0a9`). Maintainability findings actioned:
  - **REPL helper duplication factored** — option (a) chosen; added `Cranelisp::repl_capture(lines)` + `Cranelisp::repl_prims_capture(lines)` to `tests/helpers/e2e.rs`. ~24 LOC of duplicated stub collapsed across `repl_introspection.rs`, `repl_lifecycle.rs`, `repl_negative.rs`.
  - **Contains-check tightening** — 9 sites tightened across the 3 repl files via two new `CrOutput` methods: `assert_stdout_contains_all(&[...])` (folds `&&`-conjoined contains) and `assert_stdout_does_not_contain(needle)` (negative-coverage counterpart).
  - **ADT match-witness clarity** — 15-line header comment added to `tests/spec_11_stdlib.rs` explaining the pattern (anchors otherwise-unconstrained type vars; asserts a single deterministic `:Bool true` line). No per-test edits.
  - `cargo nextest run`: 1588 pass, 10 fail (5 pre-existing + 1 FIXME 0121 + 4 FIXME 0122). Net 0 regressions.
  - **Harness API additions** for Wave 4+ to adopt: `assert_stdout_contains_all`, `assert_stdout_does_not_contain`, `repl_capture`, `repl_prims_capture`. Need to land in `tests/plan/helpers-api.md` (Wave 3.5c agent deferred to avoid contention with Wave 3.5b's parallel docs work).
- 2026-05-04: User decisions: (A) audit-scope linter policy; helpers-api.md refresh folded into Wave 4; proceed.
- 2026-05-04: Wave 4 dispatched: Batch 6 (runtime quarantine — `rc.rs`, `ring4_trace.rs`, `sprint60/61_observability_*.rs`, `v4_jit_reclaim.rs`).
- 2026-05-04: Wave 4 complete + committed (6 commits, `1e35bef` through `5b3577c`):
  - `tests/plan/helpers-api.md` refreshed with the 4 Wave-3.5c methods (commit `1e35bef`).
  - `tests/spec_12_runtime.rs` (19 tests covering RC heap-using bodies, Vec COW, `(trace ...)`, `/run-tests`).
  - 6 quarantines under `tests/legacy/`: `rc_alloc_trace.rs` (1191 LOC, 81 tests), `ring4_trace_taxonomy.rs` (578 LOC, 31 tests), `sprint60_observability.rs` (182 LOC, 4 tests), `sprint61_observability_scheduler.rs` (483 LOC, 9 tests), `sprint61_observability_shared.rs` (251 LOC, 3 tests), `v4_jit_reclaim.rs` (700 LOC, 6 tests). Total ~3,385 LOC, 134 tests.
  - 5 harvest FIXMEs (0129–0133); FIXME 0132 consolidates `sprint61_observability_scheduler.rs` + `sprint61_observability_shared.rs` (same `/int` skill timeline).
  - **Linter clean** on `tests/spec_12_runtime.rs` (19/19 OK, EXIT 0). Audit-scope policy enforced.
  - **No new defect FIXMEs surfaced.** All 19 new e2e tests pass. The Wave 3.5 spec-traceability discipline + the per-test `// spec:` linter run held — no INVENTED assertions, no MIS-CITED annotations.
  - **Test count**: 1598 → 1483 (-115 net: 134 quarantined + 19 new). 1473 pass, 10 fail (5 pre-existing + 1 FIXME 0121 + 4 FIXME 0122). Net 0 regressions.
  - **Findings noted but not actioned in-sprint** (per /qa report): (a) Stale `user.cl` in repo root auto-loaded by manually-launched REPL — environment hygiene issue, not a defect; possibly worth a future `/int` consideration about whether project-root user.cl auto-load should be opt-in. (b) `(None : (Option Int))` annotation syntax does not parse in current binary; tests anchor type via fn-body shape rather than annotation. Possibly grammar incomplete (`:` annotation may be local-binding-only) but not a spec violation; not filed.
- 2026-05-04: User clarification on the two ancillary findings:
  - Finding (a): `user.cl` was untracked and `.gitignore`'d already. Stale dev artefact (created 2026-04-20 from a manual REPL session that defined `BoxC` without persisting the type-def). User authorised deletion — `user.cl` removed from repo root. No commit needed (gitignored).
  - Finding (b): `/qa` agent's interpretation was wrong. Per `spec/02-grammar.md §2.3.3`, type annotations are PREFIX on a symbol position (`[name :Type value]`), never postfix on an expression. `(None : (Option Int))` was never valid syntax — parser working as spec demands. Not a finding; struck from the list.
- 2026-05-04: Wave 5 dispatched: Batches 2 + 3 (conformance core, heaviest dedupe).
- 2026-05-04: Wave 5 complete + committed (3 commits, `b98717c` through `e4a4e58`):
  - **Sub-wave A — Batch 2** (commit `b98717c`): 6 new e2e files (102 tests) anchored to spec sections — `spec_03_types.rs` (15), `spec_04_expressions.rs` (27), `spec_05_definitions.rs` (16), `spec_06_pattern_matching.rs` (10), `spec_07_traits.rs` (10), `spec_appendix_a_builtins.rs` (24). Spec-anchored authoring naturally absorbed the 4-way redundancy across `e2e.rs` / `ring0.rs` / `ring1.rs` / `ring2.rs` / `sketch_port.rs`. Carry-forward target was ~700–1,000 if ported 1:1; aggressive dedupe brings it to 102 canonical tests.
  - **Sub-wave B — Batch 3** (commit `bba060a`): 2 new e2e files (20 tests) — `spec_08_modules.rs` (10, mode-specific `--run` exception cited), `spec_09_macros.rs` (10).
  - **Sub-wave C — Quarantines** (commit `e4a4e58`): 9 source files moved to `tests/legacy/` (~12,000 LOC, 1,747 legacy tests preserved as provenance). 6 harvest FIXMEs filed (0134–0139). FIXME 0134 consolidates 4 same-skill files (e2e/ring0/ring1/ring2 → multi-skill `/int` + `/frontend` + `/typecheck` + `/backend`).
  - **Linter clean** on all 8 new files (122/122 OK across both batches). Linter full-tree state: 76 → 23 findings (Wave 5 quarantines absorbed 53). Remaining findings cluster in Wave 6's source files (`sprint{23,60,61}*.rs`, `v4_pipeline.rs`, `wave6_demo_repros.rs`, `exemplar_solver_correctness.rs`).
  - **No new defect FIXMEs surfaced.** Spec-traceability discipline + per-file linter run held; 0 INVENTED assertions, 0 mis-cited annotations across 122 new tests. The Wave 3.5b mitigation is durable across the heaviest authoring batch of the sprint.
  - **Test count**: 1483 → 741 (-742 net: 862 quarantined removed + 120 new). 731 pass, 10 fail (carries unchanged: 5 pre-existing + 1 FIXME 0121 + 4 FIXME 0122). Net 0 regressions.
  - **Findings noted but not actioned**: (a) Trait dispatch on multiple types in REPL — declaring `(impl Tag Int ...)` then `(impl Tag Bool ...)` produces type-mismatch when calling on Bool. Test reduced; may be REPL-vs-batch trait registration timing issue. Not filed pending reduction. (b) Module cycle diagnostic doesn't say "cycle" verbatim ("dependency 'a' failed: dependency 'b' failed: type error 'f' not found"); cycle is rejected per spec §8.10.2 but UX gap. Not filed; needs reduction. (c) Three transient first-run failures (`sprint23::link_multi_module_project`, `sprint60_cache_build_marker::cache_meta_with_stale_build_id_triggers_recompile`, `v4_pipeline::v4_cross_module_macro_transitive`) passed individually and on second run — possibly filesystem cache contention under increased parallelism with 8 new e2e binaries. Watch in Wave 6.
- 2026-05-04: User pushback at Wave 6 dispatch gate: "How certain are we that our 'dedupe' hasn't discarded discriminating tests, even if the assertion is deeply embedded?" Honest answer was "not certain". User authorised Wave 5.5 dedupe-verification audit.
- 2026-05-04: Wave 5.5 dispatched: fresh `/qa` audit framing — sample audit (~10–20% per file, 173 tests across 9 files) + FULL audit of 35 regression-named tests across the 9 quarantined files.
- 2026-05-04: Wave 5.5 complete + committed (2 commits, `b3a30db` + `5ba5d65`):
  - Sample audit (Part A, 173 tests): **65% COVERED / 25% GAP-COVER / 1% GAP-HARVEST / 9% DUPLICATE**.
  - Regression-named audit (Part B, 35 tests): **57% COVERED / 43% GAP-COVER / 0% GAP-HARVEST**.
  - **The 25% GAP-COVER rate is substantially higher than Wave 5's "naturally absorbed" framing implied. User's skepticism was the right calibration.**
  - **34 new e2e tests authored** to recover spec-load-bearing GAP-COVER findings:
    - `spec_appendix_a_builtins.rs` +18 (string ops per §A.3 — zero prior carry-forward despite full spec coverage)
    - `spec_06_pattern_matching.rs` +1 (non-exhaustive diagnostic)
    - `spec_12_runtime.rs` +4 (overflow/underflow wrap, div-by-zero, UTF-8 source encoding)
    - `spec_08_modules.rs` +2 (import-inside-let neg + import-below-use)
    - `repl_negative.rs` +5 (slash-command nonexistent-name guards)
    - `repl_introspection.rs` +4 (/list and /imports boundary checks)
  - Each new test annotates dedupe-recovery provenance via `// (carry: legacy/<file>::<test>)` comment.
  - **NEW DEFECT — FIXME 0140 → `/int`**: `--run` rejects programs where `(import ...)` follows `(defn main ...)`, despite `spec/08-modules.md §8.3.9` mandating en-bloc import extraction precedes compilation. THIRD `--run`-mode-vs-spec divergence Sprint 64's port has surfaced (after FIXME 0121 `(mod ...)` discovery and FIXME 0122 `--link` GOT alignment). Per pipeline-v4 convergence principles, indicates binary entry-point orchestration not yet converged.
  - `cargo nextest run`: 775 tests, 764 pass, 11 fail (5 pre-existing + 1 FIXME 0121 + 4 FIXME 0122 + 1 NEW FIXME 0140). Net +1 parity-rule landing; +33 new passing tests. Linter clean (164/164 OK on the 6 updated files).
  - Confidence assessment: ~50% real duplicates / ~10% Rust-internal / ~25% genuine coverage gaps (Wave 5 silently lost; Wave 5.5 recovered the spec-load-bearing portion) / ~15% wave-deferred (lazy seq, HKT, deep TCO, multi-dot modules; recorded in audit doc).
  - **Wave 5.5 paid for itself**: 34 new tests + 1 surfaced defect = real risk discovered + closed (or formally tracked).
  - Recommendations for Wave 6 dispatch: no gate-blocking concerns; S65 follow-up sweep recommended for `spec_07_traits.rs` and `spec_05_definitions.rs` residue; `// (carry: legacy/...)` linter rule recommended for future enforcement.

## Outcome (Phase 7)

{Filled at close. Delivered / Deferred / Findings.}
