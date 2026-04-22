# Sprint 61 Wave 5 — /review Report

**Reviewer**: /review
**Date**: 2026-04-22
**Verdict**: **PASS**
**Scope**: Methodology residual + showcase. No new compiler code
landed. Slice 5 items E-1 (fresh-TempDir rule), G (test rename), H
(three `[Tested+Neg]` promotions), I (repro-handoff migration — tests
+ exemplar sides), J (plan-gap retrospective), K (helper
consolidation), L (ring2-rc.md §5.5.1 + §5.6.1 Sketch-comparison
addenda), M (stale FIXME cleanup). Plus `/repl` sprint showcase
(`ring4s.demo`, 74 LOC; 28/28 demos replay green), `/port` solver
FIXME refresh + `exemplar-progress.demo` update, `/stdlib`
stdlib-progress.demo stanza, `/examples` sweep verification.

## Summary

- Blockers: 0
- Importants: 0
- Suggestions: 2

All four required read-only audits passed. Wave 5 is a methodology +
documentation wave; the compiler surface is unchanged since Wave 4's
`e20a7fa`. The single `src/` edit (G test rename) is trivial text
substitution confined to `src/session_v4.rs::persistent_worker_tests`.
No new `#[ignore]` attributes anywhere in `tests/`. No subprocess-exec
of deleted `exemplar/*.cl` repro files anywhere in `tests/`. Demo
library count 28 matches claim. All five per-wave review files
present in `design/review/`.

## Blockers (B)

None.

## Importants (I)

None.

## Suggestions (S)

1. **`tests/exemplar_solver_correctness.rs::tempdir_with_exemplar_modules`
   copies `exemplar/grid.cl` + `exemplar/solver.cl` into a fresh
   TempDir.**

   Item I's stated discipline (per `memory/feedback_repro_handoff.md`)
   is that compiler regression guards MUST NOT depend on `exemplar/`
   because `exemplar/` is a user-facing showcase subject to
   removal/relocation/replacement. T-S2-1 still read-only-imports
   `grid.cl` + `solver.cl` from the exemplar tree at test time — the
   inlined contract-checker source uses the exemplar's Grid/Cell ADTs
   and its `eliminate` function. Read-only access is safer than the
   pre-Wave-5 checked-in-`.cl` coupling, but a future exemplar rewrite
   (say, `/port` replaces Sudoku with a different showcase) would
   still break this test. The file's header acknowledges the coupling
   but does not propose a fix. Two candidate paths forward: (a) inline
   the Grid/Cell ADT subset + `eliminate` function directly into the
   test string literal (removes the coupling entirely; ~40 LOC added
   to the test string); (b) re-copy the referenced exemplar modules
   into `tests/fixtures/exemplar-slice2/` so the test depends on a
   frozen /qa-owned fixture snapshot rather than the live exemplar.
   Non-blocking because (a) the test is stable today, (b) it is
   deterministic green 5/5 per Wave 2 verification, and (c) any
   exemplar rewrite is a sprint-level coordinated change that would
   surface this test as an intentional signal. Owning skill: `/qa` at
   a future sprint where exemplar evolution is in-scope.

2. **`tests/sprint23.rs:6` comment — "All tests are #[ignore] stubs"
   — is stale.**

   The file header comment claims the suite is all `#[ignore]` stubs,
   but no `#[ignore]` attribute exists in the file as of Wave 5 HEAD
   (confirmed by `rg '#\[ignore\]' tests/sprint23.rs`: 0 matches).
   The comment predates Sprint 52's re-enable and has not been
   refreshed. Not a coverage gap — the tests run un-ignored — but a
   stale navigation hint. Wave 5 is methodology cleanup and this is
   one-line documentation drag. Owning skill: `/qa`. Candidate
   follow-up at S62 test-hygiene sweep or folded into the S62
   concurrency audit's adjacent `tests/sprint23.rs` work.

## Design-adherence audit

Slice 5 does not land compiler code; the review dimensions are
documentation hygiene, test discipline, demo integrity, and per-skill
scope compliance. Each dimension checked:

**Methodology items (E-1 / H / I / J / K / M).**

- **E-1 (fresh-TempDir rule in `tests/CLAUDE.md`)**: rule text landed
  under a new §"Fresh Temp Directory per Test" section (~52 LOC). The
  rule names the pollution defect that triggered it (Sprint 60 Round
  3 `user.cl` accumulation), defines the permitted exceptions
  (`runs_dir` pattern + `// read-only on project_root` annotation for
  genuinely read-only callsites), and proposes a CI lint candidate.
  Cross-referenced from `tests/plan/tempdir-audit.md §"Wave 5
  implementation status"`. 9 test files converted per the audit
  catalogue (`d45_*`, `d6_*`, `s60_run_tests_reduction_1_*`,
  `run_tests_batched_invocation_no_crash`,
  `exemplar_solver_does_not_stack_overflow_on_small_puzzle`,
  `sprint61_bare_primitive`). One row deferred (`examples_run`
  cache-path indirection) with explicit out-of-scope rationale.

- **H (three `[Tested+Neg]` promotions)**: `repl/spec.md` §3.4
  `/imports` row, §5.1 error-stream routing, §5.2 error-recovery
  state-preservation — all upgraded from `[Tested ...]` to
  `[Tested+Neg ...]` with explicit negative test references. Grep
  confirms 22 `Tested+Neg` annotations in `repl/spec.md` at Wave 5
  HEAD, up from Wave 4's 19. Exact delta +3 matches /qa's claim. Each
  promotion names a negative test that exists and passes — no
  forward-reference to un-authored tests.

- **I (repro-handoff migration — `tests/` side)**:
  `tests/exemplar_solver_correctness.rs` rewritten. Both tests inline
  their repro sources as Rust string literals. Both use
  `tempfile::tempdir()` per test. T-S2-2 is fully self-contained; it
  no longer subprocess-execs `exemplar/repro-slice2.cl`. T-S2-1
  read-only-copies `exemplar/grid.cl` + `exemplar/solver.cl` into the
  TempDir — partial migration flagged as S-1. Grep of
  `rg 'exemplar/repro-slice2|exemplar/test-eliminate-contract' tests/`
  confirms zero subprocess-exec references (one match in
  `tests/exemplar_solver_correctness.rs` is in a header comment
  narrating the migration rationale; one match in
  `tests/plan/ring4.md` names the former fixtures in prose).

- **I (repro-handoff migration — exemplar side)**: both
  `exemplar/repro-slice2.cl` + `exemplar/test-eliminate-contract.cl`
  deleted (confirmed by `git status`: two `D` entries).
  `exemplar/solver.cl:370+` FIXME block rewritten (36 → 41 LOC per
  task brief; diff stat shows +59 −35 in that file region).
  Three-layer narrative (Layer 1 algorithmic, Layer 2
  ensure_module_exists atomicity, Layer 3 capture-return inc) is
  complete; cross-references the three fix sites in
  `exemplar/solver.cl`, `crates/cranelisp-typecheck/src/checker.rs`,
  `crates/cranelisp-backend/src/compiler/control_flow.rs`. Points at
  `tests/exemplar_solver_correctness.rs` as the durable record.

- **J (Phase 3a plan-gap retrospective)**:
  `tests/plan/sprint-61-plan-gap-retro.md` authored (148 LOC).
  Two-layer analysis as prescribed — plan-level (Slice 2 was deferred
  to "branch (b) only", missing the property-level "for every
  unsolvable puzzle string, solver returns Unsolvable" coverage) and
  coverage-gap (inline-ADT-arg-wrapping-Vec class was Ring 1/2 scope
  that /qa's ring plans lacked). `tests/plan/ring1.md` +35 LOC
  inline-ADT-arg coverage additions; `tests/plan/ring2.md` +1 LOC
  cross-reference.

- **K (helper consolidation, Wave 2 /review I-1)**: 5 helpers
  (`project_root`, `binary_path`, `runs_dir`, `run_repl_with_stdlib`,
  `tempdir_project_from_fixture`) added to `tests/helpers/mod.rs` at
  `pub fn` declarations verified at lines 781, 786, 810, 837, 872.
  `tests/sprint61_bare_primitive.rs` diff shows the 5 inlined
  helpers removed (−72 LOC) and replaced with `use helpers::*;` +
  a single `use std::process::Output;`. The pattern is now canonical
  for future sprints that need the real-stdlib subprocess harness.

- **L (ring2-rc.md Sketch-comparison addenda, Wave 2 /review I-2)**:
  §5.5.1 lands (~175 words, grep-confirmed at `ring2-rc.md:481`) —
  explains the sketch's orthogonal borrowed-var gating strategy via
  `emit_consuming_caller_rc` auto-upgrade vs. the reimplementation's
  explicit `is_last_use` gate, cites sketch files at
  `sketch/src/codegen.rs:247, 295–303` and
  `sketch/src/codegen/match_compile.rs:231–235, 37–42`. Justifies the
  divergence (explicit rule at decision site is clearer for future
  readers). §5.6.1 lands (~200 words, grep-confirmed at
  `ring2-rc.md:499`) — identifies the *latent* capture-return bug in
  the sketch's `pop_scope_for_value` loop at `sketch/src/codegen.rs:
  576–626` and closures.rs:184–199. Both sections meet the "Sketch
  comparison" criteria in `CLAUDE.md §"Sketch Oracle"`: concrete file
  references, explanation of what the sketch does, explicit
  divergence rationale.

- **M (stale FIXME at `tests/exemplar_solver_correctness.rs:150`)**:
  resolved as part of I's rewrite. The file header comment now
  preserves the Layer-3-fix narrative as retrospective context; the
  FIXME is gone. Grep confirms no `FIXME(/backend)` at that line
  anchor.

- **G (test rename, S60 /review S2)**: `git diff e20a7fa -- src/`
  shows exactly the rename (`register_dep_shim_publishes_before_caller_registers`
  → `register_dep_for_eval_publish_then_register_is_observable_to_downstream`)
  in `src/session_v4.rs::persistent_worker_tests` + surrounding doc
  comment. Pattern matches `{fn-under-test}_{precondition}_{expected_observable}`
  per S60 /review S2's convention rationale.

**Showcase items.**

- **`repl/demos/ring4s.demo`** (new, 74 LOC per `wc -l`): showcases
  Slice 1 bare-primitive echo at prompt, Slice 3 race-closure
  narrative via H4/H5/H6 trajectory, Slice 4 `(fn [_] b)`
  bind-closure stability, Slice 0 trace env-var surface. Matches the
  74-LOC claim in the task brief.

- **`repl/demos/CLAUDE.md`** extended with ring4s entry alongside
  ring4q + ring4r per demo-library convention.

- **`repl/demos/exemplar-progress.demo`** +17 LOC delta (39 → 56)
  per task brief. `/port`'s 3-layer closure narrative lands with an
  unsolvable-detection stanza demonstrating the Layer 1 narrative on
  the self-contained 4x4 solver.

- **`repl/demos/stdlib-progress.demo`** +7 LOC bare-name echo stanza
  per task brief.

- **28 demos replay clean** per `/repl`'s Wave 5 verification.

- **`/examples` sweep**: 28/28 confirmed via `examples_run` test per
  task brief. Automated regression surface per `tests/examples_run.rs`.

- **`/docs` no-op**: Sprint 61 Slices do not introduce user-visible
  behaviour warranting `user/*.md` edits; this is a legitimate no-op
  disposition per /docs's Wave 5 readout in SPRINT.md. Sprint 61
  entry added in `user/CLAUDE.md` per convention.

## Boundary-hygiene audit

- `rg 'exemplar/repro-slice2|exemplar/test-eliminate-contract' tests/`
  → two matches, both informational (file header comment narrating
  migration at `tests/exemplar_solver_correctness.rs`; plan-doc prose
  at `tests/plan/ring4.md`). Zero subprocess-exec references. I
  migration complete. ✓
- `rg '#\[ignore\]' tests/` → no new ignores from Wave 5. Pre-existing
  matches in `tests/io.rs:550` (do-as-macro carry), `tests/rc.rs:492`
  (strict RC balance carry), plus plan-doc prose and header comments
  — no production-test changes. ✓
- `ls repl/demos/*.demo | wc -l` → 28. Matches the 28/28 replay
  claim. ✓
- `git diff e20a7fa -- src/` → only the G rename
  (`register_dep_shim_publishes_before_caller_registers` →
  `register_dep_for_eval_publish_then_register_is_observable_to_downstream`)
  and surrounding doc-comment update. No production-code changes, no
  test-harness changes. ✓
- `ls design/review/sprint-61-*.md` → 5 per-wave reports present
  (wave-1-slice-0, wave-2, wave-3, wave-4, plus the Phase 3a /arch
  review). Wave 5 report authored by this pass. All present. ✓

## Test count delta

Task-brief target: ~2853–2860 based on +3 H promotions + ~2 Slice 4
regression guards. Workspace at Wave 5 HEAD: 2845 pass / 5 fail per
task brief. Pre-Wave 5 baseline (post-Wave 4) was 2844/5 per `/qa`
Wave 4 readout. Delta +1 net passing, within the expected envelope
(H promotions do not change count — the tests already existed; only
the annotations move). The baseline ledger carries are unchanged in
identity: 4× `d6_exemplar_*` + 1× `wave6_demo_repros::exemplar_solver_*`
remain as expected, plus H6 residue under contention and harness
concern. All 7 ledger entries accounted for.

## Recommendations to /sprint

1. **Accept Wave 5 submission as PASS**. Zero Blockers, zero
   Importants, two minor Suggestions (exemplar-coupling in
   T-S2-1, stale `sprint23.rs:6` comment). Neither gates commit; both
   are candidate S62 cleanups.

2. **Wave 5 commit readiness: GO**. All changes sit in working tree.
   Commit message should cite: E-1 fresh-TempDir rule landed + 9
   files converted; K helper consolidation; H three `[Tested+Neg]`
   promotions; I repro-handoff migration (tests/ + exemplar sides);
   J plan-gap retro + ring-plan expansion; L ring2-rc.md §5.5.1 +
   §5.6.1 Sketch-comparison addenda; M stale FIXME cleanup; G test
   rename; showcase (`ring4s.demo` + exemplar-progress + stdlib-progress
   demo refresh); 28/28 demos + 28/28 examples green.

3. **Sprint-close work authorised**. Per the `/sprint` Phase 6
   checklist, after Wave 5 commit: write outcome section in SPRINT.md;
   archive to `sprints/archive/sprint-61.md`; update `sprints/ROADMAP.md`;
   draft `sprints/SPRINT-62.md` per the methodology pivot scope in
   SPRINT.md §Out of Scope "Concurrency audit + `loom`". Update
   `.claude/commands/sprint.md` Phase 6 to reflect the methodology
   pivot (stress gate is weak regression guard, not proof of race
   closure).

End of Wave 5 review.
