# Sprint 61 — /review Final Sign-off

**Reviewer**: /review
**Date**: 2026-04-22
**Verdict**: **PASS — ready for /sprint close**
**Scope**: Sprint-final readiness verdict per the revised criteria
(methodology pivot, 2026-04-22). Stress-gate retired as primary
close criterion; honest baseline + named-mechanism race closures +
S62 transition plan replace it.

## Summary

- Waves closed: 5 / 5 (Wave 1 Slice 0, Wave 2 Slices 1+2, Wave 3
  Slice 3, Wave 4 Slice 4, Wave 5 Slice 5 methodology+showcase).
- Finding counts per wave (cumulative):

  | Wave | Scope | B | I | S | Verdict |
  |---|---|---|---|---|---|
  | 1 | Slice 0 observability | 0 | 1 | 4 | PASS WITH FINDINGS |
  | 2 | Slices 1 + 2 (bare-primitive + exemplar) | 0 | 2 | 4 | PASS WITH FINDINGS |
  | 3 | Slice 3 heisenbug (H4 → H5 → H6) | 0 | 1 | 4 | PASS WITH FINDINGS |
  | 4 | Slice 4 21-hello-io capture-return inc | 0 | 0 | 3 | PASS |
  | 5 | Slice 5 methodology + showcase | 0 | 0 | 2 | PASS |
  | **Σ** | | **0** | **4** | **17** | — |

- All 4 Wave-level Importants folded (Wave 1 I-1 → S62;
  Wave 2 I-1 + I-2 → Wave 5 K + L, landed;
  Wave 3 I-1 → S62 trace-module cleanup).
- Zero sprint-level Blockers across all five waves.

## Revised close-criteria audit

**Methodology pivot landed.** SPRINT.md §Scope documents retirement
of the 20-run stress gate as the primary race-closure criterion.
Three distinct reasons recorded: statistical illusion (N-run 0/N
gate proves `<1/N` with ~63% confidence only), non-deterministic
coverage (contention geometry varies), post-hoc verification (does
not enumerate interleaving space). The gate is retained as a weak
regression guard (per `.claude/commands/sprint.md` Phase 6, updated
with tiered 5/10/20 thresholds) but NOT claimed as proof. ✓

**S62 primary workstream named.** SPRINT.md §"Out of Scope"
"Concurrency audit + `loom` adoption + structured interleaving
tests" — three named work elements: (1) audit shared-state access
sites in `cranelisp-typecheck`, `src/scheduler.rs`, `src/worker.rs`,
`src/session_v4.rs`; (2) introduce `loom` for scheduler + DashMap
modules table; (3) structured interleaving tests replacing
stress-style tests. S62 precondition: Wave 3 committed + Waves 4/5
closed. ✓

**FQTypeName displaced to S63+.** SPRINT.md §"Out of Scope"
explicitly: "FQTypeName migration — ~~Sprint 62 primary workstream~~
**DISPLACED 2026-04-22**. Now Sprint 63+ or later." Consistent with
the user-memory project priority entry but re-prioritised against
the methodology-pivot evidence. ✓

**Baseline ledger integrity — zero undocumented carries.** 7 ledger
entries at Wave 5 HEAD, each with required-fields complete (test
name, SHA, signature, owning skill, target sprint, disposition,
rationale):

1. `sprint23::heisenbug_race_reduced_concurrent_import_pairs` — H6
   residue under contention, owner `/int`, target S62 concurrency
   audit, disposition `under-investigation`.
2. `sprint61_observability_io::io_trace_off_path_subprocess_completes_within_generous_ceiling`
   — harness-robustness concern, owner `/qa`, target S62 or Wave 5
   slot, disposition `under-investigation`.
3. `sprint59_defects456_repro::d6_exemplar_propagate_only_does_not_segv`
   — Defect 6 stack overflow, owner `/port` + underlying `/backend`,
   target S62, disposition `exemplar-gap`.
4. `sprint59_defects456_repro::d6_exemplar_propagate_single_pass_does_not_segv`
   — sibling Defect 6 reduction, same disposition.
5. `sprint59_defects456_repro::d6_exemplar_solve_all_dots_does_not_segv`
   — sibling, same disposition.
6. `sprint59_defects456_repro::d6_exemplar_solve_minimal_puzzle_no_io_does_not_segv`
   — sibling, same disposition.
7. `wave6_demo_repros::exemplar_solver_does_not_stack_overflow_on_small_puzzle`
   — Defect 6 end-to-end, same disposition.

All 7 have honest dispositions (none `flaky`, `timing-sensitive`, or
`pre-existing`). The 5 `d6_exemplar_*`/`wave6_demo_repros::exemplar_solver_*`
entries were ESCAPED CARRIES from Sprint 58/59/60 close-time
verification — surfaced during Wave 3 workspace stress, ledgered
honestly per `tests/plan/baseline.md §"Close-time Verification
Protocol"`. /qa's readout at SPRINT.md §Notes "escaped-carries
readout" names the discipline gap (close-time runs were
narrow-target) and the corrective (full-workspace stress is now the
Phase 6 expectation). ✓

**All Wave close reports present.** `design/review/sprint-61-wave-*.md`:

- `sprint-61-wave-1-slice-0.md` (317 LOC) — Wave 1 observability.
- `sprint-61-wave-2.md` (407 LOC) — Wave 2 Slices 1 + 2.
- `sprint-61-wave-3.md` (360 LOC) — Wave 3 three-hypothesis race
  closure (H4 falsified → H5 landed → H6 atomic).
- `sprint-61-wave-4.md` (443 LOC) — Wave 4 capture-return inc.
- `sprint-61-wave-5.md` (this pass) — Wave 5 methodology + showcase.

Plus `sprint-61-phase-3a-arch-review.md` (pre-Wave 1 arch review
artefact). ✓

**Design-doc trajectory complete.** Three new /int docs authored
(`observability.md`, `bare-primitive-value-path.md`,
`heisenbug-race-closure.md`); /backend authored
`io-trampoline-trace.md` + `slice-4-21-hello-io-investigation.md`
+ updated `ring2-rc.md §5.5 + §5.6` (three-rule expansion +
capture-return inc) + Wave 5 §5.5.1 + §5.6.1 Sketch-comparison
addenda. Each compiler-code sprint slice has an authoring design
doc cited at commit time. All major subsystems touched this sprint
have design-doc coverage (per `/review` Phase B step 6). ✓

## Wave-by-wave delivered capability

- **Wave 1 (Slice 0)**: Observability infrastructure landed in `src/`
  (scheduler trace, 25 unit tests) + `cranelisp-runtime` (IO
  trampoline trace, 18 unit tests); shared `Instant` anchor; RAII
  flush guards; panic-hook wiring; env-var-gated zero-cost-when-off.
  19 integration tests; 16 pass at Wave 1 close, 3 ledgered as
  Slice 4 preconditions (all 3 flipped green at Wave 4).

- **Wave 2 (Slices 1 + 2)**: Bare-primitive value path unified on
  the FQSymbol-threading resolution mechanism (/int); 5 integration
  tests 5/5. Exemplar `test-unsolvable` closed via a 3-layer fix —
  Layer 1 algorithmic (/port, `exemplar/solver.cl::eliminate`),
  Layer 3 compiler bug (/backend, `is_last_use` gate on
  `borrowed_vars` at `crates/cranelisp-backend/src/compiler/mod.rs`,
  normative rule in `ring2-rc.md §5.5`). 2 integration tests 5/5.

- **Wave 3 (Slice 3)**: Heisenbug race closed via three
  evidence-gated hypothesis cycles. H4 (defensive-dep-pair gate,
  `eval_in_flight`-related) authored and falsified by post-fix dump
  — landed as net-positive narrow gate. H5 (scheduler-side
  `eval_in_flight` push-gate + `EvalInFlightGuard` RAII) landed,
  closed H5 surface. H6 (non-atomic `ensure_module_exists` →
  DashMap `entry().or_insert_with()`) landed, closed most-frequent
  residue. Cross-skill /int → /typecheck precedent per /arch §3d''
  with /typecheck §3e''.review APPROVE. Residue under heavy
  contention ledgered to S62 concurrency audit. 4 evidence dumps
  committed at `tests/sprint61/race-evidence/`.

- **Wave 4 (Slice 4)**: `21-hello-io.cl` capture-return
  double-free closed via `emit_capture_return_inc` helper at
  `crates/cranelisp-backend/src/compiler/control_flow.rs`;
  normative rule in `ring2-rc.md §5.6`. 7-line minimum repro
  + `examples_run` accepted-exit tightening `[101, 133, 141] → [243]`
  converts tolerance into regression guard. 2 integration tests
  5/5; 4 ledger entries resolved.

- **Wave 5 (Slice 5)**: Methodology residual + showcase. E-1
  fresh-TempDir rule documented + 9 test files converted. H three
  `[Tested+Neg]` promotions. I repro-handoff migration (tests +
  exemplar sides). J Phase 3a plan-gap retrospective + ring-plan
  expansion. K helper consolidation. L ring2-rc.md §5.5.1 + §5.6.1
  Sketch-comparison addenda. M stale FIXME cleanup. G test rename.
  Showcase: `ring4s.demo` (74 LOC); 28/28 demos replay green;
  28/28 examples sweep green.

## Commit readiness verdict

**GO for /sprint close work**, conditional on the below
(user-review gates remain):

1. Wave 5 working-tree changes committed per Wave 5 /review
   recommendation 2 (command staged; commit message drafted there).
2. SPRINT.md §Outcome section authored by /sprint (currently empty
   with three subsections — Delivered / Deferred / Findings). Must
   cite: 3 defects closed (4, 3, 1), 1 defect partially closed
   (heisenbug H4+H5+H6 landed, residue deferred to S62), 1 defect
   closed (21-hello-io), methodology pivot recorded, S62 transition
   drafted. 7 ledger entries carried forward — all dispositioned.
3. Archive to `sprints/archive/sprint-61.md`.
4. `sprints/ROADMAP.md` update — Ring 4 stabilisation progress,
   S62 concurrency audit opening.
5. `.claude/commands/sprint.md` Phase 6 checklist update for the
   methodology pivot (stress gate re-described as weak regression
   guard, not proof of race closure).
6. S62 SPRINT.md draft — per SPRINT.md §"Out of Scope" concurrency
   audit scope + `loom` adoption + structured interleaving tests.
   Slice 5 O lists the audit targets.

No outstanding /review blockers. No outstanding /arch interface
concerns (Sprint 61 touched no `cranelisp-types` boundary types;
the narrow /int → /typecheck cross-skill precedent in Wave 3 is
documented, gated, and approved). No outstanding cross-skill
FIXMEs that block close (the carry-forward FIXMEs in
`crates/cranelisp-runtime/src/io.rs:28` and
`stdlib/plan-stdlib.md §3.2` are explicitly out-of-scope per
SPRINT.md §"Out-of-scope FIXMEs carried forward").

## /sprint close-work authorisation

/review authorises /sprint to proceed with Phase 6 close work.
The revised close criteria (methodology pivot) are all satisfied:
three named mechanisms (H4/H5/H6) with evidence + fix + unit test
+ integration regression guard; /arch approval per iteration;
/review + /typecheck pre-commit approvals on Wave 3 narrow
precedent; S62 workstream named and scoped; FQTypeName displaced
to S63+; baseline ledger honest and complete; all five per-wave
reports published.

Sprint 61 closes cleanly by the revised criteria. The
stress-verification gate is retained as a regression guard in
Phase 6 but is no longer the gating question — the gating question
is whether the sprint's named workstreams closed with durable
artefacts (design docs, tests, ledger entries, cross-skill
precedent records). They did.

End of sprint-final review.
