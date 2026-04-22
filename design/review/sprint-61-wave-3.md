# Sprint 61 Wave 3 — /review Report

**Reviewer**: /review
**Date**: 2026-04-22
**Verdict**: **PASS WITH FINDINGS**
**Scope**: Slice 3 heisenbug race closure. Three hypothesis cycles
landed evidence-gated: H4 narrow-gate in `register_dep_for_eval`
(§8.1), H5 push-gate via `eval_in_flight` + `EvalInFlightGuard`
(§8.2), H6 atomic `ensure_module_exists` via DashMap `entry()` (§8.3).
Cross-skill H6 fix authored by /int into `crates/cranelisp-typecheck/`
under /arch §3d'' narrow hybrid-ownership grant; /typecheck pre-commit
APPROVE in §3e''.review. Files: `src/scheduler.rs`, `src/session_v4.rs`,
`src/observability.rs`, `src/worker.rs`, `src/main.rs`,
`crates/cranelisp-typecheck/src/checker.rs`,
`crates/cranelisp-typecheck/src/trace.rs` (new),
`crates/cranelisp-typecheck/src/lib.rs`, `tests/sprint23.rs`,
`tests/plan/baseline.md`, `tests/plan/ring4.md`,
`tests/sprint61/race-evidence/*`, `design/int/heisenbug-race-closure.md`.

## Summary

- Blockers: 0
- Importants: 1
- Suggestions: 4

All four required audits (boundary grep, ignore grep, flaky-disposition
grep, typecheck `Cargo.toml`, FIXME(/typecheck), alloc grep) passed. The
cross-crate hook pattern mirrors `io_trace_install_panic_hook`. Three
hypothesis cycles are backed by committed evidence dumps. No boundary-
type changes; `cranelisp-typecheck/Cargo.toml` depends only on
`cranelisp-types` + `dashmap`. The single Important concerns the unit
test for the concurrent-ensure invariant, which guards its strongest
assertion behind a conditional — acceptable but worth tightening.

## Blockers (B)

None.

## Importants (I)

1. **`crates/cranelisp-typecheck/src/checker.rs:2703+` —
   `ensure_module_exists_concurrent_same_path_emits_exactly_one_created`
   hedges its strongest assertion behind a `counter_non_zero` guard.**

   Per /typecheck §3e''.review item 4, the N=8 concurrent test asserts
   (a) the strict post-condition (pre-populated `helper-val` survives
   and exactly one table is present), and (b) — conditionally on the
   trace hook having been installed by a prior test in the process —
   "exactly 1 Created + N-1 AlreadyPresent". The conditional gate
   tolerates `OnceLock`-single-install semantics in a multi-test
   process but means this test may, in some test-execution orders,
   verify only the weaker structural invariant and not the
   atomicity-of-emission invariant the test name promises. The
   `OnceLock::set` idiom in `trace.rs:74` accepts only the first
   install; if two sibling test modules both try to install their own
   forwarding hooks, whichever ran first wins.

   **Recommendation**: either (a) add a `#[cfg(test)]`
   `clear_symbol_table_ensure_hook_for_tests()` escape hatch mirroring
   `reset_panic_hook_installed_for_tests()` from the Wave 1 Slice 0
   observability wiring (same pattern, same discipline), or (b) keep
   the conditional assertion but add a second, unconditional unit
   test that installs the hook explicitly at test entry and exercises
   the N=8 scenario end-to-end so the "exactly one Created" invariant
   is always checked. /typecheck already flagged a preference for (a)
   as a future refactor. This is a narrow follow-up — it does not
   affect the correctness of the fix, only how durably the invariant
   is measured.

   **Owning skill**: `/typecheck` (now the going-forward owner of
   `trace.rs` per §3e''.review §"Narrow precedent acknowledgement").

   **Classification rationale**: Important — the H6 fix itself is
   correct and proven 10/10 by the integration harness at
   `tests/sprint23.rs::heisenbug_race_reduced_concurrent_import_pairs`
   and by the `ensure_module_exists_on_populated_table_preserves_entries`
   deterministic unit test. The invariant the conditional-guarded test
   claims to measure is additionally exercised by the integration test,
   so it is not an uncovered invariant. But /review flags the hedge as
   exactly the shape Wave 1 Slice 0 I-1 flagged for panic-hook tests:
   the `OnceLock::set`-single-install is process-global state that
   sibling tests must cooperate on. Fold into a short S62 sprint-local
   cleanup; not a Wave-3 blocker.

## Suggestions (S)

1. **`src/observability.rs:206-223` — `SymbolTableEnsure` tag overloads
   the existing `Module { module, state }` payload's `state: Option<u8>`
   rather than introducing a dedicated payload variant.**

   The decision is defensible (per /arch §3d'' steer: "mirror the
   existing `Module { module, state }` shape for `IsTypecheckedHit/Miss`")
   and is documented on the enum variant's own doc comment
   (observability.rs:206-223). The cost is purely documentation drag:
   a future reader who sees `state = Some(0)` on a `SymbolTableEnsure`
   event must dig through three layers of comments to learn it means
   "Created", whereas `ModulePool`-valued `state` on the hit/miss tags
   has intrinsic meaning. The `format_event_line` symbolic rendering
   (`outcome=Created` / `outcome=AlreadyPresent`, observability.rs:525-533)
   mitigates this at dump time. Not a finding — /arch explicitly
   adjudicated this encoding. Log as an acknowledged documentation
   choice.

2. **`src/session_v4.rs:1470-1473` — `EvalInFlightGuard` scope
   selection.** /int chose the whole-`register_dep_for_eval` scope (/arch's
   option (ii) alternative) after validating that /arch's preferred
   option (i) narrow-scope was insufficient (evidence in design doc
   §3e' "Scope selection — narrow-vs-function-entry"). The broader
   scope is correct, but the guard is materialised 2 statements after
   `caller = self.current_module_path()`, not at function entry. If a
   future refactor inserts any fallible operation between line 1469
   and 1470, the flag is NOT armed during that operation, re-opening
   a narrower H5 window. Hoisting the guard to the very first statement
   of the fn body (before the defensive-pair decision) would be safer.
   Non-blocking — the current 2-statement gap is within-function
   and the intervening operation (`current_module_path()`) does not
   drop to the scheduler.

3. **`crates/cranelisp-typecheck/src/trace.rs:65` — static is named
   `SYMBOL_TABLE_ENSURE_HOOK`, install function is
   `install_symbol_table_ensure_hook`, emit is
   `emit_symbol_table_ensure`.** The naming is correct and follows
   the `io_trace` sibling's conventions. One micro-consistency note:
   `lib.rs` re-exports `install_symbol_table_ensure_hook` and the type
   names, but not `emit_symbol_table_ensure`. This is intentional (the
   emit is called only from within the crate, at
   `checker.rs:292`); the install + types are part of the crate's
   public surface. No action needed; confirm during the S62 trace-module
   cleanup that the re-export split is the desired public API shape.

4. **`tests/sprint23.rs:2686` — `TIMEOUT` magic constant of `15` seconds
   is inline rather than named at module scope.** Per general checklist
   §3, multi-file time constants of this kind benefit from a named
   constant. Non-blocking; /qa §3f.flake disposition explicitly
   calibrates this value and documents the precedent
   (`io_trace_off_path_subprocess_completes_within_generous_ceiling`).
   A `const H5_STARVATION_ABSENCE_CEILING: Duration =
   Duration::from_secs(15);` at module scope would surface the
   calibration once and tie future ceiling changes to a single edit.

## Design-adherence audit

**Hypothesis trajectory (design doc §7)**: H4 chosen §7.1-7.6, authored
Change A + Change B, landed under /arch §3d APPROVE → **falsified
post-fix** at §7.7 (rate fell from ~80% to still-observable at ~60%
under load; signature morphed). H5 hypothesised §7.8, /arch §3d' APPROVE
with revisions (lock discipline, RAII scope) → landed §3e' (rate
0%→~20%, new signature: `'helper-val' not found in module 'helper'`
surfaced cleanly). H6 hypothesised §7.10 (non-atomic `ensure_module_exists`
compare-then-set), /arch §3d'' APPROVE WITH REVISIONS (hoist seed
clone; new trace tag; hybrid ownership) → landed §3e'' (rate ~20%→0/10).
Each cycle has an evidence dump at `tests/sprint61/race-evidence/`:
- `failing-run-35062ca.log` (pre-fix baseline)
- `post-fix-run-35062ca.log` (post-H4, shows H4 falsified)
- `post-fix-h5-35062ca.log` (post-H5, shows H6 residue signature)
- `post-fix-h6-35062ca.log` (post-H6, shows atomic outcome)

All three /arch mini-reviews documented in design doc with the
mandatory conditions enumerated and satisfied at the corresponding
step 3e / 3e' / 3e'' sections. /int's §3e'' "four mandatory conditions —
satisfaction summary" maps each condition to the concrete diff point.

**Sketch comparison**: §7a — the sketch had no scheduler + no
concurrent typecheck; the races don't exist in the prototype. Divergence
documented; no additional sketch comparison needed for H4/H5/H6 fixes
(they address reimplementation-specific concurrency surfaces).

**Unit tests alongside code** (per `memory/feedback_unit_tests_with_dev.md`):
- `src/scheduler.rs` — 3 unit tests for `try_unblock_locked` H5 gate
  (flag-active suppress, flag-inactive push, toggle).
- `src/session_v4.rs::eval_in_flight_guard_tests` — 3 unit tests for
  RAII guard Drop on normal + panic-unwind + post-unwind try_unblock.
- `crates/cranelisp-typecheck/src/checker.rs::tests` — 3 unit tests
  for `ensure_module_exists`: seed-on-first, preserve-populated-table
  (direct H6 regression), N=8 concurrent exactly-one-Created.
- `crates/cranelisp-typecheck/src/trace.rs::tests` — 3 unit tests
  (u8 stability, noop-no-hook, install-and-emit).
- `src/observability.rs` — 2 new tests for `SymbolTableEnsure`
  emission + rendering, alongside the H5 `RepublishFromSymbolTable` +
  `RegisterImportsLookup` assertion.

## Boundary-hygiene audit

Grep evidence executed per task brief (substitute `crates/cranelisp-shared`
with verified-not-a-crate — workspace has no such crate; check was
redirected to `cranelisp-types` where the boundary prohibition lives):

- `rg 'SchedulerTraceEvent|SymbolTableEnsure' crates/cranelisp-types` —
  **0 matches**. Event types stay in `src/observability.rs`; the
  `SymbolTableEnsureOutcome` lives in `cranelisp-typecheck` as a
  crate-internal enum + u8 discriminator. Principle 3 preserved.
- `crates/cranelisp-typecheck/Cargo.toml` — dependencies are
  `cranelisp-types`, `dashmap`, + dev-dep `cranelisp-frontend`. No
  `cranelisp` (binary) dep. Crate DAG compliance verified. ✓
- `rg 'cranelisp_alloc' src/observability.rs crates/cranelisp-typecheck/src/trace.rs` —
  **0 matches in code**; only the doc-comment prohibition at
  `observability.rs:33`. Both trace-path storage paths use host
  allocator (`VecDeque`, `OnceLock`, `Vec`). ✓
- `ModuleState { eval_in_flight: bool }` — `src/scheduler.rs:111`,
  `src/`-owned type. No leak to `cranelisp-types`.
- `SymbolTableEnsure` payload encoding matches existing
  `Module { module, state }` shape — no new payload variant in
  `SchedulerTracePayload`. ✓
- `install_symbol_table_ensure_hook_to_scheduler_trace()` at
  `src/observability.rs:447` installs the function pointer from the
  binary into the typecheck crate's `OnceLock`. Direction is
  DAG-legal: binary → typecheck. Mirrors
  `cranelisp_runtime::io_trace_install_panic_hook` from Wave 1.

## Evidence-gated discipline audit

The three hypothesis cycles match the /arch Phase 2 FIXME #3 mandate
(design-doc evidence citation BEFORE fix lands). Each §3d / §3d' / §3d''
mini-review cites dump-file lines + post-fix acceptance criteria. The
§7.7 falsification section is the strongest discipline signal: H4
landed, was measured post-fix, and was DOCUMENTED as falsified rather
than papered over. That triggered H5. The §3e' → §7.10 transition is
similarly clean — the H5 fix eliminated the H4/H5 signatures but
surfaced H6's distinct shape, and /int re-hypothesised rather than
declaring closure.

The /arch §3d'' H7 fallback policy (ledger-and-defer acceptable at
≥19/20 if H6 signature fully gone) was NOT invoked — H6 reached 10/10.
The 1/10 whole-suite flake (`h5_normal_completion_does_not_starve_repl_eval_thread`)
was resolved by /qa step 3f.flake as a ceiling-calibration issue, not
an H7 signature. Disposition is documented with calibration data and
a sibling-ledger precedent citation. No "flaky" disposition anywhere
in `tests/plan/baseline.md` (grep: 0 matches).

## Narrow precedent audit

/int authored the H6 fix inside `crates/cranelisp-typecheck/` under
§3d''. /arch's four mandatory conditions:

1. Hoist user-seed clone OUTSIDE `entry()` — satisfied at
   `checker.rs:240-258` (read `user` through its own `get` guard;
   collect into `seed_entries: Vec<(Symbol, ModuleEntry<C>)>`; drop
   the read guard; call `entry()` on line 274).
2. `SymbolTableEnsure` tag + `Created | AlreadyPresent` discriminator
   — satisfied (observability.rs:223; Created=0, AlreadyPresent=1).
3. `FIXME(/typecheck)` comment at the top of the rewrite citing §3d''
   — satisfied at `checker.rs:205-213`. Text explicitly flags precedent
   as narrow and non-generalisable.
4. Pre-commit /typecheck review — satisfied; §3e''.review APPROVE with
   zero revisions.

/typecheck §3e''.review explicitly acknowledges the narrow precedent
and scopes going-forward ownership: "The `trace.rs` module is now
part of the `cranelisp-typecheck` public API (re-exported from
`lib.rs`) and becomes /typecheck's maintenance responsibility going
forward". This is the correct ownership transfer — /int authored
under grant; /typecheck now owns the artefact.

**Assessment: healthy.** The precedent is bounded in all three axes
(single function, public API unchanged, author-of-design is
implementer) and both /arch and /typecheck explicitly gate against
generalisation. Record in sprint close per /arch §3d'' Recommendation 3
for future arbitration reference.

## Test coverage audit

- **No `#[ignore]` in test code**: `rg '^\s*#\[ignore\]'` on
  `tests/sprint23.rs` returned 0 matches. The two `#[ignore]`
  substring hits (lines 6, 2197) are both in doc comments that
  explicitly explain why no `#[ignore]` annotation appears. ✓
- **No `flaky` disposition in baseline**: `rg '^flaky|"flaky"'` on
  `tests/plan/baseline.md` returned 0 matches. /qa §3f.flake resolved
  the one flake candidate deterministically. ✓
- **Fresh-TempDir per test**: `heisenbug_race_reduced_concurrent_import_pairs`
  creates `tempfile::tempdir()` per trial per thread. `h5_gate_typechecking_user_fires_only_on_repl_thread`
  uses `tempfile::tempdir()`. `h5_normal_completion_does_not_starve_repl_eval_thread`
  uses `tempfile::tempdir()`. ✓
- **Wait-for-condition discriminates completed-vs-hung**: the
  15-second ceiling in `h5_normal_completion_does_not_starve_repl_eval_thread`
  is explicitly calibrated to "~30× typical, 0.5× per-test cap, still
  catches the real failure sharply". Docstring walks through the
  calibration arithmetic and cites the sibling-precedent baseline
  entry. Matches user directive "flaky is not a disposition". ✓
- **Spec traceability**: every new test carries a `// spec:` comment
  pointing at `design/int/heisenbug-race-closure.md` with the specific
  subsection. ✓
- **Baseline ledger update**: /qa moved the original
  `sprint23::cache_repl_loads_heisenbug_parallel_stress` entry out of
  the open section (now passing). `heisenbug_race_reduced_concurrent_import_pairs`
  entry was updated mid-wave from S62 deferral to in-sprint H6 cycle,
  and per /sprint step 3f'' close gate is effectively resolved by the
  H6 fix. /sprint to confirm ledger state at wave close. ✓
- **Test-plan rows**: `tests/plan/ring4.md §Sprint 61 Slice 3`
  cross-references each of the authored tests (/qa reports
  confirmed).

## Review dimensions — all 13 checked

| # | Dimension | Status |
|---|---|---|
| 1 | Design adherence (H4→H5→H6 evidence trajectory) | strong |
| 2 | Boundary hygiene (Principle 3; no cranelisp-types change) | clean |
| 3 | Allocator discipline (trace-hook function pointers; no cranelisp_alloc) | clean |
| 4 | Cross-skill precedent (narrow, /arch-arbitrated, /typecheck-APPROVE) | healthy |
| 5 | Unit tests with implementation | present in 4 locations |
| 6 | Integration tests authored in `tests/` by /qa | present |
| 7 | No `#[ignore]` in new tests | verified |
| 8 | No flaky disposition | verified |
| 9 | Fresh TempDir per test, wait-for-condition ceilings | verified |
| 10 | Function size (max 100 LOC) | largest new fn is rewritten `ensure_module_exists` at 61 LOC incl. comments; trace.rs fns all under 10 LOC |
| 11 | Error handling (no unwrap/expect/panic in pipeline) | verified — unwrap only in `#[cfg(test)]` |
| 12 | Naming (typed identifiers, named constants) | one S-suggestion on TIMEOUT constant |
| 13 | RAII + panic-unwind safety (EvalInFlightGuard Drop) | unit-test-covered |

## Recommendations to /sprint

1. **Accept Wave 3 submission as PASS WITH FINDINGS**. No Blockers.
   The single Important (I-1, conditional trace-hook assertion in
   the N=8 concurrent test) is a test-durability concern that does
   not affect correctness of the fix and does not hold up wave close.

2. **Fold I-1 into S62 trace-module cleanup** (alongside the possible
   Wave 5 `emit_symbol_table_ensure` re-export decision S3). ~15 LOC
   in `trace.rs` to add `reset_hook_for_tests()` + parallel unit test
   with unconditional assertion.

3. **Log S2 (EvalInFlightGuard hoist)** as a defensive-refactor
   candidate for any future touch of `register_dep_for_eval`. Not a
   sprint action; informational note for readers.

4. **Stress-verification recommendation for the 20-run close gate**:
   run `cargo nextest run -p cranelisp --test sprint23 -- --test-threads=6`
   for 20 consecutive iterations. Expected: 20/20 PASS on
   `heisenbug_race_reduced_concurrent_import_pairs`; expected:
   ≥19/20 PASS on
   `h5_normal_completion_does_not_starve_repl_eval_thread`
   (1/20 timeout flake still tolerated per /qa §3f.flake — the
   15-second ceiling is specifically calibrated to distinguish
   completed-vs-hung, not to be tight to typical wall-clock). If
   either metric is exceeded, treat as H7 evidence and open
   §3c''' in-sprint per /arch §3d'' R4.

5. **Baseline ledger close-time action**: /sprint MUST confirm
   `heisenbug_race_reduced_concurrent_import_pairs` moves to "resolved
   this sprint" alongside the original
   `sprint23::cache_repl_loads_heisenbug_parallel_stress`. Per /qa
   step 3f'' row "blocked-by 3e''" — H6 fix has landed; the entry
   is now pass-green by effect, not by re-authoring. Close-time
   verification per `tests/plan/baseline.md §"Close-time Verification
   Protocol"` item 3.

6. **Wave 3 commit readiness**: **GO**, pending no further /sprint
   concerns. All changes sit in working tree (no commits from /int
   yet, per /arch §3d'' condition 4 pre-commit review gate which is
   now closed with /typecheck APPROVE). The commit message should
   cite the three hypothesis cycles and name all four /arch
   mini-review verdicts.

Wave 3 closes the Slice 3 heisenbug cleanly across three evidence-gated
hypothesis cycles. The narrow cross-skill precedent was adjudicated,
scoped, and honoured end-to-end. The three post-fix dumps document the
atomic outcome (Created → AlreadyPresent × 2, no double-Created
signature). Ship Wave 3.

End of review.
