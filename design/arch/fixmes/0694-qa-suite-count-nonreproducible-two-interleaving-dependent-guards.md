---
number: 0694
target: /qa
filed_by: /review
filed_at: 2026-07-20
sprint_filed: 114
refers_to: tests/nullary_return_dispatch_method_only_import.rs + tests/macro_expansion_interior_alias_double_free.rs (suite-count ledger arithmetic)
status: open
---

# W4's "30 failed, exact" does not reproduce: 31 both runs, with two guards trading membership across runs (interleaving-dependent)

## Severity
Important

## Issue

The W4 close note records `5080 run / 5050 passed / 30 failed / 1 skipped
(exact)`. Two consecutive full `cargo nextest run --no-fail-fast` runs on the
committed tree (f9435b37) both give **5049 passed / 31 failed / 1 skipped**,
and the failing SET differs between runs:

- Run 1: `macro_clause_interior_alias_double_free_link` RED (its `_run`/`_m1`
  siblings are stably RED in both runs); `nullary_return_dispatch_…` GREEN.
- Run 2: `…_link` GREEN; `nullary_return_dispatch_method_only_import_no_codegen_leak`
  RED.

Both flickering tests trace to open defects (`// defect:` S111 uaf /src
marshal seam; S112 check-gate-leak typecheck), so neither is an untraced
regression — but:

1. `nullary_return_dispatch_method_only_import_no_codegen_leak` is
   **expected-GREEN post-W2** (its header says "RED until W2 flips the accept
   path", and it passes 8/8 in isolation). Its failure appears only under
   full-suite parallel load — an interleaving/load-dependent failure of a
   should-be-green test. Per the failing-test discipline, "flaky" is banned:
   this is evidence of a real race or load-dependent fault that needs
   characterization and attribution (candidate classes:
   `shared-state-write-race`, or resource contention in the harness).
   The failure output of the in-suite occurrence was not captured; first step
   is reproducing under controlled parallel load and reading the actual
   assertion failure.
2. The `_link` UAF face flickering red↔green is at least *consistent* with its
   class (layout-dependent corruption), but a KNOWN-open guard whose color is
   run-dependent breaks the exact-count wave-gate arithmetic (47 − 18 + 1 = 30
   assumed deterministic REDs). /review cannot rule out that W4's RC-emission
   changes shifted heap layout in that subprocess (the commit changes RC
   patterns in `main` frames); attribution needs the S98 discipline
   (verify-fix-not-symptom: perturbation reshapes layout).

## Proposed resolution

/qa: characterize both under repetition (isolation vs parallel load), capture
the in-suite failure output, attribute, and decide how the ledger arithmetic
handles guards whose manifestation is probabilistic (e.g. count them as a
named unstable set rather than folding them into an "exact" scalar). If the
nullary face's load-dependence is new since W2/W4, bisect attribution is
warranted.

## /qa S114 pre-W7 disposition (2026-07-20 — RE-SCOPED; stays open through the Phase-7 verification)

Record: `tests/plan/s114-test-plan.md` §11 item 2.

1. **The macro_clause `_link` face is CLOSED BY FIX.** W5 C2 (`58ac8e46`,
   0638 deep protect-on-build) fixed the underlying double-free; all 5 pins
   GREEN and the test is stable green through W6/cleanup (`adb8d3fb`: 8
   REDs, none macro_clause). The red↔green run-dependence was the real
   layout-dependent corruption manifesting — consistent with its class, and
   the mechanism is gone. No further action on this face.
2. **Remaining scope = the nullary load-flap only**
   (`nullary_return_dispatch_method_only_import_no_codegen_leak`: 14/14 in
   isolation, fails only under full-suite parallel load; 0/… in-suite
   output never captured). **Expectation:** W7's /dev(typecheck) work at
   the no-impl fallback seam family (F-D2-11) may stabilize it.
   **Verification (Phase-7 certification, binding):** ≥3 consecutive full
   `cargo nextest run --no-fail-fast` runs —
   - green in ALL → this FIXME closes with a watch clause (any future
     in-suite RED of this test = reopen as a root-cause row; "flake" is
     banned);
   - RED in ANY → capture the in-suite failure output (nextest captures it
     — preserve it) and open a **root-cause investigation row in S115**:
     load-dependent behaviour in a check-gate is a real defect signal
     (candidate classes: `shared-state-write-race`, or a
     harness/resource-contention mechanism — to be demonstrated, not
     presumed).
3. **Counting convention (standing, adopted):** suite-state certification
   reports stable REDs as an exact count PLUS a NAMED flap-class set; a
   run-dependent guard is never folded into an "exact" scalar (`adb8d3fb`'s
   "7 W7 residuals + the 0694 nullary load-flap" is the practiced form).
   The bisect question (new since W2/W4?) folds into the S115 row if opened
   — not worth build-window contention before the W7 seam work lands.

## /qa S115 Phase-3 disposition (2026-07-20 — the root-cause row is drawn)

The S114 Phase-7 ≥3-run verification did not complete before close (2/≥3);
the nullary flap carried into S115 as the named flap set's first member.
**Plan of record: `tests/plan/s115-test-plan.md` §2** — standing counting
convention (stable-exact = 11 + named flaps, live-verified this session:
the nullary face was GREEN in the single Phase-3 run); passive capture of
the first in-suite failure output across the ≥2/≥3 certification runs;
stabilization-hypothesis check after the S115 0709/no-impl-gate typecheck
wave (×20 under-load re-run); a time-boxed load rig SHARED with 0604's
re-induction attempt; disposition forks by what the captured output names.
Close condition unchanged: ≥3 consecutive certification runs green + the
post-fix ×20 green → close with the watch clause; any RED reopens the row
by name, never "flake".

## /testing roster update (2026-07-21, S115 W3c) — the named flap set is now THREE

`agent::y_short_flag_errors_on_non_agent_build` (`tests/agent.rs:240`) joins the
named flap family recorded in the S114 disposition item 3 / `s115-test-plan.md`
§2. Same signature as the 0694 nullary face: **passes in isolation, fails only
under full-suite parallel load**, and traces to no unattributed defect. Observed
in the W3b baseline run at `1ee57501` (suite 5255 run / 5225 passed / 28 stable
REDs / 1 skipped, plus these two flaps).

Consequences for the counting convention (unchanged in kind, wider in scope):

- the certification scalar remains **stable-REDs-exact + a NAMED flap set**, and
  that set now has TWO members: `{0694 nullary load-flap,
  agent::y_short_flag_errors_on_non_agent_build}`. Neither is folded into the
  exact count.
- the ≥3-run close condition in the S115 Phase-3 disposition applies to the
  nullary face only; the agent-lane face is a NEW observation whose
  characterization (isolation vs load, in-suite output capture, attribution) is
  owed the same treatment before it can close. Per the failing-test discipline
  "flaky" is not a disposition for either.
- note the lane asymmetry: `tests/agent.rs` cells run in BOTH lanes (the
  `#[cfg(not(feature = "agent"))]` face here runs in the DEFAULT suite, not
  through `run-agent-lane.sh`), so the binary-provenance isolation of FIXME 0615
  is not by itself an explanation — a candidate mechanism, to be demonstrated
  rather than presumed, is process/resource contention at spawn under full
  parallel load.

**THIRD member, observed live this session:
`multi_sig_module_locality::imported_multi_sig_base_direct_call_repl`
(`tests/multi_sig_module_locality.rs:83`).** Two consecutive full
`cargo nextest run --no-fail-fast` runs on the SAME tree (W3c, HEAD `1ee57501`
plus this wave's test-only edits): RED in run 1, GREEN in run 2. It is a
declared GREEN fence ("Was RED pre-W2; GREEN fence now" — the MC-X2 REPL face
of the S113 carrier-loss family, `// defect:` class=carrier-loss,
owner=/dev(typecheck)), so like the nullary face this is a should-be-green
test failing only under full-suite parallel load. Its in-suite failure output
was NOT captured (run 1 was not tee'd — my miss; run 2 onward is logged).
Notably it is a REPL-mode cell of the same multi-sig/no-impl-fallback seam
family as the nullary face — a shared-seam hypothesis worth testing before a
harness-contention one.

Both new members carry the same evidentiary obligation as the nullary face
(isolation-vs-load characterization, in-suite output capture, attribution);
none may be dispositioned as "flaky".

This FIXME stays OPEN (roster update only; no disposition change).

## Context

Found by /review W4 while verifying dispatch priority 8 (suite-state
certification). The 18 flips themselves verified green in both runs; the
MS-P7 safety-lane pin (`safety_lane_cow_set_read_returns_set_value_abort_free_red`)
is RED in both runs (fence held).
