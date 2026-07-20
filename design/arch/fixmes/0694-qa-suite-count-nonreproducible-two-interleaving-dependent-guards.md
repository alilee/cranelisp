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

## Context

Found by /review W4 while verifying dispatch priority 8 (suite-state
certification). The 18 flips themselves verified green in both runs; the
MS-P7 safety-lane pin (`safety_lane_cow_set_read_returns_set_value_abort_free_red`)
is RED in both runs (fence held).
