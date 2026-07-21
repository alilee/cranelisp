---
number: 0767
target: /qa
filed_by: /sprint
filed_at: 2026-07-21
sprint_filed: 115
refers_to: sprints/METHOD.md §2.2 "An instrument is unverified until it is
  proven to detect" + tests/plan/s115-instrumentation-matrix.md (the O-row +
  VERIFIED-IN-PLACE criterion) + tests/plan/memory-safety-coverage.md §4.1
  (the per-mode mandate this generalises) + §1.2 (the four-signal combinator
  that carried no capability fence of its own)
status: open
---

# Matrix acceptance: a row is VERIFIED only when it cites its detection proof

## Issue

The S115 matrix's criterion is "cite file:line AND the test that exercises
it". S115 proved that insufficient in the sharpest possible way: the standing
safety lane's RC face asserts `imbalance(ON) == imbalance(OFF)` — a
differential over two configurations of ONE codepath — and five real leaks
lived in the shared, non-ownership-gated part, so every cell compared
`0 == 0`. Tests exercised the lane constantly. Nothing ever planted a fault of
the class it claims to cover and checked that it fired. In `/testing`'s
words: *the lane's pass was not weak evidence, it was NO evidence.*

The rule that would have caught this already exists one level down —
`memory-safety-coverage.md` §4.1 mandates a synthetic self-test per diagnostic
MODE, and those fences exist and pass (quarantine ×2, scrub ×2, parity ×4).
The lane composed OF those modes has no such fence. **The proofs of the parts
do not compose into a proof of the composition.**

METHOD §2.2 now binds the general rule. This FIXME is its matrix half.

## Proposed resolution

1. **Upgrade the matrix criterion.** A row may be marked **VERIFIED-IN-PLACE**
   only when it cites, alongside the mechanism's file:line, the **capability
   test** that plants the fault the instrument claims to catch and observes
   detection. Rows with a mechanism and exercising tests but no detection
   proof take a distinct status — `asserted-but-unproven` — which is an open
   item, not a pass. Re-audit the current S115 rows against the stronger bar
   (expect several 14 VERIFIED rows to move; that movement is the finding, not
   a regression).
2. **Fold into the 0761 lane design.** The exact-balance lane must ship with
   its own capability fences from day one — a planted leak, a planted
   over-release (the opposite polarity no residue-allowance ever catches), and
   a planted constant-vs-scaling fault — proving the lane detects each class it
   is built to cover. §4.1's "synthetic, never a live defect" rule applies:
   planting on a real bug means the fence dies with the fix (the m1/m3
   lesson, twice now).
3. **Generalise §4.1's scope** from "diagnostic mode" to "instrument,
   including a composed one", so the next lane/combinator/oracle inherits the
   mandate rather than falling through the same gap.

Coordinates with FIXME 0768 (`/arch`, the register-status half).
