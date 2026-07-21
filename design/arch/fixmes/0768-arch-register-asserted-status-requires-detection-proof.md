---
number: 0768
target: /arch
filed_by: /sprint
filed_at: 2026-07-21
sprint_filed: 115
refers_to: design/arch/safety-invariants.md §4 (status vocabulary + register
  rows; R7's S115 history is the worked example) + sprints/METHOD.md §2.2
  "An instrument is unverified until it is proven to detect"
status: open
---

# Register status: `asserted` / `gated` / `dynamic-lane` require a cited detection proof

## Issue

The §4 status vocabulary ranks instruments by strength — `unconstructable` >
`witnessed` > `asserted` > `gated` > `dynamic-lane` > `matrix-tested` >
`example-tested` > `unasserted`. What it does not require is evidence that an
instrument at a given tier **actually detects the thing it claims**.

S115 supplied both the counterexample and the cure:

- **R7 was recorded `asserted`** (S113 W4 landed `assert_prelude_closure` at
  the live-table insertion seams, "no false-fires in the landing window"). The
  predicate was provider-existence, structurally unable to catch the live
  phantom — the row was re-graded this sprint to *asserted-but-BLIND*. "No
  false fires" was read as health; it was silence.
- **The cure that worked** is in the same sprint: W2's corrected gate shipped
  with a synthesized trigger that goes RED when the correction is reverted.
  Discrimination proven, not assumed.
- **R8 is the sibling risk**: recorded `dynamic-lane`, and the lane's RC face
  is a differential that was blind to five leaks in the shared codepath
  (FIXME 0767 has the full account).

## Proposed resolution

1. Amend the §4 status vocabulary: `asserted`, `gated`, and `dynamic-lane`
   each require a **cited capability proof** — the test that plants the fault
   and observes detection (per METHOD §2.2's shapes: fail-on-revert for gates,
   per-variant for validators, planted-synthetic for lanes/modes, per-build-
   configuration for conditional fences). Without it the honest status is
   **`asserted-but-unproven`**, ranked below `matrix-tested`, and it is an open
   item against `/arch` exactly as `example-tested` is today.
2. Re-audit the current rows at those tiers and record which carry proofs.
   R5 (`asserted`, the CS-2 model) and R10 (`asserted`, S110 hard-error arms +
   KC-N1..N6 negatives) look like they already qualify — cite the proofs
   rather than assuming them, since that assumption is what this amendment
   exists to stop.
3. Consider whether the register should record, per row, **what the instrument
   is blind to** — the S115 lesson is that an instrument's blind spot is a
   property worth writing down beside its strength, because the blind spot is
   invisible precisely when the instrument is green.

Coordinates with FIXME 0767 (`/qa`, the matrix half). Candidate for a Phase-7
principle alongside "A fix carries its repro": *an instrument carries its
proof of detection*.
