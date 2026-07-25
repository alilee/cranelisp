---
number: 0890
target: /qa
filed_by: /testing
filed_at: 2026-07-26
sprint_filed: 118
refers_to: tests/exemplar_ownership_residue_s116.rs::sudoku_warm_serial_solve_residue_at_most_1400;
  tests/plan/s118-test-plan.md §2.1 (cell #21), §2.5 (Branch F), §4.4 (verified consequents);
  design/arch/fixmes/0889-recover-the-macro-turn-marshal-leak.md;
  tests/helpers/marginal.rs (the marginal-balance harness)
status: open
---

# Cell #21's threshold must be re-derived MARGINALLY at W3 acceptance

## Severity

Important — it is an acceptance-criterion correctness issue, not a defect. If
W3 accepts against the current number the sprint records a pass whose meaning
nobody can reconstruct afterwards.

## Issue

The S118 Branch-F change-set (`/testing`, 2026-07-26) retrofitted cells
**#10 / #19 / #20 / #23** onto marginal accounting and left **#21**
(`sudoku_warm_serial_solve_residue_at_most_1400`) untouched, because it is
W3-gated and `/testing`'s dispatch scoped it out. Its acceptance criterion is
now stated in units that no longer mean what they meant when it was written.

`#21` asserts an ABSOLUTE threshold — warm serial Sudoku residue ≤ 1400,
against an "independently measured composition residue (~1,312)". The Branch-F
probe established that **1143 of any stdlib-prelude child's residual is the
ambient FIXME-0889 macro-turn marshal leak**, present identically in a program
that does nothing at all. So:

- the ~1312 the threshold was derived from is ~1143 ambient + ~169 of the 0840
  composition residue the cell is actually about;
- the 1400 bound leaves 88 of headroom over that 1312, but ~87% of what it is
  bounding is not the exemplar's behaviour at all;
- when 0889 is fixed the same cell will read ~1143 lower for a reason entirely
  unrelated to 0840 or W3, and the threshold will silently become ~8× looser
  than intended — it would then pass with roughly 1231 blocks of genuine
  composition leak.

A threshold whose slack is dominated by a term from another defect cannot
discriminate a partial fix from a complete one, which is precisely the
judgement W3 acceptance has to make.

## Proposed resolution

At W3 acceptance, re-derive the criterion **marginally** rather than adjusting
the constant:

1. Measure the exemplar child against a same-prelude, same-env control (a
   trivial `--run` program) using `helpers::marginal` — the harness landed in
   this change-set is built for exactly this and needs no extension for it. The
   quantity becomes "what the Sudoku solve retains over a child that does
   nothing", which is the number §4.4 means when it calls #21 a verified
   consequent of W3.
2. Restate the bound against that marginal (expected order ~169 pre-fix,
   0 post-fix if the composition class closes completely) — and say in the cell
   header which measurement produced it and on what HEAD.
3. Keep it a **cell-level judgement, not a mechanical translation**: `/qa` owns
   whether the post-W3 bound should be a marginal threshold at all, or an exact
   marginal balance like the four retrofitted cells. `/testing` deliberately did
   not pre-empt that call.

Note the cell also differs from the four retrofitted ones in two ways the
re-derivation must handle: it runs **cold-then-warm without `--no-cache`** (the
warm run is the measured one, so the control must be warmed the same way), and
it copies the live `exemplar/` tree, so its subject is not a fixed source.

## Context

Filed as the disposition of the one baseline cell the Branch-F instrument-
truthfulness change-set could not fix in place. The four cells it did retrofit
(`ms_p8_conj_leak` ×3, `intrinsics_m3_detection_s116` ×1) all flipped GREEN on
zero marginal residual; #21 stays RED and W3-gated, and that RED is correct —
the exemplar does retain materially more than its composition residue. Only its
acceptance ARITHMETIC is affected.
