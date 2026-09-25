---
number: 0917
target: /test
filed_by: /port
filed_at: 2026-07-26
sprint_filed: 118
refers_to: design/backend/non-concrete-release-contract.md §6;
  tests/nullary_arm_beside_boxed_arm_0917.rs;
  tests/exemplar_ownership_residue_s116.rs;
  tests/CLAUDE.md §"Defect-repro notation"
status: open
retargeted_by: /arch
retargeted_at: 2026-09-25
---

# Nullary arm beside a boxed arm — fixed; its repro notation still reads open

## Current state (verified 2026-09-25)

- **The defect is fixed.** A bare nullary constructor in one match arm no
  longer licenses an unbalanced protect increment on a fresh boxed arm. The
  fix gave `ValueProvenance` a `NoReference` bottom below `Fresh`
  (`cbb3be9e`, S120). The ruling and its monotonicity and byte-identity
  obligations are canonical in
  `design/backend/non-concrete-release-contract.md` §6.
- **The acceptance cells pass.** In the final full run of the S122 cache
  work (`.local/s122-cache-dev-full-final.log`),
  `nullary_arm_beside_boxed_arm_frees_its_loop_under_run`,
  `nullary_arm_beside_boxed_arm_frees_its_loop_under_link`,
  `forwarding_fresh_option_releases_its_payload` and the exemplar cell
  `sudoku_warm_serial_solve_residue_at_most_1400` all passed.

## Remaining obligation (`test`)

The repro notation still marks these guards open, which misleads a
`grep -L fixed=` census:

1. Add `fixed=S120/cbb3be9e` to the `// defect:` lines of the two
   `nullary_arm_beside_boxed_arm_frees_its_loop_*` cells and of
   `sudoku_warm_serial_solve_residue_at_most_1400`, keeping each `locus=`
   token unchanged. `forwarding_fresh_option_releases_its_payload` records a
   separate S121 defect; `test` supplies its own `fixed=` value from its fix.
2. Replace that exemplar cell's closing "it flips when 0917's fix lands" with
   the fact that it has flipped.

## Closure

Both edits are committed; `test` deletes this filing.
