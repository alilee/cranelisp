---
number: 0499
target: /qa
filed_by: /sprint
filed_at: 2026-07-03
sprint_filed: 101
refers_to: tests/plan/coverage-audit-s101.md §2.4 (lanes) + §2.5 (drafting rules), tests/CLAUDE.md §Plan documents
status: open
---

# E2E lane refactor — implement the S101 coverage-audit lane proposals + standing drafting rules

## Issue

The S101 risk review + coverage audit classified 12/17 misses as e2e-construction properties `/qa` owns: assertion-too-weak (1,817 presence-style assertion sites vs 13 exact-output suite-wide), canonical-script blindness (session-history preamble never a test dimension), never-exercised state combinations (multi-session over compound states, file-backed modules, cache-restored paths, dirty-cwd cells), and the diagnostic-surface substring exemption. The audit proposed 7 named lanes + 4 standing drafting rules as the structural cure. Without a tracked carrier, the lanes stay a doc.

## Proposed resolution

1. Implement the lanes in the audit's recommended order, riding the sprints whose scope touches each surface (not one monolithic refactor): **L-U1** unannotated-default siblings (S102, pairs with the T1 work) → **L-S2** session-lifecycle grid + **L-S3** file-backed dev-loop (S102, pairs with the /int persistence-defect wave) → **L-N1** display-exact + **L-N2** no-internal-artifacts sweep → **L-S1** session-history preambles → **L-M1** reference-shape × referent × instantiation-count matrix (grows with increment I's seam work).
2. Adopt the 4 standing drafting rules (§2.5) immediately — they govern all new test authorship from S102 Phase 5 stage 1 onward.
3. Housekeeping owed from the audit's edit boundary: register `coverage-audit-s101.md` in `tests/CLAUDE.md` §Plan documents (one line).

## Operational implication / Context

This is the /qa half of the S101 audit's action set; FIXMEs 0495–0498 + 0500–0502 are the per-crate /dev unit-tier half. Partial-resolution is expected — the FIXME defers per-lane with rationale at each sprint gate rather than closing all-at-once; delete when all 7 lanes exist (or are explicitly retired) and the drafting rules are in the qa skill's working docs.
