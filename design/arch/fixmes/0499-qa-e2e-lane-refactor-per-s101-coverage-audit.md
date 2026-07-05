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

## Per-lane status (S102 Phase-5 Stage-1 gate, 2026-07-03, /qa)

| Lane | Status | Where |
|---|---|---|
| **L-U1** unannotated-default siblings | **EXISTS** (S102 stage 1) | `tests/repl_redefinition.rs` + `tests/repl_persist_redefine.rs` — 8 tests incl. the §18.1.1 report acceptance pair |
| **L-S2** session-lifecycle grid | **EXISTS** | new `tests/repl_lifecycle_matrix.rs` (14 tests; grows with new session-visible state kinds per drafting rule 3) |
| **L-S3** file-backed dev-loop | **EXISTS** | new `tests/repl_mod_devloop.rs` (11 tests; + FIXME 0505 filed for the missing /repl spec pin) |
| **L-N1** display-exact | **EXISTS** | new `tests/display_exact.rs` (16 tests; first exact-line + `assert_golden_masked` adoption) |
| **L-N2** no-internal-artifacts | **EXISTS** | harness helper `assert_no_internal_artifacts` (`tests/helpers/e2e.rs`) + 24 retrofits in `repl_negative.rs` + 3 new diagnostic-shape guards; harness-DEFAULT flip deliberately deferred until Block A5 lands (would drown the signal in known-defect REDs) |
| **L-S1** session-history preambles | **DEFERRED in-sprint** (capacity-gated tail per plan §1.6) | may ride the A5 wave or defer to S103 with rationale at that gate |
| **L-M1** reference×referent×instantiation matrix | **SEEDED, rides B3** (plan §1.7) | grows with the Wave-11 `fn_as_value` seam rework — the 0483/0474 flips + corpus extension + new cells land in that wave |

Standing drafting rules (§2.5): adopted and exercised this pass (rule 1 —
the two drafting-discovered fn_as_value defects came from artifact-minting
probes; rule 2 — L-N1; rule 3 — L-S2 dirty-world rows; rule 4 — FIXME 0505).
Item-3 housekeeping (tests/CLAUDE.md registration): DONE at Phase 3.
**Remainder blocking deletion: L-S1 + L-M1's B3-wave growth.**

## Per-lane status (S103 Phase-3 plan, 2026-07-05, /qa)

The two remainder lanes are scheduled to land this sprint (increment II), per
`tests/plan/s103-test-plan.md` §1.6 + §3:

- **L-S1** session-history preambles — **PLANNED S103** (the deferred capacity-gated
  tail; author the preamble-grid helper over `repl_introspection.rs` +
  `repl_redefinition.rs`, generalizing beyond the 6a-burned cells). Defers to S104
  with rationale at the gate only if capacity forces it again.
- **L-M1** reference×referent×instantiation matrix — **GROWS WITH B3** (the
  `fn_as_value` seam rework, backend §13.3): the 0483/0474 guards already flipped
  GREEN in S102, so S103 growth = corpus EXTENSION with the newly-green shapes + the
  new value-use × ≥2-instantiation cells the reuse-token/R5 seam introduces.

**Deletion condition:** if L-S1 lands and L-M1's B3 growth is in, all 7 lanes exist
→ /qa deletes this FIXME at S103 close. Else annotate + carry.
