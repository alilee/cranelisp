---
number: 0608
target: /dev
filed_by: /sprint
filed_at: 2026-07-15
sprint_filed: 110
scheduled: S110
refers_to: src/ over-budget functions (26 > 120 lines against the context's own
  ~100-line budget) + 3 over the 8-param cap, worst-first. Narrow-deploy /dev to src/.
status: open
---

# Over-budget function batch, worst-first, with narrative relocation

## Source

S109 `src/` whole-context audit (`audits/src-s109.md` R-4), **ACCEPTED** S110 Phase 1.

## Evidence (quoting the assessment §2.3)

26 production functions > 120 lines. Worst:
- `main.rs::run` (:241, **394 lines, 9 params**)
- `exe.rs::generate_startup_object` (:50, 340)
- `worker.rs::commit_staging_to_live` (:423, 237)
- `process_form.rs::process_cluster_once` (:150, ~224 — **grown** from ~150 at S87)
- `main.rs::parse_args` (:641, 225)
- `redefine.rs::run_transaction` (:852, 185)

Three functions exceed the 8-param cap, worst `compile_macro_with_state` (11 params,
`src/process_form/macro_resolution.rs:314`).

## Shape (assessment §3 R-4)

Phase-named helper extraction (each offender already has phase comments marking the cut
points); context structs for the two param-cap violators. **Third-time narrative flag:**
when touching a function, move its ≥30-line sprint-history comment block into the relevant
`design/int/` doc, leaving a one-line pointer — couples with 0607 (R-3) so the narrative
has a current home.

## Done

The six named functions ≤ ~120 lines with named helpers; no function > 8 params;
behaviour-invariant (suite green, zero `public-api.txt` diff).

## Sequencing

src/-side hygiene track, SERIAL with 0606/0607 (same files: `process_cluster_once` and
the repl.rs handlers overlap the R-1 cut). Order after 0606's decomposition so the
extractions rebase onto the new module layout, or coordinate the cut points.
