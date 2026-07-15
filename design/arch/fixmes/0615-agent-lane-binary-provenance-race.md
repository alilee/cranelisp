---
number: 0615
target: /testing
filed_by: /qa
filed_at: 2026-07-15
sprint_filed: 110
scheduled: S110 (rides the planned W-GATE infra lane per SPRINT.md §Waves)
refers_to: SG-2 attribution — the `agent_flag_errors_on_non_agent_build`
  build-interleave failure /testing flagged at P5-S1 (SPRINT.md §Skill plans).
  Separate root from 0604 (build substrate, not runtime SharedState) — do not
  fold. Attribution record `tests/plan/s110-attribution-sg1-sg2.md`; risk row
  `tests/plan/risks.md` S110-11.
status: open
---

# Agent-lane binary provenance race — a `--features agent` build clobbers `target/debug/cranelisp` mid-suite

## Mechanism (confirmed; the forbidden dispositions do not apply — this is a
## build-artifact race, deterministic in binary provenance, not an assertion flake)

- The e2e harness hardcodes `workspace_root()/target/debug/cranelisp`
  (`tests/helpers/e2e.rs:368–371`) for EVERY spawn, in both lanes.
- The agent lane (`cargo nextest run --features agent --test agent`,
  `tests/agent.rs:23`) rebuilds the SAME artifact path with the agent feature
  compiled in.
- A concurrent/interleaved agent-lane build therefore swaps the binary
  mid-default-suite. Feature-OFF guards — e.g. `tests/agent.rs:143`
  `agent_flag_errors_on_non_agent_build`, which asserts the binary REJECTS
  `--agent` with exit 1 — then spawn an agent-capable binary that ACCEPTS the
  flag and starts the session → assertion failure. The test outcome is a pure
  function of which binary sits at the path at spawn time.
- A single-profile `cargo nextest run` is safe (cargo rebuilds with the
  invocation's own feature set before any test runs) — matching /testing's
  non-reproduction observation. The race requires two cargo invocations with
  different feature sets sharing one target dir.
- A nextest setup-script ordering fix alone CANNOT cure this: setup scripts
  order steps within ONE invocation; the race is BETWEEN invocations.

## Fix (all /testing-owned surfaces; no /dev source)

1. **Target-dir isolation for the agent lane** — committed launcher
   `tests/scripts/run-agent-lane.sh`:
   `CARGO_TARGET_DIR=target/agent cargo nextest run --features agent --test agent`.
   The agent-featured binary then lives at `target/agent/debug/cranelisp` and
   can never clobber the default binary — isolation by construction.
2. **Lane-aware harness resolution** — `e2e.rs::materialise()` resolves the
   binary root from `CARGO_TARGET_DIR` when set (falling back to `target/`),
   so the agent lane's tests exec their own lane's binary.
3. **Document the lane invocation** — replace the bare
   `cargo nextest run --features agent --test agent` in the `tests/agent.rs`
   header (and note in `tests/CLAUDE.md`) with the script.
4. Optional hardening: a provenance probe in the agent-family helper that
   produces a NAMED failure ("stale agent-featured binary at default path")
   instead of a bare assertion diff.

## Acceptance

- /testing's own bar: the agent e2e family passes **3× consecutive**
  full-suite runs, no isolation retry.
- Plus the dual-build check: deliberately launch the agent lane (via the
  script) while a default-suite run is active; `target/debug/cranelisp` mtime
  is UNCHANGED by the agent-lane run; no feature-OFF guard fails.
- Validation respects the one-agent-one-test-run rule — schedule the runs in
  the W-GATE lane when no other agent is testing.
