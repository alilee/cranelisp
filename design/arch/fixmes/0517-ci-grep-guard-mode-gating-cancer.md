---
number: 0517
target: /qa
filed_by: /sprint
filed_at: 2026-07-04
sprint_filed: 102
refers_to: src/ (5 mode-bit origin expressions), tests/ or CI config
status: open
---

# CI grep guard against the mode-gating cancer class (origin-anchored)

The S102 /arch audit established that the "mode-gating cancer" class (a language-semantic decision — error/rejection/resolution — conditioned on REPL vs `--run`/`--link`) has a **tiny, closed set of ORIGIN expressions in `src/`**, and that naive detection fails because the mode bit is laundered through renamed bool params (`reject_def_over_import`, `reject_over_local_def`) far from the origin — which is why 0514 evaded review. A cheap origin-anchored guard catches the class at commit time.

## Proposed guard (bake into CI / a test)

**Origin-anchored grep** over `src/` for the closed mode-bit origin set (re-enumerate at implementation time — the 0514 fix removed `additive`, so the current set is smaller):
```
grep -rnE '== *ModuleStrategy::(Additive|Replace)|\.is_repl\(\)|\.populates_introspection\(\)|run_mode *==' src/
```
For each hit, a reviewer-trace obligation: confirm no arm reaches an `Err(_)` / diagnostic emission / resolution-decision differently per mode. Maintain a **one-line allowlist** with rationale: `src/process_form/platform.rs` `layout_hash_gate` (user-ratified `platform-interface.md §5.5.4` — REPL WarnAndLoad vs batch Refuse on platform layout-hash mismatch is a build-integrity gate, NOT program-meaning; the REPL is the only schema-regen path — do NOT "fix" to uniform).

**Supplement — flag laundering**: grep bool params whose names encode a rejection decision (`reject_*`, `refuse_*`, `is_repl`, `additive`, `interactive`) crossing a `fn` boundary; each must trace to an allowlisted origin.

**Acid-test note** (S102 user): the guard's deeper purpose is catching *early-branch duplication* — two paths doing the same work because of an early mode branch — not only meaning-divergence. A grep can only flag the origins; the reviewer trace applies the acid test ("are we doing the same thing on two paths because we branched early?").

A true clippy/dylint boolean-taint lint (taint the bool from an origin, warn on a control-dependent `return Err`) is buildable but non-trivial (interprocedural taint through the renamed params). Ship the CI grep first (≈10 lines, zero false-negative on origins); treat the taint-lint as later hardening if the class recurs.

## Operational implication
Standing prevention — makes "find these efficiently" true going forward (catch at commit, not a sprint later). Not blocking the ownership increment; high value / low cost, worth landing this sprint. Full context: `sprints/SPRINT.md` §Notes /arch-audit entry; `memory/feedback_investigate_suspected_dual_path.md`.
