---
id: ACT-1013
title: Report a qualified-reference module cycle closed by a reload as a circular-dependency error
status: open
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-29
refers_to:
  - spec/08-modules.md
  - src/session_v4/lifecycle.rs
  - tests/spec_08_modules.rs
---

## Requirement

[Spec §8.5.4](../../spec/08-modules.md#854-auto-loading-s109)
edge 6 says that a qualified reference closing a module dependency cycle MUST
be reported as a circular-dependency error naming the cycle path, at parity
with `import` cycles (§8.10.2).

## Observation (2026-09-29, binary `b68a0e8a…db4560`)

Probes are in `.local/s122-quiescent-rebuild-final-qa-scratch/p3` and `p3c`.
They ran with no prelude and no trace variables.

- **Subject, a reload.** At the start, `a.cl` is `(defn f [] 1)`, `b.cl` is
  `(defn g [] (a/f))` and `user.cl` is `(defn run [] (b/g))`, so `(run)` gives
  1. A save of `a.cl` as `(defn h [] (b/g)) (defn f [] 5)` closes the cycle
  `a → b → a`. The results:
  - `[updated: a.cl]`, `[updated: b.cl]` and `[updated: user.cl]` are
    reported, with no error;
  - `(run)`, `(a/h)` and `(b/g)` each give 5.
- **Control, the same sources loaded fresh.** At the start, `[errors: user.cl]`
  reports `module error at 0..0: in-memory codegen incomplete for 'b'`, and
  evaluation is blocked. There is no circular-dependency error.
- **Existing evidence.** `tests/spec_08_modules.rs::fq_ref_cycle_reports_circular_dependency_path`
  and `fq_ref_mixed_cycle_import_plus_fq_reports_cycle` pass under `--run`.

## Impact

- The session accepts a cyclic program that a restart does not load. The
  session and the restart therefore diverge.
- The order check in `run_reload_plan` stops when its follow-on root set
  recurs, and that set can recur only through such a cycle. When it stops it
  reports success, leaving the dependent neither re-ordered nor locked.
  Review (src) A2 raised this, and QA read it in source. In the probe the
  values stay correct, because the cyclic modules rebuild from unchanged
  source with the same slot layout.

## Attribution

- **Provisional.** The mechanism is a hypothesis (review A2): cycle detection
  runs only while a module loads, so a reload whose qualified reference
  reaches an already-loaded module is never checked. It is unobserved at its
  seam.
- **Refuter.** The same reload shape is rejected when `b` is not yet loaded.
- **Separate face.** At a REPL fresh load, the cycle is reported as an
  incomplete codegen rather than as a cycle. It may be a shape difference
  from the `--run` cells, or a mode divergence. It is unattributed.
- **Age.** Source reading suggests the reload face predates S122's rebuild.
  Before the rebuild, `b` was not selected as a dependent. The reload face
  was not executed at `63605970`.

## Handoff

- `test` commits a failing, unignored RED for the reload face (§8.5.4 edge 6),
  with the fresh-load control. The REPL fresh-load diagnostic gets a second
  leg or cell once reduced.
- Then `design`(int) places cycle detection on the reload path and decides the
  order check's behaviour when its set recurs. Review recommends locking the
  recurring set.

## Completion

The reload is rejected with a circular-dependency error naming the path. The
REPL fresh load reports the same error. The `--run` cells stay GREEN.
