---
id: ACT-1020
title: Reconcile the file a dotted CLI entry target names with the module path mapping
status: open
priority: advisory
from: qa
to: qa
sprint: 122
filed_at: 2026-09-30
refers_to:
  - repl/spec/00-cli-invocation.md
  - spec/08-modules.md
  - src/pipeline.rs::module_relative_path
  - src/session_v4/lifecycle.rs::register_entry_module
---

## Request

Settle which file a dotted CLI entry target such as `core.str` names. Then
classify the as-built resolver against that answer.

## Observation

- **Source (read 2026-09-30, `fefd41e8…`; review A3 of K1).**
  `pipeline::module_relative_path` replaces `.` with `/`, so an entry
  `core.str` resolves to `{root}/core/str.cl`.
  - K1's batch refusal names that path.
  - The REPL empty-start arm records `{root}/core.str.cl`.
  - Not executed.
- **The requirements disagree.**
  - CLI §0.5.6: a dotted target is "a single module name, not … a path
    separator", and `core.str` "will fail if no file `core.str.cl` exists".
  - CLI §0.5.5 rule 2 names `{project_root}/{entry_module}.cl`.
  - Spec §8.1: `foo/bar.cl` defines module `foo.bar`, so module `core.str`
    lives in `core/str.cl`.
- **Class L.** The disagreement is between requirements, so QA encodes no
  condition until `spec` returns the user's answer.

## Disposition

- **Not an S122 package item and not carried.** K1 did not introduce the
  mapping. It only made the batch refusal name the resolver's path.
- `sprint` should put the `spec` question in the Phase 5 → 6a presentation,
  not in a separate question cycle.
- **When answered:**
  - `test` reduces a dotted-target cell in `--run` and the REPL;
  - the owner of any change is `dev`(src) at the resolver, or `spec` if the
    as-built mapping is ruled correct.
- **Refuted if** a located requirement already states that CLI targets follow
  §8.1's mapping.
