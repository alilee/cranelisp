---
id: ACT-1017
title: Locate a failed-dependency refusal in the right file, with one located prefix
status: resolved
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-30
refers_to:
  - repl/spec/05-error-presentation.md §5.1
  - repl/spec/05-error-presentation.md §5.5
  - src/scheduler.rs::refuse_failed_dependency_locked
  - tests/spec_08_modules.rs
  - tests/repl_persist.rs
---

## Resolution (qa, 2026-11-15, S123 W1)

Both faces are fixed: the refusal is located in the failed module's file and
carries one located prefix.

- **Location face.** Fixed at the S122 close (`aed0fcb1`), remeasured at S123
  W0; `tests/spec_08_modules.rs::failed_import_location_belongs_to_named_file_neg`
  is its guard.
- **Prefix face.** Fixed in W1 under the Phase 2 → 3 ruling that REPL §5.5
  governs it. `src/scheduler.rs::refuse_failed_dependency_locked` now wraps
  the failed module's error once. `tests/spec_08_modules.rs::failed_import_has_one_located_prefix_neg`
  and `tests/repl_persist.rs::failed_import_reload_has_one_located_prefix_neg`
  were RED at W0 and pass in the full suite of 2026-11-15, with their
  non-failed-import controls; the unit row is
  `src/scheduler/tests.rs::failed_dependency_refusal_has_one_located_prefix_in_the_failed_file`.
- **Owed.** `test` stamps `fixed=S123/<W1 commit>` on both prefix cells when
  W1 is committed.
- Delete this action once `design/int/int.md` and
  `tests/plan/s122-evidence-delta.md` no longer link it.
