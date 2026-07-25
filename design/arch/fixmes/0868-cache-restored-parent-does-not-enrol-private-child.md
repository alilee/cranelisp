---
number: 0868
target: /dev
filed_by: /testing
filed_at: 2026-07-25
sprint_filed: 117
refers_to: spec/08-modules.md §8.2.3 and §8.2.5;
  design/backend/module-caching.md §8;
  tests/cache.rs::cache_restored_parent_enrols_private_test_child
status: open
---

# Cache-restored parent does not enrol its declared private child

## Issue

A fresh REPL import of a parent containing `(mod- test)` finalizes the parent
and then drives the declared child. The same named import in a second process
restores the parent from cache but does not load the child. Consequently,
`/run-tests parent.test` reports no test functions even though the unchanged
fresh session discovers and runs the child.

The reduced guard uses only a parent with one public function and one private
child containing a single eligible test. The named public import is therefore
the documented force-load shape, not a null-import or harness misuse.

The persisted symbol table already contains the `submodules` declaration.
`register_cached_with_scheduler` installs that structural state, but the
cache-hit path does not perform the fresh path's post-finalization
`drive_submodules` step. The omission is therefore cache/fresh lifecycle
divergence, not expected private-child visibility: privacy restricts access
from outside the subtree, while the parent's own declaration still requires
the child file to be resolved and loaded.

## Proposed resolution

Make cache-hit installation enroll every declared child through the same
idempotent module-dependency mechanism used after fresh parent finalization.
Preserve the private visibility carried by `ModDecl`; do not make the test
child public and do not special-case names ending in `.test`.

The repair must retain:

- fresh/cache equivalence for both public and private declared children;
- child-file resolution relative to the declaring parent's real file;
- parent-before-child readiness, so child `super` imports see the parent;
- idempotence when a child is already live or is also reached by another
  dependency edge;
- cache invalidation and scheduler failure propagation.

The permanent failing-not-ignored discriminator is
`tests/cache.rs::cache_restored_parent_enrols_private_test_child`. A narrow
owner unit test should additionally pin the cache-hit registration-to-child
enrollment transition.

## Plan handoff

This unplanned Phase 6b defect also needs a `/qa` PLAN row before closure.
