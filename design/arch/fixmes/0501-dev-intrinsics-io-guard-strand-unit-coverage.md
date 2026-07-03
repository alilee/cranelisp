---
number: 0501
target: /dev (cranelisp-intrinsics)
filed_by: /sprint
filed_at: 2026-07-03
sprint_filed: 101
refers_to: tests/plan/coverage-audit-s101.md §3 (intrinsics row), sprints/METHOD.md §2.2
status: open
---

# Intrinsics thin-submodule drain — io_guard (zero coverage) + strand (thin)

## Issue

The S101 coverage audit's submodule map rates cranelisp-intrinsics ADEQUATE overall (226 tests / 16.6k LOC) with two named thin submodules: **io_guard has ZERO unit coverage** and **strand is thin** relative to its strategy content. Both sit on the concurrency/effect surface where the Principle-22 class lives — exactly where untested strategy scenarios have bitten before (S97/S98 baked-arg UAF; 0494-bug-#2 strand teardown).

## Proposed resolution

Per METHOD §2.2: derive the strategy scenario spaces for `io_guard` and `strand` (complexity paths, boundary/matrix cells, negative cases — what must NOT be freed/reordered/delivered), land them as per-submodule test modules. Assess whether the existing drop-glue/databuf tripwires already cover named cells (cite rather than duplicate).

## Operational implication / Context

Sibling of 0495–0498/0500/0502. Natural carrier: the effect-concurrency slice-2 reactor work or any next intrinsics touch — whichever lands first.
