---
number: 0491
target: /docs
filed_by: /sprint
filed_at: 2026-07-01
sprint_filed: 97
refers_to: user/guide/concurrency.md, design/intrinsics/reactor.md (ctx-vtable poll-fn model), design/platform/poll-support.md
status: open
---

# Phase-6 (carried): split the concurrency docs — user guide vs platform-writer's guide

## Issue

S97 scope §D (user-directed): split `user/guide/concurrency.md` into (1) a **user concurrency guide** (the inferred half + `race`/`select`/`timeout`/`sleep` + structured cancellation — **no scheduling internals**) and (2) a **new platform-writer's guide** (authoring poll-shape leaves, the ctx-vtable poll-fn skeleton `acquire`/`register_*`/`retire`, the four leaf roles, the manifest). S97 closed before Phase 6 executed, so this is carried. **The split is now cleaner than when scoped** — the platform-writer's guide documents the ctx-vtable poll-fn skeleton (`design/intrinsics/reactor.md` / `design/platform/poll-support.md`), NOT a descriptor ABI (the v9 model dissolved the descriptor).

## Proposed resolution

/docs (next-sprint Phase 6): author the two guides along the tramp-opaque/user-visible seam (the descriptor is the platform-writer's / runtime's concern, invisible to the user's mental model — the same cut the S97 ownership tidy drew). Run-validate every snippet. Cross-link `user/getting-started.md`.
