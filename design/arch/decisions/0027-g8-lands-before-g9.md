---
number: 0027
title: G8 lands before G9 (platform-registry deletion before persistent workers)
status: operative
---

# 0027 — G8 lands before G9 (platform-registry deletion before persistent workers)

Phase 4 Step 4a (G8 — delete `PlatformRegistry`) MUST land before Phase 4 Step 4b (G9 — persistent priority workers), not in parallel and not in the opposite order. The reason is a concrete borrow-checker obstacle surfaced in `/int`'s Wave 1 design audit: the current `Mutex<PlatformRegistry>` swap-in/swap-out dance around every `thread::scope` block (`src/session_v4.rs:993–1026` and `:1088–1128`) is the primary per-call mutable state that breaks the `Arc<SharedState>` threading the persistent-worker refactor requires. Deleting `PlatformRegistry` first removes the `&mut PlatformRegistry` borrow from `ModuleCompiler` and `PriorityWorkerRefs`, at which point the G9 refactor is a mechanical signature change rather than a borrow-checker obstacle course. Doing G9 before G8 would require scaffolding an `Arc<Mutex<PlatformRegistry>>` form that is then deleted one wave later — throwaway infrastructure contrary to Principle 8. Canonical reference: `design/int/persistent-workers.md` §8.1 (risk mitigation), `design/int/platform-registry-removal.md` §10 (deletion list). Sequencing invariant enforced by Sprint 57 wave ordering (Wave 2 = G6; Wave 3 = G8; Wave 4 = G9). Rationale: Principle 8 (no interim implementations of later-ring capabilities — here, no interim scaffolding to support a wave that would be unblocked by doing the other change first).
