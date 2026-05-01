---
number: 0028
title: Priority-worker JIT is per-worker, not per-session (G10)
status: superseded-by-0031
---

# 0028 — Priority-worker JIT is per-worker, not per-session (G10)

**RETRACTED (Sprint 57 Wave 4 reconciliation, superseded by Decision 31).** Previous text: "Priority-worker JIT is per-worker, not per-session (G10)". This was factually wrong about Cranelift 0.116's behaviour in two ways — it assumed a long-lived per-worker `JITModule` could be reused across codegen calls (Cranelift's `JITModule::define_function` is single-use per `FuncId`, and a long-lived JIT coalesces batches and makes batch-scoped reclaim impossible), and it assumed `Arc<Jit>` drop on the last `ModuleEntry::Def.code` referencing it would reclaim JIT pages (Cranelift's `Memory::drop` explicitly `mem::forget`s its allocations — see Decision 31 evidence point 1 — so the default drop leaks). The canonical framing is now one `JITModule` per compile batch with a custom `Drop` on our `Jit` wrapper that calls `unsafe free_memory()`. See Decision 31 for the corrected model.
