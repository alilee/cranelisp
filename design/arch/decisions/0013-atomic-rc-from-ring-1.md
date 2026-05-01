---
number: 0013
title: Atomic RC from Ring 1
status: operative
---

# 0013 — Atomic RC from Ring 1

reference count operations use `atomic_rmw` with sequentially-consistent ordering (Cranelift's default for `atomic_rmw`) even though Ring 1 is single-threaded. A separate Acquire fence is emitted on the free path (when `old_rc == 1`) before reading object fields for drop glue. This avoids a breaking ABI change when concurrency arrives in Ring 4, per NFR C.4.1. See `design/backend/ring2-rc.md` §2.1.
