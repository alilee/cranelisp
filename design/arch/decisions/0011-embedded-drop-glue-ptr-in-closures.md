---
number: 0011
title: Embedded drop_glue_ptr in closures
status: operative
---

# 0011 — Embedded drop_glue_ptr in closures

Each closure carries a `drop_glue_ptr` at offset 24 in the closure struct (`HeapClosure` layout: `[header(16) | code_ptr(8) | drop_glue_ptr(8) | captures...]`, `CAPTURES_START = 32`). The drop glue function is a per-lambda generated function that dec's all heap-typed captures; null for closures with no heap captures. This replaced an earlier side-table design (`code_ptr → drop_fn` HashMap) which was rejected during Ring 2 because cross-module closures cannot look up the creating module's side table, and the embedded pointer makes closure dec a self-contained operation. See `design/backend/ring2-rc.md` §1.3 and §9.1, and `design/arch/interfaces.md` §HeapClosure.
