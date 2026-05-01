---
number: 0020
title: Split calling convention for RC
status: superseded-by-0024
---

# 0020 — Split calling convention for RC

**RETRACTED (Sprint 56 Step 2c, superseded by Decision 24).** **Split calling convention for RC** — User functions use consuming convention (callee owns heap params, dec's them at scope exit; caller inc's variable args before the call). Builtins/externs use borrowing convention (caller dec's temporaries after the call; callee has no RC responsibility). Data constructors use plain arg lists (field values stored directly into the ADT; ADT drop glue handles recursive field dec at destruction time). The convention is determined statically at each call site based on the callee's `ResolvedCall` classification. The typecheck crate is entirely unaware of calling conventions — this is a backend-only concern. See `design/backend/ring2-rc.md` §3 for the full decision table.
