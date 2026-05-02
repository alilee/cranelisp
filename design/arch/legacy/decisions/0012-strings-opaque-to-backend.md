---
number: 0012
title: Strings opaque to backend
status: operative
---

# 0012 — Strings opaque to backend

`HeapString` layout is owned by `cranelisp-runtime`. Backend never reads/writes string bytes — all string operations go through extern functions. Enables future rope upgrade as a runtime-only change.
