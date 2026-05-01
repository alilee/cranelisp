---
number: 0035
target: /repl
filed_by: /int
filed_at: 2026-05-01
sprint_filed: 64
refers_to: design/int/persistent-workers.md:375
status: open
migrated_from_inline: true
---

# 0035 — Measure REPL eval latency with 4 priority workers mid-compile

## Issue

Measure REPL eval latency with 4 priority workers mid-compile. If >100ms for trivial `(+ 1 2)`, add a REPL-priority work level.

## Source location

`design/int/persistent-workers.md:375` (HTML-comment FIXME below §"Mitigation" of the responsiveness analysis).

## Context

The current scoped-worker path has the same latency as persistent-workers; the priority ladder prioritises `TypecheckFirst` + `BlockingJitCodegen` over `JitCodegen`, so any prelude compilation that is blocking the REPL is already prioritised. For interactive responsiveness, the REPL eval path could enqueue its `__expr` as a high-priority form — either by re-using `BlockingJitCodegen` (with the REPL module as the "blocked" waiter) or by adding a new priority level for REPL submissions. Not needed for Wave 4; file as future optimisation if users report REPL lag.

## Proposed resolution

`/repl` runs a measurement: trivial `(+ 1 2)` REPL eval latency under 4 priority workers compiling something else. If >100ms, file a follow-on FIXME(/int) requesting a REPL-priority work level.
