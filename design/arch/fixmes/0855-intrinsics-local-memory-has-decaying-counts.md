---
number: 0855
target: /dev
filed_by: /sprint
filed_at: 2026-07-22
sprint_filed: 116
refers_to: audits/cranelisp-intrinsics-s115.md §6 R-7; crates/cranelisp-intrinsics/CLAUDE.md
status: open
---

# Intrinsics local memory carries decaying test counts

## Issue

Accepted audit recommendation R-7, `/dev` portion. The seam map's structural statement remains useful, but its RC test count has already drifted from 26 to 28.

## Proposed resolution

Remove the per-module numeric counts and preserve the durable ownership/shape statement describing which modules externalize versus inline their tests.
