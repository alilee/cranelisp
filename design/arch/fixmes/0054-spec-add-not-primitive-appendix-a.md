---
number: 0054
target: /spec
filed_by: /review
filed_at: 2026-05-01
sprint_filed: 64
refers_to: design/review/ring0-report.md:118 (M-6), spec/appendix-a-builtins.md
status: open
migrated_from_inline: true
---

# 0054 — Add `not :: (Fn [Bool] Bool)` to `spec/appendix-a-builtins.md`

## Issue

The implementation provides 19 inline primitives including `not :: (Fn [Bool] Bool)`. The spec's Appendix A lists only 18 inline primitives (4 int arith + 5 int cmp + 4 float arith + 5 float cmp). `not` is exercised by tests and examples but has no spec authority.

`not` is a natural and essential boolean primitive, so this is almost certainly a spec omission.

## Source location

`design/review/ring0-report.md:118` (Ring 0 M-6 finding).

## Context

Per `spec/CLAUDE.md` "Third session" note, this was already addressed once: "Added `not :: (Fn [Bool] Bool)` inline primitive under new 'Boolean' subsection. Implementation has 19 inline primitives; spec now matches." If the spec already lists `not`, this entry can be closed without action; if not, the addition is straightforward.

## Proposed resolution

`/spec` confirms `not` is listed in `spec/appendix-a-builtins.md §A` and closes this entry; or adds the missing primitive entry and closes.
