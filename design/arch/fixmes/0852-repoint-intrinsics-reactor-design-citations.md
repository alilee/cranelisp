---
number: 0852
target: /dev
filed_by: /sprint
filed_at: 2026-07-22
sprint_filed: 116
refers_to: audits/cranelisp-intrinsics-s115.md §6 R-5; design/intrinsics/reactor.md; crates/cranelisp-intrinsics/
status: open
---

# Repoint stale intrinsics reactor-design citations

## Issue

Accepted audit recommendation R-5. Sixty-one source citations and one Cargo citation still name deleted `design/int/reactor.md`; many are test-side `// spec:` anchors. The document moved to `design/intrinsics/reactor.md` in S97.

## Proposed resolution

Mechanically repoint all 62 citations to the live document and verify no stale path remains.
