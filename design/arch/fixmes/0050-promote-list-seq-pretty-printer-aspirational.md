---
number: 0050
target: /dev
filed_by: /repl
filed_at: 2026-05-01
sprint_filed: 64
refers_to: repl/spec/01-display-format.md §1.5
status: deferred
deferred_at: 2026-06-13
deferred_reason: design exists (design/arch/display-protocol.md, user rulings 2026-07-10); implementation unscheduled. Re-verified S125 2026-11-27 — no DescriptorKind::Collection (trace_format.rs stops at TypeVar = 7), no TypeDefInfo.render (check.rs), no collection arm in src/display.rs; §1.5 still aspirational. Not a Phase-H release item (release-llvm-backend.md NG2)
deferred_trigger: a sprint scopes the display protocol; its first act is the arch public-API batch for TypeDefInfo.render + DescriptorKind::Collection (display-protocol.md §6, §9), then dev in sequence — types/intrinsics/backend/typecheck passthrough, then src/ (display.rs arm + bootstrap seed)
target_sprint: TBD
migrated_from_inline: true
---

# 0050 — Promote List/Seq aspirational pretty-printer forms to MUST when protocol exists

## Issue

Implement the settled [display design](../display-protocol.md) before promoting
its aspirational List/Seq forms to requirements. The design records the user's
2026-07-10 rulings: compiler-internal recognition and no forcing of lazy tails.
Implementation remains unscheduled.

## Source location

[Value display](../../../repl/spec/01-display-format.md#15-value-display),
including its aspirational paragraph. Generic ADT display remains normative.

## Resolution

`dev` owns implementation in the surfaces allocated by the display design;
`arch` owns cross-crate changes. After the mechanism lands, route requirement
promotion to `spec` under the user approval gate. Retain this filing until the
implementation and specification obligations are discharged.
