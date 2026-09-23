---
number: 0050
target: /dev
filed_by: /repl
filed_at: 2026-05-01
sprint_filed: 64
refers_to: repl/spec/01-display-format.md §1.5
status: deferred
deferred_at: 2026-06-13
deferred_reason: design exists (design/arch/display-protocol.md, user rulings 2026-07-10); implementation unscheduled
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
