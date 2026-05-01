---
number: 0038
target: /platform
filed_by: /int
filed_at: 2026-05-01
sprint_filed: 64
refers_to: design/int/platform-registry-removal.md:136
status: open
migrated_from_inline: true
---

# 0038 — Confirm `scheduling_class` placement (Option B: inside `PrimitiveKind::PlatformEffect`)

## Issue

Confirm Option B (`scheduling_class` inside `PrimitiveKind::PlatformEffect` variant) aligns with the DLL manifest flow and bind-chain analysis. `/platform` owns `crates/cranelisp-platform/` and may have visibility into a `scheduling_class` evolution (`ResourceSerial` token shape, future variants) that affects the choice between A and B. If Option A is preferred, edit this section in place or respond with rationale.

## Source location

`design/int/platform-registry-removal.md:136` (HTML-comment FIXME below §3.3 "/arch Decision 26 alignment").

## Context

`/arch` Decision 26 prefers Option B (tighter scope), with the call deferred to `/int`. The design records Option B as `/int`'s position. `/platform` concurrence is expected via the FIXME stub. If Option A is preferred, the shape moves to one extra `Option` field.

## Proposed resolution

`/platform` reviews the design doc §3.3 and either confirms Option B or proposes Option A with rationale. Edit in place or reply on the design doc.
