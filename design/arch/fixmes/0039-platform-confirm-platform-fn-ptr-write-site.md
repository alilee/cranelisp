---
number: 0039
target: /platform
filed_by: /int
filed_at: 2026-05-01
sprint_filed: 64
refers_to: design/int/platform-registry-removal.md:173
status: open
migrated_from_inline: true
---

# 0039 — Confirm write-site for `platform_fn_ptr` (single-pass vs two-pass)

## Issue

Confirm the write-site for `platform_fn_ptr` — inside `load_and_register_platform` (one loop, atomic) vs in `handle_platform` (two loops, looser). `/int` preference is the former; `/platform` owns the decision.

## Source location

`design/int/platform-registry-removal.md:173` (HTML-comment FIXME).

## Context

Section 4 of `platform-registry-removal.md` covers the registration path. The decision affects whether the type-signature entry and the `platform_fn_ptr` are written in one atomic loop or in two passes.

## Proposed resolution

`/platform` confirms the inline write-site (Option preferred by `/int`) or proposes the two-pass shape with rationale.
