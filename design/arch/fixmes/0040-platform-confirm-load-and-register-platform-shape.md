---
number: 0040
target: /platform
filed_by: /int
filed_at: 2026-05-01
sprint_filed: 64
refers_to: design/int/platform-registry-removal.md:279
status: open
migrated_from_inline: true
---

# 0040 — Confirm `load_and_register_platform` can take symbol_tables handle and write platform_fn_ptr inline

## Issue

Confirm the two bullets in §7 of `platform-registry-removal.md`:

1. `load_and_register_platform` can take a `symbol_tables` handle and write `platform_fn_ptr` inline.
2. No DLL code or ABI surface references `PlatformRegistry`.

If (2) is false, file the call-site path and `/int`+`/platform` will coordinate.

## Source location

`design/int/platform-registry-removal.md:279` (HTML-comment FIXME below §7).

## Context

The Sprint 58 G8 deletion of `PlatformRegistry` requires that no DLL boundary surface references it and that `load_and_register_platform` can be refactored to write `platform_fn_ptr` directly into the `SymbolTable`.

## Proposed resolution

`/platform` confirms both bullets; if (2) is false, files an inline call-site path response in the design doc.
