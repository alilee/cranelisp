---
number: 0040
target: /platform
filed_by: /int
filed_at: 2026-05-01
sprint_filed: 64
refers_to: design/int/platform-registry-removal.md:279
status: deferred
deferred_to: sprint after 0229 lands (host-side ADT marshaling)
deferred_at: 2026-05-28
deferred_by: /dev (platform)
deferred_in_sprint: 71
deferral_rationale: |
  load_and_register_platform is host-side wiring. Sprint 71 W2 stages the
  host-side hooks (HostCallbacks growth with null-callback gates per
  FIXME 0229 + FIXME 0233 — platform-as-module + parse_type_sig removal).
  The two bullets here naturally land alongside that host-wiring sprint's
  work; resolving now would predict a shape that may shift under the
  parse_type_sig removal.
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
