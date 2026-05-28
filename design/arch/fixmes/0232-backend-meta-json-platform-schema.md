---
number: 0232
target: /backend
filed_by: /dev (platform)
filed_at: 2026-05-28
sprint_filed: 71
refers_to: design/platform/sprint71-redesign.md §12 (Next skills), crates/cranelisp-backend/ (cache), FIXME 0233
status: open
---

# `.meta.json` schema for platform module symbol-table caching

## Issue

The platform-as-module migration (FIXME 0233) registers platform DLLs
as cranelisp modules in the symbol-table. The backend's cache
infrastructure (`.meta.json` per module) currently has no schema
provision for capturing the DLL's `Schema` (the ADT-marshaling layout
declarations) — only platform fn signatures.

When a platform module is cache-hit on a subsequent session, the host
must re-parse the schema literal to populate the `LazyLock<Schema>`
static inside the loaded DLL — but currently the cache has no
canonical place to store the schema text for cross-session continuity.

## Proposed resolution

Extend the `.meta.json` schema for platform modules to include:

```json
{
  "module_kind": "Platform",
  "platform_name": "stdio",
  "abi_version": 2,
  "schema_literal": "((Rectangle ((CLInt w) (CLInt h))))",  // new field
  "functions": [
    {
      "cl_name": "...",
      "type_sig": "...",
      ...
    }
  ]
}
```

The `schema_literal` field is the raw text exactly as the DLL's
`declare_platform!` macro embedded it. On cache hit:
- Backend reads `.meta.json`.
- Schema literal flows back to the host-side platform loader.
- Host re-parses (cheap; sub-millisecond) and re-validates against
  current typecheck symbol-table (via FIXME 0231).

The schema_literal field is optional — pre-S71 DLLs (stdio,
test-capture) and any DLL that omits `schema:` from its
`declare_platform!` invocation cache with `schema_literal: ""`.

## Operational implication / Context

This pairs with FIXME 0233 (platform-as-module + parse_type_sig
removal) — the platform module's cache contract is part of the
broader platform-as-module migration.

ABI_VERSION discipline (per design §6) bumps when a layout-affecting
change lands; .meta.json schema changes are NOT ABI-version-bumping
(they're cache-layer, not DLL-boundary) but are tracked separately
under the backend's own versioning if any. Cache miss + re-warm is
the fallback when an older cache shape is encountered.
