---
number: 0233
target: /int
filed_by: /dev (platform)
filed_at: 2026-05-28
sprint_filed: 71
refers_to: design/platform/sprint71-redesign.md §12 (Next skills), src/platform.rs, FIXME 0229, FIXME 0230, FIXME 0231, FIXME 0232
status: open
---

# Replace `parse_type_sig` with frontend+typecheck path; register platforms as normal modules

## Issue

Two coupled int-side changes for the host-wiring sprint:

1. **`parse_type_sig` removal**: The current `src/platform.rs`
   parser for `PlatformFn.type_sig` is ad-hoc; it duplicates a subset
   of cranelisp's frontend + typecheck logic. Replacing it with a
   call into `cranelisp_frontend::parse_type_expr` (FIXME 0230) +
   `cranelisp_typecheck::check_type_expr` (FIXME 0231) unifies the
   type-parsing surface and lets the platform sigs reference
   schema-declared ADTs through the same typechecker view that user
   code sees.

2. **Platform-as-module**: Register each loaded platform DLL as a
   normal cranelisp module in the symbol-table — the `Platform` module
   exposes its declared types (from the schema) and fns (from the
   manifest) the same way a `core.option`-style module would. This
   unifies the discovery, caching, and resolution paths for platform
   functions; the platform-specific `manifest_to_descriptors` path
   collapses into the normal module-loading flow.

## Proposed resolution

**Step 1 — `parse_type_expr` + `check_type_expr` consumption**:
Inside `load_platform_dll` (or its successor in the post-migration
shape), for each `PlatformFn.type_sig`:

```rust
let expr = cranelisp_frontend::parse_type_expr(&fn.type_sig, source_id)?;
let typ = cranelisp_typecheck::check_type_expr(&expr, &ctx, symbol_tables)?;
// register `(platform_name, fn.cl_name)` with `typ` in the symbol-table
```

Delete the int-side `parse_type_sig` implementation entirely; the
function ceases to exist post-migration.

**Step 2 — module registration shape**: The platform DLL load
populates a `ModuleEntry::Platform` (new variant, or repurpose an
existing one to carry the DLL-specific extras like `library: Library`
+ `platform_fn_ptr` per-fn). Cache uses `.meta.json` with the new
`schema_literal` field (FIXME 0232).

**Step 3 — schema validation**: Once `HostCallbacks::validate_schema`
is wired (FIXME 0229), the platform-load flow calls it with the
captured schema literal; mismatches surface as DLL-load errors with
the form's span.

## Operational implication / Context

This is the largest of the post-S71 follow-up FIXMEs — it touches
src/platform.rs, the symbol-table module-discovery path, and the
backend cache loader. Scope-sized for a single sprint focused on the
platform-as-module migration; the surface area of the change is
contained because the pre-S71 `parse_type_sig` + `manifest_to_descriptors`
path is a single integration point (not scattered).

FIXMEs 0229 / 0230 / 0231 / 0232 are pre-requisites — they expose the
APIs this FIXME consumes. Coordinated landing.

The FIXME's resolution also retires `manifest_to_descriptors` as an
int-facing public API (cranelisp-platform's `pub` re-export stays for
the DLL-author audience but the host stops calling it — module loader
takes over).
