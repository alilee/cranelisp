---
number: 0233
target: /int
filed_by: /dev (platform)
filed_at: 2026-05-28
sprint_filed: 71
refers_to: design/platform/sprint71-redesign.md §12 (Next skills), src/platform.rs, FIXME 0229, FIXME 0230, FIXME 0231, FIXME 0232
status: open
---

## Progress (S76 W3, /dev int)

**Step 1 — `parse_type_sig` removal: DONE + verified.** `src/platform.rs`'s
ad-hoc `parse_platform_type_sig` + `sexp_to_type` + `parse_fn_type` +
`parse_io_type` family (and the bespoke `intrinsic_type_from_name`-based leaf
resolution) is deleted. `register_platform_in_tc` now calls
`parse_and_check_platform_type_sig`, which routes each `PlatformFn.type_sig`
through `cranelisp_frontend::parse_type_expr` (FIXME 0230, landed) +
`cranelisp_typecheck::check_type_expr` (FIXME 0231, landed). Leaf names resolve
through the normal symbol-table view: `register_platform_in_tc` injects
`(import [primitives [*]])` into the synthetic `platform.<name>` module
(`inject_primitives_import_for_platform`) so `Int`/`String`/`IO`/etc. are
reachable, exactly like a user module (spec §8.8.1). `module_aliases` is now
threaded through `load_and_register_platform` → `register_platform_in_tc`.
Verified: `src/platform.rs::tests::test_register_platform_in_tc` (constructs a
primitives-seeded table, loads stdio, asserts `print: (Fn [String] (IO …))`
resolves) PASSES; `tests/spec_platforms.rs::{platform_form_with_stdio_compiles_in_run_mode,
io_trampoline_executes_print_to_stdout}` stay green. The two ad-hoc-parser unit
tests (`test_parse_fn_type_sig`, `test_parse_zero_param_type_sig`) were deleted
(they tested deleted code; coverage now lives in frontend/typecheck unit tests +
the stdio e2e path).

**Step 2 — platform-as-module: already in place.** `register_platform_in_tc`
already registers each fn as a `ModuleEntry::Def { kind: PlatformEffect }` in a
synthetic `platform.<name>` module with a per-fn GOT slot (worker
`handle_platform` allocates the slot + stores the descriptor ptr; the DLL is
retained on `SharedState.kept_dlls`). No change needed this sprint.

**Step 3 — schema validation: BLOCKED on S-PLAT-1 (NOT on 0229 anymore).**
Update (S76 W3 second fire): 0229's `alloc_with_tag` wiring is now DONE (the
intrinsic landed and int wired it at both sites, R1 gate removed — see 0229's
progress note). But `validate_schema` is **not** unblocked by that: the real
blocker is the **S-PLAT-1 schema-text-exposure seam**
(`design/platform/host-wiring-s76.md` §3/§6). The landed `declare_platform!`
macro parses the schema into a DLL-local `LazyLock<Schema>` static and neither
invokes `validate_schema` at init nor exposes the literal on `PlatformManifest`
— so the host never receives the schema bytes. An int-side `validate_schema`
impl (re-parse via `Schema::parse`, cross-check declared type-names against the
typecheck symbol-table) has nothing to validate until that channel exists.
S-PLAT-1 needs an **/arch ruling** (Option A ABI-bump manifest field vs Option B
macro invokes the callback; /design recommends B) **+ a platform-crate macro
change** — both outside int's court; the §6-promised `target: /arch` ruling
FIXME has not been filed. No schema-bearing DLL fixture exists yet
(`platforms/test-adt/`, FIXME 0235, `/qa`) for e2e verification regardless.
Carry to the sprint that resolves S-PLAT-1.

**Remaining for full closure:** step 3 only, blocked on S-PLAT-1 (schema-text
exposure: /arch ruling + platform-crate macro change). The
`manifest_to_descriptors` retirement-as-int-facing-API note is moot — int
already consumes it only inside `load_platform_dll`; no separate retirement
action needed.

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
