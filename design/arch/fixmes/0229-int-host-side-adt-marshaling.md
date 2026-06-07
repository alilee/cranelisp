---
number: 0229
target: /int
filed_by: /dev (platform)
filed_at: 2026-05-28
sprint_filed: 71
refers_to: design/platform/sprint71-redesign.md §9, design/arch/bounded-contexts.md §5, crates/cranelisp-platform/src/lib.rs (HostCallbacks)
status: open
---

## Re-pointed (2026-06-07, /arch) — platform-interface.md is now the normative design

The S-PLAT-1 ruling this FIXME was blocked on is **resolved**: `design/arch/platform-interface.md` (user-ratified 2026-06-07) supersedes the schema-text-exposure question entirely. **`validate_schema` RETIRES** — the layout-hash gate (regenerate-and-compare from live tables) replaces it; no schema text crosses the boundary. FIXME 0282 (the S-PLAT-1 ruling carrier) is **deleted**. **What this FIXME still owes** under the new design: only the `alloc_with_tag` KEEP (DONE + unit-verified — ADT *construction* still needs the host allocator) and coordinating the retirement of `validate_schema` / `null_validate_schema` from `HostCallbacks` (a `/dev platform` change, ABI 2→3). The cross-skill implementation work is carried by the new platform-interface FIXMEs (int load path; platform macro rework). This FIXME's step 2 (`validate_schema` host impl) is **withdrawn — there is nothing to validate**. Kept open only to track the `alloc_with_tag` KEEP + the null-callback cleanup coordination; may close once the platform-interface int/platform FIXMEs absorb it.

---

## Progress (S76 W3 second fire, /dev int) — step 1 DONE; steps 2+4 carry on S-PLAT-1 (SUPERSEDED — see re-point above)

The intrinsics producer landed (`cranelisp_intrinsics::alloc::cranelisp_alloc_with_tag`,
`crates/cranelisp-intrinsics/src/alloc.rs:252`, `pub extern "C" fn(u32,u32,*const i64)->i64`).
int wired it.

- **Step 1 (alloc_with_tag wiring) — DONE + unit-verified.** Both `HostCallbacks`
  construction sites now point at the real intrinsic:
  - `src/platform.rs` (`load_platform_dll`, JIT path): `alloc_with_tag:
    cranelisp_intrinsics::alloc::cranelisp_alloc_with_tag`.
  - `crates/cranelisp-exe-bundle/src/lib.rs` (`cranelisp_init_platform`, `--link`
    path): same.
  The **R1 gate is removed** — `CLAdt::<T>::construct(...)` no longer routes to
  the `null_alloc_with_tag` panic at either site. Verified by two int-side unit
  tests in `src/platform.rs::tests`
  (`alloc_with_tag_callback_round_trips_two_field_adt`,
  `alloc_with_tag_callback_round_trips_zero_field_adt`): build the `HostCallbacks`
  exactly as `load_platform_dll` does, invoke the `alloc_with_tag` field as a DLL
  would (via `CLAdt::construct`), and assert the heap layout `CLAdt::read_tag`/
  `read_field` expect — `[total_size | rc=1 | tag@HEAP_HEADER_SIZE | f0@+8 | ...]`,
  alloc-base returned. (The intrinsic's own layout is also unit-tested in
  `alloc.rs::test_alloc_with_tag_{zero,two}_fields`; CLAdt read path in adt.rs
  T9–T13.)
- **Step 2 (validate_schema host impl) — BLOCKED on S-PLAT-1, NOT on int.** The
  blocker is not the intrinsic and not the test fixture — it is that **the host
  has no channel to obtain the DLL's schema text**. The landed `declare_platform!`
  macro (`crates/cranelisp-platform/src/lib.rs:1450`+) parses the schema into a
  DLL-local `DLL_SCHEMA: LazyLock<Schema>` static and **neither invokes
  `validate_schema` at init nor exposes the literal on `PlatformManifest`** (no
  `schema_*` field). Without the bytes reaching the host, an int-side
  `validate_schema` impl (re-parse via `Schema::parse` + cross-check type-names
  against the typecheck symbol-table) has nothing to validate and cannot be
  written meaningfully. This is exactly the **S-PLAT-1 seam** flagged in
  `design/platform/host-wiring-s76.md` §3/§6 — it needs (a) an **/arch ruling**
  (Option A: add `schema_ptr/_len` to `PlatformManifest` → `ABI_VERSION` 2→3 bump;
  Option B: have `declare_platform!` invoke `validate_schema` at init with the
  embedded literal — /design recommends B, no ABI bump) and (b) a **platform-crate
  macro change** to actually pass/expose the bytes. Both are outside int's court.
  The §6 note said "A FIXME target: /arch will be filed for the ruling" — **that
  ruling FIXME has not been filed.** Until S-PLAT-1 resolves, `validate_schema`
  stays at `null_validate_schema` at both sites (schema typos surface at
  field-access via `SchemaLookupError`, the documented interim behaviour). The
  0235 test fixture (`platforms/test-adt/`, `/qa`) is also needed to e2e-verify,
  but the S-PLAT-1 channel is the hard prerequisite.
- **Step 3 (replace null pointers) — alloc_with_tag DONE; validate_schema carried**
  (gated by step 2).
- **Step 4 (delete null callbacks) — NOT int's; carried.** Per design §4 this is a
  `/dev (platform)` follow-on, AND both placeholders are **still in use**:
  `null_validate_schema` is the live `validate_schema` value at both sites (step 2
  blocked), and `null_alloc_with_tag` remains the `GLOBAL_ALLOC_WITH_TAG` fallback
  in `cranelisp_platform::get_host_alloc_with_tag`. Nothing to delete until
  validate_schema is wired.

**Net for this FIXME: step 1 fully resolved + unit-verified; steps 2/4 carry,
blocked on the S-PLAT-1 schema-text-exposure seam (an /arch ruling + a
platform-crate macro change — neither int's to author). Kept open.** Companion
0233 step 3 carries the same S-PLAT-1 block.

# Wire host-side ADT marshaling callbacks

## Issue

Sprint 71 Wave 2 introduced `HostCallbacks::alloc_with_tag` and
`HostCallbacks::validate_schema` as named-null callback fields (per
A6 ruling / design §5.2). The fields are currently populated with
`cranelisp_platform::null_alloc_with_tag` (panics with R1 gate
message naming this FIXME) and `cranelisp_platform::null_validate_schema`
(no-op, returns 0).

The host (`src/platform.rs:182` + `crates/cranelisp-exe-bundle/src/lib.rs:97`)
currently passes the null callbacks. CLAdt construction
(`CLAdt::<T>::construct(...)`) therefore panics at runtime under the
R1 gate. Schema validation against the host's actual deftype data is
deferred until this FIXME is resolved.

## Proposed resolution

In the host-wiring sprint:

1. **`alloc_with_tag`**: implement `cranelisp_intrinsics::cranelisp_alloc_with_tag`
   following the contract in `crates/cranelisp-platform/src/lib.rs` on
   `HostCallbacks::alloc_with_tag` rustdoc. Specifically:
   - Allocate `total_size = 16 (header) + 8 (tag+pad) + 8*field_count` bytes
     via the runtime allocator.
   - Write `[total_size: i64][rc: i64=1]` header.
   - Write `[tag: u32][pad: u32]` at payload+0.
   - Copy `field_count` i64s from `fields_ptr` at payload+8 onwards.
   - Return the alloc base pointer (matching CLString's convention).

2. **`validate_schema`**: implement a host-side validator that:
   - Re-parses the schema (via `cranelisp_platform::Schema::parse`).
   - Cross-references each declared type-name against the active
     typecheck symbol-table for matching `ModuleEntry::Type` shapes
     (variant arity, field types).
   - On mismatch, writes a diagnostic message into the provided
     `err_msg` buffer and returns non-zero.

3. **Replace the null-callback pointers in both HostCallbacks
   construction sites** with the wired implementations:
   - `src/platform.rs:182` — `load_platform_dll`
   - `crates/cranelisp-exe-bundle/src/lib.rs:97` — `cranelisp_init_platform`

4. **Delete `cranelisp_platform::null_alloc_with_tag` and
   `cranelisp_platform::null_validate_schema`** once the host wires
   real callbacks — the R1 gate is structural, not runtime, and the
   named-null functions are the gate itself.

## Operational implication / Context

Per design §9 the R1 gate's removal is "two lines in one file" (the
HostCallbacks initializer at the host's load site). The wired callbacks
unlock the full ADT-marshaling surface end-to-end, allowing platform
DLLs to construct and pass typed heap-ADT values across the FFI boundary
without runtime panic.

This FIXME also pairs with FIXMEs 0230–0233 (parse_type_sig removal +
platform-as-module migration) — coordinated landing in the host-wiring
sprint allows the platform-DLL surface to consume the cranelisp
typecheck symbol-table for schema validation.
