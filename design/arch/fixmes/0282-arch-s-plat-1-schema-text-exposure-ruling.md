---
number: 0282
target: /arch
filed_by: /dev (int)
filed_at: 2026-06-07
sprint_filed: 76
refers_to: design/platform/host-wiring-s76.md §3 (S-PLAT-1) + §6 (open /arch seams), design/arch/fixmes/0229 step 2, design/arch/fixmes/0233 step 3, design/arch/fixmes/0232, crates/cranelisp-platform/src/lib.rs (declare_platform! macro + PlatformManifest + HostCallbacks::validate_schema)
status: open
---

# S-PLAT-1 ruling — how the host obtains a DLL's schema text (validate_schema + cache)

## Issue

`design/platform/host-wiring-s76.md` §3 (S-PLAT-1) and §6 flagged that FIXME
0229-step-2 (`validate_schema` host impl) and FIXME 0232 (backend `.meta.json`
`schema_literal` for cache-restore) both require **the host to obtain the DLL's
raw schema text**, and that this "is the seam that needs an /arch ruling because
it touches the `#[repr(C)]` ABI boundary … AND … the host-side ADT-marshaling
data contract shared with int 0229." §6 stated: *"A `FIXME target: /arch` will
be filed for the ruling."* **That FIXME was never filed.**

While wiring 0229 step 1 (`alloc_with_tag`, now DONE + unit-verified — see 0229's
progress note), int confirmed the channel does not exist in source:

- The landed `declare_platform!` macro
  (`crates/cranelisp-platform/src/lib.rs:1450`+ / `__declare_platform_body!`
  `:1554`+) parses the `schema:` literal into a **DLL-local** `DLL_SCHEMA:
  LazyLock<Schema>` static and **does not invoke `validate_schema` at init**.
- `PlatformManifest` (`#[repr(C)]`) has **no `schema_*` field** — the literal
  does not ride the manifest the way `type_sig` strings do.

Therefore the host receives the schema bytes through **no channel at all**. An
int-side `validate_schema` impl (re-parse via `cranelisp_platform::Schema::parse`,
cross-check declared type-names against the typecheck symbol-table, write a
diagnostic, return non-zero on mismatch) is well-specified but cannot be authored
meaningfully — there is nothing to hand it. 0229-step-2 and 0233-step-3 are
blocked on this, not on the intrinsic (which landed) and not on the 0235 test
fixture (which is downstream e2e verification).

## Proposed resolution

/arch rules between the two options the design doc already enumerated (§3):

- **Option A** — add `schema_ptr: *const u8` + `schema_len: usize` to
  `PlatformManifest`. The macro writes the `&'static str` literal into the two
  new fields; `manifest_to_descriptors` surfaces it as an owned `String`. Cost: a
  `#[repr(C)]` layout change → `ABI_VERSION` 2→3 bump (a second bump in the arc
  immediately following S71's 1→2).
- **Option B** (/design's recommendation) — have `declare_platform!` invoke the
  already-present `HostCallbacks::validate_schema` callback at DLL init with the
  embedded literal (`validate_schema(SCHEMA.as_ptr(), SCHEMA.len(), …)`). The
  callback signature was designed for exactly this in S71. No ABI bump (the field
  already exists). The host stashes the bytes it is handed for the cache (0232).

Either way the resolution lands a **platform-crate macro change** (Option B: emit
the init-time call; Option A: write the manifest fields), which is `/dev
(platform)`'s to author once /arch rules. int then authors the `validate_schema`
host body against whichever channel /arch picks.

## Operational implication / Context

This is the single hard blocker for the schema-validation half of the
host-wiring set. `alloc_with_tag` (the construction half) is fully wired +
unit-verified this sprint; the read path was always callback-free. Resolving
S-PLAT-1 unblocks 0229-step-2 (validate), 0233-step-3 (validate), and 0232
(cache-restore round-trip) together. Until then, schema typos surface at
field-access call sites via `SchemaLookupError` (the documented interim
behaviour), not at DLL load — which is sound but loses the load-time
observability win §8 of the host-wiring doc describes.
