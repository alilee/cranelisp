---
number: 0286
target: /dev (platform)
filed_by: /arch
filed_at: 2026-06-07
sprint_filed: 76
refers_to: design/arch/platform-interface.md §5.1 §5.2 §5.4 §5.5 §6.1 §6.6, design/arch/bounded-contexts.md §5
status: open
---

# Platform-interface — `declare_platform!` macro rework + GOT/manifest/schema exports

## Issue

The platform-interface design (`design/arch/platform-interface.md`, user-ratified
2026-06-07; **normative — read in full**) re-shapes what a platform DLL exports. The
landed S71 macro emits a manifest + a DLL-local schema-DSL static + named externs with
`jit_name`s. The target is: export a **GOT** + a **manifest (FQ sigs)** + an **embedded
generated schema** + a **layout-hash symbol**; platforms stop declaring ADTs.

## Scope

Per `platform-interface.md` §6.1 + §6.6 (the retirement table is the authoritative
checklist):

- **Emit the exported GOT** `__cranelisp_got_platform_<name>` — a const array of fn
  pointers (the `cranelisp-primitives::PRIMITIVES_GOT_SLAB` precedent), entries
  linker-fixed-up via relocations; manifest order IS GOT slot order (§5.1).
- **Drop the `schema:` *declaration* arm**; **add the `schema:` *embed* arm** taking
  `include_str!("<name>.platform-schema")` (the `/platform-schema`-generated artifact) and
  **export `__cranelisp_layout_hash_<name>`** parsed from the artifact's `;; layout-hash:`
  header at build time (§5.5.4, §6.1).
- **RETIRE** the schema declaration DSL: the `LazyLock<Schema>`-as-DSL static, the
  marker-type pattern (`CLAdtType`, `AnyAdt`, `GetSchema`), the hand-authored schema
  *dialect* in `Schema::parse`, and `CLAdtType`/`GetSchema` declaration-lookup half of
  `CLAdt`. **KEEP** the schema *parser* structure (two-pass, ParseLoc, name/field lookups),
  repointed at the generated artifact; `CLAdt<T>` stays, `read_field` → name-based via the
  artifact's name→index map (typed fields drive nested-ADT navigation).
- **RETIRE `validate_schema`** from `HostCallbacks` + `null_validate_schema`; **bump
  `ABI_VERSION` 2→3** (bump freely, pre-1.0; no reserved slot).
- **RETIRE `PlatformFn.jit_name` + `derive_jit_name`** (dispatch is slot-indexed GOT, not
  mangled-name extern) — platform fns need no exported names; confirm no other consumer.
- **KEEP `alloc_with_tag`** (ADT *construction* across the FFI still needs the host
  allocator; orthogonal to the schema retirement).

## Acceptance

- A platform DLL built with the reworked macro exports `__cranelisp_got_platform_<name>`,
  the shrunk manifest (FQ sigs, no `jit_name`), the embedded `<name>.platform-schema` text,
  and `__cranelisp_layout_hash_<name>`.
- `cargo public-api` baseline for `cranelisp-platform` regenerated; `ABI_VERSION` is 3.
- The marker-type DSL / `validate_schema` / `jit_name` surfaces are gone; `Schema::parse`
  reads the generated artifact.
- `design/platform/host-wiring-s76.md` (the `/platform`-owned seam map this supersedes for
  the schema seam) **needs superseding by its owner** — file/coordinate a `/design platform`
  refresh; it is NOT `/arch`'s to edit.

## Context

This is the platform half of the platform-interface cascade. Pairs with 0287 (backend
generator + GOT-indirect dispatch), 0288 (int load path + `/platform-schema`), 0289 (qa
e2e). Supersedes the platform half of the re-pointed 0229/0232/0233/0235.
