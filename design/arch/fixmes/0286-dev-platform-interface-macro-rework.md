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

---

## /dev (platform) progress — S76 (status: PARTIAL — kept open, transitional residue owed to 0287/0288)

**Landed in `cranelisp-platform` (workspace green; 42/42 crate tests pass; baseline regenerated):**

- **Exported GOT** — the macro emits `pub static __CRANELISP_PLATFORM_GOT:
  [AtomicPtr<u8>; GOT_TABLE_SIZE]` under `#[export_name =
  "__cranelisp_got_platform_<name>"]` (the `PRIMITIVES_GOT_SLAB` precedent), and the
  `cranelisp_platform_manifest` entry self-populates slot *i* with `functions[i]`'s
  pointer at DLL load — **manifest order IS GOT slot order** (unit-tested in
  `tests/macro_expansion.rs::macro_exports_got_in_manifest_order`).
- **`schema:` embed arm** — replaces the declaration arm; takes the generated artifact
  text (e.g. `include_str!`), parses it into the per-DLL `Schema`, installs it via the new
  `set_global_schema` (the `GLOBAL_SCHEMA` OnceLock — replaces the retired `GetSchema`
  per-type trampoline). `schema:` is **optional** (absent tolerated for first builds).
- **`__cranelisp_layout_hash_<name>`** — exported as a `&'static str` data symbol,
  extracted from the artifact's `;; layout-hash:` header at compile time by the new
  `extract_layout_hash` `const fn`.
- **Schema parser repointed at the generated-artifact grammar** — `schema.rs` rewritten to
  parse the backend `generate_schema` S-expr dialect (`(schema (key (Ctor tag (fields))
  …))`), with the typed-FQ `FieldType` (`Scalar`/`Adt`/`Vec`) shape (§5.5.2). The grammar
  is **replicated** (no `cranelisp-backend` dep — frontend-independence per §5.5.1) and
  matches backend's emit. Two-pass-style structure + `ParseLoc` diagnostics kept.
- **`read_field` is name-based** — `adt.rs` reworked: `CLAdt<T>` stays; `read_field`
  resolves byte offset + declared `FieldType` by name from the installed global schema.
- **RETIRED:** the schema declaration dialect, the marker-type DSL (`AnyAdt`, `GetSchema`,
  `into_typed`, `read_tag_any`), `schema_types:`, `Variant`-shaped schema types. `CLAdtType`
  KEPT (now FQ `TYPE_NAME`); `alloc_with_tag` KEPT.
- **ABI_VERSION 2 → 3.**
- **stdio + test-capture** rebuilt against the new macro (they use the no-schema arm,
  unchanged source; dylibs rebuilt). Platform load/dispatch e2e (`spec_platforms`,
  `platform_print_via_test_capture`, `io_trampoline_executes_print_to_stdout`) **pass**.

**TRANSITIONAL RESIDUE — owed to the coordinated 0287/0288 cut (NOT removed here to keep
the workspace green):**

- **`HostCallbacks::validate_schema` + `null_validate_schema`** — retired-in-place
  (never invoked; superseded by the layout-hash gate) but the field/fn are KEPT because
  `src/platform.rs` + `crates/cranelisp-exe-bundle/src/lib.rs` construct `HostCallbacks`
  with them, and platform is the dependency (int the consumer) — removing them now breaks
  int, which `/dev (platform)` cannot edit. **0288 removes the int consumers + these two
  symbols in the same change-set.**
- **`PlatformFn.jit_name` + `OwnedPlatformFnDescriptor.jit_name` + `derive_jit_name`** —
  retained because `src/platform.rs` reads `desc.jit_name` and registers fn pointers via
  `JITBuilder::symbol`; the macro still derives jit_name for that consumer. **0288 removes
  them with the GOT-indirect load path.**
- **stdio/test-capture `#[export_name = "cranelisp_print"]` etc.** — KEPT because backend
  dispatch (`compiler/apply.rs`) still uses `compile_extern_call` → `Linkage::Import`
  against the mangled name, and `--link` force-loads the rlib to resolve it. **0287's
  GOT-indirect dispatch retires the direct-extern path; the export_name attributes
  retire with it.**

Reason for keeping the FIXME OPEN: the three C-ABI/export retirements above are blocked on
0287 (backend dispatch) + 0288 (int load path) removing the consumers. They are a single
coordinated cut across three deployments; doing them in platform alone breaks the build.
Close 0286 when 0287+0288 land and the residue is removed.

**Filed by /dev (platform):** one cross-skill note for `/design platform` — `host-wiring-s76.md`
(the schema-seam map) is now superseded by the landed embed arm + layout-hash; it needs a
`/design platform` refresh per this FIXME's Acceptance bullet 4 (not actioned here — not
`/dev`'s doc to edit).
