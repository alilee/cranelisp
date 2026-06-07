---
number: 0288
target: /dev (int)
filed_by: /arch
filed_at: 2026-06-07
sprint_filed: 76
refers_to: design/arch/platform-interface.md §5.3 §5.5.1 §6.4 §6.5 §7.2 §7.2a, design/arch/bounded-contexts.md §6, design/arch/facades/int.md §"Platform interface — the load path + /platform-schema (TARGET)", decisions/0042-platform-error-adopts-error-location.md
status: open
---

# Platform-interface — load-path rewrite + `/platform-schema` command + PlatformError hash-refusal variant

## Issue

The platform-interface design (`design/arch/platform-interface.md`, user-ratified
2026-06-07; **normative — read in full**) reworks int's platform-load path and adds a REPL
command. The target shape is set in place in `facades/int.md` §"Platform interface — the
load path + `/platform-schema` (TARGET)" and BC §6.

## Scope

1. **Load-path rewrite** (`load_platform_dll` + `register_platform_in_tc`,
   `src/platform.rs:148/247`; §6.4, §7.2):
   - dlopen → read manifest → **resolve + compile the associated `.cl` type module(s)**
     through ordinary module resolution (`resolve_module_file` — project tree +
     `CRANELISP_LIB`, NOT `CRANELISP_PLATFORM_PATH`) **before** the sigs are parsed; they
     are ordinary modules, FQ-auto-loaded per FIXME 0268.
   - **dlsym the GOT** (`__cranelisp_got_platform_<name>`) and build
     `GotTable::with_static_backing` **WRAPPING it in place — no copy** (the dlopen handle
     keeps it alive).
   - **Build the SymbolTable from the manifest**: `got_slot = manifest array index`, scheme
     from the **FQ sig** (`parse_type_expr` → `check_type_expr` resolving `primitives/Int`,
     `shapes/Rectangle` directly), `DefKind::PlatformEffect { scheduling_class }`,
     docstring/param-names; retain the DLL handle on `SymbolTable.dll`.
   - **DELETE `inject_primitives_import_for_platform`** (`src/platform.rs:325`) — zero
     injected imports under FQ sigs; correct the `parse_and_check_platform_type_sig` rustdoc.
   - **DELETE the `(jit_name, ptr)` / `JITBuilder::symbol` platform-registration path** —
     fn pointers live in the GOT, dispatched GOT-indirect (backend 0287).
2. **`/platform-schema <name>` command** (§5.5.1, §6.0): a REPL slash command
   (`SlashCommand::PlatformSchema(ModuleName)` — already in `facades/int.md`), dispatched
   in `src/` REPL command handling alongside `/imports`/`/exports`; a thin caller of the
   backend schema generator (0287) that prints the emitted artifact text.
3. **Layout-hash check at load** (§5.5.4, §6.4): regenerate via the backend generator and
   compare to `dlsym("__cranelisp_layout_hash_<name>")` — **REPL warns-and-loads**
   (regeneration bootstrap), **`--run` hard-refuses** (abort). Drive the `--link`
   startup-object hash-bake step (exe-bundle; backend 0287 owns the bake).
4. **PlatformError hash-refusal variant (Decision 0042):** the `--run` / `--link` refusals
   surface as a **new `PlatformError` variant** with `ErrorLocation` carriers (the enum is
   `cranelisp-types`-hosted; authoring the variant in `cranelisp-types` is `/arch`'s — file
   FIXME `target: /arch` or coordinate at the wave gate; int consumes it).

## Acceptance

- A platform whose `.cl` types are FQ-named loads with no injected imports, GOT wrapped not
  copied, `got_slot = manifest index`; the old `jit_name`/`JITBuilder::symbol` path is gone.
- `/platform-schema <name>` prints the generated artifact for a loaded platform.
- Stale-hash: REPL warns-and-loads; `--run` refuses with both hashes + rebuild guidance.
- `cargo public-api` baseline for `int` + the int facade table updated.

## Context

Int half of the platform-interface cascade. Pairs with 0286 (platform macro), 0287 (backend
generator + dispatch + bake), 0289 (qa e2e). Supersedes the int half of the re-pointed
0229/0233.

## Status — S76 W4b (/dev int) — CARRIED to S77 as a coordinated cross-crate cut

**Not landed this wave (deliberate — interlocked, not piecemeal-safe).** The
load-path rewrite cannot land as an isolated int change without either breaking
the green workspace or producing a half-migrated load path worse than the current
working one. Three hard interlocks:

1. **PlatformError hash-refusal variant is missing in `cranelisp-types`** (the
   §6.4 `--run`/`--link` refusal sites consume it). It is `/arch`-owned (Decision
   0042) — filed as **FIXME 0293** (`target: /arch`). The hash-gate refusal path
   cannot compile until it exists. The `schema_literal` removal (also §7 cascade)
   is named in 0293 as the sibling types-crate residue.

2. **The platform crate's three HELD retirements (validate_schema, jit_name,
   export_name) must land SIMULTANEOUSLY with the consumer deletions.** Wave 4a
   deliberately HELD them so the workspace stayed green for this int cut.
   `OwnedPlatformFnDescriptor` still carries `jit_name` + `ptr` (the transitional
   shape) and `HostCallbacks` still carries `validate_schema`
   (`null_validate_schema`). Deleting `inject_primitives_import_for_platform` + the
   `(jit_name, ptr)`/`JITBuilder::symbol` path + the `validate_schema` construction
   sites on the int side, WITHOUT the platform crate dropping those fields in the
   same commit, leaves dangling references; doing the reverse breaks the platform
   crate. This is a single atomic change-set spanning `cranelisp-platform` +
   `src/platform.rs` + `cranelisp-exe-bundle` — a `/sprint`-coordinated wave-gate
   landing (FIXME 0286 platform-side + this int-side together), not a narrow int
   deploy.

3. **The new SymbolTable-from-manifest build needs FQ sigs end-to-end.** The DLL
   now emits FQ type_sigs (`primitives/Int`, `shapes/Rectangle`); the host resolves
   them via ordinary module resolution (`check_type_expr` over FQ names) with the
   associated `.cl` type module(s) FQ-auto-loaded (0268, landed). Wiring the
   manifest-index→got_slot + `GotTable::with_static_backing` over the dlsym'd
   `__cranelisp_got_platform_<name>` (wrap-not-copy) is tractable, but it must be
   validated e2e against the stdio DLL rebuilt with the new macro — which is gated
   on (2) landing first (the stdio DLL must emit the new exports + FQ sigs).

**Producers confirmed available (Wave 4a) for when the cut lands:**
- platform macro: exports `__cranelisp_got_platform_<name>` + manifest +
  `__cranelisp_layout_hash_<name>` + embedded schema (`set_global_schema`).
- backend: `schema::generate_schema` + `schema::compute_layout_hash` (the
  `/platform-schema` generator + the hash regeneration); `PlatformLayoutCheck` +
  `generate_startup_object_checked` (the `--link` startup bake);
  `cranelisp_check_layout_hash` (intrinsic, the compare-and-abort);
  `GotTable::with_static_backing` (the wrap-not-copy GOT consumption); the
  transitional platform GOT-indirect dispatch arm (activates on `got_slot: Some`).

**Recommended sequencing for S77:** /arch lands 0293 (PlatformError variant +
schema_literal removal) → /sprint coordinates the atomic platform-retirement cut
(0286 platform-side + this int-side load-path rewrite + exe-bundle bake) in one
wave gate → 0289 /qa e2e. The `/platform-schema <name>` REPL command
(`SlashCommand::PlatformSchema`, not yet in source) is additive and can land with
the int-side cut (thin caller of `schema::generate_schema` over the loaded
platform's module tables).

Keep this FIXME OPEN.
