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
