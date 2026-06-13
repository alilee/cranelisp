---
number: 0289
target: /qa
filed_by: /arch
filed_at: 2026-06-07
sprint_filed: 76
refers_to: design/arch/platform-interface.md §4 §7.2 §7.2a §7.3, design/arch/fixmes/0235, design/arch/bounded-contexts.md §5 §6, tests/platform_errors.rs, src/platform.rs::abi_version_mismatch_detected
status: open
stage: 2                  # deferred "option 2" — ADT-typed shapes test-DLL + full drift e2e (user 2026-06-10)
---

# Platform-interface — e2e round-trip + hash-gate integration tests

## Issue

The platform-interface design (`design/arch/platform-interface.md`, user-ratified
2026-06-07; **normative**) needs e2e coverage of its walks. This supersedes the old
schema-validation-mismatch coverage in FIXME 0235 (re-pointed) — the layout-hash gate
replaces `validate_schema`.

## Scope

Per `platform-interface.md` §4 (author experience) + §7.2/§7.2a/§7.3 (the sequences):

1. **FQ-named-ADT round-trip** — a test platform (test-DLL authored by `/platform`) whose
   sigs reference an ADT defined in an ordinary `.cl` module (`shapes/Rectangle`); cranelisp
   source constructs the ADT and passes it to the platform fn; assert the value crosses
   correctly (rectangle {w=3,h=4} → 12). Works in `--run` and `--link`.
2. **The build-load-generate-embed-rebuild walk** — `/platform-schema <name>` emits the
   artifact; the platform embeds it; `--run`/`--link` ACCEPT on hash match.
3. **The dual hash-gate** — a stale/typo'd schema (sig or `deftype` edited after the DLL
   was built): **REPL warns-and-loads**; **`--run` refuses**; **`--link` refuses** (the
   startup-stub baked-hash comparison) — each with both hashes + rebuild guidance. (This is
   the re-target of old 0235 item 4 — `validate_schema` mismatch → layout-hash mismatch.)
4. **Cache-restore round-trip** — re-load from cache; ADTs cross correctly (platform types
   cache as ordinary `.cl` modules; no `schema_literal` field).

## Deferred "option 2" — the ADT-typed `shapes` test-DLL fixture + full drift e2e

User-decided 2026-06-10 (S77 W-Platform): the true platform-DRIFT e2e is deferred to this
FIXME, because none of it is e2e-triggerable against the real `stdio`/`test-capture`
platforms — those have **no ADT-typed fns** (so no `__cranelisp_layout_hash` is emitted) and
**always match the host ABI** (same workspace build). The drift detection paths ARE wired and
**unit-proven in `src/platform.rs`**:

- `abi_version_mismatch_detected` — perturbed `ABI_VERSION + 1` →
  `PlatformError::AbiVersionMismatch { expected, found }` with both values correct.
- `abi_version_match_accepts` — host's own `ABI_VERSION` passes the gate.
- (layout-hash drift → `LayoutHashMismatch`, both `--run` Refuse + REPL WarnAndLoad — wired
  in the int load path; the e2e for it is the §"Scope" item 3 above.)

What this FIXME must build (the "option 2" scope), all needing the new fixture:

1. **The ADT-typed `shapes` test-DLL** (`/platform`-owned) — a platform whose sigs reference
   an ADT (`shapes/Rectangle`) defined in an ordinary `.cl` module, so the backend schema
   generator emits a non-empty schema + `__cranelisp_layout_hash_shapes`.
2. **Clean round-trip e2e** — construct the ADT in source, pass it to the platform fn, assert
   it crosses correctly (`{w=3,h=4} → 12`); `--run` + `--link` ACCEPT on hash match.
3. **Layout-hash drift e2e** — perturb the program's `deftype` (or the sig) after the DLL was
   built → assert `LayoutHashMismatch` end-to-end: **REPL warns-and-loads**, **`--run`
   refuses**, **`--link` refuses** (startup-stub baked-hash comparison), each surfacing both
   hashes + rebuild guidance.
4. **Perturbed-ABI DLL e2e** — a test-DLL built declaring a stale `ABI_VERSION` → assert
   `AbiVersionMismatch { expected, found }` surfaces e2e with both values (the e2e companion
   to the unit-proven `abi_version_mismatch_detected`).
5. **Dispatch-error-with-fn-name e2e** — trigger a dispatch-time error against the test-DLL →
   assert the structured `PlatformError::DispatchError { fn_name }` carrier surfaces the
   offending fn name.
   **STATUS (S81, 2026-06-13): DONE.** `tests/platform_errors.rs::platform_dispatch_error_carries_fn_name`
   is GREEN — the boom fault surfaces a clean structured `PlatformError::DispatchError`
   (non-zero exit, NOT a process abort) whose `fn_name` contains the baked FQ name
   `platform.boom/crash`. The fault-guarded dispatch funnel landed end-to-end across the commit
   chain `aeff79d` (node-widen) → `d1949fb` (bake/stamp) → `f0d25dc` (guard + compose) →
   `9fb89ed` (DLL-local catch / EffectOutcome cross-ABI signal — Option A, resolving the cdylib
   foreign-exception abort) → `abe3553` (fn-name stamped at the GOT-indirect dispatch chokepoint,
   so the baked FQ name survives the fault path) → this commit (un-ignore + comment rewrite).
   FIXMEs 0327 + 0337 are closed by this green. Items 1-4 below remain separate ADT-shapes scope
   (still open).

## What landed S77 W-Platform (R9, e2e-reframe slice — NOT closing this FIXME)

The 2 mis-written e2e tests in `tests/platform_errors.rs` were reframed to assert
**e2e-observable behaviour that holds today** (the not-found gate + the success half of
platform-fn dispatch); the `panic!("synthetic DLL fixture not yet available")` placeholder
is removed. Specifically:

- `platform_abi_version_mismatch_emits_expected_vs_found` → renamed
  `platform_unknown_name_emits_structured_not_found`: asserts the structured, span-carrying
  `module error … platform '<name>' not found` for an unresolvable platform name (the real
  `CranelispError::ModuleError` shape from `resolve_platform_path → None`). The true ABI-drift
  round-trip is item 4 above.
- `platform_dispatch_error_during_run_carries_fn_name` → renamed
  `platform_fn_dispatches_across_dll_boundary`: asserts a real `stdio` platform-fn (`print`)
  resolves + dispatches across the host↔DLL boundary (output reaches stdout, exit clean). The
  structured `DispatchError { fn_name }` e2e is item 5 above.

## Acceptance

- `tests/spec_platforms_adt.rs` (or sibling) lands the round-trip + hash-gate + cache walks
  (Deferred-option-2 items 1–5), failing-first then green as 0286/0287/0288 land. Per the
  two-tier discipline the test-DLL is `/platform`'s; the `tests/`-side e2e file is `/qa`'s.

## Context

QA half of the platform-interface cascade (0286 platform, 0287 backend, 0288 int).
Re-points + absorbs FIXME 0235.
