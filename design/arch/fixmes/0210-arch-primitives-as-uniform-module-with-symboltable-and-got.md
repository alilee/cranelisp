---
number: 0210
target: /arch
filed_by: /sprint
filed_at: 2026-05-17
sprint_filed: 67
refers_to: design/arch/facades/primitives.md, design/arch/facades/intrinsics.md, design/arch/facades/backend.md §"Intrinsic registration", crates/cranelisp-primitives/src/, crates/cranelisp-exe-bundle/src/lib.rs, design/arch/decisions/0035-code-enum-integration-layer.md, design/arch/decisions/0043-runtime-split-into-primitives-intrinsics.md, src/CLAUDE.md §"JIT Symbol Names"
status: open
---

# Primitives as a uniform module with SymbolTable + GOT

## Issue

`primitives` is a real spec-defined module per `spec/08-modules.md` — users write
`(primitives/str-concat ...)`, `(import [primitives [+]])`, etc. Yet today its
calling convention is special-cased relative to every other module:

- `JITBuilder::symbol("contains?", fn_ptr)` direct registration at JIT-build
- CLIF emits `Linkage::Import "contains?"` (extern name) for primitive calls
- Bypasses the standard per-module GOT lookup that user-code-to-user-code cross-module calls use
- `crates/cranelisp-exe-bundle/src/lib.rs` force-links each primitives submodule via `pub use cranelisp_primitives::string;` etc., so the staticlib carries the extern symbols for `--link`-mode binaries

This special-casing leaks across multiple surfaces:
- backend's `intrinsic_symbols()` carries primitives entries that conceptually belong to the primitives module
- primitives' Rust pub-API has ~30 individual extern `pub c fn` entries that serve no Rust consumer — they exist only to satisfy `JITBuilder::symbol(name, ptr)` registration via fn-pointer harvesting AND to be reachable through exe-bundle's force-link `pub use` re-exports
- exe-bundle special-cases primitives differently from user modules (force-link `pub use` magic rather than module-init machinery)
- The dispatch path for "call a primitive" diverges from "call a user-defined fn in another module"

Intrinsics (runtime-internal callees — `cranelisp_rc_inc`, `heap_alloc`, `cranelisp_panic`, drop glue, observer emit) are correctly special — they're the runtime infrastructure layer that everything sits on; not a user module; not user-visible. The asymmetry with primitives is the problem.

## Proposed resolution

Make `primitives` a uniform module: it has its own `SymbolTable<Code, ()>` populated at session init, its own per-module GOT, and is dispatched through the same cross-module GOT chain as user-to-user module calls.

### Shape

- `register_builtins` populates the primitives `SymbolTable` with `ModuleEntry::Def` entries for every non-inlined primitive (string ops, marshal, per-type to_string, int/float/bool conversions). Each entry has a `got_slot` index.
- Primitives' per-module GOT (`SymbolTable.got()`) holds raw fn_ptrs to the Rust extern functions at the prescribed slots.
- `Code` enum decision needed: either a new variant `Code::Extern { name: &'static str, ptr: *const u8 }` (fits the current shape; documents the extern origin) OR direct fn_ptr storage in the GOT without `Code` wrapping (since lifecycle is process-lifetime, no Arc-style retention needed). `/arch` adjudicates per Decision 35 amendment guidance.
- Backend's cross-module call path (which already exists for user-to-user calls — see Decision 31) is the dispatch mechanism. No new codegen path for primitives.
- `JITBuilder::symbol(name, ptr)` narrows to ONLY intrinsics (genuinely runtime-special; the asymmetry becomes load-bearing — intrinsics aren't a module so they can't go through GOT).

### `--link` implications

Standalone binaries need primitives module's GOT populated at startup:

- Currently exe-bundle force-links primitives via `pub use cranelisp_primitives::string;` etc.; .o files use `Linkage::Import name`; system linker resolves
- New shape: standalone binary startup populates the primitives GOT once at startup, before any compiled code runs
- `crates/cranelisp-exe-bundle/src/lib.rs::cranelisp_init_platform` already exists as the startup hook for platform setup; add `cranelisp_init_primitives_got()` (or extend the existing function) to populate the primitives GOT
- exe-bundle's `pub use cranelisp_primitives::string;` force-link lines retire — the `#[used]` attribute on each primitive (or `extern crate cranelisp_primitives;` reference in the init function) keeps them linked

### Visibility narrowing on primitives crate

After this refactor, primitives' Rust pub-API shrinks dramatically:
- The ~30 individual `pub extern "C" fn` entries narrow to `pub(crate) extern "C" fn` (with `#[used]` to prevent DCE)
- A single `pub fn populate_primitives_got(got: &mut GotTable)` (or per-submodule variants) replaces the per-function pub surface
- primitives.md facade prescribes the small handful of pub entries (the GOT-population function + module metadata)
- The 3 current orphans (`contains?`, `ends-with?`, `starts-with?`) disappear from pub-API entirely along with their 27 siblings

### Ring 0 caveat

Backend INLINES ring 0 ops (add-i64, sub-i64, eq-i64, etc.) at compile time per `crates/cranelisp-backend/src/primitives_inline.rs`. Inlined ops never go through ANY symbol table or GOT — they're emitted as raw Cranelift IR. This refactor does NOT affect ring 0 dispatch; inline remains inline.

## Operational implication / Context

Multi-sprint architectural work. Touches:
- `crates/cranelisp-primitives/src/` — visibility narrowing + `populate_primitives_got` aggregator authoring + `#[used]` attribute application
- `crates/cranelisp-backend/src/jit.rs` — `intrinsic_symbols()` shrinks; primitives entries retire
- `crates/cranelisp-exe-bundle/src/lib.rs` — retire force-link `pub use`; add `init_primitives_got()` to startup stub
- `src/session_v4.rs` — `register_builtins` populates primitives `SymbolTable`; JIT setup uses GOT path instead of `JITBuilder::symbol` for primitives
- `design/arch/facades/primitives.md` — dramatically narrows
- `design/arch/facades/exe-bundle.md` (if it gets one — currently exe-bundle is /int implementation detail per S67 Notes) — startup-stub changes
- `design/arch/decisions/` — likely needs a new Decision: "primitives dispatched through per-module GOT; intrinsics retain `JITBuilder::symbol` registration"
- `src/CLAUDE.md` §"JIT Symbol Names" — table update reflecting the new path for primitives

The benefit is significant:
- Single codegen dispatch path for all user-callable symbols
- Primitives stop being a snowflake
- Pub-API for primitives matches Rust visibility intent (no `pub` items that serve no Rust consumer)
- `--link` startup mechanism uniformizes (init functions instead of force-link magic)
- `JITBuilder::symbol` registration narrows to intrinsics where it belongs

## Recommended next steps (for /arch)

1. Design pass: decide `Code` enum vs raw fn_ptr-in-GOT for primitives entries. Decision needed.
2. Sequence the work across sprints: typically (a) backend cross-module dispatch verification; (b) primitives `SymbolTable` + GOT population in `register_builtins`; (c) backend `intrinsic_symbols()` narrowing; (d) exe-bundle startup stub extension; (e) visibility narrowing on primitives crate.
3. Coordinate with `/dev (primitives)`, `/dev (backend)`, `/dev (int)`, `/design (primitives)`, possibly `/design (backend)`.
4. Decision register entry to capture the rationale + chosen Code-variant approach.
