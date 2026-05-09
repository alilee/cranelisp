---
number: 0164
target: /design (typecheck)
filed_by: /arch
filed_at: 2026-05-09
sprint_filed: 66
refers_to: design/typecheck/ast-annotation.md §11.3 invariant 6 (Serde round-trip identity), §13.3 (pattern-matching/construction notes), §12.5 (cache-restore observation)
status: open
---

# Update `ast-annotation.md` for the S66 fn_ptr unification rollback

## Issue

`design/typecheck/ast-annotation.md` lists `platform_fn_ptr: #[serde(skip)]` among the runtime-only fields a `SymbolTable<(), ()>` must round-trip cleanly through serde at §11.3 invariant 6 (the fundamental cache-restore invariant for Step 5b). It also references `platform_fn_ptr` in §13.3 (pattern-matching with `..` and constructor sites that write `platform_fn_ptr: None`).

These references pre-date the S66 fn_ptr unification (commit `b09ec76`, which removed `platform_fn_ptr` and added a unified `fn_ptr`) and the same-day rollback (commit `1dc57ae`, which removed the unified `fn_ptr` field after identifying it as redundant with the per-module `GotTable`).

## Proposed resolution

Update §11.3 invariant 6 and §13.3 to reflect the post-rollback shape: there is no per-entry pointer field on `ModuleEntry::Def`. The runtime ptr lives in `SymbolTable.got` (an `Arc<GotTable>` that is `#[serde(skip)]`). The `got_slot: Option<usize>` index lives ON the entry and IS persisted (plain `usize`, no skip).

Specific call-out edits:

1. **§11.3 invariant 6** (around line 1274). Replace the round-trip-identity field list:
   - From: "modulo runtime-only fields (`got: #[serde(skip)]`, `code: #[serde(skip)]`, `platform_fn_ptr: #[serde(skip)]`, `linker: #[serde(skip)]`)"
   - To: "modulo runtime-only fields (`SymbolTable.got: #[serde(skip)]` — `Arc<GotTable>`; `ModuleEntry::Def.code: #[serde(skip)]` — `Option<C>`; `SymbolTable.linker: #[serde(skip)]` — `Option<L>`)"

   No `platform_fn_ptr` field exists post-rollback. The per-entry runtime ptr is not a separate field — it lives in `SymbolTable.got`'s slot indexed by `got_slot`, and the GOT itself is `#[serde(skip)]` (re-allocated and re-populated on cache-hit load).

2. **§11.3 invariant 6 follow-up sentence** ("/typecheck's contract is that the four new fields participate in serde without quirks…"). Update from "four new fields" to "three new fields" and drop the implication that `platform_fn_ptr` is one of them. The `Vec<T>` framing for `imports`/`exports`/`platforms`/`submodules` (Step 5a structural decls) is unchanged. The unit-test fixture suggestion is still valid (round-trip a fixture with non-empty values in those structural-decl fields), with the note that runtime-only fields (got, code, linker) deserialise to default `Arc<GotTable>` / `None` / `None` respectively.

3. **§13.3 (pattern-matching on `ModuleEntry`)** (around line 1363). Update the `..`-ignores list:
   - From: "Pattern matching with `..` ignores the `code` and `platform_fn_ptr` fields entirely"
   - To: "Pattern matching with `..` ignores the `code` field entirely; `got_slot` is a plain `Option<usize>` and pattern-matchable when needed but typecheck typically ignores it (it's allocated by the registration site, read by codegen)."

4. **§13.3 constructor sites** (around line 1365). Update:
   - From: "Both sites write `code: None` and `platform_fn_ptr: None` literally."
   - To: "Both sites write `code: None` literally. `got_slot: Some(slot)` is allocated via `SymbolTable::allocate_got_slot()` at registration time for any addressable callable entry; for non-addressable kinds (TypeDef, TraitDecl, Macro, Overloaded base, constrained-fn templates) `got_slot: None`."

5. **§12.5 cache-restore observation** (around line 1404). Update:
   - From: "the Step 5c `code` / `platform_fn_ptr` / `linker` fields skipped"
   - To: "the Step 5c `code` and `linker` fields skipped (and `SymbolTable.got` skipped)"

## Operational implication / Context

This is a doc-coherence sweep — no source change implied. Source has already migrated via commits `b09ec76` and `1dc57ae`; the typecheck-side construction sites in `crates/cranelisp-typecheck/src/{builtins, checker, infer, program, traits}.rs` have already had their `fn_ptr: None,` initializer lines removed by `1dc57ae`. This doc is the only typecheck-side design artefact still referencing the old field shape.

Source-of-truth check before editing:
- `crates/cranelisp-types/src/module.rs:430–460` (`got_slot` doc-comment, no fn_ptr/platform_fn_ptr field)
- `crates/cranelisp-types/src/got.rs` (`GotTable`)
- `crates/cranelisp-typecheck/src/builtins.rs` and similar (no `fn_ptr: None` lines remain post-rollback)

/arch's canonical post-rollback statement lives in:
- `design/arch/decisions/0035-code-enum-integration-layer.md` §"Amendment (Sprint 66 — rollback, 2026-05-09)"
- `design/arch/decisions/0041-compile-to-module-per-symbol-jit-direct-writes.md` §"S66 amendment + rollback"
- `design/arch/facades/types.md` §"Symbol table — the single store" (`got_slot` doc)
