# Arbitration: `super` → parent-path rewrite location

**Sprint**: 57 Wave 0
**Decided**: 2026-04-18
**Arbiter**: `/arch`
**Status**: Decided (implementation pending)

## Decision

**Option A — Frontend capture-time rewrite** in `crates/cranelisp-frontend/src/module_extract.rs`.

`super` is rewritten to the parent `ModuleFullPath` at the point `ImportSpec` is constructed, using the `path: ModuleFullPath` already passed into `extract_module_declarations`. After extraction, `ImportSpec.module_path` NEVER contains the literal string `"super"` — every downstream consumer sees a real module path.

## Rationale

- **Principle 3 (dependency flows toward stability)**: module identity is a frontend concern. The frontend already resolves aliased `(module alias)` forms, normalises dotted paths, and owns the `ModuleFullPath` newtype. The parent-path computation is in the same conceptual cluster as the rest of the frontend's module-identity work and belongs in the most stable crate that has all the information needed (`ExtractedDeclarations` receives `path` — everything required to compute the parent is already in scope).
- **Principle 7 (single source of truth)**: consumption-time rewrite has multiple sites (`src/worker.rs:679` primary capture, `src/worker.rs:1065` `handle_import` dependency-resolution path, plus cache-hit reload and future REPL-`import` paths). Each is a potential divergence point. Frontend-time rewrite has exactly one site — `parse_import_entries` / `parse_module_spec` — and the invariant "no `super` past the frontend boundary" is enforceable by inspection.
- **Principle 12 (design for the full spec surface)**: leaving `super` as a sentinel in `ImportSpec.module_path` means every consumer must know to skip or rewrite it. Eliminating the sentinel at the parsing boundary means `ImportSpec` carries only valid module paths — a narrower, more truthful boundary type.
- **Spec framing favours it**: `spec/08-modules.md §8.3.7` describes `super` as a shorthand that "resolves to the parent module by stripping the last component from the current module's full path." The spec words this as a lexical substitution, not a scheduler-time lookup — frontend capture is the natural place to effect it.
- **Existing test inverts cleanly**: `test_import_super` in `crates/cranelisp-frontend/src/module_extract.rs:548` currently asserts `super` survives as the literal module path. Under Option A that test flips to assert the rewritten parent path (and gains a negative sibling for the root-module error case). One test file, one site, fully within `/frontend`'s ownership.
- **No scope expansion**: the `ExtractedDeclarations` constructor already takes `path: ModuleFullPath`. Computing `path.rsplit_once('.')` is a two-line branch inside the existing `parse_module_spec` / `parse_import_entries` flow — no new types, no new crate dependencies.

## Implementation site

**File**: `crates/cranelisp-frontend/src/module_extract.rs`

**Function**: the rewrite happens in `parse_import_entries` (or a helper called from there) after `parse_module_spec` returns the raw `module_path` string. Before constructing the final `ImportSpec`, check for `module_path == "super"`:

- If the containing `ExtractedDeclarations.path` has a parent (i.e., `rsplit_once('.')` returns `Some`), substitute `ImportSpec.module_path` with the parent `ModuleFullPath`.
- Otherwise, return a `CranelispError::ModuleError` per the contract below.

The signature change is minimal: `parse_import` already receives the elems and span; threading the containing `ModuleFullPath` through `parse_import` → `parse_import_entries` (or passing it on a small `ImportParseCtx` struct) is a local refactor.

## Owning skill

**`/frontend`** owns the Wave 0 implementation. `/int` updates one caller at `src/worker.rs` — `classify_form` (and its helper `separate_macros`) now thread `containing_module: &ModuleFullPath` through to `cranelisp_frontend::parse_import_sexp`, because the v4 worker's Pass-0 `classify_form` path (`design/int/step5-lazy-discovery.md:49`) bypasses `extract_module_declarations`. `/qa` writes the integration tests (positive + negative) against `spec/08-modules.md §8.3.7`. `/review` reviews a small surface.

See also **Decision 30** in `CLAUDE.md` for the known pass-order constraint on the v4 form-by-form scheduler: `super` is safe when the parent does not also import from the child, but the parent↔child mutual-import pattern (and any two mutually-importing modules more generally) deadlocks the scheduler. Test submodules should use the `discover-tests` + `run-test` builtins rather than `(import [super [*]])` when the parent imports from the child.

## Sketch comparison

The sketch implements Option B at `sketch/src/module.rs:1429-1434`, rewriting `super` → parent path inside its module-declaration resolution pass, after `decls.imports` is populated. The reimplementation **diverges** from the sketch's placement.

**Why diverge**: the sketch's placement is a symptom of the same dual-pipeline debt documented elsewhere — the sketch's module resolver was the only cross-cutting site that saw every module's declarations, so it became the default dumping ground for any module-identity normalisation. The reimplementation's crate boundaries give the frontend first-class ownership of `ImportSpec` construction (`module_extract.rs` is a dedicated frontend module), making capture-time rewrite the structurally correct choice. The sketch's solution is not wrong at the language level — it produces the same observable behaviour — but adopting its placement in the new pipeline would push a frontend concern into `/int`'s integration layer without justification.

**What the sketch got right**: the algorithmic core — `rsplit_once('.')` on the current module path, error on root — is correct and is adopted verbatim. The sketch's error message ("`super' import used in top-level module '{}' (no parent)`") is a reasonable template.

## Error contract (spec §8.3.7)

Per `spec/08-modules.md §8.3.7` line 195: "Using `super` in a top-level module (one with no parent) MUST produce a compile-time error."

The reimplementation emits `CranelispError::ModuleError` with:

- **Message template**: `"'super' import used in top-level module '{module_path}' (no parent)"` where `{module_path}` is the current `ExtractedDeclarations.path`.
- **`file` field**: `None` at the frontend layer (the caller already knows which file it passed sexps from; the scheduler attaches file info when the error propagates).
- **`span` field**: the span of the `super` symbol inside the `(import [super [...]])` form — i.e., the span returned by `parse_module_spec` for the offending entry. This is already available inside `parse_import_entries` without plumbing changes.

The error is raised immediately during `extract_module_declarations` — before any downstream consumer sees the `ImportSpec` — so root-module violations never reach the scheduler, typechecker, or codegen.

## Consequences

- `crates/cranelisp-frontend/src/module_extract.rs::test_import_super` inverts: input `(import [super [*]])` with `path = "math.test"` now asserts `ms.import_specs[0].module_path == "math"`. A new sibling `test_import_super_root_errors` asserts the error case.
- `sketch/src/module.rs:1429-1434` has no counterpart in the new code — the scheduler/worker never sees `super` as a module path, so `handle_import` and `handle_export` at `src/worker.rs:1059` and `:1274` need no changes.
- `ImportSpec.module_path` gains a documented invariant: "post-extraction, never equal to `super`" — worth a comment in `crates/cranelisp-types/src/module.rs` where `ImportSpec` is defined. That comment is `/arch`-owned under `cranelisp-types`; it may be added as a follow-up note but is not blocking for Wave 0.
- The one-page decision record that `/frontend`'s SPRINT entry calls for (`design/frontend/super-import.md`) is redundant with this arbitration document — `/frontend` may skip it or author a short pointer that cites this file.

## Next skills

- `/frontend` — implement the rewrite per §"Implementation site"; invert `test_import_super`; add the negative test.
- `/qa` — author the super-import integration tests (positive + negative) per `spec/08-modules.md §8.3.7`.
- `/review` — small surface; review after `/frontend` lands.

