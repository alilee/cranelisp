# REPL Session Persistence — Architecture Review

Sprint 23 mini-sprint. Architectural guidance for implementing `repl/spec.md` §15.

## 1. Source Regeneration Approach

### Sketch approach

The sketch regenerates the **entire** `.cl` file from `CompiledModule` data (not appending raw input). `generate_module_source()` in `sketch/src/repl/save.rs` walks the module's symbol table and structural metadata in a fixed order:

1. `(mod ...)` declarations
2. `(platform ...)` declarations
3. `(import ...)` — merged, prelude filtered out
4. `(export ...)`
5. Trait declarations (alphabetical)
6. Type definitions (alphabetical)
7. Trait implementations (order from `impl_sexps`)
8. Functions and macros (dependency-sorted via Kahn's topological sort)

Each definition's stored `Sexp` is formatted via `format_indented()`. Constructor and trait method references are qualified via `qualify_sexp()` (walks the sexp tree, calls `tc.qualify_name()` to add module prefixes).

### Recommendation: Follow the sketch

The regeneration approach is the right one. The alternatives are worse:

- **Appending raw input**: Produces unreadable files, accumulates dead redefinitions, cannot handle `(import ...)` deduplication, breaks on reordering. The sketch tried this implicitly (the user's input order is arbitrary) and chose regeneration.
- **Diffing/patching**: More complex than regeneration with no benefit — the module's symbol table is the ground truth, and regeneration is a pure function of it.
- **Storing input history**: Cannot handle deletion, redefinition, or import merging.

Regeneration from the symbol table is a pure function — easy to test in isolation, deterministic, and produces clean source files that are also valid module files.

### Key design detail: stored Sexp

The regeneration **requires** the original `Sexp` for each definition. The sketch stores `sexp: Option<Sexp>` on `DefCodegen` (for functions), `ModuleEntry::TypeDef`, `ModuleEntry::TraitDecl`, `ModuleEntry::Macro`, and `impl_sexps: Vec<ImplSexp>` on the module structure. The reimplementation already has all of these:

- `DefCodegen.sexp` — in `cranelisp-backend` (`crates/cranelisp-backend/src/codegen_types.rs`)
- `ModuleEntry::TypeDef.sexp` — in `cranelisp-types`
- `ModuleEntry::TraitDecl.sexp` — in `cranelisp-types`
- `ModuleEntry::Macro.sexp` — in `cranelisp-types`
- `ModuleStructure.impl_sexps` — in `cranelisp-types`

No new fields are needed.

## 2. When to Save

The sketch saves after every **definition-like** REPL input that mutates the module's symbol table:

- `defn` (single and multi-sig)
- `deftype`
- `deftrait`
- `impl`
- `defmacro`
- `(import ...)`
- `(mod ...)`
- `(platform ...)`

The sketch does **not** save after bare expression evaluation (e.g., `(+ 1 2)`) — expressions don't change the module state.

This is correct. Save-on-each-definition is simple and safe:
- If the REPL crashes, the user loses at most the last expression (which was ephemeral anyway).
- The write is atomic (temp file + rename), so partial writes are impossible.
- The content hash is updated immediately, preventing the file watcher from triggering a redundant reload.

Do **not** defer saves to `/quit` — that risks losing an entire session on crash.

## 3. Cache Interaction

After saving `user.cl`, the sketch calls `write_current_module_cache()` which submits a `CacheWritePacket` to the background `CacheWriter`. This produces:
- Updated `user.meta.json` (serialized symbol table + codegen state)
- Updated `user.o` (relocatable object file)
- Manifest entry update (on `CacheWriter` shutdown)

The reimplementation should do the same. Since `user.cl` now exists as a regular file with a content hash, the module graph pipeline treats it identically to any other module on startup. Cache hit = fast restore. Cache miss = recompile from the saved `.cl` file.

The `save_current_module()` method in the sketch first saves the `.cl` file (getting the new content hash), then submits the cache packet with that hash. The reimplementation should follow the same order.

## 4. File Watching Interaction

The watcher must not trigger a reload when the REPL itself writes `user.cl`. The sketch solves this elegantly with **content-hash comparison, not write suppression**:

1. `save_current_module()` writes the `.cl` file and updates `cm.content_hash` to the hash of the written content.
2. The file watcher detects the write event and calls `reload_module()`.
3. `reload_module()` reads the file, hashes the content, compares to `cm.content_hash` — they match.
4. `reload_module()` returns `Ok(false)` (content unchanged, no reload).

This is robust because:
- No race conditions with write timing or event delivery order.
- Works regardless of how many events the OS generates for one write.
- Handles edge cases (e.g., editor opens and re-saves `user.cl` with identical content).
- No mutable "ignore next write" flag that could get stuck.

The reimplementation's `repl-lifecycle.md` §1.3 already specifies content-hash verification before reload. This is exactly the mechanism needed — no additional design work required.

## 5. Startup Restore

The sketch's approach (lines 1790-1836 of `sketch/src/repl.rs`) is:

1. Check if `user.cl` exists at `project_root/user.cl`.
2. If yes, build a `ModuleGraph` from it (parsing, dependency discovery).
3. Process platform declarations.
4. Compile the module graph via `compile_module_graph()` — this hits the cache if available.
5. Set `current_module` to `user`, register the module prefix.
6. If loading fails (parse error, type error), print a warning and fall through to fresh-module creation.

The reimplementation should follow this exactly. The module graph pipeline already handles cache loading, so `user.cl` benefits from caching automatically. On a warm cache, startup restore is near-instant (deserialize metadata + load `.o`).

One note: the sketch creates a fresh `user` module (with `file_path` set to `user.cl`) even when no `user.cl` exists. This ensures the module always has a backing file path, which `save_module_file()` needs. The reimplementation must do the same.

## 6. `/reset` and Session Persistence

With session persistence, `/reset` has a natural meaning: delete `user.cl`, clear the cache entry, and restart with a fresh module. However, the user prefers improving the demo trampoline over speccing `/reset` reset-to-disk semantics. The current `/reset` (clear in-memory state, reload prelude) is sufficient — it does not need to interact with the backing file.

Note: after `/reset`, the fresh `user` module should still have `file_path` set to `user.cl`, so new definitions will be saved. If `user.cl` still exists on disk from a previous session, `/reset` should **not** load it (that would defeat the purpose of resetting). The implementation should either delete `user.cl` on reset or skip the startup-load logic when entering `/reset`.

## 7. Crate Boundaries

Source regeneration code lives in the **binary crate** (`src/`), not in `cranelisp-backend` or `cranelisp-types`. Rationale:

- It reads from `SymbolTable` (in `cranelisp-types`) and `DefCodegen` (in `cranelisp-backend`) but does not modify them.
- It writes to the filesystem — a side effect appropriate for the binary crate.
- It uses `Sexp::format_indented()` which is in `cranelisp-types` (or `cranelisp-frontend`).
- The sketch puts it in `repl/save.rs` — the reimplementation should do the same: `src/repl/save.rs`.

The `generate_module_source()` function needs:
- `&SymbolTable` — from typecheck
- `&ModuleStructure` — from typecheck
- `&HashMap<Symbol, DefCodegen>` — from `got_state.def_codegen` in the REPL session
- A way to qualify names — either a closure/trait or a reference to the typecheck state

This is a read-only operation over data the binary crate already holds. No new inter-crate dependencies.

### Qualify names

The sketch passes `&TypeChecker` to `qualify_sexp()` which calls `tc.qualify_name()`. The reimplementation should extract this as a method on the typecheck facade or pass a closure `Fn(&str) -> Option<String>` to avoid exposing the full `TypeChecker` to the save module. This is a minor detail for `/int` to resolve during implementation.

## 8. Data Availability in the Reimplementation

The sketch's `generate_module_source()` uses:

| Data needed | Sketch location | Reimplementation equivalent | Available? |
|---|---|---|---|
| `cm.mod_decls` | `CompiledModule.mod_decls` | `ModuleStructure.mod_decls` | Yes |
| `cm.import_specs` | `CompiledModule.import_specs` | `ModuleStructure.import_specs` | Yes |
| `cm.export_specs` | `CompiledModule.export_specs` | `ModuleStructure.export_specs` | Yes |
| `cm.impl_sexps` | `CompiledModule.impl_sexps` | `ModuleStructure.impl_sexps` | Yes |
| `cm.symbols` (TraitDecl with sexp) | `ModuleEntry::TraitDecl.sexp` | `ModuleEntry::TraitDecl.sexp` | Yes |
| `cm.symbols` (TypeDef with sexp) | `ModuleEntry::TypeDef.sexp` | `ModuleEntry::TypeDef.sexp` | Yes |
| `cm.symbols` (Macro with sexp) | `ModuleEntry::Macro.sexp` | `ModuleEntry::Macro.sexp` | Yes |
| `cm.symbols` (UserFn with sexp) | `DefKind::UserFn.codegen.sexp` | `DefCodegen.sexp` (in `got_state.def_codegen`) | Yes, but separate |
| `cm.symbols` (PlatformDecl) | `ModuleEntry::PlatformDecl` | `ModuleEntry::PlatformDecl` | Yes |
| `cm.file_path` | `CompiledModule.file_path` | `ModuleStructure.file_path` | Yes |
| `cm.content_hash` | `CompiledModule.content_hash` | `CacheMetadata.content_hash` | Yes |
| `tc.qualify_name()` | `TypeChecker` method | Needs equivalent in typecheck facade | **Gap** |

### Gap: Function Sexp location

In the sketch, `DefCodegen` is embedded inside `ModuleEntry::Def { kind: DefKind::UserFn { codegen } }` — the symbol table and codegen are unified. In the reimplementation, `DefCodegen` lives in `ModuleCodegenState.def_codegen: HashMap<Symbol, DefCodegen>` (backend crate), separate from `SymbolTable` (types crate).

This means `generate_module_source()` needs to join two data sources:
- `SymbolTable.symbols` to identify which symbols are `UserFn` definitions
- `got_state.def_codegen` to get the `sexp` for each function

This is a minor inconvenience, not a blocker. The function signature becomes:
```rust
fn generate_module_source(
    sym_table: &SymbolTable,
    structure: &ModuleStructure,
    def_codegen: &HashMap<Symbol, DefCodegen>,
    qualify: impl Fn(&str) -> Option<String>,
) -> String
```

### Gap: `qualify_name()`

The sketch's `qualify_sexp()` calls `tc.qualify_name(name)` to resolve bare names to qualified forms (e.g., `Some` -> `option/Some`). The reimplementation needs a similar capability. This could be:
- A method on the typecheck crate's public API that takes a module context and a bare name
- A pre-built lookup table passed to the save function
- Skipped initially — if the REPL always stores fully-qualified sexps, qualification is unnecessary

The sketch stores **unqualified** sexps (as the user typed them) and qualifies at save time. The reimplementation should consider storing **qualified** sexps from the start (the macro expander already resolves names). If sexps are already qualified, `qualify_sexp()` becomes a no-op and this gap disappears. `/int` should verify whether the stored sexps are qualified or not.

## Sketch Comparison Summary

| Aspect | Sketch | Reimplementation | Rationale |
|---|---|---|---|
| Regeneration approach | Full regeneration from symbol table | Same | Proven correct, pure function, testable |
| Save trigger | After each definition | Same | Simple, safe, no-data-loss |
| Atomic write | temp file + rename | Same | Standard pattern |
| File watcher suppression | Content-hash comparison | Same | Already designed in `repl-lifecycle.md` §1.3 |
| Cache update after save | Background `CacheWriter` | Same | Already designed in `repl-lifecycle.md` §4 |
| Startup restore | `ModuleGraph::build(user.cl)` | Same | Normal module pipeline |
| Code location | `repl/save.rs` | `src/repl/save.rs` | Binary crate, same structure |
| CompiledModule access | Unified `&CompiledModule` | Split `SymbolTable` + `ModuleStructure` + `DefCodegen` | Architecture decision 9 (decomposition) |

The only divergence is structural (split data sources due to CompiledModule decomposition), which is a deliberate architectural improvement. No design divergence from the sketch's approach.
