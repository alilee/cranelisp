# REPL Session Persistence — Implementation Design

Design for `repl/spec.md` §15 (session persistence). Covers source
regeneration, backing file management, watcher integration, and startup
restore. Supersedes the Sprint 23 architecture review.

## 1. Source Regeneration Pipeline

### 1.1 Trigger Point

Regeneration runs **after `eval()` returns `Ok(Some(EvalResult::Def { .. }))`**
in `main.rs`, before the next prompt. Expression evaluations (`EvalResult::Val`)
do not trigger regeneration — they don't mutate module state.

The call site in the REPL loop (simplified):

```
match s.eval(&src) {
    Ok(Some(result @ EvalResult::Def { .. })) => {
        s.pretty_print(&s.format_eval_result(&result), &mut stdout);
        s.regenerate_backing_file();   // <-- here
    }
    Ok(Some(result)) => { /* Val — no regen */ }
    ...
}
```

Imports (`(import ...)`) also mutate module state. The REPL intercepts imports
before `eval()` (currently in `process_commands`). After a successful import,
regeneration must also fire. The simplest approach: `regenerate_backing_file()`
is a method on `CompilerSession` called from every code path that mutates the
current module's persistent state.

### 1.2 Definition-Like Triggers

Regeneration fires after successful:
- `defn` (single and multi-sig)
- `deftype`
- `deftrait`
- `impl`
- `defmacro`
- `(import ...)`
- `(mod ...)`
- `(platform ...)`

Failed compilations must NOT trigger regeneration (§15.1).

### 1.3 Regeneration Algorithm

`regenerate_backing_file()` reads the **current module's** state from
`SharedState` and produces a complete `.cl` source file. The current module
is not necessarily the entry module — the user may have switched via `/mod`
to another module and submitted definitions there. Any module that receives
a successful definition must be regenerated.

The output sections appear in a fixed order (matching the sketch's proven approach):

1. `(mod ...)` declarations
2. `(platform ...)` declarations
3. `(import ...)` — merged, implicit prelude filtered
4. `(export ...)` — merged
5. Trait declarations (alphabetical)
6. Type definitions (alphabetical)
7. Trait implementations (insertion order from `impl_sexps`)
8. Functions and macros (dependency-sorted via topological sort)

Each section is generated from the module's current symbol table and structural
metadata. Sections are separated by blank lines. The result is a valid,
parseable Cranelisp source file.

### 1.4 Dependency Ordering

Functions and macros within the module must appear in dependency order so the
file compiles in a single forward pass without forward references.

Algorithm: Kahn's topological sort using the **per-symbol callee list** stored
on `ModuleEntry::Def.callees` and `ModuleEntry::Macro.callees` (Decision 21 —
TC-sourced call graph). This is already computed during typechecking and
persisted on the symbol table. No sexp scanning needed.

- Build adjacency: for each function/macro, filter its `callees` to only
  those whose module matches the current module (intra-module edges).
- Items with no intra-module dependencies appear first.
- Cycles (mutual recursion) are broken alphabetically — mutual recursion
  requires `(declare ...)` or let-rec, which is a separate spec concern.
- Items with no dependencies are emitted alphabetically for determinism.

**Note on types and traits**: `deftype` and `deftrait` have no `callees` field
(Decision 21 covers only `Def` and `Macro`). This is acceptable because the
regeneration section ordering (§1.3) emits traits and types BEFORE functions.
Cranelisp's type system does not require declaration-order dependencies among
types — all types and traits are available for reference after the type/trait
sections are loaded, before functions are processed. Intra-type and
intra-trait ordering is alphabetical.

This is simpler than the sketch's approach (which scanned sexps for symbol
references) because the callee list is pre-computed and authoritative.

## 2. Source Storage Strategy

### 2.1 Source/Sexp Field Review — Prerequisite

**Before implementing persistence, a review of all source/sexp fields across
SharedState is required.** Currently, sexp data is scattered:

| Definition kind | Symbol table (`ModuleEntry`) | Introspection | Issue |
|---|---|---|---|
| `defn` | no sexp field | `sexp`, `source` | split across two stores |
| `deftype` | `sexp` on `TypeDef` | — | on symbol table |
| `deftrait` | `sexp` on `TraitDecl` | — | on symbol table |
| `defmacro` | `sexp` on `Macro` | — | on symbol table |
| `impl` | no sexp field anywhere | — | **gap** |

The goal is **one copy in the right place**. Options:

**Option A: All source/sexp on Introspection.** Introspection is already
per-symbol on SharedState. Move type/trait/macro sexps there too. Symbol
table stores only what's needed for name resolution and typechecking.
Introspection becomes the persistence record. Only needed for `--repl` mode.

**Option B: All source/sexp on SymbolTable.** Add `sexp` to `ModuleEntry::Def`.
Add `ModuleEntry::TraitImpl { sexp }` for impl storage. Everything in one
place, serialized naturally via meta.json.

**Decision: Option A (Introspection) with impl_sexps on SymbolTable.**

Rationale:
- Introspection is already the home for slash command data (`/source`, `/sexp`)
- It's per-symbol, keyed by `FQSymbol`, naturally deduplicates on redefine
- It's only populated in REPL mode — no overhead for batch/link
- `impl` sexps should be stored as `ModuleEntry::TraitImpl` on the symbol
  table (like constrained/generic functions), since impls are already first-class
  module entries. This was designed in Sprint 51 (`traitimpl-symbol-table.md`).
  The sexp field just needs to be added to the existing variant.

### 2.2 Structural Metadata

The regenerator also needs module structural data (imports, exports, mod decls,
platform specs). `ModuleStructure` already holds exactly these fields and lives
on SharedState. Use it directly — do NOT create a new type (per /arch review:
a parallel struct would duplicate data and create a sync hazard).

If `ModuleStructure` is currently discarded after compilation, retain it on
SharedState. The REPL import handler appends to the existing
`ModuleStructure.import_specs` for the current module.

### 2.3 Source in Cache Metadata (§15.4.6)

The `.meta.json` file must include all source text needed for regeneration.
The sexps on symbol table entries (TypeDef, TraitDecl, Macro, TraitImpl) are
already serialized via serde. Function sexps from Introspection are serialized
into the introspection section of meta.json. The `PersistenceRecord` fields
must also be serialized.

No separate "source text" field is needed — the sexp + structural metadata
IS the source for regeneration.

## 3. Atomic Write Mechanism

### 3.1 Write Procedure

```
1. Generate source text via generate_module_source()
2. Compute SHA-256 hash of the generated text
3. Write to {file_path}.tmp
4. fsync the temp file
5. rename {file_path}.tmp → {file_path}
6. Update content_hash on the module's cached state to the new hash
```

The temp file lives in the same directory as the target to ensure rename is
atomic (same filesystem). The `.tmp` extension is filtered out by the file
watcher event handler (per `repl-lifecycle.md` §1.3).

### 3.2 File Path

The backing file path is determined by the module's `file_path` on
`TypecheckProduct`. For the entry module this is
`{project_root}/{entry_module}.cl`. For other modules the user has navigated
to via `/mod`, it is their existing source file path.

The regenerator writes to whichever module received the definition.

### 3.3 Error Handling

If the write fails (disk full, permissions), print a warning to stderr and
continue the session. The in-memory state is the ground truth — the backing
file is a convenience, not a critical path. Do not abort the REPL on write
failure.

## 4. Watcher Self-Write Suppression

### 4.1 Mechanism: Content Hash Comparison

The file watcher already uses content-hash comparison before reloading
(per `repl-lifecycle.md` §1.3 and `watch.rs`). The regeneration flow
exploits this:

1. `regenerate_backing_file()` writes `user.cl` and updates the content hash
   in the watcher's `content_hashes` map to match the written content.
2. The watcher detects the file change event.
3. The watcher reads the file, computes its hash, and compares against the
   stored hash — they match.
4. The watcher skips reloading.

This is the same approach the sketch uses. It is race-free because:
- The hash is updated synchronously before `regenerate_backing_file()` returns.
- The watcher polls at the next prompt boundary (after regeneration completes).
- Even if the OS delivers multiple events for one write, each is individually
  hash-checked and skipped.

### 4.2 Implementation Detail

`regenerate_backing_file()` must call `self.watcher.update_hash(path, hash)`
after the atomic write. The `FileWatcher` needs a public method:

```rust
impl FileWatcher {
    pub fn update_hash(&mut self, path: &Path, hash: String) {
        if let Ok(canonical) = path.canonicalize() {
            self.content_hashes.insert(canonical, hash);
        }
    }
}
```

### 4.3 External Edits

When the user edits `user.cl` in an external editor:
1. The watcher detects the change.
2. Content hash comparison shows a mismatch (external edit changed the content).
3. Normal reload triggers: re-read, re-parse, re-typecheck, re-compile.
4. The reloaded module's sexp data replaces the REPL's in-memory state.
5. No regeneration fires — the file is already on disk.

This unifies interactive and file-based development (§15.3).

## 5. Startup Restore Flow

### 5.1 Entry Module Has Backing File

When `{project_root}/{entry_module}.cl` exists at startup:

1. Build the module graph from the entry module file (normal batch pipeline).
2. If a cache hit exists, load from `.o` + `.meta.json` (fast restore).
3. If no cache, compile from source (slower but correct).
4. Set `current_module` to the entry module path.
5. Register the watcher for the backing file's directory.

The module graph pipeline handles this identically to batch `--run` — no
special REPL restore path. The prelude is loaded first (if enabled), then
the entry module, which may import other modules.

### 5.2 No Backing File (Fresh Session)

When no backing file exists:

1. Create a fresh `SymbolTable` for the entry module.
2. Set `file_path` on `TypecheckProduct` to `{project_root}/{entry_module}.cl`
   even though the file doesn't exist yet. This ensures `regenerate_backing_file()`
   knows where to write when the first definition is entered.
3. The backing file is created on the first definition (first regeneration).

### 5.3 Restore Failure

If the backing file exists but fails to load (parse error, type error from
external edit):

1. Print a warning: `Warning: failed to load {entry_module}.cl: {error}`.
2. Start with an empty module (same as fresh session).
3. Do NOT delete the file — the user may want to fix it externally.
4. The watcher monitors the file. When fixed, normal reload applies.

## 6. Redefinition Handling

### 6.1 Stateless Regeneration

The regenerator is **stateless** — it reads the current `SymbolTable` and
structural metadata at regeneration time. It does not track a history of
definitions.

When the user redefines a name:
1. `eval()` updates the `SymbolTable` entry (replacing the old one).
2. `Introspection.sexp` is overwritten with the new sexp.
3. `regenerate_backing_file()` reads the current state — only the latest
   definition exists.

The backing file naturally contains no duplicates because the symbol table
is a `HashMap<Symbol, ModuleEntry>` — each name maps to exactly one entry.

### 6.2 Import Deduplication

If the user enters `(import [core [foo]])` twice, the `import_specs` list
will contain two entries. The regenerator merges imports by module path:
- Duplicate specific imports → deduplicate names.
- Specific + glob for the same module → glob wins.

This produces a clean `(import ...)` form in the output.

## 7. Sketch Comparison

| Aspect | Sketch | Reimplementation | Rationale |
|---|---|---|---|
| Approach | Full regeneration from symbol table | **Same** | Proven correct, pure function, testable |
| Save trigger | After each definition | **Same** | Simple, safe, crash-resilient |
| Atomic write | temp + rename | **Same** | Standard pattern |
| Watcher suppression | Content-hash comparison | **Same** | Already designed in `repl-lifecycle.md` |
| Sexp storage (fns) | `ModuleEntry::Def.codegen.sexp` | `Introspection.sexp` on SharedState | Decomposed architecture — sexp not on symbol table |
| Sexp storage (types/traits/macros) | `ModuleEntry` variants | **Same** | Already present |
| Sexp storage (impls) | `CompiledModule.impl_sexps` | `ModuleEntry::TraitImpl.sexp` | First-class module entry, like other definitions |
| Module structural data | `CompiledModule` fields | `PersistenceRecord` on SharedState | REPL-only, avoids polluting TypecheckProduct |
| Scope | Entry module only | **Any current module** | User may `/mod` to another module and define there |
| Dependency ordering | Sexp scanning for symbol refs | **Callee list** on `ModuleEntry` (Decision 21) | Pre-computed during typechecking, more reliable |
| Qualification | `qualify_sexp()` at save time | **Not needed** — stored sexps preserve original form | Simpler: no name resolution at save time |
| Code location | `repl/save.rs` | `src/save.rs` (binary crate, flat) | No nested `repl/` subdir in reimplementation src |
| Startup restore | `ModuleGraph::build(user.cl)` | Normal batch pipeline | Same — entry module loaded via module graph |

### Divergence: No `qualify_sexp()`

The sketch stores unqualified sexps and qualifies at save time via
`tc.qualify_name()`. The reimplementation stores the **original sexp as the
user typed it** — if they wrote `Some`, it stays `Some`; if they wrote
`core.option/Some`, it stays qualified. This satisfies §15.4.3 (symbol
qualification preservation) without any name resolution at save time.

This means the regenerator is a pure formatter: it reads stored sexps and
structural metadata, orders them, and pretty-prints. No typecheck state needed.

## 8. Code Location and Dependencies

### 8.1 New Module

`src/save.rs` — a top-level module in the binary crate containing:
- `generate_module_source()`: pure function, reads data, returns `String`.
- `atomic_write()`: writes temp file + rename.
- `regenerate_backing_file()`: method on `CompilerSession`, orchestrates the
  above.

### 8.2 Data Dependencies

`generate_module_source()` needs:

| Data | Source | Access |
|---|---|---|
| Types, traits, macros, constructors, impls | `shared.symbol_tables[module]` | DashMap read |
| Function/defn sexps | `shared.introspection[fq_symbol].sexp` | DashMap read |
| Callee list (for ordering) | `ModuleEntry::Def.callees` | via symbol table |
| Import specs | `shared.module_structures[module].import_specs` | DashMap read |
| Export specs | `shared.module_structures[module].export_specs` | DashMap read |
| Mod decls | `shared.module_structures[module].mod_decls` | DashMap read |
| Platform specs | `shared.module_structures[module].platform_specs` | DashMap read |
| File path | `shared.typecheck_products[module].file_path` | DashMap read |

All reads are from `SharedState` which `CompilerSession` already holds via
`Arc<SharedState>`. No new inter-crate dependencies.

### 8.3 Sexp Formatting

`Sexp::format_indented()` is needed for pretty-printing. This method must
exist on the `Sexp` type in `cranelisp-types` (or `cranelisp-frontend`).
The sketch has this. If the reimplementation's `Sexp` lacks it, it needs to
be added as a prerequisite.

## 9. Implementation Prerequisites

Before implementing session persistence:

1. **Source/sexp field audit**: Review all sexp/source fields across
   `ModuleEntry`, `Introspection`, `TypecheckProduct`, and any other
   SharedState structures. Consolidate to one copy per definition in the
   right place (see §2.1). Specifically:
   - Verify `Introspection.sexp` is populated for all defn kinds
   - Add `sexp` field to `ModuleEntry::TraitImpl` for impl storage
   - Ensure types/traits/macros sexps stay on symbol table (already there)

2. **ModuleStructure retention**: Ensure `ModuleStructure` is retained on
   SharedState after compilation (not discarded). It already holds the
   structural metadata the regenerator needs. In REPL mode, the import
   handler must append to the existing `ModuleStructure.import_specs`.

3. **`ModuleEntry::TraitImpl` in interfaces.md**: Update `interfaces.md` to
   add the `TraitImpl` variant (with `sexp: Option<Sexp>` field) per the
   `traitimpl-symbol-table.md` design. FIXME(/arch) filed.

4. **`Sexp::format_indented()`**: Ensure the method exists and handles all
   sexp variants correctly (including type annotations, bracket forms, etc.).

5. **REPL import tracking**: When the REPL processes `(import ...)`, the
   import spec must be appended to the current module's `ModuleStructure`.
   Currently imports are processed and installed as `ModuleEntry::Import`
   but the original spec may not be retained.
