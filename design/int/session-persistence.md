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
| `impl` | no sexp field anywhere | verbatim `source` at the defining turn (§12) | **gap — closed by §12 via introspection, NOT a new sexp field** |

> **§2.1 amendment (S113, RT-4).** The "impl needs an `sexp` field on `ModuleEntry::TraitImpl`" prerequisite (§9.1, and Option B below) is **superseded for regen** by §12: the impl form's **verbatim source is already captured** in the REPL introspection map at the defining turn (`eval::record_defining_turn_source`, keyed `FQSymbol{writer_module, "Trait.Type"}`), on identical terms to how `deftrait`/`deftype` REPL-defined decls are captured (the `(None, Some(source))` arm of `emit_decl_or_source`). The regen fix reads that record; it needs **no `cranelisp-types` change and no schema bump** — it stays inside the W4 binary surface. The one case introspection does NOT cover is cache-restore-then-regen (introspection is REPL-only) — the single named edge in §12.4, where a cache-surviving `sexp`-on-shell would be an S114 `/arch` follow-on. Do **not** add the field speculatively (Principle 6/8).

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

---

## 10. `(mod …)` extraction write path — lib-dir-relative, not CWD (FIXME 0423)

### 10.1 Root cause

`(mod name form…)` extraction (spec §8.2.2 step 1) writes the inline body to a
child backing file `{parent_dir}/{stem}/{name}.cl`. The pre-S88 writer computed
`{parent_dir}` by joining `project_root` to the dotted module path. But
`project_root` is the *process CWD* for a run-from-elsewhere invocation (e.g. the
in-language stdlib self-test runner launched from the repo root rather than from
inside `stdlib/`). For a **lib-dir** module (`stdlib/num/int.cl`) the parent's real
on-disk directory is under `stdlib/`, not under the CWD — so the writer emitted
stray `./num/int/test.cl` (and `./collections/`, `./compare/`, `./fn/`, `./text/`)
trees at the repo root, mirroring the lib layout but holding only `…/test.cl`
bodies. 14 such files were accidentally committed in the S87 checkpoint; the
interim band-aid was a `.gitignore` entry. The write was non-destructive but rotted
the repo root — concrete evidence the CWD-relative write happens.

**Secondary symptom (same regen path):** the regen pretty-printer emitted
`: (Option String)` (space after the colon) where the source has `:(Option String)`
— violating the "`:Type` binds the immediately-following form with NO space"
reader-macro semantics (`memory/annotation-reader-macro-binds-following-form`).

### 10.2 Chosen approach (landed S88, commit 5833bd1)

The fix is the FIXME 0423 resolution, in `src/process_form/dependency.rs::
write_inline_mod_to_disk`:

1. **Resolve the backing-file directory against the PARENT module's own on-disk
   file**, located via the same `pipeline::resolve_module_file(parent_module,
   project_root, lib_dirs)` rules the loader uses (project-root, then lib-dirs).
   The backing dir is `{parent_file.parent()}/{parent_stem}/` — for a lib-dir
   parent that lands under `stdlib/`, independent of CWD. Only when the parent
   file cannot be located (it always should — it is what declared the `(mod …)`)
   does it fall back to `project_root.join(dotted_path)` so the run is not blocked.
2. **Prefer recognizing an existing extraction-stable backing file** over
   re-emitting it: `if file_path.is_file() { return Ok(()); }` — the
   hand-authored / previously-extracted `stdlib/` copy is canonical and read, not
   rewritten (FIXME 0423 point 2).
3. **Annotation spacing fixed** in `save.rs` — `render_decl_flat` /
   `render_children_flat` / `render_decl_sexp_indented` suppress the separator
   *after* a bare `:` colon marker so `:Type` binds its following form with no
   space, both flat and at line breaks (FIXME 0423 point 3).

The signature carries `lib_dirs: &[PathBuf]` (threaded from `ModuleCompiler`) so
resolution is lib-dir-aware; the function is a pure-ish FS writer with a clear
fallback, fitting `src/CLAUDE.md` testability discipline.

### 10.3 `/dev` acceptance (the unit test still owed)

The source fix landed in S88; **no unit test guards it yet** — this is the owed
`/dev` acceptance:

- **Unit (`dependency.rs` `#[cfg(test)]`):** set up a tmpdir with a lib-dir
  `lib/accum.cl` parent and a `project_root` (= CWD analogue) that is a *different*
  tmpdir. Call `write_inline_mod_to_disk(parent="accum", name="test", body, project_root, lib_dirs=[lib_dir])` and assert (a) the backing file appears at
  `{lib_dir}/accum/test.cl` (next to the parent), and (b) **no** stray file is
  created under `project_root` — the regression guard for the CWD-relative bug.
- **Unit (recognize-existing):** with an extraction-stable `{lib_dir}/accum/test.cl`
  already present, the call is a no-op (`Ok(())`) and the existing file is
  byte-identical (not rewritten) — FIXME 0423 point 2.
- **Unit (annotation spacing, `save.rs`):** a stored sexp carrying a compound
  type annotation round-trips through `render_decl_sexp` as `:(Option String)`
  (no space), never `: (Option String)` — FIXME 0423 point 3. (May already be
  covered by the existing colon-binding tests in `save.rs`; if so, cite them.)

The `.gitignore` band-aid for `/collections/ /compare/ /fn/ /num/ /text/` at the
repo root may be retired once the unit test is the durable guard (`/dev`+`/qa`
call at landing).

Principle citations: **Principle 7 (single source of truth)** — the writer
resolves through the *same* `resolve_module_file` the loader uses, not a parallel
path computation. **Principle 5 (testability is structural)** — the writer takes
`project_root` + `lib_dirs` as parameters, so the CWD-independence is unit-testable
without changing the process CWD.

---

## 11. `set-doc` docstring-into-source regen (FIXME 0430) — RATIFIED (S94)

**Status: RATIFIED (S94 `/design`).** Candidate 1 (docstring-aware `render_decl_sexp`)
is the contract `/dev` re-lands against; the reconciliation rule (§11.3a) is settled.
This closes the `/design` half of FIXME 0430. The `/dev` re-land of the S89-W3-removed
`set-doc` Document-write surface + the `/qa` e2e are a future agent-write wave (§11.4);
the FIXME stays open until that lands (the design ratification is its precondition, not
its closure — `/sprint` may carry it to the re-land wave).

### 11.1 The gap

`set-doc <symbol> <text>` (Document mode, descoped S89 W3) set the live
`ModuleEntry::Def.docstring` field. But the regen path
(`save::generate_fns_and_macros` → `render_decl_sexp`) re-renders each def from its
**stored sexp** (sourced from the `Introspection` record, or `macro_sexp` for
macros) and **never reads the live `docstring` field**. A spec §5.12 docstring is
syntactically a string literal *inside* the `defn` form
(`(defn name "doc" params body)`), so the stored sexp carries whatever docstring the
def was *authored* with — not a later `set-doc` edit. Result: a `set-doc` edit
vanishes on session restart (regen re-emits the stale/absent docstring from the
stored sexp), breaking §17.15.3's durable-memory promise. A non-persisting
half-feature is worse than none — hence the S89 descope.

`set-preamble` (the Document keystone) IS correct: its edit is a byte-stable
section-0 round-trip (`save::apply_preamble_edit`) the regen path honours. Only the
**docstring** facet lacks a persistence path.

### 11.2 The two candidate designs

**Option 1 — docstring-aware `render_decl_sexp`.** Teach `generate_fns_and_macros`
to thread the entry's live `Def.docstring` into rendering: after selecting the
stored sexp for a `UserFn`, if `entry.docstring` is `Some`, **splice/replace** the
docstring slot in the rendered `defn` form (insert a string literal between the
name and the params, or replace an existing leading string literal). The live field
becomes canonical for the emitted docstring; the stored sexp supplies everything
else (params, body, attached comments).

- *Pro:* the live `Def.docstring` is the single source of truth (matches the
  module.rs canonical-field comment: "the entry's own `docstring` field is canonical
  for that metadata" — Principle 7). One edit point; the stored sexp stays a pure
  capture of authored source and is never mutated.
- *Con:* `render_decl_sexp` (currently sexp-pure — `&Sexp -> String`) must take an
  extra `docstring: Option<&str>` argument and learn the §5.12 docstring slot
  position (between name and params for single-sig; between name and first variant
  for multi-sig). It must distinguish "first string child IS a docstring" from "first
  string child is a body string expression" — the parser already encodes this
  (a leading string in the docstring slot is the docstring), so the renderer mirrors
  the parser's slot rule. Modest renderer complexity.

**Option 2 — re-inject at edit time.** At `set-doc` apply time
(`apply_docstring_edit`, to be re-landed), rewrite the def's **stored sexp** to
carry the new docstring (insert/replace the string literal in the `defn` form), so
the existing sexp-based regen path picks it up unchanged.

- *Pro:* `render_decl_sexp` and `generate_fns_and_macros` stay untouched — zero
  regen-path change.
- *Con:* mutates stored AST (the `Introspection` record / `macro_sexp`), making the
  stored sexp no longer a faithful capture of authored source — two writers of the
  same field (original load + `set-doc` re-inject), drifting from Principle 7. The
  splice logic (find/replace the docstring slot in a `Sexp::List`) lives at edit
  time *and* must handle the same slot-position cases as Option 1 — so it is not
  actually simpler, just relocated, and it loses the "stored sexp == source" invariant
  that the regen path and `/source` both rely on.

### 11.3 RATIFIED — Option 1 (docstring-aware render)

**Option 1 is ratified as the renderer contract.** Rationale:

1. **Single source of truth (Principle 7).** `Def.docstring` is *already* declared
   canonical for the docstring metadata (module.rs §"narrowed from Defn"). Option 1
   makes regen *read* that canonical field; Option 2 creates a second writer of the
   stored sexp and lets the canonical field and the stored sexp disagree.
2. **Stored-sexp invariant preserved.** The regen path, `/source`, and the
   on-demand macro-clause recompile all treat the stored sexp as a faithful capture
   of authored source. Option 2 violates that; Option 1 keeps it.
3. **The slot logic is required either way** — Option 2 does not avoid it, only
   moves it to a worse place (edit-time mutation vs. render-time read).
4. **Symmetry with `set-preamble`.** The preamble keystone persists by having the
   regen path *read* the live `module_preamble` field at section-0 generation. A
   docstring-aware renderer makes `set-doc` persist by the *same shape* — regen reads
   the live field — rather than a one-off stored-AST rewrite.

### 11.3a The ratified renderer contract (what `/dev` re-lands against)

The contract `/dev` implements, stated precisely so the re-land is unambiguous:

1. **`generate_fns_and_macros` threads the live docstring.** The loop already holds the
   `(name, entry)` pair (`src/save.rs::generate_fns_and_macros`). For a
   `ModuleEntry::Def { kind: DefKind::UserFn, docstring, .. }` it passes
   `docstring.as_deref()` (`Option<&str>`) alongside the selected stored sexp into the
   renderer. (Macros: out of scope for S94 — a `defmacro` has no `set-doc` surface;
   pass `None`.)

2. **`render_decl_sexp` gains one optional argument** —
   `render_decl_sexp(sexp: &Sexp, docstring: Option<&str>) -> String`. All existing
   call sites pass `None` (mechanical; the colon-binding round-trip is unchanged). The
   renderer, when `docstring` is `Some`, emits/replaces the §5.12 docstring slot in the
   `defn` form: a string literal between the function **name** and the **param vector**
   (single-sig), or between the name and the **first variant** (multi-sig). It
   distinguishes "first string child IS a docstring" (the §5.12 slot) from "first
   string child is a body expression" using the parser's slot rule (a leading string in
   the docstring slot is the docstring) — the renderer mirrors the parser, it does not
   invent a new rule.

3. **The reconciliation rule (§11.3a — the one question the 0430 `/dev` assessment
   flagged): the live `Def.docstring` is AUTHORITATIVE.**
   - `docstring == Some(text)` ⇒ emit `text` in the §5.12 slot, and **drop any
     docstring already embedded in the stored sexp** (from the original
     `(defn name "old" …)` source) so the form never carries two docstrings.
   - `docstring == None` ⇒ emit the stored sexp's own docstring **if it has one**
     (a def authored with a docstring but never `set-doc`'d round-trips its original
     docstring), and emit **no** string literal if it does not (no spurious empty
     docstring — Option 1 is a strict no-op when there is nothing to inject).

   This makes `set-doc` → restart → `/doc` round-trip the live edit (the §17.15.3
   durable promise) with **no double-docstring hazard**, and leaves a never-edited def
   byte-identical to today.

4. **Stored sexp stays a faithful source capture.** The renderer *reads* the live field;
   it does **not** mutate the `Introspection` record or `macro_sexp`. `/source` and the
   on-demand macro-clause recompile continue to see the authored sexp unchanged
   (Principle 7 — one writer of the docstring metadata: `set-doc` → `Def.docstring`).

### 11.4 `/dev` acceptance (the re-land, a later sprint)

This section closes the DESIGN half of 0430; the `/dev` re-land follows a later
sprint. The acceptance the re-land must meet:

- **e2e (the keystone):** in a REPL session, `set-doc <symbol> "new doc"`, then
  restart the session against the regenerated backing file, then `/doc <symbol>`
  shows `"new doc"` — the §17.15.3 durable promise `set-preamble` already satisfies.
- **Unit (regen reads live field — `save.rs`):** `generate_fns_and_macros` (or
  `render_decl_sexp` directly) over a `Def.docstring = Some("new doc")` with a stored
  sexp that has **no** docstring emits a `defn` form carrying `"new doc"` in the §5.12
  slot.
- **Unit (reconcile arm — the §11.3a rule):** stored sexp **already carries** a
  docstring (`(defn f "old" [x] …)`) **and** `Def.docstring = Some("new doc")` ⇒ the
  emitted form carries **`"new doc"` only** — the `"old"` is dropped, exactly one
  docstring, never two. This is the load-bearing reconciliation test the 0430 `/dev`
  assessment asked `/design` to settle.
- **Unit (live `None`, sexp has docstring):** `Def.docstring = None` with a stored
  sexp that has a docstring ⇒ the sexp's own docstring round-trips unchanged (a
  never-`set-doc`'d def keeps its authored docstring).
- **Unit (round-trip):** the emitted `defn` re-parses with the docstring in the right
  slot (no double docstring, no body-string confusion) for both single-sig and
  multi-sig defns.
- **Unit (no-docstring unchanged):** `Def.docstring = None` with a stored sexp that
  has **no** docstring emits the `defn` exactly as before (no spurious empty string
  literal) — Option 1 is a strict no-op when there is nothing to inject; the existing
  colon-binding tests stay green.

Principle citations: **Principle 7 (single source of truth)** — regen reads the
canonical `Def.docstring`; the stored sexp stays a faithful source capture.
**Principle 6 (complexity has a budget)** — the renderer gains one optional slot
argument + the §5.12 slot rule (already encoded in the parser), not a new edit-time
mutation path.

---

## 12. `impl` regeneration — the RT-4 impl-source data-loss close (S113 W4)

**Status: DESIGN (S113 Phase 3, `/design`(src/)).** Closes the RT-4 ×2 pins
(`tests/repl_persist.rs::impl_regen_written_to_user_cl` +
`impl_dispatches_after_restart_without_cache`, `class=enumeration-miss`, data-loss
class). `/dev`(src/) implements in W4; `/review` checks against the
enumeration-completeness discipline (`design/arch/resolve-home-enumeration.md` §3).
Arch seam flag iv: root the design in the **D45-as-amended** storage model.

### 12.1 Root-cause verdict — the enumeration site that drops the family

The drop site is **`generate_impls` in `src/save.rs:723`**, a literal stub:

```rust
fn generate_impls(st: &crate::code::SessionSymbolTable) -> String {
    // TraitImpl entries currently don't have an sexp field (see §2.1 gap).
    // For now, skip impl regeneration …
    let _ = st;
    String::new()      // ← the whole `impl` section is silently skipped
}
```

Section 7 of `generate_module_source` (§1.3) calls it, gets `""`, and the
`if !impl_section.is_empty()` guard drops the section. So **every** `impl` — the
whole persisted-content kind — is unconditionally absent from the regenerated
`.cl`. This is precisely the illegal skip `resolve-home-enumeration.md` §3 rule 2
forbids: a whole *source kind* marked "complete" by producing zero rows for a
reason that is **not** a legal row-less outcome ("no sexp field yet" is
"someone/something else should own this", never an empty-module skip). It is the
inconsistent-resurrection face — `deftrait`/`deftype`/`defn` survive regen (they
have working section generators), `impl` vanishes.

**Compounding gap (now dissolved):** §2.1 recorded "impl — no sexp field
anywhere" as the reason for the stub. The `/design`(src/) re-investigation
(S113) finds the impl form's **verbatim source is already captured** — the impl
defining turn produces `EvalResult::Def { symbol: FQSymbol{module, "Trait.Type"},
defined: true }` (`eval.rs:552,567` — the label is `format!("{}.{}",
trait_name.name, impl_echo_type_name(t))`), which `record_defining_turn_source`
(`eval.rs:38`) writes into introspection as `source`. So the render source exists
on identical terms to a REPL-defined `deftrait`/`deftype` (the `(None,
Some(source))` arm of `emit_decl_or_source`, §"generate_traits"). The stub is not
blocked on a missing field; it was never wired.

### 12.2 The D45-amended storage model the fix roots in

Under Decision 45 **as amended** (`design/arch/backend-keyed-consumer.md` §1.1.1;
`traits.md` §1.3): for an impl **written in module M**,

- the **`TraitImpl` shell** (the discovery/metadata entry, key
  `impl${FQType}${FQTrait}`) lives at the **trait's defining module's** table,
  carrying `impl_module = M` (the writer back-pointer);
- the **mangled method `Def`s** (`dp$W`, with their GOT slots) live at **M's own
  table** (the writer's module — structurally forced by `compile_to_module`);
- the impl form's **verbatim source** lives in M's introspection under
  `FQSymbol{M, "Trait.Type"}`.

The consequence for enumeration: **"the impls written in M" is NOT "the shells in
M's table."** M's table holds shells only for traits **homed in M**; a shell in M
with `impl_module = N` is an impl of M's trait written *elsewhere* (belongs in
N's regen, not M's). This is the completeness decomposition the fix must honour.

### 12.3 The fix — enumerate the impls written in M, render from the defining-turn source

`generate_impls` gains the introspection map + `module_path`, mirroring
`generate_traits`/`generate_types` exactly (**one reader per kind**, Principle 7):

```rust
fn generate_impls(
    st: &SessionSymbolTable,
    introspection: Option<&DashMap<FQSymbol, Introspection>>,
    module_path: &ModuleFullPath,
) -> String
```

**Completeness requirement (binding on `/dev` + `/review`).** The set "impls
written in M" decomposes into three sources; the enumeration lands a row for the
first two and *legally* excludes the third:

| Source | Reached via | Disposition |
|---|---|---|
| impl of an **M-homed** trait, written in M | `st`'s `TraitImpl` shells filtered `impl_module == module_path` | **row** — the RT-4 pins live here (trait `Disp` + impl both in `user`) |
| impl of an **imported** trait, written in M | introspection keys `FQSymbol{M, "Trait.Type"}` whose shell is at the trait's home (not in `st`) | **row** — the §12.4 union backstop |
| impl of an **M-homed** trait, written in **N** | `st` shell with `impl_module == N` | **legal exclusion** — belongs to N's regen (its own `impl_module == N` scan) |

For each enumerated impl, the render key is reconstructed from the shell as
`format!("{}.{}", trait_name.name, impl_type.name)` — which equals the
`record_defining_turn_source` key, because `impl_type` is the **settled effective
target** and `impl_echo_type_name` extracts that same settled name (conventional:
the bare target head; HKT: the constructor argument — both verified equal to
`impl_type.name`, `eval.rs:75` rustdoc). Fetch `(sexp, source)` via
`introspection_sexp_and_source` and emit via `emit_decl_or_source` — the **same
re-parse-gated reader** the decl sections use, so a stale/garbage source can never
corrupt the file (it is skipped, per `sexp_matches_source`). Sort by
`(trait, type)` for deterministic output.

Recommended single-reader shape (Principle 7, strongest completeness): drive the
enumeration from the **introspection impl-label records in M** (which cover BOTH
written-in-M sub-cases in one reader) and cross-check liveness against a resolvable
shell where the symbol-table reach is available; the `st`-shell-filtered form above
is the concrete path for the pinned local case and is the minimum W4 must ship.
`/dev` picks the cleaner implementation; the **completeness requirement — every
written-in-M impl contributes a row or a legal exclusion — is the acceptance**, not
the specific traversal.

### 12.3.1 The fail-loud guard (arch-directed: a later-added kind must not silently skip)

The stub is dangerous precisely because a whole kind disappeared **silently**.
The fix installs a section-completeness `debug_assert!` in `generate_module_source`
(the R7 "assertion density" discipline applied to regen): after the eight section
generators run, sweep `st.all_symbols()` and assert **every persisted-content
entry kind is claimed by exactly one section generator** — `TraitDecl`→traits,
`TypeDef`/product-ctor→types, `TraitImpl`(with `impl_module == module_path`)→impls,
`UserFn`/`Macro`→fns — and any entry of a persisted kind NOT claimed trips the
assert (with `MODULE_TRACE` emit in release). Non-persisted kinds
(`Import`/`Reexport`/`Ambiguous`/mangled `$`-names/`__expr`/primitives/ctors that
ride their type) are the enumerated *legal* exclusions, listed in the guard so the
exclusion is deliberate, not accidental. This converts "a future persisted kind
silently dropped from regen" from a silent data-loss into a loud test/CI failure —
the structural close the RT-4 class asks for (Principle 18).

### 12.4 The one named edge — cache-restore-then-regen (parked, S114 `/arch`)

Introspection is **REPL-only** (absent on cache restore). If a session
cache-restores a module carrying impls (introspection empty) and *then*
regenerates (a later definition turn triggers `regenerate_backing_file`), the
impl-source records are gone and the impls would drop again — the SAME shape the
macro path solved by storing a cache-surviving `macro_sexp` on the entry. The
durable cure is a cache-surviving impl source: an `sexp: Option<Sexp>` on the
`TraitImpl` shell (the §2.1 Option B / §9.1 prerequisite — a `cranelisp-types`
change + schema bump, `/arch`-gated). **This edge is NOT hit by the RT-4 pins**
(session 1 is a fresh REPL — introspection present at regen; session 2 reads the
already-regenerated `.cl`, no re-regen). Per "document movable boundaries
decisively, then park": named as a PS-RT4 matrix row (persisted-kind × survives
cache-restore-then-regen), dispositioned as an S114 `/arch` follow-on, **not built
this sprint** (Principle 8 — no interface ahead of a forcing scenario). If W1's
PS-RT4 matrix surfaces a pin in this cell, it re-opens as an `/arch` FIXME.

### 12.5 Testability (Principle 5) — the PS-RT4 enumeration matrix

`/qa`'s PS-RT4 acceptance is a persisted-content matrix, not the two pins alone:
every persisted kind (`defn`/`deftype`/`deftrait`/`impl` conventional/`impl`
HKT/`defmacro`) × {survives regen, survives schema-bump-or-no-cache restore},
with the conventional-impl-vs-HKT-impl **twin** (same invariant, two impl shapes,
same assertion — a divergence names the shape that grew its own path). The fix's
`generate_impls` is a pure `(st, introspection, module_path) → String`, unit-
testable with no session (mirrors the existing `merge_imports_*` unit tier).

Principle citations: **Principle 7** — `generate_impls` reuses the one
`introspection_sexp_and_source` + `emit_decl_or_source` reader every decl section
uses; no impl-specific render path. **Principle 18** — the completeness
`debug_assert!` enforces "every persisted kind is claimed" where the sections are
assembled. **Principle 26** — the render key is reconstructed from the **settled**
`TraitImpl.impl_type`, not re-derived from surface syntax (the `impl_echo_type_name`
precedent).
