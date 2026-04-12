# Macro Resolver Design

**Sprint**: 50 (stabilisation)
**Status**: Design
**Owner**: /arch
**Implementors**: /frontend (trait), /int (impls), /typecheck (ensure_module_exists)

## 1. Problem Statement

The Sprint 49 session restructure replaced a flat JIT code pointer store with per-module `DashMap<ModuleFullPath, CodegenProduct>`. This broke macro expansion because the store and lookup disagree on the module key:

- **Store side**: `compile_macro_clause_inline` (worker.rs:1701) compiles a macro clause and registers the code pointer under `ctx.tc.current_module_path()` — the module currently being compiled, not necessarily the module that defined the macro.
- **Lookup side**: `build_persistent_macro_entries` (worker.rs:1993) follows Import/Reexport chains to find the **defining module**, then looks up code pointers there.

When module A imports a macro from module B, compilation happens while processing A (current module = A), so the code pointer lands in A's `CodegenProduct`. But lookup follows the import to B and searches B's `CodegenProduct` — miss.

Three redundant caches exacerbate the problem:

1. **`macro_names: Vec<String>`** — pre-built list for `sexp_contains_macro_call` scanning, assembled by `collect_persistent_macro_names` (worker.rs:1872) with hardcoded 2-hop Import→Reexport chain walking.
2. **`macro_infos: Vec<(Symbol, DefmacroInfo, Sexp)>`** — current-module defmacro definitions threaded through `pass2_check_bodies_with_expansion`.
3. **`HashMap<Symbol, MacroEntry>`** — assembled by `build_all_macro_entries` + `build_persistent_macro_entries`, combining current-module and persistent macros into a flat map for `expand_sexp_recursive`.

All three duplicate information already present in the symbol table (`ModuleEntry::Macro`) and codegen products (`CodegenProduct.code`). The caches were a reasonable design when code pointers lived in a single flat JIT namespace, but the per-module DashMap restructure invalidated their assumptions.

## 2. Target Architecture

Replace the pre-built cache layer with a `MacroResolver` trait that walks the symbol table on demand during expansion.

### Trait definition (in `expander.rs`)

```rust
/// Resolve a macro name to its compiled entry, if it exists.
///
/// Implementations walk the symbol table, follow Import/Reexport chains,
/// and optionally compile uncompiled macros on demand.
pub(crate) trait MacroResolver {
    /// Look up a macro by bare name in the current module's symbol table.
    ///
    /// Returns `Ok(Some(entry))` if the name resolves to a compiled macro,
    /// `Ok(None)` if the name is not a macro, or `Err` on compilation failure.
    fn resolve_macro(
        &mut self,
        name: &str,
        span: Span,
    ) -> Result<Option<MacroEntry>, CranelispError>;
}
```

### `expand_sexp_recursive` signature change

```rust
pub(crate) fn expand_sexp_recursive(
    sexp: Sexp,
    resolver: &mut dyn MacroResolver,
    depth: usize,
) -> Result<Sexp, CranelispError>
```

The `&HashMap<Symbol, MacroEntry>` parameter is replaced by `&mut dyn MacroResolver`. The expansion loop calls `resolver.resolve_macro(name, span)` instead of `macros.contains_key(name)` / `macros.get(name)`.

### `SymbolTableMacroResolver` (in `worker.rs`)

The production resolver for Pass 2 expansion and REPL eval. Performs on-demand compilation.

**Algorithm for `resolve_macro(name, span)`:**

1. Look up `name` in the current module's symbol table.
2. If not found, return `Ok(None)`.
3. If `ModuleEntry::Macro { .. }` — defining module is the current module.
4. If `ModuleEntry::Import { source }` — follow the chain recursively:
   - Look up `source.symbol` in `source.module`'s table.
   - If `ModuleEntry::Macro` — defining module is `source.module`.
   - If `ModuleEntry::Reexport { source: re }` — continue recursively with `re`.
   - If anything else or not found — return `Ok(None)`.
   - **Depth limit**: 16 hops. Return error if exceeded (prevents circular Import/Reexport loops).
5. Once defining module is known, check `codegen_products.get(&defining_module)` for all clause code pointers (`__macro_{name}_clause_{idx}`).
6. If all clauses compiled — build and return `MacroEntry`.
7. If any clause missing — compile on demand via `compile_macro_if_needed` with `target_module = defining_module`, then return the entry.

**Chain walker** (shared helper, not hardcoded 2-hop):

```rust
/// Follow Import/Reexport chains to find the defining module and
/// MacroClauseInfo for a macro name.
///
/// Returns (defining_module, clauses, docstring) or None if the
/// name does not resolve to a macro.
fn resolve_macro_definition(
    tc: &cranelisp_typecheck::TypeChecker,
    start_module: &ModuleFullPath,
    name: &str,
    max_depth: usize,
) -> Option<(ModuleFullPath, Vec<MacroClauseInfo>, Option<String>)>
```

This replaces `resolve_macro_entry`, `resolve_macro_sexp`, and `collect_persistent_macro_names` with a single recursive walker.

**Struct fields** — the resolver holds shared references, not `&mut ModuleCompiler`:

The recommended approach for on-demand compilation is **NOT to use a compile queue**, but instead to extract expansion into a scoped function that can drop the resolver's borrows before compilation (see §5 Borrow Checker Design). The `compile_queue` approach is an **alternative only** — if the scoped extraction pattern is too complex to integrate, the queue pattern is a fallback. Details in `design/int/macro-resolver-impl.md` §3.

### `ReadOnlyMacroResolver` (in `session_v4.rs`)

For the `/expand` slash command. Same lookup logic as `SymbolTableMacroResolver` but never triggers compilation — if a macro is not already compiled, it returns `Ok(None)`.

```rust
struct ReadOnlyMacroResolver<'a> {
    tc: &'a cranelisp_typecheck::TypeChecker,
    codegen_products: &'a DashMap<ModuleFullPath, CodegenProduct>,
    current_module: ModuleFullPath,
}
```

## 3. What Gets Deleted

### From `expander.rs`

| Item | Reason |
|------|--------|
| `MacroEnv` struct + `impl` | Dead code — only used by unit tests. Production path uses worker functions. |
| `compile_single_clause` function | Only called by `MacroEnv::compile_macro`. Production uses `compile_macro_clause_inline`. |
| `MacroEnv` unit tests (`test_identity_macro`, `test_quasiquote_macro`, `test_multi_clause_dispatch`, `test_is_macro_predicate`, `test_quasiquote_bracket_macro`) | Test the dead `MacroEnv` path. Marshal round-trip tests (`test_marshal_roundtrip_all_variants`, `test_slist_roundtrip`) are preserved — they test `marshal.rs`, not `MacroEnv`. |

### From `worker.rs`

| Item | Reason |
|------|--------|
| `build_all_macro_entries` | Cache assembly — replaced by resolver |
| `build_persistent_macro_entries` | Cache assembly — replaced by resolver |
| `collect_persistent_macro_names` | Pre-scanning — replaced by resolver |
| `sexp_contains_macro_call` | Pre-scanning — no longer needed (resolver is called per-symbol during expansion) |
| `collect_called_macros` + `collect_called_macros_inner` | Pre-scanning — replaced by on-demand resolution |
| `resolve_macro_entry` | Hardcoded 2-hop chain walk — replaced by generic `resolve_macro_definition` |
| `resolve_macro_sexp` | Hardcoded 2-hop chain walk — replaced by generic `resolve_macro_definition` |
| `compile_persistent_macro_if_needed` | Merged into resolver's on-demand compilation path |
| `build_macro_entry_from_got` | Inlined into resolver's entry construction |

### From `session_v4.rs`

| Item | Reason |
|------|--------|
| `build_macro_map` | Replaced by `ReadOnlyMacroResolver` |

## 4. What Changes

### `compile_macro_if_needed` (worker.rs)

Gains `target_module: &ModuleFullPath` parameter. Currently uses `ctx.tc.current_module_path()` implicitly — this is the bug. The parameter makes the store key explicit. The defining module (from `resolve_macro_definition`) is passed as `target_module`.

### `compile_macro_clause_inline` (worker.rs)

Gains `target_module: &ModuleFullPath` parameter. Code pointer registration (`compile_and_register_defn_shared`) uses `target_module` instead of `ctx.tc.current_module_path()`. This ensures code pointers land in the defining module's `CodegenProduct`, where the resolver expects them.

### `pass2_check_bodies_with_expansion` (worker.rs)

Simplified — the `macro_infos` and `macro_names` plumbing is removed:
- No more `collect_persistent_macro_names` call at the top
- No more `macro_names` vector threading through the loop
- No more `name_refs` conversion per iteration
- The `FormKind::Regular` arm calls `process_regular_form` without `macro_infos` or `macro_names`

### `process_regular_form` (worker.rs)

Simplified signature — removes `macro_infos: &[...]` and `macro_names: &[&str]` parameters. Return type changes from `Vec<String>` to `()`. The function:
1. Creates a `SymbolTableMacroResolver` (or uses a scoped extraction pattern — see §5).
2. Calls `expand_sexp_recursive(sexp, &mut resolver, 0)`.
3. Handles any on-demand compilation from the resolver's queue.
4. New macros produced by expansion (const/def → defmacro) are registered in the symbol table via `register_macro_in_module` + `compile_macro_if_needed` with `target_module` — they become visible to the resolver for subsequent forms automatically.

### `try_expand_for_pass2` (worker.rs)

Eliminated entirely. Its logic (check-if-contains-macro → compile-macros → build-map → expand) is subsumed by the resolver pattern in `process_regular_form`.

### `expand_form_sexp` (session_v4.rs)

Uses `ReadOnlyMacroResolver` instead of `build_macro_map`:

```rust
fn expand_form_sexp(&self, form_src: &str) -> Result<Sexp, CranelispError> {
    let sexps = cranelisp_frontend::parse(form_src)?;
    // ... parse handling ...
    let module = self.tc.current_module_path().clone();
    let mut resolver = ReadOnlyMacroResolver {
        tc: &self.tc,
        codegen_products: &self.shared.codegen_products,
        current_module: module,
    };
    expander::expand_sexp_recursive(sexp, &mut resolver, 0)
}
```

### `expand_macro_call` (expander.rs)

Signature changes to take `&mut dyn MacroResolver` instead of `&HashMap<Symbol, MacroEntry>`. Calls `resolver.resolve_macro(name, span)` instead of `macros.get(name)`.

### `compile_macro_for_repl` (worker.rs)

Gains `target_module` parameter, passes it through to `compile_macro_if_needed`.

## 5. Borrow Checker Design

The core borrow conflict: `SymbolTableMacroResolver` needs `&TypeChecker` for symbol table lookups, but on-demand compilation needs `&mut ModuleCompiler` (which contains `&mut TypeChecker`).

**Solution: scoped extraction into `try_expand_sexp`.**

```rust
/// Expand macros in a sexp, compiling on demand as needed.
///
/// Creates a resolver scoped to this function call. If the resolver
/// queues macros for compilation, compiles them after expansion drops
/// the resolver's borrows, then re-expands.
fn try_expand_sexp(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    sexp: &Sexp,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<Option<Sexp>, CranelispError>
```

**Borrow scoping pattern:**

```
1. Create resolver (borrows ctx.tc as &, ctx.codegen_products as &)
2. Call expand_sexp_recursive — resolver.resolve_macro may:
   a. Read symbol table (& borrow on tc — OK)
   b. Read codegen_products (& borrow — OK)
   c. Queue uncompiled macros in compile_queue (no borrow needed)
3. Drop resolver (releases & borrows)
4. If compile_queue non-empty:
   a. For each queued macro, call compile_macro_if_needed (takes &mut ctx)
   b. Re-expand with a fresh resolver (step 1 again)
5. Return expanded sexp
```

The key insight: the resolver holds only `&` borrows (shared references to `TypeChecker` and `DashMap`). It never calls `&mut` methods. When a macro needs compilation, it records the request and the caller handles it after the resolver is dropped.

**Maximum re-expansion iterations**: 3. If after 3 rounds new macros are still being discovered, return an error. In practice, one round suffices — all macros are either already compiled (from prior modules / prior forms) or compiled in the first queue drain.

**Fields the resolver needs (all `&`):**

| Field | Source | Access pattern |
|-------|--------|---------------|
| `tc` | `&ctx.tc` (via `TypeChecker` shared-ref methods) | `symbol_table()`, `module_table()` |
| `codegen_products` | `&ctx.codegen_products` | `.get(module)` to check code pointers |
| `current_module` | `&module` (cloned `ModuleFullPath`) | Starting point for symbol lookup |

The resolver does NOT need: `&mut TypeChecker`, `&scheduler`, `&platform_registry`, `&typecheck_products`, or any other `ModuleCompiler` field.

## 6. Scope Constraints

**FQ macro references are NOT supported.** `(control/cond ...)` does not work — same gap as FQ defn references (`math/add`). Module discovery only happens via `import`/`export`/`mod` declarations. The resolver only looks up bare names in the current module's symbol table. FQ support is a separate future feature that would require module auto-loading.

**Current-module macros (from `defmacro` in the current batch)** are registered in the symbol table during Pass 1 (`register_macro_in_module`). The resolver sees them naturally when it queries the symbol table. No special handling needed.

**Macros produced by expansion** (e.g., `const` and `def` expand to `defmacro` + a function) are registered inline in `process_regular_form` and compiled with `compile_macro_if_needed`. They become visible to the resolver for subsequent forms because they exist in the symbol table and their code pointers exist in `codegen_products` under the correct (current) module.

**Import/Reexport chain depth limit**: 16 hops. The Cranelisp module system uses explicit imports and re-exports, so chains deeper than a few hops indicate a bug or adversarial input. The limit prevents infinite loops from circular Import/Reexport references.

**No pre-scanning.** The current implementation pre-scans each sexp to check if it contains macro calls (`sexp_contains_macro_call`), then collects which macros are called (`collect_called_macros`), then compiles those specific macros, then builds a HashMap of all macros, then expands. The resolver eliminates all pre-scanning — expansion walks the sexp tree once, calling `resolver.resolve_macro` on each symbol encountered. If the symbol is not a macro, the resolver returns `None` and expansion continues. This is simpler, correct, and no slower in practice (HashMap lookup vs symbol table lookup are both O(1)).

## 7. Sketch Comparison

The sketch used `MacroEnv` — a flat `HashMap<Symbol, MacroEntry>` wrapped in `RwLock`. This worked because the sketch had a single `Jit` instance with a single flat code pointer namespace. All macro code pointers lived in one place, keyed by the macro's clause function name. There was no per-module partitioning to get wrong.

The reimplementation's per-module `CodegenProduct` DashMaps introduced the store/lookup mismatch. The three-cache approach (`macro_names`, `macro_infos`, `HashMap`) was an attempt to bridge between the flat-namespace mental model and the per-module reality, but the bridge was incomplete — `compile_macro_clause_inline` stored under the wrong module.

The resolver eliminates the intermediate bridge entirely. Instead of pre-building a flat cache that must agree with the per-module store, the resolver walks the authoritative data (symbol table + codegen products) on each lookup. The symbol table already knows the module structure (Import/Reexport chains); the resolver follows it.

**Divergence from sketch**: Justified. The sketch's `MacroEnv` cannot work with per-module code pointer storage. The resolver is the natural replacement — it uses the same symbol table infrastructure that name resolution already uses for functions, types, and traits.

## Implementation Sequence

1. `/frontend` writes the `MacroResolver` trait in `expander.rs`, changes `expand_sexp_recursive` and `expand_macro_call` signatures, deletes `MacroEnv` and `compile_single_clause`.
2. `/int` implements `SymbolTableMacroResolver` in `worker.rs` with `resolve_macro_definition` helper. Implements `ReadOnlyMacroResolver` in `session_v4.rs`. Wires `try_expand_sexp` into `process_regular_form`. Adds `target_module` params to `compile_macro_if_needed` and `compile_macro_clause_inline`. Deletes dead cache functions.
3. `/qa` verifies progressive restoration of test counts.

Steps 1 and 2 can proceed in parallel — `/frontend` defines the trait, `/int` implements it. The trait API is simple enough that parallel work is safe.

## Next Skills

- `/frontend` — implement `MacroResolver` trait and `expand_sexp_recursive` signature change per `design/frontend/macro-resolver-trait.md`
- `/int` — implement resolvers, wire into pipeline, delete caches per `design/int/macro-resolver-impl.md`
- `/typecheck` — fix `ensure_module_exists` builtin type leaking per `design/typecheck/sprint50-fixes.md`
