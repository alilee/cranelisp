# Macro Resolver Implementation Design

Sprint 50, Wave 2 design doc for `/int`. Covers the `SymbolTableMacroResolver` in `worker.rs`, `ReadOnlyMacroResolver` in `session_v4.rs`, borrow scoping, function-by-function changes, platform JIT fix, and dead code deletions.

## 1. Overview

The current macro expansion path in `worker.rs` uses three redundant caches (`macro_names`, `macro_infos`, and a `HashMap<Symbol, MacroEntry>`) that duplicate information already in the symbol table and codegen products. The `HashMap` cache disagrees with codegen products about which module key stores macro code pointers (current module vs defining module), causing ~100 test failures.

The fix eliminates all caches. A new `MacroResolver` trait (defined by `/frontend` in `expander.rs`) replaces the `&HashMap<Symbol, MacroEntry>` parameter on `expand_sexp_recursive`. Two implementations live in `/int` code:

- **`SymbolTableMacroResolver`** in `worker.rs` — full read-write resolver with on-demand compilation for batch and REPL eval
- **`ReadOnlyMacroResolver`** in `session_v4.rs` — read-only resolver for the `/expand` slash command

## 2. SymbolTableMacroResolver Struct

```rust
/// Macro resolver backed by the TypeChecker symbol tables and CodegenProduct DashMaps.
///
/// Walks the symbol table on each name encounter, follows Import/Reexport chains
/// to the defining module, checks codegen products there, compiles on demand if
/// needed, and returns the MacroEntry.
struct SymbolTableMacroResolver<'a> {
    /// Shared-ref to TC's per-module symbol tables (DashMap, interior mutability).
    tc_modules: &'a DashMap<ModuleFullPath, SymbolTable>,
    /// Current module path (for resolving local Macro entries).
    current_module: ModuleFullPath,
    /// Per-module codegen products (DashMap, interior mutability).
    codegen_products: &'a DashMap<ModuleFullPath, CodegenProduct>,
    /// Per-module typecheck products (DashMap, interior mutability).
    typecheck_products: &'a DashMap<ModuleFullPath, TypecheckProduct>,
    /// Mutable borrow of TypeChecker — needed for on-demand compilation
    /// (check_form + merge_form_result require &mut self).
    tc: &'a mut TypeChecker,
    /// Mutable borrow of the accumulator — needed for on-demand compilation.
    accumulator: &'a mut ModuleCheckAccumulator,
    /// Platform registry — needed for JIT setup during on-demand compilation.
    platform_registry: &'a mut PlatformRegistry,
    /// Scheduler — for notify_inmem_codegen_complete after on-demand compilation.
    scheduler: &'a CompileScheduler,
}
```

### Key design decisions

1. **`tc_modules` is a shared ref, not extracted from `tc`**: `TypeChecker::modules_ref()` returns `&DashMap<...>`, which has interior mutability. The resolver holds this shared ref. The `tc: &mut TypeChecker` is needed only for `check_form`/`merge_form_result` calls during on-demand compilation (these methods swap `self.state` and require `&mut self`).

2. **`codegen_products` and `typecheck_products` are shared refs**: Both are `DashMap` with interior mutability. The resolver reads code pointers via `codegen_products.get(module).code.get(name)` and writes them via `codegen_products.entry(module).or_default().code.insert(name, ...)` — both work through `&DashMap`.

3. **`accumulator: &mut ModuleCheckAccumulator`**: On-demand compilation needs to typecheck macro clause defns. `check_form` merges results into the accumulator. This must be the same accumulator the caller uses for subsequent forms.

## 3. Borrow Scoping — `try_expand_sexp` Extraction

The critical borrow challenge: `process_regular_form` needs `&mut ModuleCompiler` both to create the resolver and to process expansion results (AST building, signature registration, body typechecking). If the resolver held `&mut ModuleCompiler`, the caller could not use it after expansion.

### Solution: extract expansion into a scoped helper

```rust
/// Scope the resolver's borrows to just the expansion phase.
///
/// Creates a SymbolTableMacroResolver, runs expand_sexp_recursive,
/// drops the resolver, returns the expanded sexp. After this returns,
/// ctx and accumulator are available for the caller to use freely.
fn try_expand_sexp(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    sexp: &Sexp,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<Option<Sexp>, CranelispError> {
    let tc_modules = ctx.tc.modules_ref() as *const DashMap<ModuleFullPath, SymbolTable>;
    // SAFETY: tc_modules points to a field inside ctx.tc. The DashMap is
    // interior-mutable and accessed only via &-ref methods. The &mut ctx.tc
    // borrow is used only for check_form/merge_form_result inside the
    // resolver, which does not invalidate the DashMap pointer.
    let tc_modules_ref: &DashMap<ModuleFullPath, SymbolTable> = unsafe { &*tc_modules };

    let current_module = ctx.tc.current_module_path().clone();

    let mut resolver = SymbolTableMacroResolver {
        tc_modules: tc_modules_ref,
        current_module: current_module.clone(),
        codegen_products: ctx.codegen_products,
        typecheck_products: ctx.typecheck_products,
        tc: ctx.tc,
        accumulator,
        platform_registry: ctx.platform_registry,
        scheduler: ctx.scheduler,
    };

    let expanded = expander::expand_sexp_recursive(
        sexp.clone(), &mut resolver, 0,
    )?;

    // Resolver is dropped here. ctx and accumulator are free.
    // Compare expanded to original to decide if expansion happened.
    if expanded_differs_from_original(&expanded, sexp) {
        Ok(Some(expanded))
    } else {
        Ok(None)
    }
}
```

### Why this works with Rust's borrow checker

The unsafe block is needed because we need to split the borrow of `ctx.tc`: one shared ref to `tc.modules` (the DashMap) and one mutable ref to `tc` itself (for `check_form`). Rust does not allow this directly because `modules_ref()` borrows `&self` on the TypeChecker, conflicting with the later `&mut self` borrow.

**Alternative (no unsafe)**: Use `check_form_with_state` and `merge_form_result_with_state` which take `&self` on TypeChecker + explicit `&mut CheckState`. The resolver would hold `&TypeChecker` (shared ref) plus `&mut CheckState` (extracted from TC via `mem::take`/swap before creating the resolver). This avoids the split borrow:

```rust
fn try_expand_sexp(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    sexp: &Sexp,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<Option<Sexp>, CranelispError> {
    // Extract CheckState from TC so we can hold &TC + &mut CheckState simultaneously.
    let mut check_state = ctx.tc.take_state();
    let current_module = ctx.tc.current_module_path().clone();

    let mut resolver = SymbolTableMacroResolver {
        tc: &*ctx.tc,  // shared ref — no conflict
        check_state: &mut check_state,
        current_module: current_module.clone(),
        codegen_products: ctx.codegen_products,
        typecheck_products: ctx.typecheck_products,
        accumulator,
        platform_registry: ctx.platform_registry,
        scheduler: ctx.scheduler,
    };

    let expanded = expander::expand_sexp_recursive(
        sexp.clone(), &mut resolver, 0,
    )?;

    // Restore CheckState to TC.
    ctx.tc.restore_state(check_state);

    // ... compare and return
}
```

**Recommendation**: Prefer the `_with_state` approach (no unsafe). This requires adding `take_state()`/`restore_state()` to TypeChecker if they don't exist — but `check_form` already does `mem::replace(&mut self.state, ...)` internally, so exposing that swap is trivial and consistent.

If `take_state`/`restore_state` cannot be added to the TC crate in this sprint, fall back to the unsafe approach with a clear safety comment. The `_with_state` variants on `check_form_with_state` and `merge_form_result_with_state` already exist (lines 362-370 and 698-707 of `program.rs`), so the only missing piece is the state extraction.

### Resolver struct (safe variant)

```rust
struct SymbolTableMacroResolver<'a> {
    tc: &'a TypeChecker,                                    // shared ref
    check_state: &'a mut CheckState,                        // extracted from TC
    current_module: ModuleFullPath,
    codegen_products: &'a DashMap<ModuleFullPath, CodegenProduct>,
    typecheck_products: &'a DashMap<ModuleFullPath, TypecheckProduct>,
    accumulator: &'a mut ModuleCheckAccumulator,
    platform_registry: &'a mut PlatformRegistry,
    scheduler: &'a CompileScheduler,
}
```

## 4. MacroResolver::resolve_macro Implementation

The `resolve_macro` method on `SymbolTableMacroResolver`:

```
fn resolve_macro(&mut self, name: &str, span: Span) -> Result<Option<MacroEntry>>:
  1. Look up `name` in current module's symbol table
  2. Match on entry type:
     - ModuleEntry::Macro { clauses, docstring, .. }:
         defining_module = current_module
     - ModuleEntry::Import { source }:
         Follow chain recursively (see §4.1)
         If terminal entry is Macro → defining_module = terminal module
         Else → return Ok(None)
     - Anything else → return Ok(None)
  3. For each clause_info in clauses:
     - Check codegen_products[defining_module].code[clause_jit_name]
     - If present → collect MacroClauseEntry { func_ptr, params, rest_param }
     - If missing → compile on demand (see §4.2)
  4. Return Ok(Some(MacroEntry { clauses, docstring }))
```

### 4.1 Import/Reexport chain walker

```rust
fn resolve_to_macro_entry(
    &self,
    module: &ModuleFullPath,
    name: &str,
    depth: usize,
) -> Option<(Vec<MacroClauseInfo>, Option<String>, ModuleFullPath)> {
    if depth > 16 { return None; }  // prevent infinite loops
    let table = self.tc.module_table(module)?;
    match table.get(name)? {
        ModuleEntry::Macro { clauses, docstring, .. } => {
            Some((clauses.clone(), docstring.clone(), module.clone()))
        }
        ModuleEntry::Import { source } | ModuleEntry::Reexport { source } => {
            let next_mod = source.module.clone();
            let next_sym = source.symbol.to_string();
            drop(table);  // release DashMap guard before recursing
            self.resolve_to_macro_entry(&next_mod, &next_sym, depth + 1)
        }
        _ => None,
    }
}
```

This is a generic recursive chain walker, replacing the hardcoded 2-hop logic in `resolve_macro_entry` and `resolve_macro_sexp`. Depth limit prevents infinite loops from cyclic imports (which should not exist but are cheap to guard against).

### 4.2 On-demand compilation

When a clause lacks a code pointer, call `compile_macro_clause_inline` with the **defining module** as `target_module`. This is the core fix for the store/lookup mismatch: code pointers are always stored under the defining module, and lookups always check the defining module.

The on-demand path reuses the existing `compile_macro_clause_inline` logic but with the `target_module` parameter (see section 5.3).

## 5. Function-by-Function Changes

### 5.1 `pass2_check_bodies_with_expansion` (worker.rs:701)

**Before**: Collects `macro_infos` and `macro_names` from sexps + symbol table. Passes both to `process_regular_form`. Extends `macro_names` with new macros from expansion results.

**After**: Remove `macro_infos` collection (lines 710-718), `macro_names` construction (lines 718-729), `persistent_macro_names` collection (lines 723-729), and `name_refs` construction (line 735). The `FormKind::Regular` branch becomes:

```rust
FormKind::Regular => {
    process_regular_form(
        ctx, module, sexp, accumulator, expanded_program,
    )?;
}
```

No return value needed — new macros from expansion are registered in the symbol table directly and visible to the resolver on subsequent forms.

### 5.2 `process_regular_form` (worker.rs:805)

**Before**: Takes `macro_infos`, `macro_names`, returns `Vec<String>` of new macro names.

**After**: Signature simplifies to:
```rust
fn process_regular_form(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    sexp: &Sexp,
    accumulator: &mut ModuleCheckAccumulator,
    expanded_program: &mut Vec<TopLevel>,
) -> Result<(), CranelispError>
```

Body replaces `try_expand_for_pass2(...)` with `try_expand_sexp(ctx, module, sexp, accumulator)`. The rest (flatten_begin, defmacro partition, AST build, typecheck) is unchanged. Return type changes from `Vec<String>` to `()`.

The `new_macro_names` vector and `macro_names.extend(new_macros)` in the caller are both deleted. Macros produced by expansion (`const`/`def` → `defmacro`) are registered in the symbol table via `register_macro_in_module` and compiled via `compile_macro_if_needed` — the resolver sees them on the next form.

### 5.3 `compile_macro_if_needed` (worker.rs:1493)

**Before**: Takes `(ctx, module, info, span, accumulator)` where `module` is always the current module.

**After**: Gains `target_module: &ModuleFullPath` parameter:
```rust
fn compile_macro_if_needed(
    ctx: &mut ModuleCompiler,
    target_module: &ModuleFullPath,
    info: &cranelisp_frontend::DefmacroInfo,
    span: Span,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<(), CranelispError>
```

`target_module` is the **defining** module where code pointers are stored. For local macros this equals the current module. For imported macros, it is the module where the `ModuleEntry::Macro` lives (the terminal of the Import/Reexport chain).

The `has_code_ptr` checks (line 1501-1503) and `compile_macro_clause_inline` calls (line 1545) use `target_module` instead of `module`.

### 5.4 `compile_macro_clause_inline` (worker.rs:1701)

**Before**: Derives `module` from `ctx.tc.current_module_path()` (line 1725, 1755).

**After**: Gains `target_module: &ModuleFullPath` parameter. The typechecking steps (check_form Register + CheckBody) still use the current module context (needed for name resolution of Sexp constructors etc.). But the codegen step (compile_and_register_defn_shared) and GOT registration use `target_module`. This ensures the code pointer is stored where lookups will find it.

```rust
fn compile_macro_clause_inline(
    ctx: &mut ModuleCompiler,
    target_module: &ModuleFullPath,
    macro_name: &Symbol,
    clause_idx: usize,
    clause: &cranelisp_frontend::MacroClause,
    span: Span,
    accumulator: &mut ModuleCheckAccumulator,
) -> Result<(), CranelispError>
```

Line 1755 changes from:
```rust
let module = ctx.tc.current_module_path().clone();
```
to using the `target_module` parameter for JIT setup and `compile_and_register_defn_shared`.

### 5.5 `compile_macro_for_repl` (worker.rs:1978)

Already a thin wrapper around `compile_macro_if_needed`. Passes the current module as `target_module` (correct for REPL — macros defined at the REPL are local).

### 5.6 `expand_form_sexp` in session_v4.rs (line 2092)

**Before**: Calls `self.build_macro_map()` to build a `HashMap<Symbol, MacroEntry>`, then passes it to `expand_sexp_recursive`.

**After**: Creates a `ReadOnlyMacroResolver` and calls `expand_sexp_recursive`:

```rust
fn expand_form_sexp(&self, form_src: &str) -> Result<Sexp, CranelispError> {
    let sexps = cranelisp_frontend::parse(form_src)?;
    // ... same empty-check as before ...
    let sexp = sexps.into_iter().next().unwrap();
    let resolver = ReadOnlyMacroResolver {
        tc: &self.tc,
        codegen_products: &self.shared.codegen_products,
        current_module: self.tc.current_module_path().clone(),
    };
    crate::expander::expand_sexp_recursive(sexp, &resolver, 0)
}
```

## 6. ReadOnlyMacroResolver (session_v4.rs)

```rust
/// Read-only macro resolver for /expand slash command.
/// Same lookup logic as SymbolTableMacroResolver but never compiles on demand.
/// If a macro's clauses are not compiled, it is silently skipped (returns None).
struct ReadOnlyMacroResolver<'a> {
    tc: &'a TypeChecker,
    codegen_products: &'a DashMap<ModuleFullPath, CodegenProduct>,
    current_module: ModuleFullPath,
}

impl MacroResolver for ReadOnlyMacroResolver<'_> {
    fn resolve_macro(&mut self, name: &str, _span: Span)
        -> Result<Option<MacroEntry>, CranelispError>
    {
        // Same chain-walking logic as SymbolTableMacroResolver::resolve_to_macro_entry
        // but returns None instead of compiling if any clause lacks a code pointer.
    }
}
```

This replaces `build_macro_map` (session_v4.rs:2112-2170). The `ReadOnlyMacroResolver` takes `&mut self` (required by the trait) but has no mutable state — the `&mut` is needed only because `SymbolTableMacroResolver` needs it for on-demand compilation and the trait must accommodate both.

## 7. Platform JIT Symbol Resolution Fix (RC2)

### Problem

`collect_jit_setup_for_module` (worker.rs:282-314) only scans `ModuleEntry::Def` with `PrimitiveKind::PlatformEffect` in the current module's symbol table. But platform functions appear as `ModuleEntry::Import` in non-platform modules (they are imported from the platform module). This means non-platform modules cannot resolve platform function JIT symbols during codegen.

### Fix

Add a second scan pass that follows Import entries to their source:

```rust
pub fn collect_jit_setup_for_module(
    &self,
    platform_registry: &PlatformRegistry,
) -> (Vec<(String, *const u8)>, Vec<(String, *const u8)>) {
    let mut jit_symbols = Vec::new();
    let mut got_data_defs = Vec::new();

    // Scan current module's symbol table for platform functions.
    if let Some(st) = self.tc_modules.get(&self.current_module) {
        for (_name, entry) in st.all_symbols() {
            match entry {
                // Direct platform function definition.
                ModuleEntry::Def { kind, .. } => {
                    if let DefKind::Primitive {
                        primitive_kind: PrimitiveKind::PlatformEffect,
                        jit_name: Some(jit_name),
                    } = kind.as_ref()
                    {
                        if let Some(ptr) = platform_registry.fn_ptr_by_jit_name(jit_name) {
                            jit_symbols.push((jit_name.0.clone(), ptr));
                        }
                    }
                }
                // Import that resolves to a platform function.
                ModuleEntry::Import { source } => {
                    if let Some(source_table) = self.tc_modules.get(&source.module) {
                        if let Some(ModuleEntry::Def { kind, .. }) =
                            source_table.get(source.symbol.as_ref())
                        {
                            if let DefKind::Primitive {
                                primitive_kind: PrimitiveKind::PlatformEffect,
                                jit_name: Some(jit_name),
                            } = kind.as_ref()
                            {
                                if let Some(ptr) = platform_registry.fn_ptr_by_jit_name(jit_name) {
                                    jit_symbols.push((jit_name.0.clone(), ptr));
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }

    // ... GOT literal pool entries (unchanged) ...
}
```

**Alternative (simpler)**: Register ALL platform registry entries unconditionally, regardless of module. Platform registries are small (~20 entries). This avoids the symbol-table scan entirely:

```rust
// Register all platform functions from the registry.
for (jit_name, ptr) in platform_registry.all_jit_symbols() {
    jit_symbols.push((jit_name.clone(), ptr));
}
```

**Recommendation**: Use the unconditional approach. It is simpler, correct, and the performance difference is negligible. The symbol table scan is a premature optimization for a set of ~20 entries.

This requires `PlatformRegistry` to expose an `all_jit_symbols()` method (or equivalent iterator). If that method does not exist, the import-following approach is the fallback.

## 8. Entry-Module Primitives Inconsistency

Entry modules (the initial `user` module in REPL, or the main module in `--run`) currently receive primitives implicitly without an `(import [primitives [...]])` declaration, violating spec 8.9.1.

**Fix**: Remove implicit primitive seeding from entry module creation. Entry modules should be created empty (like any other module). Primitives become available only via explicit import or through the prelude (which itself imports primitives explicitly).

**Impact**: Tests that rely on bare primitive names in entry modules (e.g., `(add-i64 1 2)` without import) will fail. This is correct — those tests need `(import [primitives [add-i64]])`. The /qa task in this sprint covers fixing those test fixtures.

## 9. Deletions

### 9.1 worker.rs — dead macro cache functions

All of these are replaced by the `SymbolTableMacroResolver`:

| Function | Lines | Reason |
|----------|-------|--------|
| `build_all_macro_entries` | 1848-1865 | Replaced by resolver's on-demand lookup |
| `collect_persistent_macro_names` | 1872-1910 | No pre-scanning needed |
| `compile_persistent_macro_if_needed` | 1916-1938 | Resolver compiles on demand |
| `resolve_macro_sexp` | 1941-1972 | Replaced by generic chain walker |
| `build_persistent_macro_entries` | 1993-2037 | Replaced by resolver |
| `resolve_macro_entry` | 2040-2075 | Replaced by `resolve_to_macro_entry` |
| `sexp_contains_macro_call` | 1465-1484 | No pre-scanning needed |
| `collect_called_macros` | 1429-1433 | No pre-scanning needed |
| `collect_called_macros_inner` | 1435-1462 | No pre-scanning needed |
| `try_expand_for_pass2` | 1378-1426 | Replaced by `try_expand_sexp` |

Retained:
- `macro_clause_jit_name` — shared naming convention, used by resolver and compile_macro_clause_inline
- `has_code_ptr` — used by resolver and compile_macro_if_needed
- `get_code_ptr` — used by resolver to construct MacroEntry
- `build_macro_entry_from_got` — used by resolver to build MacroEntry from code pointers
- `compile_macro_if_needed` — used by resolver for on-demand compilation (with `target_module` param)
- `compile_macro_clause_inline` — used by compile_macro_if_needed (with `target_module` param)
- `compile_macro_for_repl` — used by session_v4.rs for REPL macro compilation
- `register_macro_in_module` — used by process_regular_form for expansion-produced macros

### 9.2 session_v4.rs — dead macro map builder

| Function | Reason |
|----------|--------|
| `build_macro_map` (line 2112-2170) | Replaced by `ReadOnlyMacroResolver` |

### 9.3 session.rs — ObjectWorkerState dead code

Delete `ObjectWorkerState` struct and its impl (lines 139-173 of `src/session.rs`). This is dead code — the v4 pipeline uses `SharedState` with DashMaps instead.

### 9.4 expander.rs — MacroEnv dead code (owned by /frontend)

`MacroEnv` struct, its impl, `compile_single_clause`, and unit tests are dead code. Deletion is `/frontend`'s responsibility per their design doc.

## 10. Risks

1. **Borrow checker complexity**: The `try_expand_sexp` extraction requires either unsafe pointer manipulation or TypeChecker API additions (`take_state`/`restore_state`). The `_with_state` variants already exist on `check_form` and `merge_form_result`, so the safe approach is viable but requires a small TC crate change.

2. **On-demand compilation during expansion**: If a macro calls another macro that is not yet compiled, the resolver compiles it inline. This is the same behavior as `try_expand_for_pass2` today, but the code path is now inside the `MacroResolver::resolve_macro` callback rather than pre-expansion. The depth limit on `expand_sexp_recursive` prevents infinite loops.

3. **DashMap guard lifetimes**: The chain walker (`resolve_to_macro_entry`) must drop DashMap guards before recursing to avoid deadlocks. The design explicitly shows `drop(table)` before recursive calls.

4. **Platform JIT fix scope**: The unconditional registration approach is simple but may register symbols that are not needed. This is harmless — unused JIT symbols are inert. If `PlatformRegistry::all_jit_symbols()` does not exist, implementing it is trivial (iterate the internal HashMap).

5. **Entry-module primitives change**: Removing implicit primitive seeding changes behavior for all entry modules. Tests that worked before by accident (using bare primitives) will break. The /qa task must land in the same wave or tests will regress further before they improve.

## 11. Sketch Comparison

The sketch used `MacroEnv` (a flat `RwLock<HashMap<Symbol, MacroEntry>>`) because it had a single JIT with a single flat code pointer namespace. Every macro's code pointer was registered globally, so lookup was trivial.

The reimplementation's per-module `CodegenProduct` DashMaps introduced the store/lookup mismatch: code pointers stored under the compiling module but looked up under the defining module. The three-cache approach (`macro_names`, `macro_infos`, `HashMap`) attempted to bridge this gap but got the module key wrong.

The resolver eliminates the intermediate cache entirely: lookup goes directly to the symbol table, follows the import chain to the defining module, and checks codegen products there. No intermediate data structure that can diverge from the source of truth.

## 12. Dependencies

- **`/frontend`** must define the `MacroResolver` trait and update `expand_sexp_recursive` before `/int` can implement it. The trait signature from `/frontend`'s design doc determines the exact struct layout.
- **`/typecheck`** may need to expose `take_state()`/`restore_state()` for the safe borrow approach. If not, the unsafe approach is the fallback.
- **`/qa`** must fix test fixtures with bare primitives (RC3) in the same wave as the entry-module primitives fix.
