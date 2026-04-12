# MacroResolver Trait — expander.rs Refactor

**Sprint**: 50, Wave 2
**Skill**: /frontend
**Umbrella design**: `design/arch/macro-resolver.md`

## Current State

`src/expander.rs` contains:

1. **`MacroEnv` struct** (lines 42-145) — wraps `RwLock<HashMap<Symbol, MacroEntry>>`. Provides `compile_macro`, `expand_sexp`, `is_macro`, `remove_macro`. Production code does NOT use `MacroEnv` — it was the sketch-era interface. The v4 pipeline builds a `HashMap<Symbol, MacroEntry>` directly in worker.rs and passes it to the free functions. `MacroEnv` is only exercised by unit tests in this file.

2. **`compile_single_clause`** (lines 532-605) — compiles a macro clause through the full pipeline (synthesize defn, expand quasiquotes, build AST, typecheck, codegen). Production code uses `compile_macro_clause_inline` in worker.rs instead. This function is dead code outside of `MacroEnv::compile_macro`.

3. **`expand_sexp_recursive`** (lines 438-487) — the core expansion loop. Takes `&HashMap<Symbol, MacroEntry>` for macro lookup. This IS used by production code.

4. **`expand_macro_call`** (lines 490-519) — dispatches a single macro call. Takes `&HashMap<Symbol, MacroEntry>`. Also used by production code.

5. **Supporting functions** — `clause_matches`, `find_matching_clause`, `invoke_clause`, `rewrite_spans`, `invoke_jit_protected`, signal handling. All retained.

6. **Tests** — 7 tests total:
   - 5 depend on `MacroEnv`: `test_identity_macro`, `test_quasiquote_macro`, `test_multi_clause_dispatch`, `test_is_macro_predicate`, `test_quasiquote_bracket_macro`
   - 2 are marshal round-trips: `test_marshal_roundtrip_all_variants`, `test_slist_roundtrip`

## Target State

After this change, `expander.rs` provides:

1. **`MacroResolver` trait** — the single abstraction for macro lookup during expansion
2. **`expand_sexp_recursive`** — takes `&mut dyn MacroResolver` instead of `&HashMap<Symbol, MacroEntry>`
3. **`expand_macro_call`** — removed as a standalone function; logic inlined into `expand_sexp_recursive` or replaced by `expand_macro_call_with_entry`
4. **All supporting functions** — retained unchanged
5. **Marshal round-trip tests** — retained unchanged

## Trait Design

```rust
/// Trait for resolving macro names to compiled entries during expansion.
///
/// Implementations look up the symbol table, follow import chains, and
/// optionally compile macros on demand. The `&mut self` receiver allows
/// on-demand compilation (the `SymbolTableMacroResolver` in worker.rs
/// compiles macro clauses the first time they are referenced).
pub(crate) trait MacroResolver {
    /// Resolve a name to a compiled macro entry, if one exists.
    ///
    /// Returns:
    /// - `Ok(Some(entry))` — name is a macro, here are its compiled clauses
    /// - `Ok(None)` — name is not a macro (or not visible in the current scope)
    /// - `Err(...)` — lookup or on-demand compilation failed
    fn resolve_macro(
        &mut self,
        name: &str,
        span: Span,
    ) -> Result<Option<MacroEntry>, CranelispError>;
}
```

### Why `&mut self`

The primary implementation (`SymbolTableMacroResolver` in worker.rs) may need to compile a macro clause on first encounter. Compilation mutates codegen products (stores function pointers, GOT slots). A `&self` receiver would require interior mutability (`RefCell` or similar), adding complexity. Since expansion is single-threaded within a module compilation unit, `&mut self` is natural.

### What `MacroEntry` represents

`MacroEntry` is unchanged — it holds `Vec<MacroClauseEntry>` (each with a JIT function pointer, parameter patterns, and optional rest param) plus an optional docstring. The trait returns an owned `MacroEntry` rather than a reference because the resolver may construct it on the fly from codegen products.

### Read-only variant

The `/expand` slash command needs macro resolution without compilation capability. `session_v4.rs` will implement a `ReadOnlyMacroResolver` that returns `Ok(None)` if a macro isn't already compiled, rather than attempting on-demand compilation. This is a separate impl of the same trait, owned by `/int`.

## Expansion Loop Changes

The algorithm in `expand_sexp_recursive` is unchanged — walk the tree, check each list head and bare symbol against known macros, dispatch matching calls, recurse on the result. Only the lookup mechanism changes.

### Before (HashMap)

```rust
pub(crate) fn expand_sexp_recursive(
    sexp: Sexp,
    macros: &HashMap<Symbol, MacroEntry>,
    depth: usize,
) -> Result<Sexp, CranelispError> {
    // ...
    if let Sexp::Symbol(ref name, _) = children[0]
        && macros.contains_key(name.as_str())
    {
        let args = &children[1..];
        return expand_macro_call(name, args, span, macros, depth);
    }
    // ...
}
```

### After (MacroResolver)

```rust
pub(crate) fn expand_sexp_recursive(
    sexp: Sexp,
    resolver: &mut dyn MacroResolver,
    depth: usize,
) -> Result<Sexp, CranelispError> {
    // ...
    if let Sexp::Symbol(ref name, _) = children[0] {
        if let Some(entry) = resolver.resolve_macro(name, children[0].span())? {
            let args = &children[1..];
            return expand_macro_call_with_entry(
                name, args, span, &entry, resolver, depth,
            );
        }
    }
    // ...
}
```

The two-step check-then-get collapses to one `resolve_macro` call that returns `Option<MacroEntry>`.

### `expand_macro_call_with_entry`

Replaces `expand_macro_call`. Takes a resolved `MacroEntry` directly instead of looking it up:

```rust
pub(crate) fn expand_macro_call_with_entry(
    name: &str,
    args: &[Sexp],
    span: Span,
    entry: &MacroEntry,
    resolver: &mut dyn MacroResolver,
    depth: usize,
) -> Result<Sexp, CranelispError> {
    let clause = find_matching_clause(&entry.clauses, args).ok_or_else(|| {
        CranelispError::MacroError {
            message: format!(
                "no matching clause for macro '{name}' with {} arguments",
                args.len()
            ),
            span,
        }
    })?;

    let mut result = invoke_clause(clause, args, span)?;
    rewrite_spans(&mut result, span);

    // Re-expand the result (may contain further macro calls).
    expand_sexp_recursive(result, resolver, depth + 1)
}
```

The old `expand_macro_call` (which took `&HashMap`) is deleted.

### Bare symbol expansion

Same pattern — the bare-symbol branch in `expand_sexp_recursive` calls `resolver.resolve_macro(name, span)` and dispatches to `expand_macro_call_with_entry` with an empty args slice.

## Deletions

| Item | Lines | Reason |
|------|-------|--------|
| `MacroEnv` struct + `impl MacroEnv` + `impl Default` | 42-145 | Dead code. Production uses free functions with HashMap (soon: trait). Only unit tests use MacroEnv. |
| `unsafe impl Send/Sync for MacroEnv` | 49-54 | Goes with MacroEnv. |
| `compile_single_clause` | 532-605 | Dead code. Production uses `compile_macro_clause_inline` in worker.rs. Only called by `MacroEnv::compile_macro`. |
| `expand_macro_call` (HashMap variant) | 490-519 | Replaced by `expand_macro_call_with_entry` which takes `&MacroEntry` directly. |
| `use std::sync::RwLock` | 7 | Only used by MacroEnv. |
| `test_identity_macro` | 633-650 | Depends on MacroEnv. |
| `test_quasiquote_macro` | 653-674 | Depends on MacroEnv. |
| `test_multi_clause_dispatch` | 677-706 | Depends on MacroEnv. |
| `test_is_macro_predicate` | 709-722 | Depends on MacroEnv. |
| `test_quasiquote_bracket_macro` | 769-795 | Depends on MacroEnv. |
| `setup()` test helper | 617-621 | Only used by deleted tests. |
| `parse_one()` test helper | 624-628 | Only used by deleted tests. |

### Retained

| Item | Reason |
|------|--------|
| `MacroClauseEntry`, `MacroEntry` | Core types used by trait and all callers |
| `clause_matches`, `find_matching_clause` | Used by `expand_macro_call_with_entry` |
| `invoke_clause` | Used by expansion |
| `invoke_jit_protected` + signal handling | Used by `invoke_clause` |
| `rewrite_spans`, `rewrite_spans_unique` | Used by expansion |
| `EXPANSION_DEPTH_LIMIT` | Used by expansion |
| `test_marshal_roundtrip_all_variants` | Independent of MacroEnv |
| `test_slist_roundtrip` | Independent of MacroEnv |

## Sketch Comparison

The sketch used `MacroEnv` as a flat `HashMap<Symbol, MacroEntry>` because it had a single JIT with a single code pointer namespace. There was no store/lookup mismatch because there was only one place to store and one place to look. The reimplementation's per-module `CodegenProduct` DashMaps introduced the mismatch — macro code pointers are stored under one module key but looked up under another.

The `MacroResolver` trait eliminates the intermediate cache entirely. Resolution goes directly to the symbol table and codegen products. This is a cleaner design than the sketch's flat map — it respects module boundaries and makes the lookup path explicit rather than relying on a pre-built snapshot that must be kept in sync.

Divergence from sketch: intentional. The sketch's approach cannot work with per-module codegen products. The trait abstraction also enables the read-only variant for `/expand` without duplicating logic.
