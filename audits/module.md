# Module System Audit

**Module**: `src/module.rs`, `src/names.rs` (2 files, 2,690 lines)
**Date**: 2026-03-03
**Scope**: Simplicity, maintainability, complexity, duplication, data modeling, test coverage

## Module Overview

The module system provides the compiler's namespace and linking infrastructure. `module.rs` defines the `CompiledModule` symbol table (with `ModuleEntry` variants for all definition kinds), the `ModuleGraph` discovery and topological sort pipeline, import/export parsing, GOT (Global Offset Table) allocation, and the `resolve_module_imports` function used by both batch and REPL compilation. `names.rs` provides strongly-typed newtype wrappers for module paths, symbols, and fully-qualified names. The module system sits between the typechecker (which owns `tc.modules`) and the JIT (which reads GOT addresses from `CompiledModule`).

### File Metrics

| File | Lines | Responsibility | Tests |
|---|---|---|---|
| `src/module.rs` | 2,216 | CompiledModule, ModuleEntry, GOT management, ModuleGraph discovery, import/export parsing, topo sort, resolve_module_imports | 33 |
| `src/names.rs` | 474 | Symbol, ModuleFullPath, FQSymbol newtypes, split_qualified, split_dotted, parse_name, resolve_bare_name | 22 |

**Total tests**: 55

---

## Findings

### HIGH-1: `discover()` is 329 lines — the entire module graph pipeline in a single function

**File**: `src/module.rs:1280-1608`
**Severity**: High (complexity)

`ModuleGraph::discover` is a static recursive method that does everything: reads the file, parses sexps, extracts module declarations, extracts and re-serializes inline modules, rewrites the parent file, resolves `super` imports, injects the implicit prelude import, discovers child modules from `(mod ...)` declarations, discovers export dependencies, discovers import-triggered root modules, and finally inserts the completed `ModuleInfo`. This is seven or eight distinct phases crammed into one function.

```rust
// src/module.rs:1280-1608
fn discover(
    file_path: &Path, project_root: &Path, lib_dir: Option<&Path>,
    modules: &mut HashMap<ModuleFullPath, ModuleInfo>,
    visit_stack: &mut Vec<ModuleFullPath>,
    visited: &mut HashSet<ModuleFullPath>,
) -> Result<ModuleFullPath, CranelispError> {
    // Phase: compute is_lib + effective roots
    // Phase: cycle detection
    // Phase: read + parse source
    // Phase: extract_module_decls
    // Phase: extract inline modules to files + rewrite parent
    // Phase: resolve `super` imports
    // Phase: inject implicit prelude import
    // Phase: discover child modules (mod ...)
    // Phase: discover export dependencies
    // Phase: discover import-triggered root modules
    // Phase: insert ModuleInfo
}
```

**Impact**: The function is hard to navigate and reason about. Each phase shares local variables with the others, making it impossible to test any phase in isolation. The inline-module extraction (lines 1356–1426) mutates the filesystem (creates directories, writes two files, rewrites the parent), making this effect invisible from the call site. Bugs in any phase (e.g., the `super` resolution, the cycle avoidance for import discovery) are hard to isolate.

**Recommendation**: Extract each phase into a named private function. Suggested split: `extract_inline_modules(file_path, decls, &mut source)` (filesystem mutation), `resolve_super_imports(module_id, decls)`, `inject_prelude_if_needed(module_id, effective_root, effective_lib, decls)`, `discover_child_mods(child_names, ...)`, `discover_export_deps(exports, ...)`, `discover_import_roots(imports, ...)`. `discover` becomes an orchestrator calling these in order.

---

### HIGH-2: `require_public` flag dropped on the recursive Import/Reexport chain traversal

**File**: `src/typechecker.rs:1015-1018`
**Severity**: High (robustness)

When `resolve_entry_in_module` encounters an `Import` or `Reexport` entry, it recurses with `require_public: false` regardless of the original caller's intent. This means: if module A imports (privately) from module B, and B imports (privately) from C, a cross-module qualified access like `a/name` that maps through B to C will succeed even if the intermediate link was private. The visibility check is applied only at the first hop.

```rust
// src/typechecker.rs:1015-1017
crate::module::ModuleEntry::Import { source }
| crate::module::ModuleEntry::Reexport { source } => {
    self.resolve_entry_in_module(&source.module, &source.symbol, depth + 1, false)
    //                                                                       ^^^^^ hardcoded false
}
```

For the current scheme — where `Import` entries only appear in the importing module's table, and the final entry in the defining module is always a `Def`/`Constructor`/etc. — this is usually harmless. However, private `Def` entries reachable through an `Import` chain from another module will be returned as if public. The actual visibility check is performed correctly only at the terminal `Def`/`Constructor`/`TypeDef`/`TraitDecl`/`Macro` arm.

**Impact**: A private function in module B could be accessed cross-module if B re-exports it through a chain that uses `Import` instead of `Reexport`. The current code uses `Import` for direct imports (not re-exports), but the type system cannot prevent this from changing.

**Recommendation**: Either document precisely why `require_public: false` is correct in recursive hops (adding an invariant comment), or thread the original `require_public` flag through the recursion and apply it at each intermediate `Import`/`Reexport` hop: `self.resolve_entry_in_module(&source.module, &source.symbol, depth + 1, require_public)`.

---

### HIGH-3: `discover()` uses `Vec::contains` for cycle detection and deduplication — O(n) on each visited check

**File**: `src/module.rs:1306, 1501, 1556, 1565, 1580`
**Severity**: High (performance)

The `visit_stack` that tracks the DFS path for cycle detection is a `Vec`, so `visit_stack.contains(&module_id)` is O(n) on each call. In a project with many modules this is done repeatedly. Similarly, `dependencies.contains(&tentative_id)` (line 1565 and 1580) and `child_info.dependencies.contains(&module_id)` (line 1501) are O(n) per check.

```rust
// src/module.rs:1306
if visit_stack.contains(&module_id) { ... }      // O(n)

// src/module.rs:1556
if visit_stack.contains(&tentative_id) { ... }   // O(n) again

// src/module.rs:1565, 1580
if !dependencies.contains(&tentative_id) { ... } // O(n) per import
```

For a project with hundreds of modules these O(n) searches stack up. `visited` is already a `HashSet`, so `visited.contains` is O(1), but `visit_stack.contains` is not.

**Impact**: Quadratic time complexity in the discovery phase for projects with large module graphs.

**Recommendation**: Add a parallel `HashSet<ModuleFullPath>` named `in_progress` that mirrors `visit_stack`; push/pop it alongside `visit_stack`. Replace all `visit_stack.contains` checks with `in_progress.contains` (O(1)). For `dependencies.contains`, also use a `HashSet<ModuleFullPath>` accumulator during discovery and convert to `Vec` only when inserting into `ModuleInfo`.

---

### MED-1: `begin_module_scope` and `install_imported_names` are identical — full body duplication

**File**: `src/typechecker.rs:834-893`
**Severity**: Medium (duplication)

`begin_module_scope` (lines 834–863) and `install_imported_names` (lines 868–893) have identical bodies. The only documented difference is that one is called "at the start of a module" and the other is called "incrementally." Both call `insert_import_checked`, both emit the same ambiguity warning. `begin_module_scope` returns `Result<(), _>` but never produces an error; `install_imported_names` returns `()`.

```rust
// src/typechecker.rs:834-893 — BOTH functions have this identical body:
for (bare_name, source_module) in resolved_imports {
    let current = self.current_module_path.clone();
    let cm = self.modules.entry(current.clone())
        .or_insert_with(|| CompiledModule::new(current));
    let poisoned = cm.insert_import_checked(
        Symbol::from(bare_name.as_str()),
        FQSymbol::new(ModuleFullPath::from(source_module.as_str()), Symbol::from(bare_name.as_str())),
    );
    if poisoned {
        let alts = self.find_ambiguous_alternatives(bare_name);
        if !alts.is_empty() { eprintln!("warning: ..."); }
    }
}
```

**Impact**: Any bug fix or enhancement to the import installation logic must be applied twice. The `Result<(), _>` return on `begin_module_scope` implies error handling that doesn't happen.

**Recommendation**: Extract a private `install_imports_inner(&mut self, resolved_imports: &[(String, String)])` that contains the shared loop. Have `begin_module_scope` and `install_imported_names` both delegate to it. Alternatively, remove `begin_module_scope` entirely and have callers use `install_imported_names` (changing the return type to `()` removes the misleading `Result`).

---

### MED-2: `ImportSpec::module_path` and `ExportSpec::module_path` are untyped `String`

**File**: `src/module.rs:723-741`
**Severity**: Medium (data modeling)

Both `ImportSpec` and `ExportSpec` store the module path as a plain `String`, not a `ModuleFullPath`. The same applies to `resolve_module_imports`'s `mod_name_to_short` parameter (`HashMap<String, String>`). This means the compiler cannot distinguish between a module path and an arbitrary string, and there is no enforcement that the path is well-formed.

```rust
// src/module.rs:723-730
pub struct ImportSpec {
    pub module_path: String,     // should be ModuleFullPath
    pub alias: Option<String>,   // could be ModuleName
    pub names: ImportNames,
    pub span: Span,
}
```

Module paths appear as raw strings in at least six places in `module.rs` and many more in `batch.rs` and `repl.rs`, where they are compared against `ModuleFullPath` using `.as_str()` or string equality. A `ModuleFullPath` wrapping an empty string is the root module; an `ImportSpec::module_path` of `""` would be silently accepted.

**Impact**: No compile-time separation between "a module path written in source" and "a resolved module identity." Mistakes (e.g., using the full dotted path `"core.option"` when the short name `"option"` is needed for a lookup) fail silently or produce confusing errors.

**Recommendation**: Change `ImportSpec::module_path` and `ExportSpec::module_path` to `ModuleFullPath`. The `mod_name_to_short: HashMap<String, String>` in `resolve_module_imports` and callers should become `HashMap<ModuleFullPath, ModuleFullPath>` (long form → short form).

---

### MED-3: `ModuleEntry::Def` carries a denormalized `meta: Option<SymbolMeta>` field marked for removal

**File**: `src/module.rs:129-131`
**Severity**: Medium (data modeling)

`ModuleEntry::Def` has a `meta: Option<SymbolMeta>` field that is a "denormalized copy" of the original `SymbolMeta` kept for backward compatibility. The comment explicitly states it "will be removed once callers migrate to DefKind." This means every `Def` entry carries an extra heap allocation that duplicates data already present in `docstring`, `param_names`, and `kind`.

```rust
// src/module.rs:129-131
/// Denormalized copy of the original SymbolMeta. Kept for backward compatibility
/// with callers that use get_symbol_meta(). Will be removed once callers migrate to DefKind.
meta: Option<SymbolMeta>,
```

`insert_def` (lines 204–266) converts `SymbolMeta` into `DefKind`, `docstring`, and `param_names` — then stores the original `SymbolMeta` again in `meta`. `update_meta` (lines 493–523) updates both `docstring`/`param_names` and `meta`, keeping them in sync manually.

**Impact**: Every `Def` entry stores redundant data. Any code path that updates only one representation (e.g., through `update_meta`) risks inconsistencies. The migration is open-ended with no clear completion criterion.

**Recommendation**: Complete the migration: replace `resolve_symbol_meta_via_modules` in `typechecker.rs` (which reads `meta`) with a function that reconstructs `SymbolMeta` from `DefKind`+`docstring`+`param_names`. Then remove the `meta` field from `ModuleEntry::Def`.

---

### MED-4: `topo_sort` re-sorts the priority queue on every insertion — O(n log n) per node

**File**: `src/module.rs:1631-1643`
**Severity**: Medium (performance)

Kahn's algorithm uses a `Vec<&ModuleFullPath>` as its ready queue and calls `queue.sort_by(...)` once at initialization and then again inside the inner loop every time a new zero-in-degree node is added. For a graph with `n` modules and `e` edges this makes the sort cost O(n * n log n) in the worst case instead of O(n log n).

```rust
// src/module.rs:1631-1643
queue.sort_by(|a, b| a.0.cmp(&b.0));  // initial sort

while let Some(id) = queue.pop() {
    result.push(id.clone());
    for dep_id in deps {
        *deg -= 1;
        if *deg == 0 {
            queue.push(dep_id);
            queue.sort_by(|a, b| a.0.cmp(&b.0));  // re-sorted on every insertion
        }
    }
}
```

**Impact**: Unnecessary work on every module graph build. For typical project sizes (tens of modules) this is not a bottleneck, but the pattern is incorrect and will scale poorly.

**Recommendation**: Use a `BinaryHeap<Reverse<&ModuleFullPath>>` as the ready queue (naturally ordered). Alternatively, insert into the Vec without sorting and sort once at the end when total order must be deterministic within a level. A simpler fix: collect newly-zeroed nodes in a temp vec, sort it, then extend the queue.

---

### MED-5: `resolve_module_imports` calls `get_module_public_names` twice for `MemberGlob`

**File**: `src/module.rs:1707-1715`
**Severity**: Medium (performance)

For an `ImportNames::MemberGlob` import, the function fetches the full public names list (`tc.get_module_public_names(&source_short)`) and then iterates over all constructors filtering by membership. For `Specific` (line 1686) and `Glob` (line 1702) the same call is made but the results are not shared across arms since each arm is its own match branch. While not a major issue, the `MemberGlob` case also allocates a `Vec<String>` (`public`) and then uses `public.contains` (O(n)) inside a loop over constructors.

```rust
// src/module.rs:1707-1715
ImportNames::MemberGlob(type_or_trait) => {
    let public = tc.get_module_public_names(&source_short);  // Vec<String> allocation
    // ...
    for ctor in &tdi.constructors {
        if public.contains(&ctor.name) {  // O(n) per constructor
            resolved.push((ctor.name.clone(), source_short.clone()));
        }
    }
}
```

**Impact**: `get_module_public_names` returns a freshly-allocated `Vec<String>` on every call (because `public_names()` iterates `symbols`). The `contains` check inside the loop makes the overall complexity O(constructors * public_names).

**Recommendation**: Convert `public` to a `HashSet<String>` before the loop, or directly check visibility via the module's symbol table instead of going through the public-names list. For `MemberGlob`, the check `if public.contains(&ctor.name)` could be replaced by `cm.get_visibility(&ctor.name) == Some(Visibility::Public)`.

---

### MED-6: `update_code_ptr_for_slot` does a linear scan over all symbols to find a slot by index

**File**: `src/module.rs:631-653`
**Severity**: Medium (performance)

`update_code_ptr_for_slot` iterates the entire `symbols` HashMap to find the `UserFn` `Def` entry whose `got_slot` matches a given integer. This is an O(n) scan used during cache loading.

```rust
// src/module.rs:631-653
pub fn update_code_ptr_for_slot(&mut self, slot: usize, code_ptr: *const u8) {
    for entry in self.symbols.values_mut() {
        if let ModuleEntry::Def {
            kind: DefKind::UserFn { codegen: DefCodegen { got_slot: Some(s), code_ptr: cp, .. }, .. },
            ..
        } = entry {
            if *s == slot { *cp = Some(code_ptr); return; }
        }
    }
}
```

**Impact**: During cache loading, each function pointer update triggers a full symbol scan. For modules with hundreds of functions this becomes O(n^2) overall.

**Recommendation**: Add an inverse index on `CompiledModule`: `slot_to_symbol: HashMap<usize, Symbol>` populated alongside GOT slot allocation. Then `update_code_ptr_for_slot` becomes an O(1) lookup: find the symbol, then update its entry. Alternatively, pass the symbol name to the function and do a direct `symbols.get_mut(name)` lookup.

---

### LOW-1: `extract_mod_decls` is dead code — only called from its own tests

**File**: `src/module.rs:793-814`
**Severity**: Low (complexity)

`extract_mod_decls` is a narrower version of `extract_module_decls` that only handles `(mod name)` declarations. It is `pub` but is only referenced in the three unit tests below it (lines 1746–1770). `ModuleGraph::discover` uses `extract_module_decls` everywhere.

```rust
// src/module.rs:793-814
pub fn extract_mod_decls(sexps: Vec<Sexp>) -> (Vec<(String, Span)>, Vec<Sexp>) {
    // Only used by tests at lines 1748, 1757, 1767
}
```

**Impact**: A public function that exists only to test a subset of functionality already covered by `extract_module_decls`. Callers outside the module may accidentally use the narrower function.

**Recommendation**: Remove `extract_mod_decls`. Replace its test cases with equivalent calls to `extract_module_decls`, then extract `decls.mod_names`.

---

### LOW-2: `write_got_slot` and `restore_got_entries` call `unwrap()` on the GOT table after `ensure_got`

**File**: `src/module.rs:452-463`
**Severity**: Low (robustness)

`write_got_slot` and `restore_got_entries` call `ensure_got()` and then immediately call `.unwrap()` on `self.got_table`. Because `ensure_got` always allocates the table when it is `None`, the `unwrap()` can never actually panic — but it reads as if there were a fallible path.

```rust
// src/module.rs:452-463
pub fn write_got_slot(&mut self, slot: usize, code_ptr: *const u8) {
    self.ensure_got();
    self.got_table.as_mut().unwrap()[slot] = code_ptr;  // unwrap after ensure_got
}
pub fn restore_got_entries(&mut self, saved: &[(usize, *const u8)]) {
    self.ensure_got();
    let table = self.got_table.as_mut().unwrap();        // unwrap after ensure_got
    // ...
}
```

**Impact**: No runtime danger, but the pattern obscures intent. A reader must trace `ensure_got` to confirm the `unwrap` is safe.

**Recommendation**: Restructure `ensure_got` to return a mutable reference to the table: `fn ensure_got(&mut self) -> &mut [*const u8; GOT_TABLE_SIZE]`. Then `write_got_slot` and `restore_got_entries` call `let table = self.ensure_got();` and use it directly, with no `unwrap`.

---

### LOW-3: `insert_def_checked` silently permits `TraitDecl`/`TypeDef`/`PlatformDecl` entries to be overwritten by a new `Def` without ambiguity

**File**: `src/module.rs:305-306`
**Severity**: Low (robustness)

When `insert_def_checked` detects an existing entry, it marks only `Def`, `Constructor`, and `Macro` entries as `Ambiguous`. `TraitDecl`, `TypeDef`, and `PlatformDecl` fall into the empty arms and are silently replaced by the new `Def`.

```rust
// src/module.rs:301-313
match existing {
    ModuleEntry::Ambiguous => return true,
    ModuleEntry::Import { .. } | ModuleEntry::Reexport { .. } => {}  // shadowed — ok
    ModuleEntry::TraitDecl { .. } | ModuleEntry::TypeDef { .. } => {}  // silently overwritten
    ModuleEntry::PlatformDecl { .. } => {}                             // silently overwritten
    ModuleEntry::Def { .. } | ModuleEntry::Constructor { .. } | ModuleEntry::Macro { .. } => {
        self.symbols.insert(name, ModuleEntry::Ambiguous);
        return true;
    }
}
```

**Impact**: If a module defines a type `Foo` and then a function named `Foo` (or vice versa), the type entry is silently overwritten rather than flagged as ambiguous. This could cause confusing downstream type errors.

**Recommendation**: Verify whether `TypeDef`/`TraitDecl` names are expected to overlap with `Def` names by design (e.g., single-constructor product types use the same name). If not, add those variants to the ambiguity-triggering arm. If they can legitimately coexist, add a comment explaining why.

---

### LOW-4: `resolve_module_imports` takes `mod_name_to_short: &HashMap<String, String>` — an ad-hoc parallel structure that duplicates information already in `tc.modules`

**File**: `src/module.rs:1667`
**Severity**: Low (data modeling)

`resolve_module_imports` receives a `HashMap<String, String>` mapping full module paths to short names. This map is constructed by callers (batch.rs, repl.rs) by iterating `ModuleGraph::compile_order` and `tc.modules`. The same information is available through `ModuleFullPath::short_name()` and `tc.modules.keys()`.

```rust
// src/module.rs:1667
mod_name_to_short: &std::collections::HashMap<String, String>,
```

The map is built in batch.rs lines 211–222 and repl.rs via two separate builder functions (`build_mod_name_map` / `build_loaded_mod_name_map`).

**Impact**: The caller is required to construct and pass a redundant data structure. Both builder functions must be kept in sync with the module loading logic.

**Recommendation**: Have `resolve_module_imports` look up the short name directly from `tc.modules` using `ModuleFullPath::short_name()`. If the full-path-to-short mapping is needed, derive it on-demand from `tc.modules.keys()`. Alternatively, make `resolve_module_imports` accept `ModuleFullPath` references rather than plain strings.

---

### LOW-5: `discover`'s inline-module extraction silently mutates the filesystem during compilation

**File**: `src/module.rs:1356-1426`
**Severity**: Low (robustness)

When `(mod name forms...)` inline module declarations are found, `discover` writes new `.cl` files and rewrites the parent file. This mutation happens unconditionally on every call to `ModuleGraph::build`, not just on first encounter. If the file write fails partway through (e.g., disk full), the parent file may be partially rewritten with no rollback.

```rust
// src/module.rs:1387-1425
if let Err(e) = fs::create_dir_all(&child_dir) { return Err(...); }
if let Err(e) = fs::write(&child_file, ...) { return Err(...); }
// ...
if let Err(e) = fs::write(file_path, &new_source) { return Err(...); }
// No rollback if write fails after partial success
```

**Impact**: A disk error mid-extraction leaves child files written but the parent file unrewritten, corrupting the project state.

**Recommendation**: Document this behavior prominently, or use an atomic write sequence: write all child files to temp locations, then atomically rename both the child files and the rewritten parent. At minimum, check whether extracted child files already exist and match expected content (idempotent extraction) to avoid redundant writes on repeated builds.

---

## Prioritized Improvement Plan

### Phase 1: Safety and Correctness

1. **HIGH-2**: Fix the `require_public` flag being dropped on Import/Reexport chain traversal. Document the invariant or propagate the flag. (1–2 hours)
2. **LOW-3**: Decide whether `TypeDef`/`TraitDecl` names should trigger ambiguity when overwritten by a `Def`. Add a comment or extend the ambiguity check. (30 minutes)

### Phase 2: Complexity Reduction

3. **HIGH-1**: Decompose `discover()` (329 lines) into 6–7 single-responsibility private functions. This is the largest maintainability risk in the module. (Half day)
4. **MED-1**: Unify `begin_module_scope` and `install_imported_names` into a single private function. Remove the misleading `Result<(), _>` return from `begin_module_scope`. (1 hour)

### Phase 3: Data Modeling Cleanup

5. **MED-3**: Complete the `SymbolMeta` migration: implement `SymbolMeta` reconstruction from `DefKind` and remove the `meta` field from `ModuleEntry::Def`. (Half day)
6. **MED-2**: Change `ImportSpec::module_path` and `ExportSpec::module_path` from `String` to `ModuleFullPath`. Update `mod_name_to_short` parameter types to match. (Half day, cascades into batch.rs and repl.rs)
7. **LOW-1**: Remove `extract_mod_decls` (dead code). Migrate its tests to use `extract_module_decls`. (30 minutes)

### Phase 4: Performance

8. **HIGH-3**: Replace `visit_stack: Vec` with `visit_stack: Vec` + `in_progress: HashSet`. Replace `dependencies.contains` with a set-based accumulator. (1–2 hours)
9. **MED-4**: Replace the Kahn priority queue with a `BinaryHeap` or single-sort approach to eliminate per-insertion re-sorts. (30 minutes)
10. **MED-6**: Add `slot_to_symbol: HashMap<usize, Symbol>` to `CompiledModule` and use it in `update_code_ptr_for_slot`. (1 hour)
11. **MED-5**: Change `MemberGlob` resolution to use `HashSet` for membership check, or query visibility directly from the module symbol table. (30 minutes)

### Phase 5: Polish

12. **LOW-2**: Return `&mut [*const u8; GOT_TABLE_SIZE]` from `ensure_got` to eliminate `unwrap()` calls in `write_got_slot` and `restore_got_entries`. (30 minutes)
13. **LOW-4**: Remove `mod_name_to_short` parameter from `resolve_module_imports`; derive short names from `ModuleFullPath::short_name()` instead. (1 hour)
14. **LOW-5**: Document the filesystem side-effects of inline module extraction, or add idempotency checks. (30 minutes)

---

## Verification

After implementing changes, validate with:

```sh
# Run all tests (must remain at ~987 tests passing)
just test

# Static analysis (must have zero warnings beyond existing ones)
just check

# Verify extract_mod_decls removal (should return no results)
grep -rn 'extract_mod_decls\b' src/

# Verify meta field removal (should return no results after MED-3)
grep -rn 'ModuleEntry::Def.*meta:' src/

# Verify unwrap removal in GOT methods (should return no results after LOW-2)
grep -n 'got_table.*unwrap\|unwrap.*got_table' src/module.rs

# Verify begin_module_scope / install_imported_names unification (MED-1)
grep -n 'fn begin_module_scope\|fn install_imported_names' src/typechecker.rs

# Run examples to confirm batch mode still works
just hello
just factorial
```
