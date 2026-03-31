# Step 8: Platform Registry

**Pipeline v4 roadmap step**: `design/arch/pipeline-v4-roadmap.md` §Step 8
**Architecture spec**: `design/arch/pipeline-v4.md` §5.1
**Sprint**: 45
**Arch review findings addressed**: A-1 (FQSymbol keys), A-2 (PlatformFunction in src/)

## Summary

Platform function pointers and scheduling classes are currently scattered across two fields on `CompilationSession`:

- `platform_symbols: Vec<(String, *const u8)>` — JIT symbol name + fn pointer pairs
- `scheduling_registry: SchedulingRegistry` (= `HashMap<Symbol, SchedulingClass>`) — bare function name to scheduling class

These are populated during `(platform ...)` form processing and consumed by codegen (platform_symbols) and bind-chain analysis (scheduling_registry). They share the same data source (the platform DLL manifest) but are stored separately.

Step 8 consolidates them into a single `PlatformRegistry` on `CompilerSession`, keyed by `FQSymbol` per `pipeline-v4.md` §5.1. The registry is populated during platform loading and read-only during codegen.

## PlatformFunction Struct

**Location**: `src/platform_registry.rs` (new file in the binary crate)

Per arch finding A-2, `PlatformFunction` stays in `src/` because it contains `*const u8` (not serializable) and depends on `cranelisp_platform::SchedulingClass`. Putting it in `cranelisp-types` would create a forbidden `cranelisp-types -> cranelisp-platform` dependency.

```rust
use cranelisp_platform::SchedulingClass;
use cranelisp_types::{FQSymbol, ModuleFullPath, Symbol};
use std::collections::HashMap;

/// A platform function registered from a DLL manifest.
///
/// Stores the JIT-linkable function pointer and the scheduling class
/// for bind-chain independence analysis. Keyed by FQSymbol in the
/// registry (e.g., `platform.stdio/print`).
pub struct PlatformFunction {
    /// JIT symbol name used by `Jit::new_with_symbols` (e.g., "cranelisp_print").
    pub jit_name: String,
    /// Function pointer into the loaded DLL.
    pub fn_ptr: *const u8,
    /// Scheduling class from the manifest (Sequential, Commutative, ResourceSerial).
    pub scheduling_class: SchedulingClass,
}

// SAFETY: PlatformFunction contains a raw *const u8 pointing into a loaded DLL.
// The DLL is kept alive for the process lifetime via `loaded_platforms`. The
// pointer is never written through — only passed to JITBuilder::symbol() for
// linking. Send/Sync are needed for the Mutex wrapper on CompilerSession.
unsafe impl Send for PlatformFunction {}
unsafe impl Sync for PlatformFunction {}

/// Registry of all platform functions, keyed by fully qualified symbol.
///
/// Populated during `(platform ...)` form processing. Read-only during
/// codegen and bind-chain analysis. The Mutex wrapper lives on CompilerSession
/// (pipeline-v4.md §5.1), but single-threaded Step 8 accesses it without
/// locking (direct field access before Mutex is added in Step 10).
pub struct PlatformRegistry {
    entries: HashMap<FQSymbol, PlatformFunction>,
}
```

### Key Type: FQSymbol

Per arch finding A-1, the registry uses `FQSymbol` keys (not bare `String`). Platform functions are qualified by their platform module path:

- `platform.stdio/print` — FQSymbol `{ module: "platform.stdio", symbol: "print" }`
- `platform.stdio/read-line` — FQSymbol `{ module: "platform.stdio", symbol: "read-line" }`

This prevents name collisions when two platforms export the same bare name (e.g., `platform.db/query` vs `platform.cache/query`).

### Registry API

```rust
impl PlatformRegistry {
    pub fn new() -> Self {
        PlatformRegistry { entries: HashMap::new() }
    }

    /// Register a platform function. Called during platform DLL loading.
    pub fn register(&mut self, fq: FQSymbol, func: PlatformFunction) {
        self.entries.insert(fq, func);
    }

    /// Get the scheduling class for a symbol, for bind-chain analysis.
    ///
    /// Tries FQSymbol lookup first, then falls back to bare symbol match
    /// (iterating entries where `entry.symbol == symbol`). The fallback
    /// handles the common case where bind-chain analysis has only the
    /// bare name or a partially-qualified name.
    pub fn scheduling_class(&self, symbol: &Symbol) -> Option<SchedulingClass> {
        // Fast path: check all entries for matching bare symbol.
        // Platform registries are small (typically < 20 entries), so
        // linear scan is acceptable.
        for (fq, func) in &self.entries {
            if fq.symbol == *symbol {
                return Some(func.scheduling_class);
            }
        }
        None
    }

    /// Get the scheduling class for a fully qualified symbol.
    pub fn scheduling_class_fq(&self, fq: &FQSymbol) -> Option<SchedulingClass> {
        self.entries.get(fq).map(|f| f.scheduling_class)
    }

    /// Return JIT symbol pairs for Jit::new_with_symbols().
    ///
    /// Produces `Vec<(&str, *const u8)>` matching the existing codegen API.
    /// This is the primary consumption path during compilation.
    pub fn jit_symbols(&self) -> Vec<(&str, *const u8)> {
        self.entries.values()
            .map(|f| (f.jit_name.as_str(), f.fn_ptr))
            .collect()
    }

    /// True if no platform functions are registered.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Build a SchedulingRegistry (HashMap<Symbol, SchedulingClass>) for
    /// backward compatibility with bind_chain_analysis.rs during migration.
    /// Prefer scheduling_class() accessor for new code.
    pub fn to_scheduling_registry(&self) -> HashMap<Symbol, SchedulingClass> {
        self.entries.iter()
            .map(|(fq, func)| (fq.symbol.clone(), func.scheduling_class))
            .collect()
    }
}
```

## Migration Plan for bind_chain_analysis.rs

`bind_chain_analysis.rs` currently defines and consumes `SchedulingRegistry` (`HashMap<Symbol, SchedulingClass>`). The analysis pass needs only the scheduling class for a given symbol name — it does not need the fn pointer.

**Approach**: Option (a) from the arch review — give `PlatformRegistry` a `scheduling_class(symbol) -> Option<SchedulingClass>` accessor. Bind-chain analysis calls this accessor instead of looking up `SchedulingRegistry` directly.

**Changes to bind_chain_analysis.rs**:

1. **Delete** the `SchedulingRegistry` type alias.
2. **Change** `auto_schedule_defn`, `auto_schedule_expr`, `auto_schedule_expr_owned` to accept `&PlatformRegistry` instead of `&SchedulingRegistry`.
3. **Change** `classify_expr` to call `registry.scheduling_class(&symbol)` instead of `registry.get(&symbol)`.
4. **Change** `scheduling_of` public helper similarly.
5. **Update tests** to construct a `PlatformRegistry` instead of a `HashMap<Symbol, SchedulingClass>`. Add a test helper `test_registry()` that registers entries with dummy fn pointers.

The bind-chain analysis pass will depend on the new `PlatformRegistry` type (in `src/platform_registry.rs`). Both are in the binary crate, so no cross-crate dependency change.

The qualified-name fallback in `classify_expr` (stripping `module/` prefix) remains, but now the primary lookup uses `scheduling_class()` which already does bare-symbol matching across all registered entries.

## Call-Site Migration List

### platform_symbols sites (~15 occurrences)

All sites currently take `&[(String, *const u8)]` or `&mut Vec<(String, *const u8)>` and pass them to `Jit::new_with_symbols()`. After migration, they call `registry.jit_symbols()` to produce the same data.

| File | Line(s) | Current | After |
|------|---------|---------|-------|
| `src/session_v4.rs` | 166 | `platform_symbols: &mut self.inner.platform_symbols` on WorkerContext | `platform_registry: &self.platform_registry` |
| `src/worker.rs` | 38 | `pub platform_symbols: &'a mut Vec<(String, *const u8)>` field | `pub platform_registry: &'a PlatformRegistry` |
| `src/worker.rs` | 573 | `ctx.platform_symbols.extend(jit_syms)` in handle_platform | `ctx.platform_registry.register(...)` — see §Platform Loading below |
| `src/worker.rs` | 765 | `ctx.platform_symbols` passed to compile_dep_symbol_inline | `ctx.platform_registry` |
| `src/worker.rs` | 850 | `platform_symbols: &[(String, *const u8)]` param on compile_dep_symbol_inline | `platform_registry: &PlatformRegistry` |
| `src/worker.rs` | 882, 973 | `compile_and_register_defn(inmem_worker, platform_symbols, ...)` | `compile_and_register_defn(inmem_worker, platform_registry, ...)` |
| `src/worker.rs` | 984 | `compile_macro_defn_no_dealloc` param | `platform_registry: &PlatformRegistry` |
| `src/worker.rs` | 1278 | `codegen_module_symbols` param | `platform_registry: &PlatformRegistry` |
| `src/worker.rs` | 1338, 1369 | `compile_mono_defns`, `compile_regular_defns` params | `platform_registry: &PlatformRegistry` |
| `src/worker.rs` | 1466 | `ctx.platform_symbols` passed to codegen_module_symbols in worker loop | `ctx.platform_registry` |
| `src/pipeline.rs` | 283 | `session.platform_symbols.extend(jit_syms)` in load_platform_forms | Delete — old path |
| `src/pipeline.rs` | 508, 643, 664 | `&session.platform_symbols` passed to compile functions | `&session.platform_registry()` or similar |
| `src/pipeline.rs` | 560, 676, 787, 823, 900, 975, 1082 | `platform_symbols: &[(String, *const u8)]` params on compile helpers | `platform_registry: &PlatformRegistry` |
| `src/repl/mod.rs` | 650, 709, 723, 782 | `platform_symbols: &mut self.core.platform_symbols` | `&self.core.platform_registry` — old REPL path |
| `src/session.rs` | 549, 760, 997, 1034 | `self.platform_symbols` field and usages | Field deleted; old-path callers migrate to registry |

### scheduling_registry sites (~4 occurrences)

| File | Line(s) | Current | After |
|------|---------|---------|-------|
| `src/pipeline.rs` | 278 | `session.scheduling_registry.insert(Symbol, SchedulingClass)` | Delete — registry populated by handle_platform |
| `src/pipeline.rs` | 306-309 | `if !session.scheduling_registry.is_empty()` + `apply_bind_chain_analysis(&mut program, &session.scheduling_registry)` | `apply_bind_chain_analysis(&mut program, &session.platform_registry)` — pass PlatformRegistry |
| `src/session.rs` | 553, 599, 633, 666 | `scheduling_registry` field and initialization | Delete field |
| `src/bind_chain_analysis.rs` | 27 | `pub type SchedulingRegistry = HashMap<Symbol, SchedulingClass>` | Delete type alias |

## WorkerContext Field Change

**Before**:
```rust
pub struct WorkerContext<'a> {
    pub tc: &'a mut cranelisp_typecheck::TypeChecker,
    pub scheduler: &'a mut CompileScheduler,
    pub inmem_worker: &'a mut InMemWorkerState,
    pub platform_symbols: &'a mut Vec<(String, *const u8)>,
    pub lib_dirs: &'a [PathBuf],
    pub project_root: &'a Path,
}
```

**After**:
```rust
pub struct WorkerContext<'a> {
    pub tc: &'a mut cranelisp_typecheck::TypeChecker,
    pub scheduler: &'a mut CompileScheduler,
    pub inmem_worker: &'a mut InMemWorkerState,
    pub platform_registry: &'a mut PlatformRegistry,
    pub lib_dirs: &'a [PathBuf],
    pub project_root: &'a Path,
}
```

The field remains `&'a mut` (not `&'a`) because `handle_platform` mutates the registry during platform loading. Once all platform forms are processed, the registry is effectively read-only for the remainder of compilation. Codegen functions receive `&PlatformRegistry` (immutable borrow), obtained via re-borrowing.

**Construction site** (session_v4.rs `register_module`):
```rust
let mut ctx = WorkerContext {
    tc: &mut self.inner.tc,
    scheduler: &mut self.scheduler,
    inmem_worker: &mut self.inner.inmem_worker,
    platform_registry: &mut self.platform_registry,
    lib_dirs: &self.inner.lib_dirs,
    project_root: &self.inner.project_root,
};
```

## Platform Loading Change

`handle_platform` in `worker.rs` currently:
1. Calls `load_and_register_platform(tc, name, root, span)` which returns `(LoadedPlatform, Vec<(String, *const u8)>)`.
2. Extends `ctx.platform_symbols` with the JIT symbols.

After migration, `handle_platform` additionally registers each function in the `PlatformRegistry`:

```rust
fn handle_platform(ctx: &mut WorkerContext, spec: &PlatformSpec) -> Result<(), CranelispError> {
    let (platform, _jit_syms) = crate::platform::load_and_register_platform(
        ctx.tc, &spec.name, ctx.project_root, spec.span,
    )?;

    // Register each function in the unified platform registry.
    let module_path = ModuleFullPath::from(format!("platform.{}", platform.name));
    for desc in &platform.descriptors {
        let fq = FQSymbol {
            module: module_path.clone(),
            symbol: Symbol::from(desc.name.as_str()),
        };
        ctx.platform_registry.register(fq, PlatformFunction {
            jit_name: desc.jit_name.clone(),
            fn_ptr: desc.ptr,
            scheduling_class: desc.scheduling_class,
        });
    }

    // Platform DLLs are leaked (kept alive for process lifetime).
    Ok(())
}
```

The `_jit_syms` return from `load_and_register_platform` is now unused by the v4 path. The old-path `load_platform_forms` in `pipeline.rs` still uses it until Step 15 cleanup. Consider adding a `#[allow(unused)]` or removing the return value from `load_and_register_platform` once the old path is deleted.

## CompilerSession Field Addition

```rust
pub struct CompilerSession {
    inner: CompilationSession,
    pub scheduler: CompileScheduler,
    pub project_root: PathBuf,
    /// Unified platform function registry (Step 8).
    /// Populated during platform loading, read-only during codegen.
    pub platform_registry: PlatformRegistry,
}
```

Initialized in `CompilerSession::new()` and `new_for_link()`:
```rust
platform_registry: PlatformRegistry::new(),
```

## Deletion Checklist

Once all call sites are migrated to `PlatformRegistry`:

| Item | Location | Notes |
|------|----------|-------|
| `platform_symbols: Vec<(String, *const u8)>` | `CompilationSession` (session.rs:549) | Field + initialization in `new()`, `new_async()`, `new_async_with_cache()` |
| `scheduling_registry: SchedulingRegistry` | `CompilationSession` (session.rs:553) | Field + initialization in same three constructors |
| `platform_symbols` clone in `CodegenPacket` | session.rs:760 | Used by old-path async codegen |
| `SchedulingRegistry` type alias | bind_chain_analysis.rs:27 | Replaced by PlatformRegistry API |
| `apply_bind_chain_analysis` scheduling_registry param | session.rs (wherever called) | Takes PlatformRegistry instead |

**Old-path coexistence**: The old `CompilationSession` fields (`platform_symbols`, `scheduling_registry`) may still be needed by the old REPL path (`src/repl/mod.rs`) and old batch path (`pipeline.rs`'s `compile_unit` method) until Step 15 deletes them. If so, keep both during this sprint and mark the old fields with a `// Step 15: delete` comment. If the old path is already dead for all modes, delete immediately.

## Codegen Interface

Codegen functions (`compile_and_register_defn`, `compile_and_execute_expr`, etc.) currently receive `platform_symbols: &[(String, *const u8)]` and convert it to `Vec<(&str, *const u8)>` for `Jit::new_with_symbols()`:

```rust
let extra_symbols: Vec<(&str, *const u8)> = platform_symbols
    .iter()
    .map(|(name, ptr)| (name.as_str(), *ptr))
    .collect();
let mut jit = Jit::new_with_symbols(&extra_symbols)?;
```

After migration, the conversion uses the registry's `jit_symbols()` method:

```rust
let extra_symbols = platform_registry.jit_symbols();
let mut jit = Jit::new_with_symbols(&extra_symbols)?;
```

This is a mechanical signature change. The `Jit::new_with_symbols` API remains unchanged.

## Testability

Per arch principle 5, the registry should be testable without loading a real DLL.

```rust
#[cfg(test)]
impl PlatformRegistry {
    /// Create a test registry with synthetic entries.
    pub fn with_test_entries(entries: Vec<(FQSymbol, SchedulingClass)>) -> Self {
        let mut reg = PlatformRegistry::new();
        for (fq, sc) in entries {
            reg.register(fq, PlatformFunction {
                jit_name: format!("test_{}", fq.symbol),
                fn_ptr: std::ptr::null(),
                scheduling_class: sc,
            });
        }
        reg
    }
}
```

The bind-chain analysis tests migrate from constructing `HashMap<Symbol, SchedulingClass>` to using `PlatformRegistry::with_test_entries`.

## Sketch Comparison

**How the sketch handles this**: The sketch stores platform function pointers in the JIT builder via `register_non_platform_symbols` (jit.rs:143) and accumulates scheduling classes in the typechecker's primitives module (typechecker/primitives.rs:979). There is no unified registry — the two data paths are separate, matching the reimplementation's pre-Step-8 state. The sketch has no `FQSymbol` concept; platform functions are registered by bare name.

**Whether the reimplementation follows or diverges**: The reimplementation **diverges** from the sketch by:
1. Consolidating platform data into a single `PlatformRegistry` (the sketch keeps them separate).
2. Using `FQSymbol` keys (the sketch uses bare strings).
3. Making the registry a first-class session field (the sketch scatters data across JIT builder and typechecker).

**Rationale for divergence**: The sketch's scattered approach is the exact debt being repaired. The dual-pipeline defect analysis (`pipeline-convergence-review.md`) identified scattered state as a root cause of code duplication. The unified registry follows the "single source of truth" principle (arch principle 7) and the pipeline-v4.md target architecture (§5.1). `FQSymbol` keys prevent name collisions per the string newtype convention (`src/CLAUDE.md`).

## Verification

- All existing tests pass (no behavioral change).
- Programs with `(platform ...)` forms compile and execute correctly.
- IO trampoline works (platform functions called through registry fn pointers).
- Bind-chain analysis produces the same `ParBind` nodes as before.
- `cargo test` in `src/bind_chain_analysis.rs` passes with updated test helpers.
