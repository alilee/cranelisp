# compile_to_module<M: Module> — Unified Compilation Function

Design for replacing all compilation paths — JIT batch, REPL expression, and object file — with a single generic function parameterised by Cranelift module type.

`compile_to_module<M>` is the ONLY compilation entry point in the backend crate. The backend's public compilation API is exactly two functions: `compile_to_module<M: Module>` and `declare_intrinsics<M: Module>`. Nothing else.

**Status**: Design document — PRESCRIPTIVE for §2 and §15. Replaces the ad-hoc object compilation path described in module-caching.md §13.11, and subsumes the REPL expression compilation path (`compile_expr_with_got_and_symbols`).

**Revision history**:
- Original: five-parameter signature `(module_path, program, typecheck, symbol_tables, module)`.
- Sprint 55 (Phase 1): dropped `typecheck: &CheckResult`; annotations moved onto AST nodes, mangled bodies moved onto symbol-table entries (see `ast-sourced-codegen.md`).
- Sprint 56 (Phase 2, this revision): dropped `program: &Program`; backend reads defn bodies from `symbol_tables[module_path]` via `names: &[Symbol]`. Current normative signature is four parameters — see §2.1 and §16. §13 describes the Sprint-55 migration path; §16 describes the Sprint-56 migration path.

## 1. Problem Statement

The JIT batch path (`compile_program` in `lib.rs`), the REPL expression path (`compile_expr_with_got_and_symbols` in `lib.rs`), and the object path (`compile_module_to_object` in `cache/object.rs`) all perform the same logical work but are separate implementations:

1. **Defn collection**: JIT uses `collect_and_declare_defns` (handles multi-sig, constrained, mono, defaults). Object uses `collect_defns_for_cache` (broken — panics on `DefnMulti`).
2. **Function declaration**: JIT declares against `JITModule`. Object declares against `ObjectModule`. Same Cranelift `Module` API.
3. **GOT / cross-module references**: JIT reads live GOT state via bespoke session plumbing. Object invents sequential slot numbers instead of reading `SymbolTable.got_slot`. The Phase 2 design replaces both with uniform emission against `Linkage::Import` data symbols (§12).
4. **Function compilation**: Both use `FnCompiler<M: Module>`. Same code, different wiring.
5. **Intrinsic declaration**: JIT uses `Jit::declare_intrinsics()`. Object uses `declare_intrinsic_imports()`. Same set of symbols, different declaration paths.

Additionally, `compile_expr_with_got_and_symbols` is a third compilation path for REPL expressions. It creates a fresh JIT, declares intrinsics, defines GOT data entries, wraps the expression in a synthetic zero-arg `Defn`, declares and compiles that one function, finalizes, and returns the pointer. This is exactly `compile_to_module<JITModule>` with a one-defn program — the only caller-specific parts are the extra symbols on the JITBuilder and the GOT data definitions, both of which are the caller's responsibility before module creation.

This triplication causes:
- Multi-sig crash in the object path (`defn.params()` panics on `DefnMulti`).
- Invented GOT slot numbers that don't match the JIT's actual slots.
- Redundant data assembly in `ObjectCompileInput`, `CodegenInput`, `build_object_compile_input`.
- Three code paths that can (and do) diverge silently.
- `CompiledExpr` struct that exists only to hold a `Jit` alive — unnecessary once the caller owns the module.

## 2. Target API — PRESCRIPTIVE

This section is normative. The function signature, parameter list, and constraints MUST be implemented exactly as written. No additional parameters. No restructuring of the signature.

### 2.1 Exact Signature

```rust
pub fn compile_to_module<M: Module>(
    module_path: ModuleFullPath,
    names: &[Symbol],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable>,
    module: &mut M,
) -> Result<CompilationResult, CranelispError>
```

**Four parameters. No more. No optional parameters. No feature flags.** This signature is normative — the Phase 2 target. It replaces the five-parameter `(path, program, typecheck, symbol_tables, module)` shape from earlier revisions, and the four-parameter `(path, program, symbol_tables, module)` intermediate shape introduced in Sprint 55 when `CheckResult` was eliminated.

| Parameter | What it is | Where caller gets it |
|-----------|-----------|---------------------|
| `module_path` | Identity of the module being compiled | DashMap key, scheduler, or hardcoded for batch |
| `names` | The set of defined symbols in `module_path` that codegen must produce | `symbol_tables[module_path].defined_symbols().collect()` for a full module compile; filtered subset for partial compile / mono batches / per-function JIT |
| `symbol_tables` | All module symbol tables (GOT slots, imports, schemes, AST bodies, annotations) | `SharedState.symbol_tables` |
| `module` | Cranelift module to populate | Caller creates `JITModule` or `ObjectModule` |

`names` carries only symbol identifiers — no AST, no types, no resolutions. The backend retrieves everything from `symbol_tables[module_path]` by name:

- **Body + annotations**: `ModuleEntry::Def.ast: Some(Defn)` — a single-variant `Defn` whose `Expr` nodes carry `inferred_type` and `resolved_call` (Sprint 55 Phase 1 groundwork — see `ast-sourced-codegen.md`).
- **Type signature**: `ModuleEntry::Def.scheme`.
- **GOT slot**: `ModuleEntry::Def.got_slot`.
- **Kind** (regular / `Overloaded` base / `UserFn { constrained_fn }` template / etc.): `ModuleEntry::Def.kind`.

**Precondition on `names` (Wave 0 contract, enforced by `/typecheck`)**: for every name in `names`, the symbol table entry must carry `ast: Some(_)` — including mangled multi-sig variants and mono specializations. See `design/typecheck/ast-annotation.md` for the authoritative table of which entry categories carry `ast: Some(_)` post-Phase-2. A `None` body is a typecheck bug, not a legitimate input state; `compile_to_module` returns a codegen error naming the symbol rather than silently skipping it.

**Callers obtain `names` via `SymbolTable::defined_symbols()`**, which yields exactly the set of names that codegen must produce (filtered to `ast.is_some()` AND kind-is-not-`Overloaded` AND kind-is-not-`UserFn { constrained_fn: Some(_) }`). This is the shared predicate — the same filter is used by the priority worker when deciding what to hand to `compile_to_module` and by the backend if it re-enumerates internally. It lives on `SymbolTable` in `cranelisp-types` so both sides agree without duplication (addresses `/arch` review §6 condition 5).

### 2.2 Hard Constraints

1. **No caller-provided intrinsic IDs.** `compile_to_module` declares intrinsics internally on the module.
2. **No caller-provided GOT resolution.** GOT *slot assignments* are read from `symbol_tables[module_path]` entries (`ModuleEntry::Def { got_slot }`). GOT *base addresses* are resolved at module finalize time by the `Module` implementation — never internally by `compile_to_module`. The backend emits the same CLIF regardless of mode: a `global_value` against a `Linkage::Import` data symbol named `__cranelisp_got_{module}`. For `ObjectModule`, the linker patches the relocations at load. For `JITModule`, the caller pre-registers `JITBuilder::symbol_lookup_fn` that resolves `__cranelisp_got_{name}` → `symbol_tables[name].got.base_ptr()` before the module is built (see `design/arch/pipeline-v4.md` §9.3 and Decision 22 / Principle 11 in `design/arch/CLAUDE.md`).
3. **No caller-provided function arities.** Derived from the defns being compiled.
4. **No JIT prefix parameter.** Module-qualified JIT names derived from `module_path` internally.
5. **No traced_fns parameter.** Tracing is a runtime/GOT concern, not a compilation concern.
6. **No prior_funcs or cross-module func sigs.** Cross-module references resolved from `symbol_tables` (follow Import chains).
7. **No extra JIT symbols or GOT data defs.** Caller registers these on the JITBuilder/module before creating it — not a compile_to_module concern.

### 2.3 What the function derives internally

| Concern | Source | NOT passed by caller |
|---------|--------|---------------------|
| Intrinsic FuncIds | Declares intrinsics on `module` internally | Not a parameter |
| **Defn bodies** | `symbol_tables[module_path].get(name).ast.as_ref()` — required to be `Some(_)` | Not a parameter |
| **Resolved calls** | `Expr::Apply.resolved_call` on each AST node in the body | Not a parameter — on the AST |
| **Expression types** | `Expr.inferred_type` on each AST node | Not a parameter — on the AST |
| **Constrained-fn filter** | `SymbolTable::defined_symbols()` excludes `UserFn { constrained_fn: Some(_) }` templates at enumeration time | Not a parameter — and no inline scan of the symbol table inside `compile_to_module` |
| **Multi-sig variant bodies** | Pre-materialised by Wave 0 as mangled `ModuleEntry::Def` entries carrying `ast: Some(_)` — backend never expands at codegen time | Not a parameter |
| **Mono specialization bodies** | Pre-materialised by Wave 0 as mangled `ModuleEntry::Def` entries carrying `ast: Some(_)` with all post-pass resolutions applied | Not a parameter |
| **Default method bodies** | Already materialised on mangled entries (Phase 1 — `register_mangled_method`) | Not a parameter |
| GOT slot assignments | `symbol_tables[module_path]` → `ModuleEntry::Def { got_slot }` | Not a parameter |
| GOT base resolution | **Uniform** — backend emits `global_value` against `Linkage::Import` data symbol `__cranelisp_got_{module}`. Object: linker patches relocation. JIT: caller pre-registers `JITBuilder::symbol_lookup_fn` mapping `__cranelisp_got_{name}` → `symbol_tables[name].got.base_ptr()`. See §12. | Not a parameter |
| Cross-module refs | `symbol_tables[module_path]` → `ModuleEntry::Import { source }` chain | Not a parameter |
| Function arities | `Defn.params().len()` on the AST retrieved from each entry | Not a parameter |
| JIT name prefix | Derived from `module_path` | Not a parameter |

The rows marked in bold are new or changed in Phase 2. In particular, `CheckResult` no longer appears anywhere in this table — Sprint 55 removed it as a boundary type (`method_resolutions` and `expr_types` live on AST nodes; `mono_defns`, `default_method_defns`, and `constrained_fn_names` are all sourced from symbol-table entries after Wave 0).

### 2.4 No Internal Fork

There is no internal fork inside `compile_to_module`. Backend IR is byte-identical across JIT and object modes — same CLIF, same instruction selection, same GOT reference encoding. Mode differences live entirely in the `Module` implementation at finalize time. See §12 for the uniform GOT emission strategy.

### 2.5 Caller Usage

The caller creates the module, builds the `names` list, and passes them in. `compile_to_module` reads bodies and annotations from `symbol_tables[module_path]` for each name, populates and finalises the module. The caller then processes the result:

```rust
// JIT caller (priority worker, per-function isolation per §9.4):
// Typical case: compile exactly one symbol at a time into its own JITModule.
let names = vec![symbol_name.clone()];
let result = compile_to_module(module_path.clone(), &names, &symbol_tables, &mut jit_module)?;
for (jit_name, func_id) in &result.func_ids {
    let ptr = jit_module.get_finalized_function(*func_id);
    // Write ptr into the module's GOT slot
}

// JIT caller (REPL expression — synthetic `__expr` defn):
// Typecheck has registered `__expr` on the REPL module's symbol table with
// `ast: Some(...)` carrying the wrapped expression body. The REPL just hands
// that one name to compile_to_module.
let names = vec![Symbol::from("__expr")];
let result = compile_to_module(repl_module.clone(), &names, &symbol_tables, &mut jit_module)?;
let entry_ptr = jit_module.get_finalized_function(result.entry_func_id.unwrap());

// Object caller (nice worker, --link):
// Full module compile — enumerate every defined symbol.
let names: Vec<Symbol> = symbol_tables
    .get(&module_path)
    .map(|t| t.defined_symbols().collect())
    .unwrap_or_default();
let result = compile_to_module(module_path.clone(), &names, &symbol_tables, &mut obj_module)?;
let bytes = obj_module.finish().emit()?;
// Write bytes to .o file
```

`Jit` is `pub(crate)` — callers work with `JITModule` directly (from cranelift_jit). No backend wrapper types in the public API except `CompilationResult`.

**`names` as an ordered list**. The iteration order of `names` determines compilation order, which determines the "last zero-arg defn" chosen for `entry_func_id` and the order of `func_ids` population. Callers that care (e.g., `--run` batch mode picking a main entry) pass a deterministic order (typically source order); callers that don't (nice worker `.o` emission) may pass any stable enumeration.

## 3. Function Signature and Generic Constraints

### What `M: Module` provides

The `cranelift_module::Module` trait (from Cranelift v0.125) provides all APIs needed for function/data declaration, definition, and compilation. Both `JITModule` and `ObjectModule` implement it. `FnCompiler` is already generic over `M: Module`. No additional trait bounds are needed.

## 4. Defn Collection — Symbol-Table Sourced

After Phase 2, `compile_to_module` does not collect defns from a `Program` and does not expand multi-sig base defns. Every name the backend will compile already exists as a mangled `ModuleEntry::Def` entry with `ast: Some(_)`. The "collection" step is a direct lookup loop:

```rust
// Phase 2: look up each name's entry and retrieve its AST body.
let table = symbol_tables.get(&module_path).ok_or_else(|| CranelispError::CodegenError {
    message: format!("no symbol table for module '{}'", module_path),
    span: Span::SYNTHETIC,
})?;

let mut defns: Vec<Defn> = Vec::with_capacity(names.len());
for name in names {
    let entry = table.get(name.as_ref()).ok_or_else(|| CranelispError::CodegenError {
        message: format!("symbol '{}' not found in module '{}'", name, module_path),
        span: Span::SYNTHETIC,
    })?;
    let ModuleEntry::Def { ast, .. } = entry else {
        return Err(CranelispError::CodegenError {
            message: format!("symbol '{}' in module '{}' is not a compilable Def (wrong ModuleEntry variant)", name, module_path),
            span: Span::SYNTHETIC,
        });
    };
    let defn = ast.as_ref().ok_or_else(|| CranelispError::CodegenError {
        message: format!(
            "symbol '{}' in module '{}' has no AST body (ast: None) — Wave 0 invariant violated; \
             see design/typecheck/ast-annotation.md for the categories of entries that must carry ast: Some(_)",
            name, module_path
        ),
        span: Span::SYNTHETIC,
    })?;
    defns.push(defn.clone()); // or &'a Defn if we hold the DashMap guard
}
```

**No base-defn expansion.** The pre-Phase-2 backend split `DefnMulti` into per-variant `Defn`s at codegen time via `expand_multi_sig_defn`. After Wave 0, each variant is already a separate symbol-table entry keyed by its mangled name (`add$Int+Int`, `add$Float+Float`, …), each carrying a single-variant `Defn` in its `ast`. The backend treats them as ordinary defns. `expand_multi_sig_defn` (currently at `crates/cranelisp-backend/src/lib.rs:379-436`) is deleted.

**No constrained-template scan.** The pre-Phase-2 backend scanned the symbol table for `UserFn { constrained_fn: Some(_) }` templates and excluded them from compilation inline (`lib.rs:95-109`). After Phase 2 that filter lives in `SymbolTable::defined_symbols()` — the iterator never yields template names, so `compile_to_module` sees only things it can compile. The inline scan is deleted.

**No default-method / mono injection.** The pre-Phase-2 backend received `default_method_defns` and `mono_defns` via `CheckResult` (since Sprint 55, the caller in `finalize_module` inlined them into `program` before calling the backend). After Wave 0 every such body already lives on a mangled `ModuleEntry::Def` entry; the `finalize_module` inlining path goes away (owned by `/int` in Step 2b, but the backend-side consequence is that `compile_to_module` does no special handling for these categories — they appear in `names` like any other symbol).

### GOT slot assignments

GOT slots continue to be **read from the symbol table**, not invented:

```rust
for name in names {
    if let Some(ModuleEntry::Def { got_slot: Some(slot), .. }) = table.get(name.as_ref()) {
        fn_slot_assignments.insert(name.clone(), FnSlotInfo {
            slot: *slot,
            param_count: /* defn.params().len() from the ast retrieved above */,
        });
    }
}
```

This is unchanged in structure from the Sprint-55 shape — the only difference is that the `defn_ref.params().len()` comes from the AST retrieved by symbol-table lookup rather than from an AST owned by an incoming `program: &Program`.

## 5. GOT Reference Encoding — Uniform Across Modes

The JIT path and object path emit **identical** CLIF for every GOT reference. There is no per-mode fork inside `compile_to_module` — see §12 for the authoritative description.

At each GOT load site `FnCompiler` emits:

| Step | CLIF |
|------|------|
| 1. Declare | `module.declare_data_in_func` on a `Linkage::Import` data symbol named `__cranelisp_got_{target_module}` |
| 2. Load base | `global_value(got_data_gv)` — the data symbol's address |
| 3. Indexed load | `load(i64, base, slot * 8)` where `slot` is read from `symbol_tables[target_module].get(name).got_slot` |

Mode differences live in the passed-in `Module` implementation at finalize time:
- `ObjectModule` emits relocations; the linker patches the data symbol at load.
- `JITModule` queries the caller-registered `JITBuilder::symbol_lookup_fn`, which returns `symbol_tables[name].got.base_ptr()`.

### What changes for compile_to_module

Nothing specific to GOT emission. Both modes receive the same IR. `FnCompiler` reads slot assignments from `symbol_tables` and emits `global_value` uniformly; it does not know (and does not need to know) which `Module` implementation it is targeting.

### GOT data symbols (ObjectModule only)

For the object path, `compile_to_module` must declare GOT data symbols before compilation. This is a pre-step that only applies when `M` is `ObjectModule`:

```rust
// Before calling compile_to_module for ObjectModule:
let got_data_ids = declare_got_data_symbols(&mut obj_module, &current_module, &fn_to_module)?;
define_got_data(&mut obj_module, ...)?;
```

These helper functions (`declare_got_data_symbols`, `define_got_data`) remain in `cache/object.rs` as ObjectModule-specific setup. They are called by the nice worker before `compile_to_module`, not inside it.

**Alternative considered**: making `compile_to_module` internally detect `ObjectModule` and set up GOT data symbols. Rejected — this would require runtime type detection (`TypeId`/downcasting) or a second trait bound, both ugly. Keeping GOT data symbol setup outside `compile_to_module` is cleaner: the function compiles code, the caller prepares the module.

## 6. Intrinsic Declaration

Currently handled differently:
- JIT: `Jit::declare_intrinsics()` — declares runtime + primitive functions against `JITModule`.
- Object: `declare_intrinsic_imports()` — declares the same set against `ObjectModule` as imports.

### Unified approach

Extract a generic `declare_intrinsics<M: Module>(module: &mut M)` function:

```rust
/// Declare all runtime and primitive intrinsics in a Cranelift module.
///
/// For JITModule: these resolve to function pointers registered via JITBuilder::symbol().
/// For ObjectModule: these become Import symbols resolved by the linker.
pub fn declare_intrinsics<M: Module>(
    module: &mut M,
) -> Result<IntrinsicFuncIds, CranelispError> {
    let mut ids = IntrinsicFuncIds::default();

    for sym in intrinsic_symbols() {
        let mut sig = module.make_signature();
        for _ in 0..sym.param_count {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let linkage = Linkage::Import; // JITModule resolves imports via symbol table
        let func_id = module.declare_function(sym.name, linkage, &sig)?;
        ids.register(sym.name, func_id);
    }

    Ok(ids)
}
```

`IntrinsicFuncIds` replaces the current approach where intrinsic FuncIds are scattered across `Jit` fields and ad-hoc lookup maps:

```rust
/// FuncIds for all intrinsic functions, populated during declare_intrinsics.
///
/// Convenience-accessor fields are stored as `Option<FuncId>` internally because
/// intrinsic declaration is a two-phase affair on the `Jit` wrapper (the struct
/// exists before `declare_intrinsics` runs). Once intrinsics have been declared
/// and the `CompileContext` is built, the fields consumed inside codegen are
/// non-optional `FuncId` values — see Decision 24.
#[derive(Default)]
pub struct IntrinsicFuncIds {
    by_name: HashMap<Symbol, FuncId>,
    // Convenience accessors for commonly-used intrinsics
    pub alloc: Option<FuncId>,
    pub dealloc: Option<FuncId>,
    pub alloc_string: Option<FuncId>,
    pub panic: Option<FuncId>,
    pub vec_new: Option<FuncId>,
    pub vec_drop: Option<FuncId>,
}
```

The `IntrinsicTable` struct (currently in `cache/object.rs`) becomes unnecessary for compilation — it was a workaround for the object path not sharing the JIT's intrinsic declaration. It may be retained for cache metadata serialization if needed, but is no longer an input to `compile_to_module`.

**Note**: For `JITModule`, the symbols must be registered in the `JITBuilder` before module creation (via `JITBuilder::symbol()`). This happens before `compile_to_module` is called and is unchanged.

## 7. Function Compilation

`FnCompiler<M: Module>` is already generic. The compilation loop inside `compile_to_module`:

```rust
// Declare all functions (Pass 1)
let mut func_ids: HashMap<Symbol, FuncId> = intrinsic_ids.by_name.clone();
for defn in &defns { // defns collected per §4 from symbol-table entries
    let mut sig = module.make_signature();
    for _ in defn.params() {
        sig.params.push(AbiParam::new(types::I64));
    }
    sig.returns.push(AbiParam::new(types::I64));
    let func_id = module.declare_function(defn.name.as_ref(), Linkage::Export, &sig)?;
    func_ids.insert(defn.name.clone(), func_id);
}

// Compile each function body (Pass 2)
let mut func_ctx = FunctionBuilderContext::new();
for defn in &defns {
    let compile_ctx = CompileContext {
        // Note: method_resolutions / expr_types removed from CompileContext
        // in Sprint 55 — those live on AST nodes now.
        func_ids: &func_ids,
        func_arities: &func_arities,
        symbol_tables,
        current_module: module_path.clone(),
        env,
        traced_fns: None,
        alloc_func_id: intrinsic_ids.alloc,
        dealloc_func_id: intrinsic_ids.dealloc.expect("dealloc must be declared"),
        alloc_string_func_id: intrinsic_ids.alloc_string,
        panic_func_id: intrinsic_ids.panic,
        vec_new_func_id: intrinsic_ids.vec_new,
        vec_drop_func_id: intrinsic_ids.vec_drop,
    };
    // CompileContext.dealloc_func_id is a non-optional FuncId per Decision 24 —
    // the split convention's caller-suppressible dealloc flag is gone. Extract
    // the concrete FuncId once at the compile-site and pass it in unconditionally.

    FnCompiler::compile_body(defn, &mut func, &mut func_ctx, module, compile_ctx)?;

    let mut ctx = Context::for_function(func);
    module.define_function(func_id, &mut ctx)?;
}
```

**No separate mono loop.** Mono specializations are ordinary entries in `names` after Wave 0; their AST nodes carry their own `inferred_type` and `resolved_call` annotations. The pre-Phase-2 "merge base resolutions with per-specialization resolutions" dance is obsolete — there is no base `method_resolutions` map to merge against, and nothing per-specialization to splice in; each mono defn reads its resolutions from its own AST.

### What changes in FnCompiler

Nothing. `FnCompiler` is already `FnCompiler<'a, M: Module>`. Its `compile_body` method takes `&mut M` and works with both `JITModule` and `ObjectModule`. GOT reference encoding is uniform — `FnCompiler` reads slot assignments from `symbol_tables` and emits a `global_value` against a `Linkage::Import` data symbol for every mode (§12). There is no env parameter on `CompileContext`.

### Cross-module function references (ObjectModule)

For the object path, cross-module functions must be declared as `Linkage::Import` so the linker can resolve them. This is done before the compilation loop:

```rust
// For ObjectModule only: declare cross-module function imports
// (already done by the nice worker before calling compile_to_module)
for (name, param_count) in &cross_module_fns {
    if func_ids.contains_key(name) { continue; }
    let bare_name = bare_fn_name(name);
    let mut sig = module.make_signature();
    // ...
    let func_id = module.declare_function(bare_name, Linkage::Import, &sig)?;
    func_ids.insert(name.clone(), func_id);
}
```

For JIT, cross-module functions are already in the shared JIT symbol table and don't need separate declaration.

**Decision**: Cross-module function declarations are part of module preparation (done by the caller), not part of `compile_to_module`. This keeps `compile_to_module` focused on compilation, not module setup. The caller (priority worker or nice worker) handles the mode-specific preparation before calling the shared function.

## 8. Return Type

```rust
/// Result of compiling a program's functions into a module.
///
/// Module-type-agnostic: the caller extracts what it needs.
/// For JIT: uses `entry_func_id` to get the entry point after finalization.
/// For ObjectModule: ignores `entry_func_id` (no entry needed for .o files).
pub struct CompilationResult {
    /// FuncIds for all compiled functions (name -> FuncId).
    /// The caller uses these to get finalized pointers (JIT) or
    /// to verify all expected functions were compiled (Object).
    pub func_ids: HashMap<Symbol, FuncId>,

    /// Per-symbol compilation artifacts for introspection
    /// (CLIF IR, disassembly, code size). See §8.1.
    pub artifacts: HashMap<Symbol, FunctionArtifacts>,

    /// FuncId of the entry function (last zero-arg defn), if any.
    /// Used by JIT batch mode to get the entry point.
    /// None for modules that have no zero-arg function (library modules, .o files).
    pub entry_func_id: Option<FuncId>,

    /// Function arities for all compiled functions (for closure wrapper generation).
    pub func_arities: HashMap<Symbol, usize>,

    /// Warnings accumulated during codegen.
    pub warnings: Vec<Warning>,
}
```

### 8.1 Artifacts by symbol (Phase 3a — condition 1)

`compile_to_module` captures per-symbol codegen byproducts needed for introspection slash commands (`/clif`, `/disasm`, `/time`) and returns them keyed by `Symbol`. This keeps `Introspection` (defined in `pipeline-v4.md` §9.6) strictly **separate** from compilation: the backend does not know, and does not care, whether the caller intends to display these artifacts, persist them, or drop them.

```rust
pub struct FunctionArtifacts {
    /// Human-readable CLIF dump of the compiled function, captured after
    /// FnCompiler finalises the Cranelift IR but before `module.define_function`
    /// consumes the context. Same text rendered by `/clif`.
    pub clif_ir: String,

    /// Human-readable machine-code disassembly, captured from the compiled
    /// `CompiledCode` after `define_function`. Same text rendered by `/disasm`.
    pub disasm: String,

    /// Size in bytes of the compiled machine code. Captured from
    /// `CompiledCode::code_info().total_size`.
    pub code_size: u32,
}
```

**Contract**:

1. **Keying**. Both `func_ids` and `artifacts` are keyed by `Symbol` — the *local* name of the entry in `symbol_tables[module_path]`. For multi-sig variants and mono specializations, the local name IS the mangled name (that is how Wave 0 stores them on the symbol table — see `design/typecheck/ast-annotation.md`). There is no separate "mangled vs unmangled" key; the backend compiles what `names` says, and keys both maps by those same identifiers.

2. **No separate pass**. Artifacts are populated during the SAME `FnCompiler` pass that declares and defines the function — captured from the `FunctionBuilder`'s function before `module.define_function` consumes the context, and from `CompiledCode` immediately after. There is no second compilation pass, no round-trip through the object file, and no recompilation for `/clif` or `/disasm`. (Intrinsics declared via `declare_intrinsics` are not compiled by this function and do NOT appear in `artifacts`.)

3. **Empty is valid**. `artifacts` is a `HashMap`, not an `Option<HashMap>`. Callers that do not want introspection overhead (e.g., release builds, batch `--run`) may configure `compile_to_module` to skip capture so the map is returned empty. The *type* of the field is not optional per entry; the entry's *presence* signals whether capture ran. A follow-up revision may gate capture behind a feature flag or a no-op arena strategy — the shape does not change. Object-path callers typically request an empty map since `.o` emission has no display surface; JIT callers under a REPL request a populated one.

4. **Caller routes artifacts wherever**. The priority worker's loop (per `pipeline-v4.md` §9.4) is:

   ```rust
   let result = compile_to_module(module_path.clone(), &names, &symbol_tables, &mut jit_module)?;
   for (sym, art) in result.artifacts {
       let fq = FQSymbol { module: module_path.clone(), symbol: sym };
       shared.introspection.insert(fq, Introspection { clif_ir: art.clif_ir, disasm: art.disasm, code_size: art.code_size, /* ... */ });
   }
   ```

   The backend never touches `shared.introspection`. An in-process caller writes to a `DashMap`; a serializing caller writes to a file; a discarding caller drops the map. All three paths use the same `CompilationResult` shape.

**Rationale** (referencing `pipeline-v4.md` §9.6): `Introspection` is display-only, caller-owned, and keyed by `FQSymbol` on `SharedState` — it must not be an input to or output of `compile_to_module`, because that would couple the backend to the integration layer's concurrent storage model. Returning artifacts on `CompilationResult` preserves the separation: codegen produces the artifacts (only codegen *can* — the CLIF and disasm don't exist before compilation runs), and the caller owns placement. A symbol-table-sourced alternative (write artifacts onto `ModuleEntry` during codegen) was rejected because artifacts are not part of the compilable contract — they are an output, not durable state; writing them onto the symbol table would entangle the per-module symbol tables with display-only data that the cache has no interest in.

**What this replaces**: the pre-Phase-2 shape returned one flattened `(Option<String>, Option<String>, Option<u32>)` triple tied to "the last compiled function" or "the batch entry". That shape assumed `compile_to_module` compiled exactly one driving symbol. Once `names: &[Symbol]` is the input, per-symbol keying is the only coherent shape.

The caller finishes the job:

```rust
// JIT path: get entry pointer
let result = compile_to_module(..., &mut jit_module, ...)?;
jit_module.finalize_definitions()?;
if let Some(entry_id) = result.entry_func_id {
    let entry_ptr = jit_module.get_finalized_function(entry_id);
    // Execute...
}

// Object path: emit bytes
let result = compile_to_module(..., &mut obj_module, ...)?;
let bytes = obj_module.finish().emit()?;
// Write to .o file...
```

### What it replaces

- `CompiledProgram` (JIT batch) — replaced by `CompilationResult` + caller-side finalization.
- `CompiledModuleInfo` (shared-JIT multi-module) — replaced by `CompilationResult.func_ids` + `func_arities`.
- `Vec<u8>` (object path return) — the caller calls `obj_module.finish().emit()` directly.

## 9. What to Delete

### Structs and types

| Item | Location | Replacement |
|------|----------|-------------|
| `CompiledExpr` | `lib.rs` | Caller owns the `JITModule` directly; no wrapper struct needed |
| `CompiledProgram` | `lib.rs` | `CompilationResult` + caller-side `execute()` |
| `CompiledModuleInfo` | `lib.rs` | `CompilationResult` |
| `CollectedDefns` (backend) | `lib.rs` | Inline logic in `compile_to_module` |
| `CollectedDefns` (pipeline) | `pipeline.rs` | Deleted entirely |
| `ObjectCompileInput` | `cache/object.rs` | Deleted — `compile_to_module` reads from `symbol_tables[module_path]` by name |
| `ObjFnSlot` | `cache/object.rs` | Deleted — GOT encoding is uniform (`global_value` + `Linkage::Import` data symbol); see §12 |
| `CrossModuleRefs` | `pipeline.rs` | Deleted — derived from symbol tables inside `compile_to_module` or caller |
| `CompilationEnv` trait | `crates/cranelisp-backend/src/lib.rs` | Deleted — no env parameter; mode lives on the `Module` impl (§12) |
| `ObjectCompilationEnv` | `cache/object.rs` | Deleted — withdrawn from the Sprint 56 Phase 3a design |
| `SessionCompilationEnv` | `src/session_v4.rs` | Deleted — no env plumbing; uniform GOT strategy (§12) |

### Functions

| Function | Location | Replacement |
|----------|----------|-------------|
| `compile_expr_with_got_and_symbols` | `lib.rs` | Caller wraps expr in one-defn `Program`, calls `compile_to_module<JITModule>` |
| `compile_and_run_expr` | `lib.rs` | Caller wraps expr, calls `compile_to_module<JITModule>`, executes pointer |
| `compile_program` | `lib.rs` | `compile_to_module<JITModule>` |
| `compile_module_program` | `lib.rs` | `compile_to_module<JITModule>` with shared JIT |
| `collect_and_declare_defns` | `lib.rs` | Logic inlined in `compile_to_module` |
| `find_entry_and_finalize` | `lib.rs` | Caller-side after `compile_to_module` returns |
| `collect_extra_defns` | `lib.rs` | Trivial inline |
| `compile_mono_defns` | `lib.rs` | Logic inlined in `compile_to_module` |
| `compile_module_to_object` | `cache/object.rs` | `compile_to_module<ObjectModule>` |
| `compile_all_functions` | `cache/object.rs` | Logic inlined in `compile_to_module` |
| `collect_defns_for_cache` | `pipeline.rs` | Deleted entirely (the broken path) |
| `build_object_compile_input` | `pipeline.rs` | Deleted entirely |
| `collect_cross_module_refs` | `pipeline.rs` | Deleted entirely |
| `scheme_for_defn` | `pipeline.rs` | Deleted (schemes come from symbol table) |
| `build_intrinsic_table` | `pipeline.rs` | Replaced by `declare_intrinsics<M>` |

### Fields

| Field | Location | Replacement |
|-------|----------|-------------|
| `CodegenInput.cross_module_func_sigs` | `session_v4.rs` | Deleted — derived from symbol tables at compile time |

### Functions to keep (ObjectModule-specific, called by nice worker)

| Function | Location | Why kept |
|----------|----------|----------|
| `declare_got_data_symbols` | `cache/object.rs` | ObjectModule-specific GOT setup |
| `define_got_data` | `cache/object.rs` | ObjectModule-specific GOT data section |
| `build_obj_fn_slots` | `cache/object.rs` | ObjectModule-specific GOT slot info (or deleted outright — slot info now read directly from `symbol_tables[module].get(name).got_slot` per §12) |
| `declare_intrinsic_imports` | `cache/object.rs` | Subsumed by generic `declare_intrinsics<M>` — delete |
| `declare_module_functions` | `cache/object.rs` | Subsumed by `compile_to_module` declaration loop — delete |
| `build_isa` | `cache/object.rs` | Kept (single ISA construction point) |
| `build_cache_packet` | `cache/object.rs` | Kept (cache write logic) |
| `process_cache_packet` | `cache/object.rs` | Kept (cache write logic, but simplified — calls `compile_to_module<ObjectModule>` instead of `compile_module_to_object`) |

## 10. CodegenInput Simplification

Currently `CodegenInput` in `session_v4.rs`:

```rust
pub struct CodegenInput {
    pub method_resolutions: MethodResolutions,
    pub expr_types: HashMap<Span, Type>,
    pub mono_defns: Vec<MonoDefn>,
    pub default_method_defns: Vec<Defn>,
    pub program: Vec<TopLevel>,
    pub cross_module_func_sigs: Vec<(Symbol, usize)>,  // DELETE
}
```

After unification, `cross_module_func_sigs` is deleted. The remaining fields are exactly `CheckResult` (minus `warnings`, `display`, `constrained_fn_names`) plus `program`.

### Option A: Keep CodegenInput as a slimmed struct

```rust
pub struct CodegenInput {
    pub check: CheckResult,
    pub program: Program,
}
```

### Option B: Stash CheckResult and Program separately

```rust
pub codegen_checks: DashMap<ModuleFullPath, CheckResult>,
pub codegen_programs: DashMap<ModuleFullPath, Program>,
```

### Recommendation

Option A. A single DashMap entry per module is simpler to manage (atomic insert/remove). The nice worker takes the entry, extracts `check` and `program`, and calls `compile_to_module`.

Note: `constrained_fn_names` must be included in the stashed `CheckResult`. The current code discards it at stash time and passes an empty set to the object path — this is a pre-existing bug that the unification fixes for free (both workers get the same `CheckResult`).

## 11. Call Site Changes

> **Historical note (Sprint 56)**: The code snippets in this section show the Sprint-55 five-parameter call shape (`&program, &check, &symbol_tables, ...`). They are retained as a record of the transition through Sprint 55's `CheckResult` elimination. The current call shape is four parameters `(module_path, names, symbol_tables, module)` — see §2.5 for present-tense examples and §16 for the Phase 2 caller contract. The structural points below (which worker owns which setup, `CompiledExpr` deletion, REPL wrapper ownership moving to `src/`) remain accurate.

### Priority worker (JIT path)

Current flow in `session_v4.rs`:
1. Typecheck produces `CheckResult`.
2. For each defn: `compile_and_register_defn_shared()` creates a fresh `Jit`, compiles one defn, registers in GOT.
3. Stashes `CodegenInput` for nice worker.

**Change**: The priority worker's per-defn compilation is unchanged — it doesn't use `compile_program` (that's only for `--run` batch mode). The priority worker already uses `compile_and_register_defn_shared` which creates individual JITs per defn.

For `--run` mode (batch), the caller currently uses `compile_program`. This becomes:

```rust
let mut jit = Jit::new()?;
jit.declare_intrinsics()?;
let result = compile_to_module(&program, &check, &symbol_tables, jit.module_mut(), module_path)?;
let entry_ptr = jit.finalize_and_get_ptr_by_id(result.entry_func_id.unwrap())?;
```

### Nice worker (object path)

Current flow:
1. Takes `CodegenInput` from DashMap.
2. Calls `build_object_compile_input()` — re-derives defn lists, invents slot numbers.
3. Calls `compile_module_to_object()` — separate compilation path.

**Change**:

```rust
fn compile_module_object(shared: &SharedState, module: &ModuleFullPath, cache_dir: &Path) {
    let Some((_, input)) = shared.codegen_inputs.remove(module) else { return; };

    if !has_compilable_defns(&input.program) { return; }

    // Build ObjectModule
    let isa = build_isa(true)?;
    let obj_builder = ObjectBuilder::new(isa, format!("cranelisp_{}", module), default_libcall_names())?;
    let mut obj_module = ObjectModule::new(obj_builder);

    // Declare intrinsics (generic over Module)
    let intrinsic_ids = declare_intrinsics(&mut obj_module)?;

    // ObjectModule-specific: declare GOT data symbols, define GOT data
    // (reads fn_to_module and slot assignments from symbol_tables)
    setup_object_got(&mut obj_module, module, &shared.symbol_tables)?;

    // Compile — same function as JIT
    let result = compile_to_module(
        &input.program, &input.check, &shared.symbol_tables,
        &mut obj_module, module.clone(),
    )?;

    // Emit .o bytes
    let bytes = obj_module.finish().emit()?;

    // Write .o file
    let (_, o_path) = cache::module_cache_path(cache_dir, module);
    cache::atomic_write(&o_path, &bytes)?;
}
```

The `ObjectCompileInput` struct, `build_object_compile_input()`, `collect_defns_for_cache()`, and `collect_cross_module_refs()` are all deleted. The nice worker reads everything it needs from `CheckResult`, `Program`, and `SymbolTable` — the same inputs the JIT path uses.

### REPL expression eval

Current flow in `lib.rs`:
1. `compile_expr_with_got_and_symbols` receives an `Expr` + extra symbols + GOT data defs.
2. Creates a fresh `Jit` with extra symbols on the `JITBuilder`.
3. Declares intrinsics.
4. Defines GOT data entries on the JIT module.
5. Wraps the expression in a synthetic zero-arg `Defn` named `__repl_expr__`.
6. Declares and compiles that one function.
7. Finalizes and returns a `CompiledExpr` (which holds the `Jit` alive so the pointer stays valid).

**Change**: The REPL caller (in `src/`) takes over the wrapper and module setup:

```rust
fn compile_repl_expr(
    expr: &Expr,
    check: &CheckResult,
    extra_symbols: &[(&str, *const u8)],
    got_data_defs: &[(String, *const u8)],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable>,
    current_module: ModuleFullPath,
) -> Result<(JITModule, *const u8), CranelispError> {
    // 1. Wrap expr in a one-defn Program (caller's responsibility)
    let wrapper_name = Symbol::from("__repl_expr__");
    let wrapper_defn = Defn {
        name: wrapper_name.clone(),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            param_annotations: vec![],
            body: expr.clone(),
            span: expr.span(),
        }],
        visibility: Visibility::Public,
        span: expr.span(),
    };
    let program = vec![TopLevel::Defn(wrapper_defn)];

    // 2. Create JITModule with extra symbols (caller's responsibility)
    let mut jit_builder = JITBuilder::new(...)?;
    for (name, ptr) in extra_symbols {
        jit_builder.symbol(name, *ptr);
    }
    let mut jit_module = JITModule::new(jit_builder)?;

    // 3. Declare intrinsics (shared API)
    declare_intrinsics(&mut jit_module)?;

    // 4. Define GOT data entries (caller's responsibility)
    for (name, ptr) in got_data_defs {
        define_got_data(&mut jit_module, name, *ptr)?;
    }

    // 5. Compile — same function as batch and object
    let result = compile_to_module(
        &program, &check, &symbol_tables,
        &mut jit_module, current_module,
    )?;

    // 6. Finalize and get pointer
    jit_module.finalize_definitions()?;
    let entry_ptr = jit_module.get_finalized_function(result.entry_func_id.unwrap());

    // Caller keeps jit_module alive while executing the pointer
    Ok((jit_module, entry_ptr))
}
```

`CompiledExpr` is deleted. The caller owns the `JITModule` directly and is responsible for keeping it alive while the function pointer is in use. `compile_and_run_expr` (the convenience wrapper) is also deleted — callers use the pattern above.

The `define_got_data` helper (currently `Jit::define_got_data`) is extracted as a free function that works on any `Module` that supports `declare_data` / `define_data`, or kept as a JIT-specific utility in the caller's code.

### --link mode

Works identically to the nice worker: creates `ObjectModule`, calls `compile_to_module`, emits bytes. No special handling needed.

## 12. GOT Reference Emission

> **Historical note**: Earlier drafts proposed a `CompilationEnv` trait with two implementations (`ObjectCompilationEnv`, `JitCompilationEnv`), two public wrapper entry points (`compile_to_module_object`, `compile_to_module_jit`), and a crate-private `compile_to_module_core`. That design was retracted during Sprint 56 Phase 3a review in favour of the uniform strategy below. See `design/arch/pipeline-v4.md` §9.1 / §9.3 and Principle 11 + Decision 22 in `design/arch/CLAUDE.md`.

GOT reference emission is **uniform across JIT and object modes**. The backend emits the same CLIF at every GOT load site — mode differences live entirely in the `Module` implementation at finalize time.

### The uniform strategy

For every cross-module function reference, `compile_to_module` emits:

1. A `Linkage::Import` data symbol declaration named `__cranelisp_got_{target_module}`.
2. A `global_value` load that reads the GOT base from that data symbol.
3. An indexed load at `base + slot * 8` to reach the target function pointer, where `slot` is read from `symbol_tables[target_module].get(name).got_slot` (or, post-G7, `symbol_tables[target_module].got.slot_of(name)`).

The backend does not know, and does not care, whether the data symbol will be resolved by a linker or by a runtime callback. Both modes get byte-identical IR.

### How each `Module` implementation resolves `__cranelisp_got_{module}`

- **`ObjectModule` (`.o` emission)**: The relocation entries emitted for `__cranelisp_got_{module}` are left unresolved in the object file. The platform linker (or the cache `Linker` at load time) patches concrete addresses — against the per-module GOT data block emitted into the same `.o` for the module's own symbols, or against an imported data symbol for cross-module references.

- **`JITModule` (in-process codegen)**: Before creating the `JITModule`, the caller registers `JITBuilder::symbol_lookup_fn(|name|)` that maps `__cranelisp_got_{name}` → `symbol_tables[name].got.base_ptr()`. When Cranelift resolves the import at finalize, it invokes this callback and receives a concrete runtime address.

### Caller contract

Callers are responsible for ensuring the `Module` they pass can resolve `__cranelisp_got_{module}` symbols:

- **Object callers** (nice worker, `--link`): no extra wiring — the default `ObjectModule` relocation machinery handles it.
- **JIT callers** (priority worker, REPL): **MUST** register a `symbol_lookup_fn` on the `JITBuilder` before constructing the `JITModule`. After G7 lands in Wave 0, `got` lives on `SymbolTable` — the lookup closure walks `symbol_tables[name].got.base_ptr()`. See `design/typecheck/ast-annotation.md` §9.8 for the symbol-table shape post-G7 and `design/arch/pipeline-v4.md` §9.3 for the caller's end-to-end responsibility.

### Why uniform

1. **Principle 7 (single source of truth)**: one CLIF emission path for every GOT reference. No possibility of JIT-path and object-path IR drifting.
2. **Principle 11 (single pipeline, mode parameters)**: the difference between JIT and object is a mode-appropriate `Module` impl, not a fork inside the backend. Decision 22 in `design/arch/CLAUDE.md` recorded this after the dual-wrapper / crate-private-core design was rejected.
3. **No behaviour-carrying parameters**: §2.1's 4-parameter signature stays data-only. No trait object, no env, no runtime dispatch on mode.
4. **Testability (Principle 5)**: a fake `Module` or fake `symbol_lookup_fn` is all a test needs to exercise GOT emission — no environment scaffolding per-mode.

## 13. Migration Steps

> **Historical note (Sprint 56)**: The steps below describe the original migration plan leading up to the five-parameter `compile_to_module` and then through Sprint 55's `CheckResult` removal. They have landed. For the Phase 2 (Sprint 56) migration — replacing `program` with `names` and deleting `expand_multi_sig_defn` — see §16. §13 is retained as a record of how we arrived at the pre-Phase-2 shape.

Ordered implementation plan with dependency constraints.

### Step 1: Extract `declare_intrinsics<M: Module>`

**Files**: `crates/cranelisp-backend/src/jit.rs`, `crates/cranelisp-backend/src/cache/object.rs`

Extract the intrinsic declaration logic from `Jit::declare_intrinsics()` into a free function `declare_intrinsics<M: Module>(module: &mut M) -> Result<IntrinsicFuncIds>`. Both `Jit::declare_intrinsics` and `declare_intrinsic_imports` delegate to this function.

**Verification**: All existing tests pass. No behavioural change.

### Step 2: Implement `compile_to_module<M: Module>`

**Files**: `crates/cranelisp-backend/src/lib.rs`

Write the unified function using the defn collection logic from `collect_and_declare_defns` (the working path). Initially, `compile_program`, `compile_module_program`, and `compile_expr_with_got_and_symbols` become thin wrappers that call `compile_to_module<JITModule>`.

**Verification**: All existing tests pass. `compile_program`, `compile_module_program`, and REPL expression compilation produce identical results.

### Step 3: ~~Implement `ObjectCompilationEnv`~~ (WITHDRAWN)

The Sprint-55 migration briefly introduced an `ObjectCompilationEnv` scaffold as an interim step. The entire `CompilationEnv` design was subsequently retracted in Sprint 56 Phase 3a review in favour of the uniform GOT emission described in §12. There is no env to implement. Slot assignments are read directly from `symbol_tables[target].get(name).got_slot` at each GOT load site; GOT base resolution is a `Module`-implementation concern at finalize time.

### Step 4: Wire nice worker to `compile_to_module<ObjectModule>`

**Files**: `src/session_v4.rs`, `src/pipeline.rs`

Replace `compile_module_object`'s call to `build_object_compile_input` + `compile_module_to_object` with direct calls to `compile_to_module<ObjectModule>`. Delete `CodegenInput.cross_module_func_sigs`.

**Verification**: `.o` files are generated without crashes (the multi-sig panic is fixed). Run the existing cache integration tests.

### Step 5: Delete dead code

**Files**: `lib.rs`, `cache/object.rs`, `pipeline.rs`, `session_v4.rs`

Delete all items listed in section 9 (including `CompiledExpr`, `compile_expr_with_got_and_symbols`, and `compile_and_run_expr`). Clean up imports. Move the REPL wrapper logic (synthetic `Defn` construction, `JITBuilder` symbol registration, GOT data defs) to the caller in `src/`.

**Verification**: `cargo build` succeeds. All tests pass. `cargo clippy` clean.

### Step 6: Simplify `CodegenInput`

**Files**: `src/session_v4.rs`

Replace `CodegenInput` with `CodegenInput { check: CheckResult, program: Program }`. Ensure `constrained_fn_names` is preserved in the stashed `CheckResult`.

**Verification**: All tests pass. Nice worker correctly handles constrained polymorphic functions.

## 14. Sketch Comparison

### How the sketch handles this

The sketch has the same dual-path problem but at a lower layer. Its `compile_function_indirect<M: Module>` (codegen.rs line 1787) is already generic over `Module`. However, the module-level orchestration (`compile_module_to_object` in cache.rs) is a separate 285-line function with 21 positional parameters that re-derives defn lists, declares functions, sets up GOT data symbols, and compiles — all duplicating the JIT batch path.

The sketch's `FnCompiler` equivalent is not a struct but a set of free functions that take `&mut impl Module`. The GOT reference encoding uses `GotReference::Immediate(usize)` vs `GotReference::DataSymbol(DataId)` on the `FnSlot` struct, checked at each GOT load site.

### Where the reimplementation diverges

| Aspect | Sketch | Reimplementation | Rationale |
|--------|--------|------------------|-----------|
| Module-level unification | Separate JIT batch, REPL expr, and object orchestration | Single `compile_to_module<M>` for all three | Eliminates the root cause of the multi-sig crash, slot mismatch bugs, and REPL/batch divergence |
| GOT reference dispatch | `match got_ref` inside `FnSlot` at each GOT load | Uniform emission: `global_value` against `Linkage::Import` data symbol; mode handled by the `Module` impl at finalize (§12) | Removes the fork entirely; FnCompiler emits identical CLIF in both modes |
| Intrinsic declaration | Separate per-path | `declare_intrinsics<M>` | Single source of truth for intrinsic set |
| Defn collection | Separate per-path (object path broken) | One path, reused | Fixes multi-sig handling for object path |
| Parameter passing | 21 positional params | `(ModuleFullPath, names, SymbolTable, Module)` — 4 params, everything else (AST bodies, resolutions, types, arities, GOT) derived from the symbol table | Addresses HIGH-3 without inventing a new input struct; Phase 2 replaced `(Program, CheckResult)` with a name list into the symbol table |

### What we adopt from the sketch

- `FnCompiler<M: Module>` generic pattern (already adopted).
- GOT data symbol naming convention (`__cranelisp_got_<module>`).
- `__data` vs `__bss` workaround (explicit zero bytes, not `define_zeroinit`).
- ObjectModule-specific GOT setup as a pre-step before compilation.
- Background cache writing pattern (unchanged by this design).

## 15. Acceptance Criteria — PRESCRIPTIVE

These criteria MUST ALL pass before the implementation is accepted. They are not suggestions.

### 15.1 Signature compliance

`compile_to_module` MUST have EXACTLY this signature (Phase 2 target — see §2.1):

```rust
pub fn compile_to_module<M: Module>(
    module_path: ModuleFullPath,
    names: &[Symbol],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable>,
    module: &mut M,
) -> Result<CompilationResult, CranelispError>
```

Four parameters. No additional parameters of any kind. No `program`, no `CheckResult`, no extra input struct, no feature flag.

### 15.2 No test coverage loss

Every test that existed before the migration MUST either:
- (a) Be ported to call `compile_to_module` (preferred), or
- (b) Still call a deprecated function (acceptable during migration)

No test may be deleted.

### 15.3 Internal derivation

`compile_to_module` must NOT receive from callers:
- **Defn AST bodies / Program** (reads `ModuleEntry::Def.ast` from `symbol_tables[module_path]` by name — Phase 2)
- **CheckResult / method_resolutions / expr_types / mono_defns / default_method_defns / constrained_fn_names** (removed as a boundary type in Sprint 55; annotations live on AST nodes, mangled bodies live on symbol-table entries)
- Intrinsic FuncIds (declares them internally on the module)
- GOT slot assignments (reads from symbol_tables)
- GOT base pointers (not a compile-time concern — resolved at module finalize by the `Module` impl via `__cranelisp_got_{module}` data symbols; see §12)
- Function arities (derives from the AST retrieved per name)
- Cross-module function sigs (resolves from symbol_tables)
- JIT name prefix (derives from module_path)
- Traced function list (not a compilation concern)
- Extra JIT symbols (caller registers on `JITBuilder` — including the `symbol_lookup_fn` that resolves `__cranelisp_got_{name}` — before creating the module)

### 15.4 Build state

- `cargo build --lib -p cranelisp-backend` passes with zero errors
- Backend crate tests pass (or call deprecated functions during transition)
- Full workspace `cargo build` will have errors in `src/` callers from deprecated functions — that is expected and correct

### 15.5 Public API surface

The backend crate's public compilation API is:
- `compile_to_module<M: Module>` — the only compilation entry point
- `declare_intrinsics<M: Module>` — intrinsic declaration for callers that pre-populate a `Module`
- `CompilationResult` — the return type
- `build_isa(pic: bool)` — for callers creating ObjectModule

`Jit` and all its methods are `pub(crate)`. Callers work with `JITModule` directly.
No `CompilationEnv` in the public API (the trait does not exist — see §12). No `compile_to_module_jit` / `compile_to_module_object` wrappers. No `CodegenTarget` enum. No `ObjectCompileInput`. No `IntrinsicTable`.

## 16. Phase 2 Migration (Sprint 56)

Phase 2 of `design/arch/pipeline-v4-roadmap.md` — Step 2a (signature flip from `program` to `names`) and Step 2b (delete `codegen_module_symbols`). This section is the `/backend` Wave-1 deliverable: it documents the target shape, preconditions owned by `/typecheck` (Wave 0), and the deletion list. It supersedes the migration-step narrative in §13 (which described the Sprint-55 path through the old five-parameter signature).

### 16.1 Precondition — Wave 0 (owned by `/typecheck`)

Step 2a cannot land green until Wave 0 is in place:

1. `register_mangled_variants` must insert each multi-sig variant entry with `ast: Some(single_variant_Defn)` — the `DefnVariant` selected for that mangled name, cloned into a single-variant `Defn` under the mangled key.
2. `register_mono_entry` must insert each mono specialization with `ast: Some(annotated_Defn)` — the monomorphised body with all post-pass `resolved_call` / `inferred_type` annotations applied.
3. `SymbolTable::defined_symbols()` (or an equivalent iterator method in `cranelisp-types`) is exposed, returning exactly the names codegen must compile. Predicate: `ast.is_some() AND kind is not Overloaded AND kind is not UserFn { constrained_fn: Some(_) }`. This is the shared filter used by both `compile_to_module`'s callers and (if ever needed) the backend itself — a single source of truth. See `/arch` review §6 condition 5.

`/typecheck`'s `ast-annotation.md` carries the authoritative table of which symbol-table entry categories must carry `ast: Some(_)` post-Phase-2. The backend relies on that contract; violations are surfaced as codegen errors (§16.3) rather than silently tolerated.

### 16.2 What replaces `collect_and_declare_defns` / the program loop

The Sprint-55 shape of `compile_to_module` (see `crates/cranelisp-backend/src/lib.rs:73` at the start of this sprint) has a single loop over `program: &Program` that:

1. Skips `TopLevel::Defn`s whose name is in the inline `constrained_fn_names` set derived from the symbol table at `lib.rs:95-109`.
2. Splits remaining defns into `regular_defns` (pushed by reference) and `multi_sig_defns` (expanded into mangled variants via `expand_multi_sig_defn` at `lib.rs:379-436`).
3. Compiles the union.

Phase 2 replaces that loop with the §4 lookup loop: iterate `names`, pull each entry's `ast`, push into `defns`. The filter is gone (moved into `defined_symbols()`); the expansion is gone (moved into `register_mangled_variants`).

### 16.3 Caller contract for `names`

**Typical case** — compile a whole module:

```rust
let names: Vec<Symbol> = symbol_tables
    .get(&module_path)
    .map(|t| t.defined_symbols().collect())
    .unwrap_or_default();
```

**Nice worker** (`.o` emission) and **`--link` mode** use the typical case.

**Priority worker** (per-function JIT isolation per `pipeline-v4.md` §9.4) passes a one-element slice per symbol it compiles:

```rust
let names = vec![symbol_name.clone()];
```

**REPL expression eval**: typecheck registers the wrapped expression under a known synthetic name (e.g., `__expr`) on the REPL module's symbol table, with `ast: Some(...)` carrying the annotated wrapper. The REPL caller passes that one name. The synthetic-`Defn` construction currently owned by the backend (`compile_expr_with_got_and_symbols` or its Phase-2 successor in `/int`) moves fully to the caller side, driven by typecheck's registration rather than backend wrapping.

**Partial recompile / mono batch** (future use): pass the filtered subset. The backend treats `names` as authoritative — it compiles exactly what it is told to compile, nothing more.

### 16.4 Error behaviour for `ast: None`

If a name in `names` resolves to a `ModuleEntry::Def` with `ast: None`, `compile_to_module` returns a `CranelispError::CodegenError` naming the symbol and module and pointing at `design/typecheck/ast-annotation.md` for the expected annotation contract. Rationale: per Principle 7 (single source of truth), the backend does not have a fallback synthesis path — if the symbol table promises a compilable entry, it must deliver the AST. A silent skip would hide typecheck bugs; an `unreachable!` would panic production builds on a recoverable wiring error. A named codegen error is the right middle ground.

If a name resolves to a non-`Def` variant (`Import`, `Constructor`, `Macro`, `TypeDef`, `TraitDecl`, `Ambiguous`, `Reexport`), the same error path fires — those are not compilable by `compile_to_module` and must not appear in `names`. `defined_symbols()` filters them out; if a caller builds `names` by hand and includes one, the error names the kind.

### 16.5 GOT emission is uniform (§2.4, §12) — no mode fork

The signature change touches **what** to compile. Mode handling — **how** GOT base addresses materialise — is uniform across JIT and object modes per Decision 23 (`design/arch/CLAUDE.md`) and §12 of this document. The backend emits the same CLIF for every GOT reference (`global_value` against a `Linkage::Import` data symbol named `__cranelisp_got_{module}`); mode differences live entirely in the `Module` implementation at finalize time. Earlier drafts of this doc described a `CompilationEnv` fork that has since been withdrawn.

### 16.6 Deletions (Wave 1 — backend side)

These are deleted as part of the Phase 2 implementation wave:

- `expand_multi_sig_defn` — currently `crates/cranelisp-backend/src/lib.rs:379-436`. Wave 0 pre-materialises mangled variant entries with `ast: Some(_)`; there is nothing left to expand.
- The inline `constrained_fn_names` HashSet construction at `crates/cranelisp-backend/src/lib.rs:95-109`. Filtering moves into `SymbolTable::defined_symbols()`.
- `concrete_type_name` / `build_mangled_name` helpers at `lib.rs:347-369` if they were used only by `expand_multi_sig_defn`. (Check dependencies during implementation — they may still be needed by cross-module resolution; if so, they survive.)
- The `program: &Program` parameter on `compile_to_module`; every type, function, or field that only existed to plumb `program` into this function.
- The inline `for tl in program { if let TopLevel::Defn(defn) = tl { ... } }` loop — replaced by the §4 symbol-table lookup loop.
- `CompilationEnv` trait and every related type: `ObjectCompilationEnv`, `JitCompilationEnv`, and shared helpers (`resolve_got_module_shared`, `func_arity_shared`, `resolve_cross_module_ref_shared`) introduced for the withdrawn dual-env design.
- `CodegenTarget` enum (or any equivalent mode discriminator) — mode lives on the `Module` implementation, not inside `compile_to_module`.

Deletions on the `/int` side (Step 2b) are out of scope for this doc (covered in `design/int/phase2-codegen-convergence.md`), but the principal ones are: `codegen_module_symbols`, `compile_regular_defns`, `compile_and_register_defn_shared`, `pre_register_got_slots_in_tc`, `SessionCompilationEnv` (all of it — env plumbing is gone), and the `finalize_module` program-inlining path that currently splices `mono_defns` and `default_method_defns` into the program before codegen.

### 16.7 Phase 3 seam — `code: Option<Code>` on `ModuleEntry::Def`

Phase 2 keeps `Code` (JIT module + code pointer) living in `CodegenProduct`, the existing integration-layer `DashMap<ModuleFullPath, CodegenProduct>` that holds JIT-module ownership and per-function pointers. `CompilationResult` (see §8) is unchanged — it still carries `func_ids`, `entry_func_id`, `func_arities`, and `warnings`. Per `/arch` review §2 and §6 condition 4, this is an intentional Phase-2→Phase-3 bridge, not interim architecture: moving `Code` onto `ModuleEntry::Def.code` is G6 in `pipeline-v4-roadmap.md` Phase 3, deliberately scoped as a **refactor** (mechanical relocation of a field) rather than a rewrite.

The implication for `/backend`: `CompilationResult` stays as-is for Phase 2. Do not preemptively collapse it into per-entry writes — Phase 3 will collapse it, and conflating the two phases muddies both. The Phase 3 transition will flip the write side (the priority worker writes `code` onto the entry) without changing `compile_to_module`'s contract — `compile_to_module` will still return `CompilationResult`, and the caller will still be responsible for extracting pointers and storing them, only the storage location moves from `CodegenProduct` to `ModuleEntry::Def.code`.

### 16.8 Relationship to §13

§13 documents the Sprint-55 migration path (five-parameter → four-parameter, `CheckResult` elimination). Its steps are historical at this point — they describe work that has landed. §16 is the Phase-2 continuation: `program` elimination, symbol-table-sourced defn collection, `expand_multi_sig_defn` deletion. Treat §16 as authoritative for Phase 2 and §13 as a historical record of how we got here.
