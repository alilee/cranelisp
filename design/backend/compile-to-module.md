# compile_to_module<M: Module> — Unified Compilation Function

Design for replacing all compilation paths — JIT batch, REPL expression, and object file — with a single generic function parameterised by Cranelift module type.

`compile_to_module<M>` is the ONLY compilation entry point in the backend crate. The backend's public compilation API is exactly two functions: `compile_to_module<M: Module>` and `declare_intrinsics<M: Module>`. Nothing else.

**Status**: Design document. Replaces the ad-hoc object compilation path described in module-caching.md §13.11, and subsumes the REPL expression compilation path (`compile_expr_with_got_and_symbols`).

## 1. Problem Statement

The JIT batch path (`compile_program` in `lib.rs`), the REPL expression path (`compile_expr_with_got_and_symbols` in `lib.rs`), and the object path (`compile_module_to_object` in `cache/object.rs`) all perform the same logical work but are separate implementations:

1. **Defn collection**: JIT uses `collect_and_declare_defns` (handles multi-sig, constrained, mono, defaults). Object uses `collect_defns_for_cache` (broken — panics on `DefnMulti`).
2. **Function declaration**: JIT declares against `JITModule`. Object declares against `ObjectModule`. Same Cranelift `Module` API.
3. **GOT / cross-module references**: JIT reads live GOT state via `CompilationEnv`. Object invents sequential slot numbers instead of reading `SymbolTable.got_slot`.
4. **Function compilation**: Both use `FnCompiler<M: Module>`. Same code, different wiring.
5. **Intrinsic declaration**: JIT uses `Jit::declare_intrinsics()`. Object uses `declare_intrinsic_imports()`. Same set of symbols, different declaration paths.

Additionally, `compile_expr_with_got_and_symbols` is a third compilation path for REPL expressions. It creates a fresh JIT, declares intrinsics, defines GOT data entries, wraps the expression in a synthetic zero-arg `Defn`, declares and compiles that one function, finalizes, and returns the pointer. This is exactly `compile_to_module<JITModule>` with a one-defn program — the only caller-specific parts are the extra symbols on the JITBuilder and the GOT data definitions, both of which are the caller's responsibility before module creation.

This triplication causes:
- Multi-sig crash in the object path (`defn.params()` panics on `DefnMulti`).
- Invented GOT slot numbers that don't match the JIT's actual slots.
- Redundant data assembly in `ObjectCompileInput`, `CodegenInput`, `build_object_compile_input`.
- Three code paths that can (and do) diverge silently.
- `CompiledExpr` struct that exists only to hold a `Jit` alive — unnecessary once the caller owns the module.

## 2. Target API

```rust
/// Compile a program's functions into a Cranelift module.
///
/// Works for any module type: JITModule (in-memory execution),
/// ObjectModule (relocatable .o file), or any future Module impl.
///
/// The caller creates the module; this function populates it.
/// After return, the caller finalizes (JIT: `finalize()`, Object: `finish().emit()`).
pub fn compile_to_module<M: Module>(
    program: &Program,
    check: &CheckResult,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable>,
    module: &mut M,
    current_module: ModuleFullPath,
) -> Result<CompilationResult, CranelispError>
```

The caller creates the appropriate module. All three use cases — batch JIT, REPL expression, and object file — use the same function:

```rust
// Batch JIT (--run mode):
let mut jit_module = JITModule::new(jit_builder)?;
declare_intrinsics(&mut jit_module)?;
let result = compile_to_module(&program, &check, &symbol_tables, &mut jit_module, module_path)?;
jit_module.finalize_definitions()?;
let entry_ptr = jit_module.get_finalized_function(result.entry_func_id.unwrap());

// REPL expression eval:
// Caller wraps the expr in a synthetic one-defn Program, sets up JITBuilder
// with extra symbols and GOT data, then uses the same entry point.
let mut jit_builder = JITBuilder::new(settings::builder(), ...)?;
for (name, ptr) in &extra_symbols { jit_builder.symbol(name, *ptr); }
let mut jit_module = JITModule::new(jit_builder)?;
declare_intrinsics(&mut jit_module)?;
// GOT data defs set up on the module by the caller
for (name, ptr) in &got_data_defs { define_got_data(&mut jit_module, name, *ptr)?; }
let result = compile_to_module(&wrapper_program, &check, &symbol_tables, &mut jit_module, module_path)?;
jit_module.finalize_definitions()?;
let entry_ptr = jit_module.get_finalized_function(result.entry_func_id.unwrap());
// Caller keeps jit_module alive while executing the pointer.

// Nice worker (object / .o file):
let isa = build_isa(true)?;
let obj_builder = ObjectBuilder::new(isa, name, default_libcall_names())?;
let mut obj_module = ObjectModule::new(obj_builder);
declare_intrinsics(&mut obj_module)?;
let result = compile_to_module(&program, &check, &symbol_tables, &mut obj_module, module_path)?;
let bytes = obj_module.finish().emit()?;

// --link mode:
// Same as nice worker — creates ObjectModule, calls compile_to_module.
```

## 3. Function Signature and Generic Constraints

### What `M: Module` provides

The `cranelift_module::Module` trait (from Cranelift v0.125) provides:

- `declare_function(&str, Linkage, &Signature) -> ModuleResult<FuncId>`
- `declare_data(&str, Linkage, bool, bool) -> ModuleResult<DataId>`
- `define_function(FuncId, &mut Context) -> ModuleResult<()>`
- `define_data(DataId, &DataDescription) -> ModuleResult<()>`
- `declare_func_in_func(FuncId, &mut Function) -> FuncRef`
- `declare_data_in_func(DataId, &mut Function) -> GlobalValue`
- `make_signature() -> Signature`
- `target_config() -> TargetFrontendConfig`

Both `JITModule` and `ObjectModule` implement this trait. `FnCompiler` is already generic over `M: Module`. No additional trait bounds are needed.

### Additional bounds

None. The `Module` trait provides everything `compile_to_module` needs. GOT reference encoding (the one genuine difference) is handled by `CompilationEnv` and `GotReference`, not by additional trait bounds.

## 4. Defn Collection — Unified Approach

The unified defn collection replaces both `collect_and_declare_defns` (JIT path) and `collect_defns_for_cache` (object path). The logic lives inside `compile_to_module`:

```rust
// Step 1: Collect defns from program
let mut regular_defns: Vec<&Defn> = Vec::new();
let mut multi_sig_defns: Vec<Defn> = Vec::new();

for tl in program {
    if let TopLevel::Defn(defn) = tl {
        if check.constrained_fn_names.contains(&defn.name) {
            continue; // Template only — mono specializations compiled below
        }
        if defn.is_multi_sig() {
            // Expand into individual mangled-name variants
            let expanded = expand_multi_sig_defn(defn, &check.expr_types)?;
            multi_sig_defns.extend(expanded);
        } else {
            regular_defns.push(defn);
        }
    }
}

// Step 2: Collect extra defns from CheckResult
let mut extra_defns: Vec<&Defn> = Vec::new();
for d in &check.default_method_defns {
    extra_defns.push(d);
}
// Mono specializations handled separately (per-specialization resolutions)

// Step 3: All defns to declare (excludes mono — declared in their own loop)
let all_declare: Vec<&Defn> = regular_defns.iter().copied()
    .chain(extra_defns.iter().copied())
    .chain(multi_sig_defns.iter())
    .collect();
```

This is the existing `collect_and_declare_defns` logic, which correctly handles multi-sig expansion. The broken `collect_defns_for_cache` is deleted entirely.

### GOT slot assignments

GOT slots are **read from the symbol table**, not invented:

```rust
// Read GOT slot assignments from the authoritative source
let symbol_table = symbol_tables.get(&current_module)
    .ok_or_else(|| /* error */)?;

for defn_ref in &all_declare {
    if let Some(ModuleEntry::Def { got_slot: Some(slot), .. }) = symbol_table.get(defn_ref.name.as_ref()) {
        fn_slot_assignments.insert(defn_ref.name.clone(), FnSlotInfo { slot: *slot, param_count: defn_ref.params().len() });
    }
}
```

This eliminates the sequential `next_slot += 1` assignment in `collect_defns_for_cache` that produced incorrect slot numbers.

## 5. GOT Reference Encoding — The One Genuine Difference

The JIT path and object path differ in how the GOT base pointer is materialised in generated code:

| Path | GOT base | Mechanism |
|------|----------|-----------|
| JIT | `iconst(got_base_ptr)` | Runtime pointer known at compile time |
| Object | `global_value(data_id)` | Symbolic reference resolved by linker |

This difference is already abstracted by the `CompilationEnv` trait:

- **JIT path**: `SessionCompilationEnv::resolve_got()` returns `(got_base_ptr_as_i64, slot)`. `FnCompiler` emits `iconst`.
- **Object path**: `ObjectCompileInput::resolve_got_module()` returns `(defining_module, slot)`. `FnCompiler` looks up the module's `DataId` from a `got_data_ids` map and emits `global_value`.

### What changes for compile_to_module

The `CompilationEnv` implementation is provided by the caller, not by `compile_to_module`. This is correct — the caller knows the GOT topology:

- Priority worker: passes `SessionCompilationEnv` (live GOT pointers).
- Nice worker: passes an `ObjectCompilationEnv` that returns `(module, slot)` pairs and uses `got_data_ids` to emit `DataSymbol` references.

`FnCompiler` already handles both cases via `resolve_got_entry` (legacy) and `resolve_got_module` (target). No FnCompiler changes are required for this unification.

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
for defn_ref in &all_declare {
    let mut sig = module.make_signature();
    for _ in defn_ref.params() {
        sig.params.push(AbiParam::new(types::I64));
    }
    sig.returns.push(AbiParam::new(types::I64));
    let func_id = module.declare_function(defn_ref.name.as_ref(), Linkage::Export, &sig)?;
    func_ids.insert(defn_ref.name.clone(), func_id);
}

// Compile each function body (Pass 2)
let mut func_ctx = FunctionBuilderContext::new();
for defn_ref in &all_declare {
    let compile_ctx = CompileContext {
        method_resolutions: &check.method_resolutions,
        expr_types: &check.expr_types,
        func_ids: &func_ids,
        func_arities: &func_arities,
        symbol_tables,
        current_module: current_module.clone(),
        env,
        traced_fns: None,
        alloc_func_id: intrinsic_ids.alloc,
        dealloc_func_id: intrinsic_ids.dealloc,
        alloc_string_func_id: intrinsic_ids.alloc_string,
        panic_func_id: intrinsic_ids.panic,
        vec_new_func_id: intrinsic_ids.vec_new,
        vec_drop_func_id: intrinsic_ids.vec_drop,
    };

    FnCompiler::compile_body(defn_ref, &mut func, &mut func_ctx, module, compile_ctx)?;

    let mut ctx = Context::for_function(func);
    module.define_function(func_id, &mut ctx)?;
}

// Mono specializations with per-specialization resolutions
for mono in &check.mono_defns {
    // Merge base resolutions with per-specialization resolutions
    let mut merged = check.method_resolutions.clone();
    merged.extend(mono.resolutions.clone());
    // ... same FnCompiler::compile_body call
}
```

### What changes in FnCompiler

Nothing. `FnCompiler` is already `FnCompiler<'a, M: Module>`. Its `compile_body` method takes `&mut M` and works with both `JITModule` and `ObjectModule`. The GOT reference encoding is handled through `CompileContext.env` (the `CompilationEnv` trait object), not through `M`.

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
| `ObjectCompileInput` | `cache/object.rs` | Deleted — `compile_to_module` reads from `(Program, CheckResult, SymbolTable)` directly |
| `ObjFnSlot` | `cache/object.rs` | Deleted — GOT encoding handled by `CompilationEnv` |
| `CrossModuleRefs` | `pipeline.rs` | Deleted — derived from symbol tables inside `compile_to_module` or caller |

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
| `build_obj_fn_slots` | `cache/object.rs` | ObjectModule-specific GOT slot info (may be refactored into `ObjectCompilationEnv`) |
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
    env: Option<&dyn CompilationEnv>,
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

## 12. CompilationEnv for the Object Path

The object path needs a `CompilationEnv` implementation that resolves GOT slots from symbol tables (not from live runtime state). Currently this is `ObjectCompileInput impl CompilationEnv`. After deleting `ObjectCompileInput`, we need a replacement.

### ObjectCompilationEnv

```rust
/// CompilationEnv for ObjectModule compilation.
/// Resolves GOT slots by reading from symbol tables (not live runtime state).
pub struct ObjectCompilationEnv<'a> {
    symbol_tables: &'a DashMap<ModuleFullPath, SymbolTable>,
    current_module: ModuleFullPath,
}

impl CompilationEnv for ObjectCompilationEnv<'_> {
    fn resolve_got(&self, name: &Symbol) -> Option<(i64, usize)> {
        // Object path doesn't use runtime pointers.
        // Return a sentinel GOT base — the actual GOT reference
        // will be emitted via resolve_got_module + DataSymbol.
        None
    }

    fn resolve_got_module(&self, name: &Symbol) -> Option<(ModuleFullPath, usize)> {
        // Look up in current module's symbol table, following Import chains
        let table = self.symbol_tables.get(&self.current_module)?;
        match table.get(name.as_ref())? {
            ModuleEntry::Def { got_slot: Some(slot), .. } => {
                Some((self.current_module.clone(), *slot))
            }
            ModuleEntry::Import { source } => {
                let source_table = self.symbol_tables.get(&source.module)?;
                if let Some(ModuleEntry::Def { got_slot: Some(slot), .. }) = source_table.get(source.symbol.as_ref()) {
                    Some((source.module.clone(), *slot))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn func_arity(&self, name: &Symbol) -> Option<usize> {
        let table = self.symbol_tables.get(&self.current_module)?;
        match table.get(name.as_ref())? {
            ModuleEntry::Def { scheme, .. } => {
                if let Type::Fn(params, _) = &scheme.ty {
                    Some(params.len())
                } else {
                    None
                }
            }
            ModuleEntry::Import { source } => {
                let source_table = self.symbol_tables.get(&source.module)?;
                if let Some(ModuleEntry::Def { scheme, .. }) = source_table.get(source.symbol.as_ref()) {
                    if let Type::Fn(params, _) = &scheme.ty {
                        Some(params.len())
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}
```

This reads from the same `symbol_tables` DashMap that the priority worker uses, ensuring both paths see identical GOT slot assignments.

## 13. Migration Steps

Ordered implementation plan with dependency constraints.

### Step 1: Extract `declare_intrinsics<M: Module>`

**Files**: `crates/cranelisp-backend/src/jit.rs`, `crates/cranelisp-backend/src/cache/object.rs`

Extract the intrinsic declaration logic from `Jit::declare_intrinsics()` into a free function `declare_intrinsics<M: Module>(module: &mut M) -> Result<IntrinsicFuncIds>`. Both `Jit::declare_intrinsics` and `declare_intrinsic_imports` delegate to this function.

**Verification**: All existing tests pass. No behavioural change.

### Step 2: Implement `compile_to_module<M: Module>`

**Files**: `crates/cranelisp-backend/src/lib.rs`

Write the unified function using the defn collection logic from `collect_and_declare_defns` (the working path). Initially, `compile_program`, `compile_module_program`, and `compile_expr_with_got_and_symbols` become thin wrappers that call `compile_to_module<JITModule>`.

**Verification**: All existing tests pass. `compile_program`, `compile_module_program`, and REPL expression compilation produce identical results.

### Step 3: Implement `ObjectCompilationEnv`

**Files**: `crates/cranelisp-backend/src/cache/object.rs`

Implement the `CompilationEnv` trait for the object path that reads GOT slots from symbol tables.

**Verification**: Unit test that creates a populated `SymbolTable` and verifies `resolve_got_module` returns correct (module, slot) pairs.

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
| GOT reference dispatch | `match got_ref` inside `FnSlot` at each GOT load | `CompilationEnv` trait dispatches once | Cleaner separation: FnCompiler doesn't know which module type it targets |
| Intrinsic declaration | Separate per-path | `declare_intrinsics<M>` | Single source of truth for intrinsic set |
| Defn collection | Separate per-path (object path broken) | One path, reused | Fixes multi-sig handling for object path |
| Parameter passing | 21 positional params | `(Program, CheckResult, SymbolTable)` — same inputs as typecheck output | Addresses HIGH-3 without inventing a new input struct |

### What we adopt from the sketch

- `FnCompiler<M: Module>` generic pattern (already adopted).
- GOT data symbol naming convention (`__cranelisp_got_<module>`).
- `__data` vs `__bss` workaround (explicit zero bytes, not `define_zeroinit`).
- ObjectModule-specific GOT setup as a pre-step before compilation.
- Background cache writing pattern (unchanged by this design).
