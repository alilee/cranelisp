# Backend Plan — Ring 0 Codegen and JIT

**Skill**: `/backend`
**Sprint**: 0 (planning only — no Rust code)
**Scope**: Plan for `cranelisp-backend` crate, Ring 0 expression codegen, JIT execution

## 1. Ring 0 Scope

Ring 0 property: **Expressions, types, functions, let, if, match (enum-only). No heap allocation, no reference counting.**

Ring 0 types: `Int`, `Bool`, `Float`, `Fn` (bare function pointers, no closures), `ADT` (nullary constructors only — bare i64 tags).

Ring 0 expression forms:
- `IntLit`, `FloatLit`, `BoolLit` — literal values
- `Var` — variable references (local and top-level, including nullary constructors)
- `Let` — sequential bindings (no lenient evaluation in Ring 0)
- `If` — conditional branching
- `Lambda` — non-capturing lambdas (bare function pointers)
- `Apply` — function application (builtins and user-defined)
- `Match` — pattern matching over enum-only ADTs (nullary constructors)
- `Annotate` — type annotations (transparent to codegen, resolved by typechecker)

Ring 0 top-level forms:
- `Defn` — function definitions
- `TypeDef` — enum-only ADTs (no fields on any constructor)

Ring 0 does NOT include:
- Heap allocation or reference counting
- Closures (capturing lambdas)
- Strings, Vecs, Lists, Seqs
- Data constructors with fields
- Traits, multi-sig dispatch, constrained polymorphism
- Modules (beyond the implicit `"user"` module)
- Macros
- IO, trace, test discovery (`discover-tests` / `catch-runtime-error` builtins, `spec/appendix-a-builtins.md §A`)
- Caching, linking, executable generation

---

## 2. Cranelift 0.125 ISA Setup

### 2.1 Single ISA Construction Point

The prototype has three separate ISA constructions (`jit.rs:77-103`, `cache.rs:385-403`, `exe.rs:46-60`) with divergent flags — documented as cache audit HIGH-2. The reimplementation MUST have a single ISA construction function.

**Design**:

```
pub fn build_isa_flags(is_pic: bool) -> settings::Flags
```

This function lives in `cranelisp-backend` and applies all shared Cranelift flags:
- `use_colocated_libcalls = false`
- `is_pic` = parameter (false for JIT, true for ObjectModule in later rings)

The ISA is constructed once during `Jit::new()` via:
```
let isa = cranelift_native::builder()?.finish(build_isa_flags(false))?;
```

This ISA is passed to `JITBuilder::with_isa()`. No other code path constructs an ISA. When caching (Ring 4) needs an ObjectModule ISA, it calls `build_isa_flags(true)` — same flags, different PIC setting.

### 2.2 Dependencies

```toml
[dependencies]
cranelisp-types = { path = "../cranelisp-types" }
cranelisp-runtime = { path = "../cranelisp-runtime" }
cranelift = "0.125"
cranelift-module = "0.125"
cranelift-jit = "0.125"
cranelift-native = "0.125"
cranelift-codegen = { version = "0.125", features = ["disas"] }
```

`cranelift-object` is deferred to Ring 4 (standalone executable generation).

### 2.3 ABI Convention

All Cranelisp values are i64 at runtime. Every function signature uses only `AbiParam::new(types::I64)` for parameters and returns. There is exactly one return value per function. This is invariant across all rings.

---

## 3. `FnCompiler` Design

### 3.1 Ring 0 Fields

The prototype `FnCompiler` has 28+ fields — documented as codegen audit HIGH-1 for triple-duplication of struct initialization. The reimplementation structures `FnCompiler` to:
1. **Separate shared context from per-function state**
2. **Provide an `inner_compiler()` constructor** for nested compilation (lambdas in Ring 1+)

```
pub struct CodegenContext<'a> {
    // Shared across all compilations in a unit
    pub call_mode: &'a CallMode,
    pub method_resolutions: &'a MethodResolutions,
    pub expr_types: &'a HashMap<Span, Type>,
    pub type_defs: &'a HashMap<TypeName, TypeDefInfo>,
    pub constructor_to_type: &'a HashMap<Symbol, TypeName>,
    pub panic_func_id: Option<FuncId>,
}

pub struct FnCompiler<'a, 'ctx> {
    // Cranelift state
    pub(crate) builder: FunctionBuilder<'a>,
    pub(crate) module: &'a mut JITModule,

    // Shared context (immutable borrows)
    pub(crate) ctx: &'ctx CodegenContext<'ctx>,

    // Per-function state
    pub(crate) variables: HashMap<Symbol, Variable>,
    pub(crate) current_fn_name: Option<Symbol>,
    pub(crate) tail_loop_block: Option<Block>,
    pub(crate) in_tail_position: bool,
    pub(crate) fn_param_count: usize,
}
```

**Ring 0 simplifications**: No `scope_stack`, `drop_fn_cache`, `vec_elem_inc_cache`, `consumed_vars`, `unique_vars`, `borrowed_vars`, `borrowed_temps`, `branch_depth`, `in_trace_body`, `last_uses`, `variable_types`, `liveness_globals`, `alloc_func_id`, `free_func_id`, `par_eval_func_id`, `ivar_*_func_id`. These are all heap/RC/lenient/trace infrastructure that Ring 0 does not exercise.

**Addressing codegen audit HIGH-1**: The `CodegenContext` struct holds shared references, preventing the triple-duplication of initialization. When Ring 1 adds `inner_compiler()` for lambda bodies, the inner struct shares the same `&CodegenContext` and only initializes fresh per-function state.

### 3.2 `CallMode`

```
pub enum CallMode {
    Direct {
        func_ids: HashMap<Symbol, FuncId>,
    },
    Indirect {
        fn_slots: HashMap<Symbol, FnSlot>,
    },
}
```

- `Direct` — batch mode. All functions in the compilation unit are declared as `FuncId`s. Calls emit `call` instructions.
- `Indirect` — interactive (REPL) mode. Functions are called via GOT slots. Calls emit `load` from GOT + `call_indirect`.

The `CompileMode` enum (`Interactive`, `Batch`, `Release`) determines which `CallMode` to use. `Interactive` maps to `Indirect`, `Batch` maps to `Direct`, `Release` is deferred.

### 3.3 Method Resolution Dispatch in Ring 0

Ring 0 has only `ResolvedCall::BuiltinFn` resolutions — for inline primitive operators (`+`, `-`, `*`, `/`, `=`, `<`, `>`, `<=`, `>=`, `not`). The dispatch in `compile_apply` is:

1. Check `method_resolutions` for the call site's span.
2. If `BuiltinFn { name }`, call `compile_inline_primitive(name, arg_vals, span)`.
3. If not resolved, and callee is a `Var` referencing a known function, emit direct/indirect call.
4. If callee is a `Var` referencing a nullary constructor, return tag as `iconst`.
5. Otherwise, `CodegenError("undefined function")`.

Ring 0 does NOT exercise `TraitMethod`, `SigDispatch`, or `AutoCurry`. No closure calls. No accessor calls. No data constructor calls (all ADTs are enum-only).

---

## 4. Expression Codegen Plan

### 4.1 Literals

- `IntLit { value }` -> `builder.ins().iconst(types::I64, value)`
- `FloatLit { value }` -> `builder.ins().iconst(types::I64, value.to_bits() as i64)` (IEEE 754 bitcast)
- `BoolLit { value }` -> `builder.ins().iconst(types::I64, if value { 1 } else { 0 })`

No heap allocation. All literals are immediate i64 values.

### 4.2 Variables

`Var { name }`:
1. Local variable? -> `builder.use_var(variables[name])`
2. Nullary constructor? -> `builder.ins().iconst(types::I64, tag as i64)`
3. Top-level function used as a value? -> Ring 1 (closure wrapping required). In Ring 0, functions are only called, never passed as values. If this is attempted, emit `CodegenError("function values require closures — not yet supported")`.
4. Otherwise -> `CodegenError("undefined variable")`

### 4.3 Let

`Let { bindings, body }`:
```
for (name, expr) in bindings:
    val = compile_expr(expr)
    var = fresh_var(I64)
    builder.def_var(var, val)
    variables.insert(name, var)
body_val = compile_expr(body)
// remove bindings from variables map
return body_val
```

Ring 0 `let` is purely sequential — no lenient evaluation (that requires IVar intrinsics from `cranelisp-runtime`). Lenient evaluation is a Ring 4 feature.

Variables are scoped: bindings introduced in a `let` are removed from the `variables` map after the body is compiled. Since Ring 0 has no heap types, no scope cleanup (RC dec) is needed.

### 4.4 If

`If { cond, then_branch, else_branch }`:
```
save in_tail_position
in_tail_position = false
cond_val = compile_expr(cond)

then_block = create_block()
else_block = create_block()
merge_block = create_block()
append_block_param(merge_block, I64)

builder.ins().brif(cond_val, then_block, &[], else_block, &[])

switch_to_block(then_block)
seal_block(then_block)
restore in_tail_position
then_val = compile_expr(then_branch)
builder.ins().jump(merge_block, &[BlockArg::Value(then_val)])

switch_to_block(else_block)
seal_block(else_block)
else_val = compile_expr(else_branch)
builder.ins().jump(merge_block, &[BlockArg::Value(else_val)])

switch_to_block(merge_block)
seal_block(merge_block)
result = block_params(merge_block)[0]
return result
```

**Cranelift API pattern**: `brif` takes `Value` (i64 truthiness — 0 is false, non-zero is true). `jump` takes `&[BlockArg]` not `&[Value]` — must wrap with `BlockArg::Value(val)`. The merge block uses a block parameter to receive the result from whichever branch executed.

**Tail position**: Both branches inherit the enclosing tail position. The condition is never in tail position.

### 4.5 Function Application

`Apply { callee, args }`:

1. **TCO check** (see section 5): if in tail position and callee is `self`, jump to loop header.
2. Set `in_tail_position = false` for argument compilation.
3. Compile arguments left-to-right -> `arg_vals: Vec<Value>`.
4. Restore `in_tail_position`.
5. Check `method_resolutions` for `BuiltinFn` -> inline primitive.
6. Check if callee is a known top-level function -> direct/indirect call.
7. Otherwise -> error (no closures in Ring 0).

**Direct call (Batch)**:
```
let func_id = func_ids[name];
let local = module.declare_func_in_func(func_id, builder.func);
let call = builder.ins().call(local, &arg_vals);
builder.inst_results(call)[0]
```

**Indirect call (Interactive)**:
```
let fn_slot = fn_slots[name];
let sig = make_signature(param_count params of I64, 1 return of I64);
let sig_ref = builder.import_signature(sig);
let base = emit_got_base(fn_slot);
let offset = iconst(I64, slot * 8);
let ptr_addr = iadd(base, offset);
let fn_ptr = load(I64, MemFlags::trusted(), ptr_addr, 0);
let call = builder.ins().call_indirect(sig_ref, fn_ptr, &arg_vals);
builder.inst_results(call)[0]
```

### 4.6 Inline Primitives

For Ring 0, inline primitives handle both trait-mangled names (from `BuiltinFn` resolution) and raw names (from direct calls):

**Integer arithmetic** (wrapping — spec 12.7.2 says integer overflow wraps silently):
- `+` / `add-i64` -> `iadd`
- `-` / `sub-i64` -> `isub`
- `*` / `mul-i64` -> `imul`
- `/` / `div-i64` -> `sdiv` (division by zero: implementation-defined per spec)

**Integer comparison**:
- `=` / `eq-i64` -> `icmp(Equal, l, r)` then `uextend(I64, cmp)` (i8 -> i64)
- `<` / `lt-i64` -> `icmp(SignedLessThan, ...)` then `uextend`
- `>` / `gt-i64` -> `icmp(SignedGreaterThan, ...)` then `uextend`
- `<=` / `le-i64` -> `icmp(SignedLessThanOrEqual, ...)` then `uextend`
- `>=` / `ge-i64` -> `icmp(SignedGreaterThanOrEqual, ...)` then `uextend`

**Float arithmetic** (IEEE 754 bitcast pattern):
```
let lf = bitcast(F64, MemFlags::new(), l);
let rf = bitcast(F64, MemFlags::new(), r);
let res = fadd(lf, rf);   // or fsub, fmul, fdiv
bitcast(I64, MemFlags::new(), res)
```

**Float comparison**:
```
let lf = bitcast(F64, MemFlags::new(), l);
let rf = bitcast(F64, MemFlags::new(), r);
let cmp = fcmp(FloatCC::Equal, lf, rf);  // or LessThan, GreaterThan, etc.
uextend(I64, cmp)
```

**Boolean negation** (`not`):
- Unary, not binary. Must be handled separately from the 2-arg dispatch.
- `not x` -> `icmp(Equal, x, iconst(I64, 0))` then `uextend(I64, cmp)`

**Addressing codegen audit LOW-3**: The prototype's `compile_inline_primitive` silently returns `Ok(None)` for non-2-arg calls, which would miss unary primitives like `not`. The reimplementation dispatches by arity explicitly:
```
match args.len() {
    1 => match name { "not" => ..., _ => Ok(None) },
    2 => match name { "+" => ..., "-" => ..., ... },
    _ => Ok(None),
}
```

### 4.7 Match (Enum-Only)

`Match { scrutinee, arms }`:

Ring 0 match operates over enum-only ADTs — all constructors are nullary, so the scrutinee is a bare i64 tag.

```
scrut_val = compile_expr(scrutinee)

merge_block = create_block()
append_block_param(merge_block, I64)
panic_block = create_block()

arm_blocks = [create_block() for each arm]

jump(arm_blocks[0])  // or panic_block if arms is empty

for (i, arm) in arms.enumerate():
    next_block = arm_blocks[i+1] if i+1 < arms.len() else panic_block

    switch_to_block(arm_blocks[i])
    seal_block(arm_blocks[i])

    match arm.pattern:
        Wildcard:
            body_val = compile_expr(arm.body)  // inherits tail position
            jump(merge_block, [body_val])

        Var { name }:
            var = fresh_var(I64)
            def_var(var, scrut_val)
            variables.insert(name, var)
            body_val = compile_expr(arm.body)
            // remove name from variables
            jump(merge_block, [body_val])

        Constructor { name, bindings: [] }:  // always empty in Ring 0
            tag_val = iconst(I64, constructor_tag)
            cmp = icmp(Equal, scrut_val, tag_val)
            body_block = create_block()
            brif(cmp, body_block, &[], next_block, &[])

            switch_to_block(body_block)
            seal_block(body_block)
            body_val = compile_expr(arm.body)  // inherits tail position
            jump(merge_block, [body_val])

// Panic block: match exhaustiveness failure
switch_to_block(panic_block)
seal_block(panic_block)
// call runtime/panic ("match failed")
zero = iconst(I64, 0)
jump(merge_block, [zero])

switch_to_block(merge_block)
seal_block(merge_block)
result = block_params(merge_block)[0]
```

**Key Cranelift pattern**: Use `arm_blocks[i+1]` as the fallthrough target for arm `i`. Do NOT create separate `next_blocks` (prototype gotcha documented in MEMORY.md).

**Tail position**: Each arm body inherits the enclosing tail position. The scrutinee is NOT in tail position.

### 4.8 Lambda (Non-Capturing, Ring 0)

`Lambda { params, body }`:

In Ring 0, lambdas do not capture variables. They compile as bare function pointers. However, since Ring 0 does not support function values (closures are Ring 1), the primary codegen path for lambdas in Ring 0 is within `Defn` bodies. If a lambda appears as a standalone expression (e.g., `(fn [x] (+ x 1))`), the backend should emit `CodegenError("function values require closures — not yet supported")`.

Named functions (via `Defn`) compile as top-level functions without closure overhead.

### 4.9 Annotate

`Annotate { expr, annotation }`:

Transparent to codegen. Compile the inner `expr` and return its value. The annotation was consumed by the typechecker.

---

## 5. Tail Call Optimization (Self-Recursive TCO)

### 5.1 Loop-Based TCO

Self-recursive tail calls are optimized into loops. The pattern (from the prototype, `codegen.rs:1880-1960`):

1. **Entry block**: receives function parameters, jumps to loop header.
2. **Loop header block**: has one i64 block parameter per function parameter. NOT sealed eagerly (back-edges from tail calls will be added during body compilation).
3. **Body compilation**: proceeds from the loop header. Parameters are bound from the loop header's block params, not the entry block's.
4. **Tail self-call detection**: in `compile_apply`, if `in_tail_position && callee == current_fn_name && args.len() == fn_param_count`, compile args, jump to loop header with new values instead of calling.
5. **Dead block**: after the jump, create a dead block and switch to it (Cranelift requires the builder to be positioned at a block; the dead block is unreachable and will be eliminated).
6. **Finalization**: after compiling the body, `seal_all_blocks()` seals the loop header (and any other unsealed blocks), then `finalize()`.

### 5.2 Tail Position Tracking

`in_tail_position` is propagated through the AST:
- Function body: starts as `true`
- `If`: both branches inherit; condition is NOT tail
- `Let`: body inherits; binding values are NOT tail
- `Match`: arm bodies inherit; scrutinee is NOT tail
- `Apply`: callee and args are NOT tail. `in_tail_position` is saved, set to `false` before compiling args, and restored after.

### 5.3 Ring 0 TCO Simplification

Ring 0 TCO is simpler than the prototype because there are no heap types:
- No `emit_scope_cleanup_for_tco` (no RC decs to emit before the jump)
- No borrowed var/temp upgrades
- Just: compile args, jump to loop header with new values

---

## 6. GOT (Global Offset Table) for Interactive Mode

### 6.1 Per-Module GOT

Each module gets a GOT — a fixed-size array of function pointers (`Box<[*const u8; GOT_TABLE_SIZE]>`). In Ring 0, there is one module (`"user"`), so one GOT.

```
pub const GOT_TABLE_SIZE: usize = 1024;

pub struct ModuleCodegenState {
    pub got_table: Option<Box<[*const u8; GOT_TABLE_SIZE]>>,
    pub next_got_slot: usize,
    pub def_codegen: HashMap<Symbol, DefCodegen>,
}
```

### 6.2 GOT Allocation Flow

1. When a function is defined in interactive mode, allocate a GOT slot (`next_got_slot++`).
2. Compile the function.
3. After `module.finalize_definitions()`, get the function pointer via `module.get_finalized_function(func_id)`.
4. Write the function pointer to `got_table[slot]`.
5. Store `DefCodegen { got_slot, code_ptr, clif_ir, ... }` in `ModuleCodegenState`.

### 6.3 GOT-Indirect Calls

When compiling a call in `Indirect` mode:
```
got_base = iconst(I64, got_table_ptr_as_i64)  // immediate in JIT mode
offset = iconst(I64, slot * 8)
ptr_addr = iadd(got_base, offset)
fn_ptr = load(I64, trusted, ptr_addr, 0)
call_indirect(sig_ref, fn_ptr, args)
```

The `GotReference::Immediate(i64)` variant embeds the GOT base address as an immediate constant. This is sound because the GOT allocation is stable for the lifetime of the JIT module.

### 6.4 Hot Reload

When a function is redefined at the REPL:
1. Compile the new version.
2. Get the new function pointer.
3. Overwrite `got_table[slot]` with the new pointer.
4. All existing callers (which load from the GOT at runtime) automatically pick up the new version.

This is the key advantage of GOT-indirect calls: redefinition does not require recompiling callers.

---

## 7. `CompileMode` Handling

### 7.1 Batch vs Interactive

Both modes share a single compilation function (`compile_unit`). The `CompileMode` determines:

| Aspect | `Batch` | `Interactive` |
|---|---|---|
| Call dispatch | `CallMode::Direct` (FuncId) | `CallMode::Indirect` (GOT slot) |
| Function lookup | All declared up-front | GOT slot assigned incrementally |
| Hot-reload | Not supported | Supported (GOT slot overwrite) |
| Entry point | `main` function (Ring 4) | Evaluated expression |
| Result | Compiled module, no execution | Execute and display result |

### 7.2 compile_unit Entry Point

```
pub fn compile_unit(
    program: &Program,
    check_result: &CheckResult,
    symbol_table: &SymbolTable,
    mode: CompileMode,
    codegen_state: &mut ModuleCodegenState,
    jit: &mut Jit,
) -> Result<CompileResult, CranelispError>
```

This is the single entry point for both batch and interactive compilation. It:
1. Builds the `CodegenContext` from `check_result` and `symbol_table`.
2. For `Batch`: declares all functions up-front, builds `CallMode::Direct`.
3. For `Interactive`: allocates GOT slots, builds `CallMode::Indirect`.
4. Compiles each `Defn` in the program.
5. Returns `CompileResult { symbols, codegen, warnings }`.

For REPL expression evaluation, a wrapper function wraps the expression in a synthetic zero-arg `Defn`, compiles it, executes it, and returns the result.

---

## 8. JIT Execution and Result Extraction

### 8.1 Jit Struct (Ring 0)

```
pub struct Jit {
    module: JITModule,
    ctx: cranelift::codegen::Context,
    func_ctx: FunctionBuilderContext,
    panic_func_id: FuncId,
}
```

Ring 0 needs only `panic_func_id` — for match exhaustiveness failure. No `alloc_func_id`, `free_func_id`, or IVar intrinsics (those are Ring 1+/Ring 4).

### 8.2 Intrinsic Registration

Ring 0 intrinsics registered on the `JITBuilder`:
- `runtime/panic` (Rust: `runtime_panic`) — match failure handler (spec 12.7.2)

Ring 0 does NOT register:
- `runtime/alloc` / `runtime/dealloc` (no heap)
- `runtime/par_eval` / `runtime/ivar_*` (no lenient evaluation)
- `runtime/rc_dec_*` / `runtime/rc_*` (no RC)
- `runtime/trace_*` (no tracing)
- Extern primitives (`int-to-string`, `str-concat`, etc. — no strings)
- Operator wrappers (operators are inlined in Ring 0, not registered as JIT symbols)

### 8.3 Compilation Flow

```
// 1. Clear context
jit.ctx.func.clear();

// 2. Build signature (N params -> 1 return, all I64)
for _ in 0..param_count {
    jit.ctx.func.signature.params.push(AbiParam::new(types::I64));
}
jit.ctx.func.signature.returns.push(AbiParam::new(types::I64));

// 3. Compile body into jit.ctx.func
compile_body(defn, &mut jit.ctx.func, &mut jit.func_ctx, &mut jit.module, ...)?;

// 4. Define the function in the JIT module
let func_id = jit.module.declare_function(name, Linkage::Local, &jit.ctx.func.signature)?;
jit.module.define_function(func_id, &mut jit.ctx)?;

// 5. Finalize (make code executable)
jit.module.finalize_definitions()?;

// 6. Get function pointer
let code_ptr = jit.module.get_finalized_function(func_id);
```

### 8.4 Execution and Result Extraction

For REPL expression evaluation:
```
// Cast to extern "C" fn() -> i64 (zero args for REPL wrapper)
let f: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
let result: i64 = f();
```

Result formatting (per `repl/spec.md` section 1.5):

| Type | Extraction | Display |
|---|---|---|
| `Int` | `result` as i64 | Decimal integer |
| `Bool` | `result != 0` | `true` / `false` |
| `Float` | `f64::from_bits(result as u64)` | Decimal float |
| `ADT(name, [])` | `result` as tag, look up constructor name | `Type.Ctor` (e.g., `Color.Red`) |
| `Fn(_, _)` | function pointer (Ring 0: display not supported) | `<fn>` |

REPL output format: `:QualifiedType value` (e.g., `:primitives/Int 42`, `:user/Color Color.Red`).

### 8.5 CLIF IR and Disassembly Capture

For `/clif` and `/disasm` REPL commands, capture the IR and disassembly:
```
// CLIF IR (before finalization)
let clif_ir = format!("{}", jit.ctx.func.display());

// Disassembly (after definition, requires "disas" feature)
let disasm = jit.ctx.compiled_code()
    .and_then(|cc| cc.disasm.clone());
```

These are stored in `DefCodegen` for later retrieval.

---

## 9. Audit Finding Resolution

### 9.1 Codegen Audit Findings

#### HIGH-1: FnCompiler struct initialization duplicated three times

**Resolution**: Separate `CodegenContext` (shared, immutable) from `FnCompiler` (per-function, mutable). The `CodegenContext` is constructed once and shared via reference. When Ring 1 adds `inner_compiler()` for lambda bodies, it takes `&CodegenContext` and only initializes per-function state. The three-site duplication is structurally impossible.

#### HIGH-2: heap_category duplicated as method and free function

**Resolution**: Ring 0 has no heap classification logic (all types are `NeverHeap`). When heap classification is added in Ring 1, implement it as a single free function `HeapCategory::classify(ty: &Type, type_defs: &HashMap<TypeName, TypeDefInfo>) -> HeapCategory` on the `HeapCategory` enum in `cranelisp-types`. No method on `FnCompiler`. No duplication.

#### HIGH-3: vec-set/vec-push inline codegen ~230 lines each with tripled paths

**Resolution**: Deferred to Ring 1 (Vecs are not in Ring 0). When implemented, extract `emit_vec_bounds_check` and `emit_vec_mutate_inplace` helpers from the start.

#### HIGH-4: compile_run_tests is 233 lines with inline struct and unrolled loop

**Resolution**: Moot — the `(run-tests init pass-fn fail-fn)` special form was retired and `compile_run_tests` no longer exists in the backend tree. Test discovery is now the `discover-tests` / `catch-runtime-error` builtins (`spec/appendix-a-builtins.md §A`), which carry no bespoke backend codegen of this shape.

#### HIGH-5: compile_par_bind_continuation duplicates lambda compilation pattern

**Resolution**: `par-bind!` has been removed from the language (Sprint 0 FIXME resolution). No action needed.

### 9.2 Cache Audit Findings

#### HIGH-1: RC/trace/operator intrinsics not declared in ObjectModule

**Resolution**: Deferred to Ring 4 (caching is not in Ring 0). When implemented, the single `IntrinsicRegistry` table (see section 10.6) will serve both JIT and ObjectModule paths, making divergence structurally impossible.

#### HIGH-2: Duplicate ISA construction diverges from build_isa()

**Resolution**: Addressed in section 2.1. Single `build_isa_flags(is_pic: bool)` function. One construction point for Ring 0.

#### HIGH-3: compile_module_to_object() has 21 positional parameters

**Resolution**: Deferred to Ring 4. When implemented, use `CacheInputs` struct to bundle parameters. The `CodegenContext` pattern established in Ring 0 will naturally reduce parameter counts.

---

## 10. Cranelift 0.125 API Patterns and Gotchas

### 10.1 Block Arguments

`jump` and `brif` take `&[BlockArg]`, not `&[Value]`. Always wrap values:
```rust
builder.ins().jump(target, &[BlockArg::Value(val)]);
builder.ins().brif(cond, then_block, &[], else_block, &[]);
```

For blocks with parameters, the sender must provide `BlockArg::Value(val)` for each parameter. The receiver reads them via `builder.block_params(block)[i]`.

### 10.2 Comparison Results

`icmp` and `fcmp` return `i8`, not `i64`. Always `uextend` to `i64`:
```rust
let cmp = builder.ins().icmp(IntCC::Equal, l, r);
let result = builder.ins().uextend(types::I64, cmp);
```

### 10.3 Float Bitcast

Float values are stored as their bit pattern in i64. Use `bitcast` with `MemFlags::new()`:
```rust
let f_val = builder.ins().bitcast(types::F64, MemFlags::new(), i64_val);
// operate
let result = builder.ins().bitcast(types::I64, MemFlags::new(), f_val);
```

### 10.4 Block Sealing

- Seal a block after all its predecessors are known.
- Entry block: seal immediately (one predecessor: function entry).
- Branch targets (then/else/merge blocks): seal when switched to (predecessors already emitted).
- Loop header: do NOT seal eagerly — back-edges from tail calls are added during body compilation. Seal via `seal_all_blocks()` at the end.

### 10.5 Function Context Reuse

`FunctionBuilderContext` is reusable across compilations. Create once in `Jit::new()`, clear between compilations. This avoids re-allocating internal data structures.

`cranelift::codegen::Context` is also reusable — call `ctx.func.clear()` before each compilation.

### 10.6 Future Ring Patterns (noted for planning)

**IntrinsicRegistry** (Ring 1+): A single `struct IntrinsicRegistry` will declare all runtime intrinsics (alloc, free, panic, RC dec, trace) in one authoritative location. Both JIT and ObjectModule paths will read from this registry. This addresses cache audit HIGH-1 structurally.

**Module declaration**: `module.declare_function(name, Linkage::Import, &sig)` for externally-defined functions (intrinsics). `module.declare_function(name, Linkage::Local, &sig)` for locally-defined functions (user code).

---

## 11. Module Structure — `cranelisp-backend` Crate

### 11.1 File Layout (Ring 0)

```
cranelisp-backend/
  src/
    lib.rs           -- crate root, re-exports
    CLAUDE.md        -- crate conventions (ISA, ABI, gotchas)
    isa.rs           -- build_isa_flags(), ISA construction
    jit.rs           -- Jit struct, JITModule lifecycle, execution
    codegen.rs       -- FnCompiler, CodegenContext, compile_body
    codegen/
      expr.rs        -- compile_expr: literals, var, let, if, annotate
      apply.rs       -- compile_apply: function calls, inline primitives, TCO
      match_compile.rs -- compile_match: enum pattern matching
      primitives.rs  -- compile_inline_primitive: arithmetic, comparison
    got.rs           -- ModuleCodegenState, GOT allocation, FnSlot
    format.rs        -- Result value formatting for REPL display
```

### 11.2 Responsibility Separation

| File | Lines (est.) | Responsibility |
|---|---|---|
| `isa.rs` | ~30 | ISA flag construction — single source of truth |
| `jit.rs` | ~200 | JIT lifecycle: new, compile, execute, intrinsic registration |
| `codegen.rs` | ~150 | `FnCompiler` struct, `CodegenContext`, `compile_body`, `compile_unit` |
| `codegen/expr.rs` | ~100 | Expression dispatch: literals, var, let, if, annotate |
| `codegen/apply.rs` | ~150 | Function application, TCO self-call, direct/indirect calls |
| `codegen/match_compile.rs` | ~80 | Enum-only match: test-and-branch chain |
| `codegen/primitives.rs` | ~100 | Inline primitive IR: arithmetic, comparison, boolean |
| `got.rs` | ~80 | GOT allocation, `ModuleCodegenState`, `DefCodegen` |
| `format.rs` | ~50 | Value formatting for REPL display |

**Estimated total Ring 0**: ~940 lines (vs. prototype's 6,192 lines for the full codegen module).

### 11.3 No-Unwrap Policy

All codegen functions return `Result<..., CranelispError>`. No `.unwrap()` or `.expect()` in production paths (addressing codegen audit MED-1). Module/function declaration errors propagate as `CranelispError::CodegenError { message, span }`.

Debug assertions (`debug_assert!`) are acceptable for invariants that are proven by construction (e.g., "loop header block exists when TCO is enabled").

### 11.4 Function Size Limit

No function exceeds 100 lines (addressing codegen audit LOW-2 and codegen audit MED-2). Each `Expr` variant gets its own method. `compile_apply` dispatches to extracted helpers.

---

## 12. Interface Gaps

### 12.1 Panic Intrinsic Signature

The `cranelisp-runtime` crate must export a `runtime_panic` function (JIT name: `runtime/panic`) with signature `extern "C" fn(i64) -> i64` that prints a panic message and aborts. This is needed in Ring 0 for match exhaustiveness failure. The panic message representation needs to be defined:

**Proposed**: In Ring 0 (no strings), the panic function receives a statically allocated C string pointer embedded as `iconst`. The function prints it via `eprintln!` and calls `std::process::exit(1)`. This avoids needing heap allocation for panic messages in Ring 0.

When Ring 1 adds string support, the panic function will receive a Cranelisp heap string pointer.

### 12.2 REPL Integration

The `cranelisp` binary crate will need to:
1. Construct a `Jit` instance.
2. For each REPL input: parse -> expand (no-op) -> AST build -> typecheck -> codegen -> execute.
3. Format the result using `format.rs` and the inferred `Type`.
4. Display with timing (`compile_ms + eval_ms`).

The integration between the pipeline stages and the REPL loop lives in the binary crate, not in `cranelisp-backend`. The backend exports `compile_unit()`, `Jit`, and `format_result()`.

### 12.3 `not` Primitive Resolution

The `BuiltinFn` resolution currently stores only a name. For Ring 0 to correctly dispatch `not` (which is a 1-arg primitive), the typechecker must resolve `(not true)` as `ResolvedCall::BuiltinFn { name: "not" }`, and the backend must handle 1-arg builtins. This is consistent with the current `ring0-interfaces.md` which lists `not` among the Ring 0 builtins.

### 12.4 No Remaining Gaps

The Ring 0 interface subset (`ring0-interfaces.md`) is complete for the backend's needs. All types consumed by the backend (`CheckResult`, `MethodResolutions`, `SymbolTable`, `ModuleCodegenState`, `DefCodegen`, `CompileMode`) are fully specified.

---

## 13. Risk Assessment

| Risk | Mitigation |
|---|---|
| Cranelift 0.125 API breaks vs prototype patterns | Prototype is pinned to 0.125; patterns are validated |
| Ring 0 scope creep (adding closures/strings early) | Strict ring discipline; `CodegenError` for unsupported features |
| ISA flag management | Single construction point from day 1 |
| TCO correctness | Ring 0 TCO has no RC cleanup; simpler than prototype |
| Block sealing bugs | Follow prototype pattern exactly; test with recursive functions |

---

## Next skills

- `/frontend` -- reader and AST builder provide the input Ring 0 codegen consumes; implementation can proceed in parallel
- `/typecheck` -- typechecker produces `CheckResult` and `MethodResolutions` that Ring 0 codegen consumes; implementation can proceed in parallel
- `/qa` -- once `/frontend`, `/typecheck`, and `/backend` plans are complete, integration test scaffolding can begin for Ring 0 acceptance criteria
