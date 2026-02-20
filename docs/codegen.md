# Code Generation

## AST to Cranelift IR Mapping

Each expression type maps to specific Cranelift instructions:

| Expression | Cranelift IR |
|---|---|
| `IntLit(n)` | `iconst.i64 n` |
| `BoolLit(b)` | `iconst.i64 0` or `iconst.i64 1` |
| `FloatLit(v)` | `f64const v` then `bitcast.i64` |
| `StringLit(s)` | `call alloc(8 + len)`, `istore64 len` at offset 0, `istore8` loop for bytes |
| `Var(name)` | `use_var(variable)` |
| `Apply(Var(op), [a, b])` | Trait-dispatched: inline primitive or `call` to mangled method (see below) |
| `Let([x e], body)` | `def_var(x, compile(e)); compile(body)` |
| `If(c, t, e)` | `brif` + then/else/merge blocks (see below) |
| `Lambda([p], body)` | Compile body as separate function, allocate closure (see `docs/closures.md`) |
| `Apply(f, args)` | Direct `call` for known functions, `call_indirect` via closure for dynamic calls |
| `Var(name)` (function) | Wrap named function in closure with env_ptr-dropping wrapper |
| `Do(exprs)` | Compile each expr, return value of last |
| `Pure(expr)` | Compile inner expression (no-op — `IO a` = `a` at runtime) |
| `Bind(io, cont)` | Compile `io`, compile `cont`, call continuation as closure with io result |
| `Match(scrut, arms)` | Test-and-branch chain: compare tag, bind fields, fallthrough on mismatch |
| `Apply(Var("read-line"), [])` | Resolved via `ResolvedCall::BuiltinFn` → lookup `FuncId` from module entry → `call` |

## Trait-Dispatched Operators

Operators are parsed as `Apply(Var("+"), [a, b])`. The codegen checks the `MethodResolutions` table to find the resolved call:

**Inline primitives** (Int) — compiled to direct Cranelift instructions via `compile_inline_primitive`, zero overhead:

| Resolved Name | Cranelift IR |
|---|---|
| `+$Int` / `add-i64` | `iadd(lhs, rhs)` |
| `-$Int` / `sub-i64` | `isub(lhs, rhs)` |
| `*$Int` / `mul-i64` | `imul(lhs, rhs)` |
| `/$Int` / `div-i64` | `sdiv(lhs, rhs)` |
| `=$Int` / `eq-i64` | `icmp(Equal, lhs, rhs)` + `uextend.i64` |
| `<$Int` / `lt-i64` | `icmp(SignedLessThan, lhs, rhs)` + `uextend.i64` |
| `>$Int` / `gt-i64` | `icmp(SignedGreaterThan, lhs, rhs)` + `uextend.i64` |
| `<=$Int` / `le-i64` | `icmp(SignedLessThanOrEqual, lhs, rhs)` + `uextend.i64` |
| `>=$Int` / `ge-i64` | `icmp(SignedGreaterThanOrEqual, lhs, rhs)` + `uextend.i64` |

**Inline primitives** (Float) — bitcast i64→f64, operate, bitcast f64→i64:

| Resolved Name | Cranelift IR |
|---|---|
| `+$Float` / `add-f64` | `bitcast` + `fadd` + `bitcast` |
| `-$Float` / `sub-f64` | `bitcast` + `fsub` + `bitcast` |
| `*$Float` / `mul-f64` | `bitcast` + `fmul` + `bitcast` |
| `/$Float` / `div-f64` | `bitcast` + `fdiv` + `bitcast` |
| `=$Float` / `eq-f64` | `bitcast` + `fcmp(Equal)` + `uextend.i64` |
| `<$Float` / `lt-f64` | `bitcast` + `fcmp(LessThan)` + `uextend.i64` |
| `>$Float` / `gt-f64` | `bitcast` + `fcmp(GreaterThan)` + `uextend.i64` |
| `<=$Float` / `le-f64` | `bitcast` + `fcmp(LessThanOrEqual)` + `uextend.i64` |
| `>=$Float` / `ge-f64` | `bitcast` + `fcmp(GreaterThanOrEqual)` + `uextend.i64` |

**User-defined trait methods** — compiled as `call` to the mangled function name (e.g., `show$Int` calls `int-to-string`).

## If Expression: brif + Merge Block Pattern

Since `if` is an expression (returns a value), we use block parameters for the SSA phi:

```
entry_block:
    cond_val = compile(cond)
    brif cond_val, then_block, else_block

then_block:
    then_val = compile(then_branch)
    jump merge_block(then_val)

else_block:
    else_val = compile(else_branch)
    jump merge_block(else_val)

merge_block(result: i64):
    ; result is the value from whichever branch was taken
```

The merge block has one block parameter that receives the result from either branch.

## Comparison Operators

Cranelift's `icmp` returns an `i8` (0 or 1). Since all our values are `i64`, we `uextend` the result to `i64`. This ensures comparisons can be used in arithmetic or passed as function arguments.

## JIT Module Lifecycle

1. **Create ISA**: `cranelift_native::builder()` for the host machine
2. **Create JITModule**: via `JITBuilder` with registered builtin symbols
3. **Declare all functions**: `module.declare_function(name, Linkage::Local, &sig)` — returns `FuncId`
4. **Declare builtins**: `module.declare_function("cranelisp_alloc", Linkage::Import, &sig)` — intrinsics, platform functions, and extern primitives declared via `Linkage::Import` (symbol strings are internal JIT keys)
5. **Define all functions**: For each function:
   - Set `ctx.func.signature` and `ctx.func.name`
   - Build IR with `FunctionBuilder`
   - `module.define_function(func_id, &mut ctx)`
   - `module.clear_context(&mut ctx)` for reuse
6. **Finalize**: `module.finalize_definitions()` — resolves relocations, makes code executable
7. **Execute**: `module.get_finalized_function(main_id)` → `transmute` → call

## Builtin FFI

Builtins are Rust functions with `extern "C"` calling convention, split into three layers:

- **`platform.rs`** — user-visible effects: `print_string(ptr: i64) -> i64` (String -> IO Int), `read_line() -> i64` (() -> IO String). Registered via `builtin_stdio_platform()` descriptors. Dispatched through `ResolvedCall::BuiltinFn` — codegen looks up the `FuncId` from the `DefKind::Primitive` module entry, not from hard-coded name checks.
- **`intrinsics.rs`** — internal machinery: `cranelisp_alloc(size: i64) -> i64` (heap allocation for closures and strings), `cranelisp_panic` (match exhaustiveness failure)
- **`primitives/`** — per-type extern functions: `int_to_string`, `bool_to_string`, `float_to_string`, `string_identity`, `parse_int`, plus operator wrapper functions for first-class operator values

Registration (example for intrinsics and primitives):
1. `JITBuilder::symbol("cranelisp_alloc", fn_ptr as *const u8)` — registers the symbol
2. `module.declare_function("cranelisp_alloc", Linkage::Import, &sig)` — declares it importable
3. Inside each function body: `module.declare_func_in_func(func_id, &mut builder.func)` — makes it callable
4. At `finalize_definitions()`, the JIT linker resolves the symbol to the registered pointer

Platform functions follow the same registration path but dispatch differently: the typechecker emits `ResolvedCall::BuiltinFn(FQSymbol)` during inference, and codegen resolves the `FuncId` from the target module's `CompiledModule` entry via `populate_builtin_func_ids()`.

## Calling Convention

All functions use `extern "C"` (SystemV on x86-64/aarch64). All parameters and return values are `i64`.

## Two-Pass Compilation

**Pass 1 — Declare**: Register all function signatures with the module. This creates `FuncId`s that can be referenced during code generation.

**Pass 2 — Define**: Compile each function body. When a function calls another (including itself for recursion), it uses `declare_func_in_func` to get a local reference to the already-declared function.

This two-pass approach means functions can call each other regardless of definition order.
