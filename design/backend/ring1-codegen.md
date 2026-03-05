# Ring 1 Backend Codegen Design

## Overview

Ring 1 extends the backend from Ring 0 (pure stack-based values: Int, Bool, Float) to heap-allocated values: Strings, ADTs with fields, and closures. This document describes the codegen patterns, heap layout decisions, and architectural trade-offs.

## Module Structure

```
cranelisp-backend/src/
  lib.rs             -- public API: compile_program, compile_and_run_expr_with_got
  jit.rs             -- Cranelift ISA setup, JIT module lifecycle, intrinsic registration
  got.rs             -- GOT (Global Offset Table) for Interactive mode
  codegen_types.rs   -- re-exports (NULLARY_TAG_THRESHOLD)
  operators.rs       -- inline arithmetic/comparison/boolean IR emission
  heap.rs            -- heap layout structs, load/store helpers, RC emission, last-use analysis
  compiler/
    mod.rs           -- FnCompiler struct, CompileContext, compile_body, compile_expr dispatch
    literals.rs      -- int, float, bool, string literal codegen + variable reference
    apply.rs         -- function application: direct, GOT-indirect, data constructor, extern, closure
    control_flow.rs  -- let, if, lambda (with captures), named-function-as-value wrappers
    match_codegen.rs -- pattern matching: nullary, data, wildcard, variable patterns
```

## Heap Layout

All heap objects share a common header (`HeapHeader` from `cranelisp-types`):

```
Offset 0:  alloc_size  (i64) -- total allocation size in bytes
Offset 8:  rc          (i64) -- reference count (initial: 1)
Offset 16: ...payload...
```

Base-pointer convention: heap pointers point to offset 0 (where `alloc_size` lives). All field accesses use positive offsets. This departs from the sketch's interior-pointer convention (which used negative offsets for the header).

### HeapAdt Layout

ADTs with data constructors (`HeapAdt` in `heap.rs`):

```
[header(16 bytes) | tag(8 bytes) | field_0(8 bytes) | ... | field_n(8 bytes)]
 ^-- base pointer
```

- `TAG_OFFSET = 16` (offset of tag from base)
- `FIELDS_START = 24` (offset of first field)
- `field_offset(i) = 24 + i * 8`
- `payload_size(n) = 8 + n * 8` (tag + n fields)

Nullary constructors (e.g., `None`, `Red`, `Green`) are NOT heap-allocated. They are bare i64 tags (0, 1, 2, ...). This is a key optimization: enum-only ADTs have zero heap overhead.

### HeapClosure Layout

Closures (`HeapClosure` in `heap.rs`):

```
[header(16 bytes) | code_ptr(8 bytes) | cap_0(8 bytes) | ... | cap_n(8 bytes)]
 ^-- base pointer
```

- `CODE_PTR_OFFSET = 16`
- `CAPTURES_START = 24`
- `capture_offset(i) = 24 + i * 8`
- `payload_size(n) = 8 + n * 8` (code_ptr + n captures)

### Compile-Time Assertions

Both `HeapAdt` and `HeapClosure` have compile-time assertions (`const _: () = assert!(...)`) validating their offset constants against `#[repr(C)]` struct layouts. This ensures offset constants stay in sync with the actual memory layout.

## Representation Containment

Per `src/CLAUDE.md` "Heap Access", only the emit helpers in `heap.rs` may import layout constants. All other codegen code calls `heap_load`, `heap_store`, `emit_alloc`, `emit_rc_inc`, `emit_rc_dec`. This confines layout assumptions to a single module.

## Intrinsic Registration

All runtime functions are registered on the `JITBuilder` by function pointer in `jit.rs::register_intrinsics()`. This is the single source of truth for the JIT name -> function pointer mapping (addresses cache audit HIGH-1).

Naming convention:
- Runtime infrastructure: `runtime/alloc`, `runtime/dealloc`, `runtime/panic`, `runtime/alloc_string`, `runtime/string_read`, `runtime/rc_underflow_check`
- User-visible extern primitives: `str-concat`, `str-eq`, `str-len`, `string-identity`, `int-to-string`, `float-to-string`, `bool-to-string`, `parse-int`

The `IntrinsicIds` struct captures the `FuncId`s for the four core runtime functions (alloc, dealloc, alloc_string, panic) so they can be threaded into `CompileContext` for use by emission helpers.

## String Codegen

Strings are Rust-managed via extern functions in `cranelisp-runtime`. The backend never reads or writes string bytes directly.

### String Literal Compilation

`compile_string_lit` in `literals.rs`:

1. Store the UTF-8 bytes of the literal in a Cranelift anonymous data section (`declare_anonymous_data` + `define_data`).
2. Get a `global_value` reference to the data section pointer.
3. Call `runtime/alloc_string(data_ptr, len)` to allocate a `HeapString` on the runtime heap.
4. The returned i64 is a base pointer to the `HeapString`.

Empty strings: call `alloc_string(null, 0)` (null pointer, zero length).

### String Primitive Dispatch

String operations (`str-concat`, `str-eq`, etc.) are dispatched as extern calls via `compile_extern_call` in `apply.rs`. The `is_extern_primitive()` function identifies these names and routes them through the extern call path instead of the inline operator path.

## ADT Codegen

### Data Constructor Call

`compile_data_constructor_call` in `apply.rs`:

1. Look up the constructor's `(tag, field_count)` via `data_constructor_info()` in `literals.rs`.
2. Validate argument count matches field count.
3. Call `emit_alloc(payload_size)` where payload = tag + n fields.
4. Store tag at `HeapAdt::TAG_OFFSET`.
5. Store each compiled field value at `HeapAdt::field_offset(i)`.
6. Return the base pointer.

### Match Compilation

`compile_match` in `match_codegen.rs`:

The match compiler generates a test-and-branch chain:
1. Evaluate the scrutinee once.
2. For each arm: test the pattern, branch to the next arm on failure.
3. On match: bind pattern variables (if any), compile the arm body, jump to merge block.
4. The merge block uses a block parameter to receive the result from whichever arm matched.

#### Mixed Nullary/Data Discrimination

When a type has both nullary constructors (bare tags) and data constructors (heap pointers), the match must first determine which category the scrutinee falls into:

- If `scrutinee < NULLARY_TAG_THRESHOLD (1024)`: it's a nullary tag. Compare directly against expected tags.
- Otherwise: it's a heap pointer. Load the tag from `base + TAG_OFFSET (16)` and compare.

The `is_mixed_adt()` function in `heap.rs` determines whether a type requires this two-phase discrimination.

#### Pattern Types

- **Constructor (nullary)**: Compare scrutinee (or loaded tag) against expected tag.
- **Constructor (data)**: Compare tag, then load fields from heap and bind to pattern variables.
- **Wildcard**: Always matches (no test, direct fallthrough).
- **Variable**: Always matches, binds the scrutinee to the pattern variable.

## Closure Codegen

### Lambda Compilation

`compile_lambda` in `control_flow.rs`:

1. **Free variable analysis**: `find_free_vars(body, params)` collects variables referenced in the lambda body that are not bound by the lambda's own parameters. Variables that exist in the enclosing scope's `variables` map are captures.

2. **Inner function compilation**: A separate JIT function is emitted with signature `(env_ptr: i64, param_0: i64, ..., param_n: i64) -> i64`. This function:
   - Loads captured values from the environment pointer at `HeapClosure::capture_offset(i)`.
   - Binds lambda parameters from the remaining function parameters (skipping `env_ptr`).
   - Compiles the body.

3. **Closure allocation**: At the lambda site, allocate a closure `[header | code_ptr | captures...]`:
   - Call `emit_alloc(payload_size)` with `payload_size = 8 + n_captures * 8`.
   - Store the inner function's code address at `CODE_PTR_OFFSET`.
   - Store each captured value at `capture_offset(i)`.

### Closure Call

`compile_closure_call` in `apply.rs`:

1. Load `code_ptr` from `closure_ptr + CODE_PTR_OFFSET (16)`.
2. Build a `call_indirect` signature: `(env_ptr, param_0, ..., param_n) -> i64`.
3. Call with `[closure_ptr, arg_0, ..., arg_n]` -- the closure pointer itself serves as the environment pointer.

### Callee Routing in `compile_apply`

When the callee is `Expr::Var`:
1. Check if it's a data constructor -> `compile_data_constructor_call`.
2. Check if it's a local variable (in `self.variables`) -> `compile_closure_call` (the variable holds a closure value).
3. Otherwise -> `compile_direct_call` (named top-level function).

When the callee is any other expression (e.g., a lambda expression, a function call returning a closure) -> compile the callee expression, then `compile_closure_call`.

### Named Functions as Values

When a top-level function name is referenced as a value (e.g., `(let [f add-i64] ...)`), it must be wrapped in a closure for uniform representation.

`compile_fn_as_value` in `control_flow.rs`:

1. Look up the function's arity from `func_arities`.
2. Compile a wrapper function with signature `(env_ptr, params...) -> i64` that:
   - Ignores `env_ptr`.
   - Calls the real function directly (Batch) or via GOT-indirect (Interactive).
3. Allocate a zero-capture closure `[header | wrapper_code_ptr]`.

This ensures all function values have uniform closure representation: any value of type `Fn` can be called via the closure protocol (`load code_ptr, call_indirect`).

## Batch vs. Interactive Mode

The backend supports two compilation modes:

- **Batch** (`CompileMode::Batch`): All functions in a program are compiled together. Function calls use direct `call` instructions via `FuncId`.
- **Interactive** (`CompileMode::Interactive`): Functions are compiled one at a time (REPL). Function calls use GOT-indirect `call_indirect`: load a function pointer from a known offset in the GOT table, then call through it. This supports function redefinition: updating the GOT slot redirects all callers.

The mode affects:
- `compile_direct_call`: direct `call` vs. GOT-indirect `call_indirect`.
- `emit_wrapper_call` (named-function-as-value): same distinction.
- GOT slot management: only in Interactive mode.

## TCO (Tail Call Optimization)

Self-recursive tail calls are compiled as jumps to a loop header block instead of function calls. This is unchanged from Ring 0.

Key invariant: `in_tail_position` is set to `false` before compiling arguments, conditions, and binding values. It is propagated to:
- If branches (both then and else)
- Let body
- Match arm bodies

## RC Scaffolding (Ring 2 preparation)

Ring 1 includes scaffolding for RC emission that will be activated in Ring 2:

- `emit_rc_inc`: inline atomic `atomic_rmw(Add, rc_addr, 1)`.
- `emit_rc_dec`: inline atomic `atomic_rmw(Sub, rc_addr, 1)`, then conditional dealloc when rc reaches 0 (with optional drop glue call).
- `compute_last_uses`: walks the expression tree to determine the final use of each variable.
- `FnCompiler` fields: `variable_types`, `last_uses`, `consumed_vars`, `captured_vars` -- all `#[allow(dead_code)]` scaffolding.

These are tested at the unit level but not yet wired into the expression compilation pipeline. Ring 2 will activate them for the consuming calling convention and scope cleanup.

## REPL Value Display

`format_result_value` in `src/repl.rs` formats JIT results for REPL display:

| Type | Display format | Example |
|------|---------------|---------|
| Int | `:Int value` | `:Int 42` |
| Bool | `:Bool true/false` | `:Bool true` |
| Float | `:Float value` | `:Float 3.14` |
| String | `:String "contents"` | `:String "hello"` |
| Fn | `:(Fn [params] ret) <closure>` | `:(Fn [Int] Bool) <closure>` |
| ADT (nullary) | `:Type CtorName` | `:Color Red` |
| ADT (data) | `:(Type args) (Ctor fields)` | `:(Option Int) (Some 42)` |

String display reads heap memory via `cranelisp_runtime::read_string_as_str`. ADT display reads tag and fields from heap memory using the `HeapAdt` layout offsets. Recursive ADT fields (e.g., `(Some (Some 1))`) are formatted recursively.

## Rejected Alternatives

### Interior Pointer Convention (Sketch)

The sketch returned payload pointers (past the header) and used negative offsets for RC access. This was rejected because:
- Negative offsets are error-prone and confuse debugging.
- Base-pointer convention makes all offsets positive and uniform.
- No performance difference (both are constant-offset loads).

### Drop Function Pointer in Closure Struct (Sketch)

The sketch stored a `drop_ptr` field in the closure layout. Rejected because:
- Most closures have no heap captures, so `drop_ptr` was null and wasted 8 bytes.
- A side-table (`HashMap<code_ptr, drop_fn>`) keeps the layout uniform.
- The side-table approach is deferred to Ring 2 when drop glue is activated.

### Separate Closure Module

Considered creating a `compiler/closure.rs` for closure compilation. Instead, closures are split between:
- `control_flow.rs`: lambda compilation (which is a control flow construct, like let and if)
- `apply.rs`: closure calling (which is an application concern)

This matches the "one dispatch method per Expr variant" convention from `src/CLAUDE.md`.
