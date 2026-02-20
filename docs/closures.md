# Closures and First-Class Functions

## Overview

Functions in cranelisp are first-class values. They can be created anonymously with `fn`, bound to variables, passed as arguments, and returned from other functions. Lambdas that reference variables from enclosing scopes capture those variables, forming closures.

```clojure
(fn [x] (+ x 1))                          ; anonymous function
(let [f (fn [x] (+ x 1))] (f 5))          ; bind and call → 6
(defn apply-fn [f x] (f x))               ; higher-order function
(defn make-adder [n] (fn [x] (+ n x)))    ; closure capturing n
```

## Syntax

### Lambda Expression

```clojure
(fn [param1 param2 ...] body)
```

Creates an anonymous function. Parameters are listed in square brackets. The body is a single expression. The result is a function value that can be called, bound, or passed.

### Function Application

```clojure
(callee arg1 arg2 ...)
```

The callee is any expression that evaluates to a function — a symbol naming a top-level function, a variable bound to a lambda, or a lambda expression itself. This replaces the previous `(func-name args...)` form where the callee had to be a literal symbol.

```clojure
((fn [x] (* x x)) 7)               ; immediate call → 49
(let [f (fn [x] (* x 2))] (f 5))   ; call via variable → 10
(apply-fn (fn [x] (+ x 1)) 5)      ; pass lambda as argument → 6
(apply-fn double 5)                 ; pass named function as argument → 10
```

## Type Inference

### Lambda Typing

A lambda expression `(fn [x y] body)` gets a function type by:

1. Creating fresh type variables for each parameter
2. Pushing the parameters into the type environment
3. Inferring the body type
4. Returning `Fn([param_types], body_type)`

```
(fn [x] (+ x 1))  →  Fn([Int], Int)  =  Int -> Int
(fn [x] x)        →  Fn([t0], t0)    =  t0 -> t0   (polymorphic)
```

### Apply Typing

All function calls use the same `Apply` inference rule, regardless of whether the callee is a named function, a variable, or a lambda:

1. Infer the callee type
2. Infer each argument type
3. Unify the callee type with `Fn([arg_types], fresh_ret_var)`
4. Return the resolved return type

This uniform treatment means higher-order functions "just work":

```clojure
(defn apply-fn [f x] (f x))
;; f : t0, x : t1
;; (f x) unifies t0 with Fn([t1], t2)
;; apply-fn : Fn([Fn([t1], t2), t1], t2)
```

## Runtime Representation

### Closure Layout

A function value at runtime is a pointer to a heap-allocated closure struct:

```
closure_ptr → [ code_ptr | cap_0 | cap_1 | ... | cap_n ]
               offset 0    +8      +16           +(n+1)*8
```

- **`code_ptr`** (offset 0): pointer to the compiled function code
- **`cap_0..cap_n`** (offsets 8, 16, ...): captured variable values, stored as i64

Non-capturing lambdas allocate a single-word closure `[code_ptr]`. The code still receives the closure pointer as `env_ptr` but ignores it.

### Calling Convention

All lambda bodies are compiled with signature `(env_ptr: i64, params...) -> i64`. The `env_ptr` is the closure pointer itself, allowing the body to load captures by offset.

At a dynamic call site:

```
code_ptr = load(callee_ptr, offset 0)      ; load code pointer from closure[0]
result   = call_indirect(code_ptr, [callee_ptr, arg0, arg1, ...])
```

The closure pointer is passed as the first argument so the callee can access its captured values.

### Direct Call Optimization

When the callee is a known top-level function called by name (e.g. `(fact 10)`, `(print 42)`), the compiler bypasses the closure convention entirely and emits a direct call or fn_table indirect call. This avoids heap allocation and the extra env_ptr argument for the common case.

### Named Functions as Values

When a top-level function is used as a value rather than called directly (e.g. `(apply-fn double 5)` where `double` appears as an argument), the compiler:

1. Generates a **wrapper function** with signature `(env_ptr: i64, params...) -> i64` that ignores `env_ptr` and calls the real function
2. Allocates a closure `[wrapper_code_ptr]`
3. Returns the closure pointer

This makes named functions compatible with the uniform closure calling convention.

## Capture Analysis

The module `captures.rs` computes free variables for each lambda expression:

```rust
pub fn free_vars(expr: &Expr, globals: &HashSet<String>) -> HashSet<String>
```

A variable is **free** in an expression if it is referenced but not bound by a `let`, `fn`, or function parameter within that expression. **Globals** (top-level function names and builtins like `print`) are excluded from captures — they are accessed via direct calls or wrapper generation instead.

### Examples

| Expression | Free Variables |
|---|---|
| `42` | ∅ |
| `x` | {x} |
| `(fn [x] x)` | ∅ |
| `(fn [x] (+ x n))` | {n} |
| `(let [x 1] (+ x y))` | {y} |
| `(fn [x] (fn [y] (+ x (+ y z))))` | {z} |

The analysis is recursive: for `Lambda { params, body }`, the free variables are `free_vars(body) - params - globals`.

## Codegen Detail

### Lambda Compilation

When the compiler encounters a `Lambda` expression:

1. **Analyze captures**: call `free_vars(lambda_expr, globals)` to determine which variables are captured
2. **Declare function**: `module.declare_anonymous_function(&sig)` with signature `(env_ptr: i64, params...) -> i64`
3. **Compile body** in a fresh `Function` and `FunctionBuilder`:
   - Block parameters: `[env_ptr, p0, p1, ...]`
   - Bind lambda parameters from block params (indices 1..N)
   - Load captured values from `env_ptr` at offsets `(i+1) * 8`
   - Compile the body expression
4. **Define function**: `module.define_function(func_id, &mut ctx)`
5. **Allocate closure**: call `cranelisp_alloc((1 + num_captures) * 8)`
6. **Store code pointer** at offset 0 using `func_addr` instruction
7. **Store captures** at offsets 8, 16, ... by reading current values of captured variables

The inner function is compiled within a scoped block. The outer `FunctionBuilder` is "paused" — its `module` borrow is lent to the inner compiler, then returned when the inner scope ends.

### Memory Management

Closures are heap-allocated via `cranelisp_alloc`, which uses Rust's global allocator. Memory is intentionally leaked — garbage collection is deferred to a future phase per the ROADMAP. Each closure allocation costs one `alloc` call and `(1 + num_captures) * 8` bytes.

## Limitations

- **Closure drop glue deferred**: closures are reference-counted and freed when their count reaches zero, but captured heap values (strings, ADTs, other closures) are not decremented because closures don't encode captured value types. Captures leak. See KNOWN_ISSUES.md.
- **No mutable closures**: captured values are copied at closure creation time. There is no shared mutable state between closures.
- **Per-use wrapper generation**: each time a named function appears as a value, a new wrapper and closure are allocated. A future optimization could cache these.
- **HashSet ordering**: capture order is non-deterministic (depends on HashSet iteration). This is correct but means closure layouts may vary between compilations.
