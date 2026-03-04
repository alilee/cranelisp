# 12. Runtime Model

This section defines the abstract runtime semantics of Cranelisp. It specifies observable behavior without prescribing a particular implementation strategy. A conforming implementation MAY use JIT compilation, ahead-of-time compilation, interpretation, or any hybrid approach.

## 12.1 Value Representation

All Cranelisp values are represented at runtime as machine-word-sized quantities (64-bit on all supported platforms). The interpretation of a word depends on its type, which is always known statically.

### 12.1.1 Scalar Types

| Type | Representation |
|---|---|
| `Int` | Signed 64-bit two's complement integer |
| `Bool` | `0` for `false`, `1` for `true` (in a 64-bit word) |
| `Float` | IEEE 754 double-precision (64-bit) float, stored as its bit pattern in a 64-bit integer word |

Scalar values are NOT heap-allocated. They require no memory management.

### 12.1.2 String

Strings are heap-allocated, immutable, UTF-8 byte sequences. The layout from the returned pointer is:

```
ptr → [length: i64 | bytes: u8...]
       offset 0      offset 8
```

- `length` (offset 0): The number of bytes in the string (not characters)
- `bytes` (offset 8): The raw UTF-8 byte data, NOT null-terminated

### 12.1.3 Function Values (Closures)

All function values at runtime are closures — a code pointer paired with zero or more captured values:

```
ptr → [code_ptr: i64 | cap_0: i64 | cap_1: i64 | ... | cap_n: i64]
       offset 0         offset 8     offset 16          offset (n+1)*8
```

- `code_ptr` (offset 0): Pointer to executable code
- `cap_0..cap_n`: Captured variable values, each stored as an i64

Non-capturing functions (including top-level named functions used as values) still use this representation with zero captures: `[code_ptr]`.

### 12.1.4 Algebraic Data Types

**Nullary constructors** (constructors with no fields) are represented as bare integer tags, NOT heap-allocated:

```
None  → 0
Red   → 0
Green → 1
Blue  → 2
```

Tags are assigned sequentially starting from 0 in definition order.

**Data constructors** (constructors with fields) are heap-allocated:

```
ptr → [tag: i64 | field_0: i64 | field_1: i64 | ... | field_n: i64]
       offset 0    offset 8       offset 16           offset (n+1)*8
```

- `tag` (offset 0): Integer tag identifying the constructor variant
- `field_0..field_n`: Field values, each stored as an i64

For sum types mixing nullary and data constructors, tags are assigned to ALL constructors (nullary and data) in definition order.

Example: `(deftype (Option a) None (Some [:a val]))` assigns tag 0 to `None` and tag 1 to `Some`. At runtime, `None` is the bare integer `0`, and `(Some 42)` is a heap pointer to `[1, 42]`.

### 12.1.5 Vec

Vec is a built-in resizable array type. Its layout is:

```
ptr → [length: i64 | capacity: i64 | data_ptr: i64]
       offset 0      offset 8        offset 16
```

- `length`: Number of elements currently in the Vec
- `capacity`: Number of elements the data buffer can hold
- `data_ptr`: Pointer to a separate heap-allocated buffer of `capacity * 8` bytes

Elements in the data buffer are stored as contiguous i64 values.

## 12.2 Calling Convention

### 12.2.1 Direct Calls

When calling a known function by name (the common case), the implementation SHOULD use a direct call with the function's declared parameter types. All parameters and return values are i64.

### 12.2.2 Indirect Calls (Closures)

When calling a function value (closure), the calling convention is:

```
result = call_indirect(code_ptr, [closure_ptr, arg_0, arg_1, ...])
```

The closure pointer is passed as the first argument, allowing the callee to load captured values from it. The remaining arguments follow. The return value is a single i64.

### 12.2.3 Top-Level Functions as Values

When a top-level function is used as a value (passed as an argument, stored in a data structure), the implementation MUST wrap it in a closure-compatible representation. This typically involves generating a wrapper function with signature `(env_ptr, params...) -> i64` that ignores the environment pointer and calls the real function.

## 12.3 Memory Management

### 12.3.1 Requirements

A conforming implementation MUST satisfy the following:

1. Heap-allocated values (strings, closures, data constructors, Vecs) MUST be freed when they are no longer reachable from any live binding or data structure.
2. Freed memory MUST NOT be accessed after deallocation.
3. The user MUST NOT need to manage memory manually — allocation and deallocation are entirely the implementation's responsibility.

### 12.3.2 Implementation Freedom

The implementation MAY use any memory management strategy:

- **Reference counting**: Insert increment/decrement operations at binding and scope-exit points. Note: since all values in Cranelisp are immutable, reference cycles cannot form, so reference counting is sufficient for correctness.
- **Tracing garbage collection**: Periodically trace live references from roots.
- **Region-based allocation**: Group allocations by lifetime.
- **Hybrid approaches**: Any combination of the above.

### 12.3.3 Vec Copy-on-Write

Vec operations (`vec-set`, `vec-push`) return a new Vec value. The implementation MAY optimize by mutating the backing storage in place when the Vec has a single owner. This is semantically invisible — the caller observes pure functional behavior regardless.

## 12.4 Evaluation Order

### 12.4.1 Strict Evaluation

Cranelisp uses **strict (eager) evaluation**. All sub-expressions are fully evaluated before their results are used. Specifically:

- Function arguments are evaluated left-to-right before the function body executes.
- `let` bindings are evaluated left-to-right.
- Both branches of `if` exist but only the selected branch is evaluated.
- `match` arms are tested top-to-bottom; only the first matching arm's body is evaluated.

### 12.4.2 Lazy Sequences

The `Seq` type provides lazy evaluation through thunks (zero-argument closures). Laziness is explicit and user-controlled — it is NOT a property of the evaluation model itself.

### 12.4.3 Lenient Evaluation

An implementation MUST evaluate independent `let` bindings in parallel where a cost heuristic determines it is beneficial. This is called **lenient evaluation**. Because all binding expressions in a `let` are pure, evaluating them concurrently produces the same result as sequential evaluation — the non-determinism in evaluation order is not observable.

A binding is independent if its free variables do not include any name bound earlier in the same `let` block. The implementation MUST apply a cost heuristic to avoid parallelizing trivially cheap bindings (e.g., arithmetic operations, variable references). Only bindings whose estimated cost exceeds the heuristic threshold are candidates for parallel evaluation.

Lenient evaluation is semantically transparent — programs MUST NOT depend on whether any particular binding is parallelized. An implementation MAY provide an opt-out mechanism (e.g., an environment variable) for debugging purposes.

## 12.5 Tail Call Optimization

Implementations SHOULD optimize self-recursive tail calls into loops. A tail call is a function call in tail position — the last operation before the function returns.

Tail position is defined recursively:
- The body of a function is in tail position
- In `(if c t e)`: both `t` and `e` are in tail position if the `if` is
- In `(let [bindings] body)`: `body` is in tail position if the `let` is
- In `(do e1 e2 ... en)`: `en` is in tail position if the `do` is
- In `(match scrut [p1 b1 p2 b2 ...])`: each `b_i` is in tail position if the `match` is
- Arguments to function calls are NOT in tail position
- Conditions in `if` are NOT in tail position
- Binding values in `let` are NOT in tail position

Implementation-defined: Whether mutual recursion, lambda self-recursion, or constrained polymorphic self-recursion are optimized.

## 12.6 Entry Point

In batch mode, a program MUST define a function named `main` with no parameters that returns `IO _` (IO of any type). Execution begins by calling `main` and the program's exit code is the integer value inside the resulting `IO Int` (or 0 for non-integer IO results).

```clojure
(defn main []
  (print "hello"))   ; print returns IO Int
```

## 12.7 Error Model

### 12.7.1 Compile-Time Errors

The following are compile-time errors:

- Parse errors (malformed syntax)
- Type errors (unification failure, arity mismatch)
- Unbound variable references
- Ambiguous name resolution
- Macro expansion errors (non-Sexp return type, expansion limit exceeded)

### 12.7.2 Runtime Errors

The following cause runtime errors (program termination):

| Error | Behavior |
|---|---|
| Non-exhaustive match | Runtime panic with "match failed" message |
| Division by zero | Implementation-defined (trap, panic, or error value) |
| Vec out-of-bounds access | Implementation-defined |
| Stack overflow | Implementation-defined |
| Integer overflow | Silent wraparound (two's complement) — NOT an error |

Note: Integer overflow silently wraps. This is specified behavior, not an error. `Int` values are 64-bit two's complement integers and arithmetic operations wrap on overflow.

## 12.8 Platform ABI

Platform functions (loaded via `(platform "name")`) use the C calling convention. All parameters and return values are i64. The platform ABI defines the contract between the Cranelisp runtime and external platform libraries.

Platform functions that perform side effects MUST return `IO _`. The implementation MUST provide a mechanism for platform functions to allocate Cranelisp values (strings, IO wrappers) through a host callback interface.

The specific details of the platform loading mechanism and host callback interface are implementation-defined.
