# stdio Platform Specification

**Name**: stdio
**Version**: 0.1.0
**ABI Version**: 1 (cranelisp-platform ABI_VERSION)
**Purpose**: Standard input/output platform for interactive and batch programs. Provides console IO via stdin/stdout.

## Consumer Requirements

### From /repl

- `print :: (Fn [String] (IO Int))` -- REPL needs print for user-visible IO output at the interactive prompt. The trampoline forces the IO tree after each REPL evaluation, so print output appears immediately.
- `read-line :: (Fn [] (IO String))` -- Future REPL input capability (not yet required by active sprints).

### From /port

- `print :: (Fn [String] (IO Int))` -- Exemplar project (Sudoku solver) needs print for solution output. Used in `bind!` chains to display formatted results.

### From /examples

- `print :: (Fn [String] (IO Int))` -- IO examples need print to demonstrate the effect system. Examples show `bind!`, `do`, and raw IO tree construction.

## Function Table

| Cranelisp Name | Type Signature | Scheduling Class | JIT Symbol | Description |
|---|---|---|---|---|
| `print` | `(Fn [String] (IO Int))` | Sequential | `cranelisp_print` | Print a string followed by a newline to stdout. Returns `(IO Int)` with value 0. Uses capture-RC protocol for the string parameter. |
| `read-line` | `(Fn [] (IO String))` | Sequential | `cranelisp_read_line` | Read a line from stdin. Trims trailing newline/carriage return. Returns the line as `(IO String)`. |

### Heap Parameter Ownership

The compiler uses a consuming calling convention (`compile_consuming_arg_list`): callers transfer ownership of heap-typed arguments to the callee. The caller does NOT decrement the reference count after the call returns. This means every platform function MUST consume every heap-typed parameter it receives, regardless of whether it needs to retain the value.

**Rules for platform function implementors:**

1. **If you capture the value** (e.g., storing it in a closure or buffer): call `.own()` on the `CL*` wrapper. This takes ownership without incrementing the reference count, since the caller already transferred its count to you.
2. **If you do not capture the value** (e.g., you read it and discard): call `.own()` to take ownership, then let the owned value drop normally. The `Drop` impl will decrement the reference count and free the allocation if it reaches zero.
3. **Never borrow without `.own()`**: A platform function that reads a heap parameter without calling `.own()` will leak the allocation. The caller has already relinquished its reference count, so nobody will free the value.

**Example — `print`**: The `print` function receives a `CLString` parameter. It calls `.own()` to take ownership, reads the string content for output, and then the owned value is dropped at function exit, decrementing the reference count.

### Scheduling Rationale

Both functions use `Sequential` scheduling because they share global resources (stdout, stdin). Two `print` calls in a `par-bind!` group must not interleave output. Two `read-line` calls must consume input lines in program order.

### Return Conventions

- `print` returns `(IO Int)` with value 0 (success). The return value exists so `bind!` chains can sequence print with other IO operations. A non-zero return value is reserved for future error reporting.
- `read-line` returns `(IO String)` containing the input line with trailing newline/carriage return stripped. On EOF or read error, returns an empty string.

## ABI Contract

Functions are declared via `declare_platform!` in the platform DLL and exported with `cranelisp_` prefix. The host loads the DLL, calls `cranelisp_platform_manifest` (which receives `HostCallbacks` containing the host allocator), and registers each function with the JIT using the declared type signature.

All platform functions:
- Are `extern "C"` with `i64` parameter/return ABI
- Use `CL*` wrapper types (`CLString`, `CLInt`) for type safety within the DLL
- Return `CLIO<CL*>` which allocates an IO Effect node on the host heap
- Must use `CLString.own()` (capture-RC protocol) when capturing heap parameters into deferred closures

## Conformance

Any platform that exports the same function names with the same type signatures can substitute for stdio. The test-capture platform is the canonical substitute for deterministic testing. A conforming substitute:

1. MUST export `print` with signature `(Fn [String] (IO Int))`
2. MUST export `read-line` with signature `(Fn [] (IO String))`
3. MUST use the same scheduling classes (Sequential for both)
4. MUST respect the capture-RC protocol for heap parameters
5. MAY differ in observable behavior (e.g., capturing output instead of printing)
