# 12. Runtime Model

This section defines the abstract runtime semantics of Cranelisp. It specifies observable behavior without prescribing a particular implementation strategy. A conforming implementation MAY use JIT compilation, ahead-of-time compilation, interpretation, or any hybrid approach.

## 12.1 Value Representation [Tested]

All Cranelisp values are represented at runtime as machine-word-sized quantities (64-bit on all supported platforms). The interpretation of a word depends on its type, which is always known statically.

### 12.1.1 Scalar Types [Tested tests/ring0.rs::dual_mode_simple_int]

| Type | Representation |
|---|---|
| `Int` | Signed 64-bit two's complement integer |
| `Bool` | `0` for `false`, `1` for `true` (in a 64-bit word) |
| `Float` | IEEE 754 double-precision (64-bit) float, stored as its bit pattern in a 64-bit integer word |

Scalar values are NOT heap-allocated. They require no memory management.

### 12.1.2 String [Tested tests/rc.rs::rc_string_alloc_and_drop]

Strings are heap-allocated, immutable, UTF-8 byte sequences. The layout from the returned pointer is:

```
ptr -> [length: i64 | bytes: u8...]
       offset 0      offset 8
```

- `length` (offset 0): The number of bytes in the string (not characters)
- `bytes` (offset 8): The raw UTF-8 byte data, NOT null-terminated

### 12.1.3 Function Values (Closures) [Tested tests/rc.rs::rc_closure_env_alloc]

All function values at runtime are closures — a code pointer paired with zero or more captured values:

```
ptr -> [code_ptr: i64 | cap_0: i64 | cap_1: i64 | ... | cap_n: i64]
       offset 0         offset 8     offset 16          offset (n+1)*8
```

- `code_ptr` (offset 0): Pointer to executable code
- `cap_0..cap_n`: Captured variable values, each stored as an i64

Non-capturing functions (including top-level named functions used as values) still use this representation with zero captures: `[code_ptr]`.

### 12.1.4 Algebraic Data Types [Tested tests/repl_experience.rs::constructor_tags_are_sequential]

**Nullary constructors** (constructors with no fields) are represented as bare integer tags, NOT heap-allocated:

```
None  -> 0
Red   -> 0
Green -> 1
Blue  -> 2
```

Tags are assigned sequentially starting from 0 in definition order.

**Data constructors** (constructors with fields) are heap-allocated:

```
ptr -> [tag: i64 | field_0: i64 | field_1: i64 | ... | field_n: i64]
       offset 0    offset 8       offset 16           offset (n+1)*8
```

- `tag` (offset 0): Integer tag identifying the constructor variant
- `field_0..field_n`: Field values, each stored as an i64

For sum types mixing nullary and data constructors, tags are assigned to ALL constructors (nullary and data) in definition order.

Example: `(deftype (Option a) None (Some [:a val]))` assigns tag 0 to `None` and tag 1 to `Some`. At runtime, `None` is the bare integer `0`, and `(Some 42)` is a heap pointer to `[1, 42]`.

### 12.1.5 Vec [Tested tests/rc.rs::rc_vec_alloc_drop]

Vec is a built-in resizable array type. Its layout is:

```
ptr -> [length: i64 | capacity: i64 | data_ptr: i64]
       offset 0      offset 8        offset 16
```

- `length`: Number of elements currently in the Vec
- `capacity`: Number of elements the data buffer can hold
- `data_ptr`: Pointer to a separate heap-allocated buffer of `capacity * 8` bytes

Elements in the data buffer are stored as contiguous i64 values.

## 12.2 Calling Convention [Tested]

### 12.2.1 Direct Calls [Tested tests/ring0.rs::chained_function_calls]

When calling a known function by name (the common case), the implementation SHOULD use a direct call with the function's declared parameter types. All parameters and return values are i64.

### 12.2.2 Indirect Calls (Closures) [Tested tests/ring0.rs::lambda_passed_to_function]

When calling a function value (closure), the calling convention is:

```
result = call_indirect(code_ptr, [closure_ptr, arg_0, arg_1, ...])
```

The closure pointer is passed as the first argument, allowing the callee to load captured values from it. The remaining arguments follow. The return value is a single i64.

### 12.2.3 Top-Level Functions as Values [Tested tests/ring0.rs::named_function_as_value]

When a top-level function is used as a value (passed as an argument, stored in a data structure), the implementation MUST wrap it in a closure-compatible representation. This typically involves generating a wrapper function with signature `(env_ptr, params...) -> i64` that ignores the environment pointer and calls the real function.

## 12.3 Memory Management [Tested]

### 12.3.1 Requirements [Tested tests/rc.rs::rc_string_alloc_and_drop]

A conforming implementation MUST satisfy the following:

1. Heap-allocated values (strings, closures, data constructors, Vecs) MUST be freed when they are no longer reachable from any live binding or data structure. [Tested tests/rc.rs::rc_string_alloc_and_drop]
2. Freed memory MUST NOT be accessed after deallocation. [Tested tests/rc.rs::rc_string_in_let_scope]
3. The user MUST NOT need to manage memory manually — allocation and deallocation are entirely the implementation's responsibility. [Tested tests/rc.rs::rc_string_alloc_and_drop]

### 12.3.2 Implementation Freedom [Tested tests/rc.rs::rc_string_alloc_and_drop]

The implementation MAY use any memory management strategy:

- **Reference counting**: Insert increment/decrement operations at binding and scope-exit points. Note: since all values in Cranelisp are immutable, reference cycles cannot form, so reference counting is sufficient for correctness.
- **Tracing garbage collection**: Periodically trace live references from roots.
- **Region-based allocation**: Group allocations by lifetime.
- **Hybrid approaches**: Any combination of the above.

### 12.3.3 Vec Copy-on-Write [Tested tests/rc.rs::rc_vec_set_copy]

Vec operations (`vec-set`, `vec-push`) return a new Vec value. The implementation MAY optimize by mutating the backing storage in place when the Vec has a single owner. This is semantically invisible — the caller observes pure functional behavior regardless.

## 12.4 Evaluation Order [Tested]

### 12.4.1 Strict Evaluation [Tested tests/ring0.rs::chained_function_calls]

Cranelisp uses **strict (eager) evaluation**. All sub-expressions are fully evaluated before their results are used. Specifically:

- Function arguments are evaluated left-to-right before the function body executes.
- `let` bindings are evaluated left-to-right.
- Both branches of `if` exist but only the selected branch is evaluated.
- `match` arms are tested top-to-bottom; only the first matching arm's body is evaluated.

### 12.4.2 Lazy Sequences [R3 S17]

The `Seq` type provides lazy evaluation through thunks (zero-argument closures). Laziness is explicit and user-controlled — it is NOT a property of the evaluation model itself.

### 12.4.3 Lenient Evaluation [R4 S11]

An implementation MUST evaluate independent `let` bindings in parallel where a cost heuristic determines it is beneficial. This is called **lenient evaluation**. Because all binding expressions in a `let` are pure, evaluating them concurrently produces the same result as sequential evaluation — the non-determinism in evaluation order is not observable.

A binding is independent if its free variables do not include any name bound earlier in the same `let` block. The implementation MUST apply a cost heuristic to avoid parallelizing trivially cheap bindings (e.g., arithmetic operations, variable references). Only bindings whose estimated cost exceeds the heuristic threshold are candidates for parallel evaluation.

Lenient evaluation is semantically transparent — programs MUST NOT depend on whether any particular binding is parallelized. An implementation MAY provide an opt-out mechanism (e.g., an environment variable) for debugging purposes.

## 12.5 Tail Call Optimization [Tested tests/ring0.rs::tco_deep_countdown]

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

## 12.6 Entry Point [R4 S10]

In batch mode, a program MUST define a function named `main` with no parameters that returns `IO _` (IO of any type). Execution begins by calling `main` and the program's exit code is the integer value inside the resulting `IO Int` (or 0 for non-integer IO results).

```clojure
(defn main []
  (print "hello"))   ; print returns IO Int
```

## 12.7 Error Model [Tested]

Cranelisp distinguishes two error categories: **compile-time errors** (detected before execution) and **runtime panics** (detected during execution). There is no exception mechanism, no user-exposed `try`/`catch`, and no `Result`-based error propagation for runtime faults. Runtime panics are **fatal to the current evaluation** but the execution environment (REPL session) survives.

### 12.7.1 Compile-Time Errors [Tested]

The following are compile-time errors:

- Parse errors (malformed syntax) [Tested tests/ring0.rs::error_parse_error_unclosed_paren]
- Type errors (unification failure, arity mismatch) [Tested tests/ring0.rs::type_error_add_bool]
- Unbound variable references [Tested tests/ring0.rs::error_unbound_symbol]
- Ambiguous name resolution [Tested crates/cranelisp-typecheck/src/checker.rs::test_import_ambiguity]
- Macro expansion errors (non-Sexp return type, expansion limit exceeded) [Tested tests/macros::neg_macro_non_sexp_return_type_batch, tests/macros::neg_macro_expansion_depth_limit_exceeded]

### 12.7.2 Runtime Panics [Tested]

A **runtime panic** terminates the current evaluation. It does NOT terminate the process in REPL mode (see §12.7.4). There is no mechanism for user code to catch or recover from a runtime panic — it is unconditionally fatal to the expression being evaluated.

#### 12.7.2.1 Panic Sources [Tested]

The following conditions cause a runtime panic:

| Condition | Message | Notes |
|---|---|---|
| Non-exhaustive match | `"match failed"` | All match arms tested, none matched [Tested tests/ring0.rs::error_non_exhaustive_match_runtime] |
| Integer division by zero | `"division by zero"` | `div-i64` with zero divisor [R4 S18] |
| Vec index out of bounds | `"vec-get: index out of bounds"` | `vec-get` or `vec-set` with index < 0 or >= length [R4 S18] |
| Stack overflow | Implementation-defined message | Exhaustion of the call stack (e.g., unbounded recursion without TCO) [R4 S18] |

#### 12.7.2.2 Conditions That Are NOT Panics

| Condition | Behavior | Rationale |
|---|---|---|
| Integer overflow | Silent wraparound (two's complement) | Specified behavior, not an error. `Int` values are 64-bit two's complement; `add-i64`, `sub-i64`, `mul-i64` wrap on overflow. [Tested tests/ring0.rs::integer_overflow_wraps] |
| Float division by zero | IEEE 754 result (`Inf`, `-Inf`, or `NaN`) | Follows IEEE 754 semantics. NOT a panic. [R4 S18] |
| `parse-int` with invalid input | Returns `None` | Parsing failure is a normal `Option` result, not an error. [Tested tests/ring1.rs::parse_int_valid] |
| IO operation failure | Platform-defined `IO` result | See §12.7.6. |

### 12.7.3 Arithmetic Policy [R4 S18]

Cranelisp uses **unchecked (wrapping) integer arithmetic** and **checked integer division**:

- **Integer addition, subtraction, multiplication**: Use two's complement wrapping. No overflow detection. This matches the `Int` type definition (signed 64-bit two's complement, §12.1.1). Programs that need overflow detection MUST implement it in user code (e.g., checking operand signs and comparing with the result).

- **Integer division** (`div-i64`): A divisor of zero causes a runtime panic. Division of `Int.MIN` by `-1` (which would overflow) also causes a runtime panic. All other integer divisions truncate toward zero.

- **Float arithmetic**: Follows IEEE 754 semantics throughout. Division by zero produces `Inf`, `-Inf`, or `NaN` depending on the operands. Float operations NEVER panic.

- **Modulo/remainder**: If provided, follows the same policy as integer division — zero divisor causes a runtime panic.

### 12.7.4 REPL vs Batch Error Behavior [R4 S18]

The execution environment determines what happens after a runtime panic:

#### 12.7.4.1 REPL Mode [R4 S18]

In REPL mode, a runtime panic terminates the current expression evaluation but MUST NOT terminate the REPL session. The REPL MUST:

1. Display the panic message to the user (see §12.7.5).
2. Preserve all session state: previously defined functions, types, imports, and module context remain available.
3. Return to the input prompt, ready for the next expression.

```
user> (match 42 [(Some x) x])
error: runtime panic: match failed
user> (+ 1 2)
3 :: Int
```

Heap allocations from the panicking evaluation MAY be leaked. This is acceptable because the REPL session continues and leaked memory is bounded by the size of the single failed evaluation.

#### 12.7.4.2 Batch Mode [R4 S18]

In batch mode (`cranelisp --run file.cl`), a runtime panic terminates the process with a non-zero exit code. The implementation MUST print the panic message to stderr before exiting.

### 12.7.5 Error Message Format [R4 S18]

Runtime panic messages MUST be displayed with a consistent prefix that distinguishes them from normal output:

**REPL mode**:

```
error: runtime panic: <message>
```

**Batch mode** (to stderr):

```
error: runtime panic: <message>
```

The `<message>` is the panic source's descriptive string (e.g., `"match failed"`, `"division by zero"`, `"vec-get: index out of bounds"`).

Implementations SHOULD include source location information (file and line) when available. The format for source-located panics is:

```
error: runtime panic at <file>:<line>: <message>
```

### 12.7.6 Interaction with IO Model [R4 S18]

Runtime panics and the IO model (§10) interact as follows:

**Panics during IO trampoline execution**: When a runtime panic occurs inside an `Effect` thunk (i.e., during execution of a platform operation's closure), the panic propagates up through the trampoline and terminates the current IO evaluation. The trampoline does NOT catch panics from individual effects — a panic in any effect aborts the entire IO tree evaluation.

**Platform operation failures**: Platform operations (e.g., file I/O, network) that encounter recoverable errors (file not found, connection refused) SHOULD return an error-indicating value within the IO type rather than panicking. The recommended pattern is to return `IO (Option a)` or a platform-specific error ADT:

```clojure
;; Platform operation that may fail — returns None on failure
(defn read-file [path] ...)   ; :: (Fn [String] (IO (Option String)))

;; User code handles the failure case explicitly
(bind! [contents (read-file "data.txt")]
  (match contents
    [(Some text) (print text)]
    [None (print "file not found")]))
```

Platform operations MUST NOT panic for expected failure modes (file not found, permission denied, network timeout). Panics from platform code are reserved for **contract violations** (null pointers, corrupted state) that indicate programming errors rather than environmental conditions.

**Panics during `Par` execution** (§10.12): If any branch of a `Par` node panics during concurrent execution, the panic propagates to the parent trampoline. Other concurrently executing branches MAY or MAY NOT complete before the panic is observed. The implementation is NOT required to cancel in-flight branches.

### 12.7.7 No User-Exposed Panic Mechanism [R4 S18]

There is no `panic`, `error`, `throw`, or `raise` special form or function available to user code. User code cannot deliberately trigger a runtime panic. Runtime panics originate only from the conditions listed in §12.7.2.1.

Programs that need to signal error conditions MUST use the type system:

```clojure
;; Use Option for "might not have a value"
(defn safe-div [:Int x :Int y]
  (if (= y 0) None (Some (/ x y))))

;; Use a custom error ADT for richer error information
(deftype (Result a e) (Ok [:a val]) (Err [:e err]))

(defn parse-config [:String s]
  (match (parse-int s)
    [(Some n) (if (> n 0) (Ok n) (Err "must be positive"))]
    [None (Err "not a number")]))
```

This design keeps the runtime simple (no unwinding machinery beyond the panic boundary) and encourages programs to make error conditions visible in their types.

### 12.7.8 Implementation Requirements [R4 S18]

A conforming implementation MUST satisfy:

1. **Panic boundary**: The implementation MUST catch runtime panics at the boundary between the runtime and JIT-compiled code. Panics MUST NOT propagate as uncaught signals or cause undefined behavior. [R4 S18]
2. **REPL survival**: The REPL MUST continue operating after a runtime panic, with all prior session state intact. [R4 S18]
3. **Batch exit**: In batch mode, a runtime panic MUST cause a non-zero process exit code and a message on stderr. [R4 S18]
4. **No UB on panic**: A runtime panic MUST NOT cause undefined behavior, even if it occurs during heap allocation, closure invocation, or IO trampoline execution. Heap leaks are acceptable; use-after-free and double-free are not. [R4 S18]
5. **Deterministic panics**: Given the same inputs, the same panic condition MUST be triggered. The implementation MUST NOT silently suppress panics or convert them to arbitrary values (except for integer overflow, which is specified as wrapping). [R4 S18]

## 12.8 Platform ABI [R4 S10]

Platform functions (loaded via `(platform "name")`) use the C calling convention. All parameters and return values are i64. The platform ABI defines the contract between the Cranelisp runtime and external platform libraries.

Platform functions that perform side effects MUST return `IO _`. The implementation MUST provide a mechanism for platform functions to allocate Cranelisp values (strings, IO wrappers) through a host callback interface.

The specific details of the platform loading mechanism and host callback interface are implementation-defined.

## 12.9 Value Display Format [R4 S20]

This section defines the **canonical value display format** — the standard string representation of Cranelisp values. This format is used by the REPL for displaying expression results, by the `trace` special form for formatting traced arguments and return values, and by the `Display` trait's default implementations.

### 12.9.1 Format by Type [R4 S20]

Each type has a defined display representation:

| Type | Format | Examples |
|---|---|---|
| `Int` | Decimal integer, with leading `-` for negative | `42`, `-7`, `0` |
| `Bool` | `true` or `false` | `true`, `false` |
| `Float` | Decimal float, with leading `-` for negative. Trailing `.0` MUST be included for whole numbers to distinguish from Int. | `3.14`, `-0.5`, `1.0` |
| `String` | The string contents surrounded by double quotes, with escape sequences for special characters (`\"`, `\\`, `\n`, `\t`) | `"hello"`, `"line1\nline2"` |
| Nullary ADT constructor | `Type.Constructor` using dot notation | `Color.Red`, `Option.None` |
| Data ADT constructor | `(Type.Constructor field1 field2 ...)` — constructor in dot notation, fields formatted recursively, space-separated, wrapped in parentheses | `(Option.Some 42)`, `(Cons 1 (Cons 2 Nil))` |
| `Vec` | `[elem1, elem2, ...]` — elements formatted recursively, comma-separated | `[1, 2, 3]`, `["a", "b"]` |
| Closure / function value | `<closure>` | `<closure>` |
| `IO` | Displayed as the ADT value after trampoline execution resolves to `Pure` | `(IO.Pure 42)` |
| `Trace` | Displayed as the ADT value | `(Trace.TraceCall ...)` |

### 12.9.2 Qualified Names in Display [R4 S20]

Constructor names in display output MUST use the `Type.Constructor` dot notation without module qualification of the type name. Field values are formatted recursively using this same format.

When the display format is used in a context that includes a type prefix (e.g., REPL output), the type prefix carries the module qualification. The value portion uses bare `Type.Constructor` names:

```
:(user/Option primitives/Int) (Option.Some 42)
```

Here `user/Option` and `primitives/Int` are in the type prefix; `Option.Some` and `42` are in the value display.

### 12.9.3 Elision [R4 S20]

Implementations SHOULD truncate displayed values that exceed a reasonable size to keep output manageable and trace overhead bounded. Specifically:

- **Collections** (Vec, List): When a collection contains more than an implementation-defined threshold of elements (SHOULD default to approximately 10), the display SHOULD truncate with an ellipsis indicator: `[1, 2, 3, ... (997 more)]`.
- **Nesting depth**: When ADT values are nested beyond an implementation-defined depth threshold (SHOULD default to approximately 4 levels), inner values SHOULD be replaced with `...`.
- **String length**: When a string value exceeds an implementation-defined character threshold, the display SHOULD truncate: `"very long str..."`.

Elision is purely a display concern — it does not affect the actual value. The elision thresholds are implementation-defined; the examples above are illustrative, not normative.

Elision applies uniformly: the same rules apply to REPL output, trace parameter/result formatting, and any other use of the canonical value display format.

### 12.9.4 Relationship to REPL Output [R4 S20]

The REPL displays expression results using the format `:QualifiedType value` where `value` follows this canonical display format. See the REPL experience specification for the full REPL output format including type prefixes, definition feedback, and related symbol display.

### 12.9.5 Relationship to Trace [R4 S20]

The `trace` special form (see [Section 4.12](04-expressions.md#412-trace-expression)) captures function arguments and return values as strings using this canonical display format. The `params` and `result` fields of the `TraceCall` constructor contain formatted value strings conforming to this section.
