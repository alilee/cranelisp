# 12. Runtime Model

This section defines the abstract runtime semantics of Cranelisp. It specifies observable behavior without prescribing a particular implementation strategy. A conforming implementation MAY use JIT compilation, ahead-of-time compilation, interpretation, or any hybrid approach.

## 12.1 Value Representation [Tested tests/spec_12_runtime::adt_sum_some_alloc_and_match]

**The runtime representation of each concrete type is a backend-internal detail; no language-level or ABI-level uniformity across types is required or guaranteed.** Because every value's concrete type is known statically at every code-generation site — a consequence of rank-1 Hindley-Milner (see [§3.10](03-types.md#310-rank-1-hindley-milner)) together with full monomorphisation-from-roots (see [§3.6.3](03-types.md#363-monomorphisation)), made total by the concreteness rule that rejects any residual free type variable in a codegen-reaching position (see [§3.11](03-types.md#311-ambiguous-types)) — the implementation MAY choose each concrete type's runtime representation independently. It MAY use a narrower-than-word encoding (e.g. a packed scalar, a `u16` for a small character type, an `f32`), an unboxed small ADT, or any other layout, provided the **observable semantics** of [§12.3](#123-memory-management) (memory management) and [§12.4](#124-evaluation) (evaluation) are preserved. There is no requirement that distinct types share a representation, and there is no guarantee that any particular type is machine-word-sized. Representation is not part of the language definition or any stable ABI — it is chosen per concrete type by the backend.

### 12.1.1 — 12.1.5: Current reference representation (descriptive, not prescriptive) [Tested crates/cranelisp-primitives/src/bool.rs::test_bool_to_string_nonzero_is_true]

The layout tables and diagrams in §12.1.1–§12.1.5 below document the **current reference representation** chosen by the present backend: a uniform machine-word (64-bit) encoding in which the interpretation of each word depends on its statically-known type. They are **descriptive of the current backend choice, not a normative uniform-word mandate.** A conforming implementation is free to deviate from any of them for any concrete type, subject only to preserving the observable semantics of §12.3 and §12.4. Where other sections of this specification reference these layouts (e.g. the i64 element/field/capture descriptions), read them as describing the current reference representation, not as imposing a uniform-word requirement.

### 12.1.1 Scalar Types [Tested crates/cranelisp-primitives/src/bool.rs::test_bool_to_string_nonzero_is_true]

| Type | Representation |
|---|---|
| `Int` | Signed 64-bit two's complement integer |
| `Bool` | `0` for `false`, `1` for `true` (in a 64-bit word) |
| `Float` | IEEE 754 double-precision (64-bit) float, stored as its bit pattern in a 64-bit integer word |

Scalar values are NOT heap-allocated. They require no memory management.

### 12.1.2 String [Tested crates/cranelisp-intrinsics/src/heap_string.rs::test_alloc_string_empty]

Strings are heap-allocated, immutable, UTF-8 byte sequences. The layout from the returned pointer is:

```
ptr -> [length: i64 | bytes: u8...]
       offset 0      offset 8
```

- `length` (offset 0): The number of bytes in the string (not characters)
- `bytes` (offset 8): The raw UTF-8 byte data, NOT null-terminated

### 12.1.3 Function Values (Closures) [Tested tests/spec_12_runtime::closure_multiple_captures]

All function values at runtime are closures — a code pointer paired with zero or more captured values:

```
ptr -> [code_ptr: i64 | cap_0: i64 | cap_1: i64 | ... | cap_n: i64]
       offset 0         offset 8     offset 16          offset (n+1)*8
```

- `code_ptr` (offset 0): Pointer to executable code
- `cap_0..cap_n`: Captured variable values, each stored as an i64

Non-capturing functions (including top-level named functions used as values) still use this representation with zero captures: `[code_ptr]`.

### 12.1.4 Algebraic Data Types [Tested tests/spec_12_runtime::adt_sum_some_alloc_and_match]

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

### 12.1.5 Vec [Tested tests/spec_12_runtime::vec_of_strings_alloc_drop]

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

### 12.2.1 Direct Calls [Tested tests/spec_04_expressions::application_chained]

When calling a known function by name (the common case), the implementation SHOULD use a direct call with the function's declared parameter types. All parameters and return values are i64.

### 12.2.2 Indirect Calls (Closures) [Tested tests/spec_04_expressions::lambda_closure_captures]

When calling a function value (closure), the calling convention is:

```
result = call_indirect(code_ptr, [closure_ptr, arg_0, arg_1, ...])
```

The closure pointer is passed as the first argument, allowing the callee to load captured values from it. The remaining arguments follow. The return value is a single i64.

### 12.2.3 Top-Level Functions as Values [Tested tests/spec_04_expressions::named_defn_passed_as_value_to_higher_order_fn]

When a top-level function is used as a value (passed as an argument, stored in a data structure), the implementation MUST wrap it in a closure-compatible representation. This typically involves generating a wrapper function with signature `(env_ptr, params...) -> i64` that ignores the environment pointer and calls the real function.

## 12.3 Memory Management [Tested]

### 12.3.1 Requirements [Tested tests/spec_12_runtime::string_literal_alloc_drop_balanced]

A conforming implementation MUST satisfy the following:

1. Heap-allocated values (strings, closures, data constructors, Vecs) MUST be freed when they are no longer reachable from any live binding or data structure. [Tested tests/spec_12_runtime::string_literal_alloc_drop_balanced]
2. Freed memory MUST NOT be accessed after deallocation. [Tested tests/spec_12_runtime::string_literal_alloc_drop_balanced]
3. The user MUST NOT need to manage memory manually — allocation and deallocation are entirely the implementation's responsibility. [Tested tests/spec_12_runtime::string_literal_alloc_drop_balanced]

### 12.3.2 Implementation Freedom [Tested crates/cranelisp-intrinsics/src/alloc.rs::test_live_allocs_tracking]

The implementation MAY use any memory management strategy:

- **Reference counting**: Insert increment/decrement operations at binding and scope-exit points. Note: since all values in Cranelisp are immutable, reference cycles cannot form, so reference counting is sufficient for correctness.
- **Tracing garbage collection**: Periodically trace live references from roots.
- **Region-based allocation**: Group allocations by lifetime.
- **Hybrid approaches**: Any combination of the above.

### 12.3.3 Vec Copy-on-Write [Tested tests/spec_12_runtime::vec_set_cow_preserves_original]

Vec operations (`vec-set`, `vec-push`) return a new Vec value. The implementation MAY optimize by mutating the backing storage in place when the Vec has a single owner. This is semantically invisible — the caller observes pure functional behavior regardless.

## 12.4 Evaluation Order [Tested]

### 12.4.1 Strict Evaluation [Tested tests/spec_04_expressions::application_chained]

Cranelisp uses **strict (eager) evaluation**. All sub-expressions are fully evaluated before their results are used. Specifically:

- Function arguments are evaluated left-to-right before the function body executes.
- `let` bindings are evaluated left-to-right.
- Both branches of `if` exist but only the selected branch is evaluated.
- `match` arms are tested top-to-bottom; only the first matching arm's body is evaluated.

The left-to-right ordering of `let` bindings and function arguments is the **observable** evaluation order: it is the order that constrains effect sequencing and first-error selection, and a conforming implementation MUST *behave as if* it holds. Because cranelisp arguments and binding values are pure — effects are sequenced through `IO`/`bind!` (see [§10.12](10-io.md#1012-automatic-io-scheduling)), never through raw argument or binding evaluation — the order in which *independent* pure sub-expressions are actually evaluated is unobservable. An implementation MAY therefore evaluate them concurrently or out of order under the lenient permission of [§12.4.3](#1243-lenient-evaluation) without weakening this left-to-right guarantee. [S92]

### 12.4.2 Lazy Sequences [Tested tests/spec_12_runtime::lazy_stream_take_from_infinite_terminates_with_demanded_element, tests/spec_12_runtime::lazy_stream_construction_does_not_force_tail]

The `Seq` type provides lazy evaluation through thunks (zero-argument closures). Laziness is explicit and user-controlled — it is NOT a property of the evaluation model itself.

### 12.4.3 Lenient Evaluation [Tested tests/spec_12_runtime::lenient_no_lenient_env_var_preserves_correctness]

An implementation MUST evaluate independent `let` bindings in parallel where a cost heuristic determines it is beneficial, and MAY likewise evaluate independent arguments of a function application in parallel under the same heuristic. This is called **lenient evaluation**. Because all binding expressions in a `let` and all argument expressions in an application are pure (effects are sequenced through `IO`/`bind!`, never through raw binding or argument evaluation — see [§10.12](10-io.md#1012-automatic-io-scheduling)), evaluating independent sub-expressions concurrently produces the same result as sequential left-to-right evaluation — the non-determinism in evaluation order is not observable. The permission is granted precisely *because* it is unobservable: a conforming implementation that evaluates everything sequentially left-to-right also conforms. [S92]

A `let` binding is independent if its free variables do not include any name bound earlier in the same `let` block. An apply-argument is independent when its evaluation cannot observe the result of evaluating any sibling argument; because arguments are pure, sibling arguments of an application are always mutually independent in this sense. In both cases the implementation MUST apply a cost heuristic to avoid parallelizing trivially cheap sub-expressions (e.g., arithmetic operations, variable references); only sub-expressions whose estimated cost exceeds the heuristic threshold, and only when at least two such candidates are present, are eligible for parallel evaluation. [S92]

Lenient evaluation is semantically transparent — programs MUST NOT depend on whether any particular binding or argument is parallelized. An implementation MAY provide an opt-out mechanism (e.g., an environment variable) for debugging purposes.

A runtime error (§12.7) raised while evaluating any binding or argument — whether evaluated sequentially or in parallel — MUST propagate as if the sub-expressions were evaluated sequentially left-to-right: the first such error aborts the whole enclosing expression (the `let`, or the application). An implementation that evaluates sub-expressions on separate threads MUST therefore convey a worker-thread error back to the joining thread; a parallelised binding's or argument's panic MUST NOT be silently discarded. This is what makes the observational-equivalence promise above hold for panics, and it is what lets a `catch-runtime-error` bracket (§12.7.2) enclosing a lenient `let` or a lenient application observe a panic raised in any of its parallelised sub-expressions. Because apply-argument sparking is the same structured fork-join (all sparked arguments forced at a barrier before the call) over the same machinery as the `let` case, the first-error-wins rule carries over by construction. The same propagation rule applies to the structured fork-join of automatic `IO` scheduling (§10.12).

This propagation rule, and the sequential-equivalence guarantee it preserves, govern **structured joins only** — computations the enclosing expression awaits. A **detached strand** (a launched-and-not-joined effect, [§10.12.7](10-io.md#10127-launch-and-continue-detached-effects)) is deliberately outside both: it has no join point, so its fault does not ferry anywhere and the first-error-wins rule does not reach it, and it is not part of the sequential-equivalence guarantee (its result is discarded, so the value the program computes is unchanged, but its timing overlaps the continuation and its fault is contained by the supervisor rather than aborting the program — see §10.12.7 and §12.7.9). A **cancelled effect** (a `race`/`select` loser, a `timeout`'d effect — §12.4.4) is likewise outside both: it is abandoned before completion, so it produces no value to join and no completion side-effect, and it is not part of the sequential-equivalence guarantee. The first-error-wins propagation, the detached-strand carve-out, and the cancellation carve-out are the three boundaries of the structured-join guarantee. [S77 — defect repro S76; S92 — apply-arg extension; S96 — detached-strand + cancellation carve-outs]

### 12.4.4 Structured Control Combinators and Cancellation [S96]

The explicit-control combinators — `race`, `select`, and the derived `timeout` ([§10.12.8](10-io.md#10128-structured-control-combinators--race--select--timeout)) — and the **structured cancellation** they rest on ([§10.12.9](10-io.md#10129-structured-cancellation)) are part of the language's IO model. This subsection pins their **typing** and **runtime semantics**; §10.12.8–§10.12.10 state the user-observable contract.

**They are ordinary typed functions, not special forms and not platform effects.** Each combinator is a normal value with a normal type; it takes `IO` value(s) and returns a new `IO` value. Because an `IO a` is already a lazy *description* of an effect (§10.1–§10.3), no special evaluation rule is needed: the combinators sit at the same layer as the IO constructors (`Pure`, `Bind`, the compiler-inserted `Par` of §10.12.5), constructing an internal IO node that the trampoline interprets. They are **not** GOT-dispatched platform effects — the entire control vocabulary lives in the runtime, and a platform DLL never sees it (§12.8); this keeps the platform boundary thin even for the explicit surface. Their indicative types:

```
sleep   : Int -> IO Int
race    : forall a.   IO a -> IO a -> IO a
select  : forall a.   Vec (IO a) -> IO a
timeout : forall a.   Int -> IO a -> IO (Option a)
```

`race`/`select` are homogeneous: the competing branches share one result type `a`, and the combinator returns that `a` (the winner's value). A program that must distinguish *which* branch won encodes the discriminant in `a` (§10.12.8 item 3). `timeout` wraps the result in `Option` to carry the timer-fired outcome (`None`).

**Collection and duration units.** `select` takes a `Vec (IO a)` — the `[..]` literal of §10.12.8 is a `Vec`, not the `Nil`/`Cons` `List` ADT. Durations are plain `Int` **milliseconds**: `sleep : Int -> IO Int` parks for the given number of milliseconds and resumes with `0`, and `timeout`'s deadline is likewise an `Int` count of milliseconds (§10.12.8 "Duration unit"). The language has no dedicated `Duration` type. An **empty** `select` (`(select [])`) has no branch that can win; the runtime MUST raise a runtime panic (§12.7.2) — "select over empty collection" — rather than return a synthesised value, which at a heap-typed `a` would be an unsound null (§10.12.8 "Empty `select`"). Because that raise happens at **effect-run time** (when the trampoline interprets the node), it is **fatal and non-catchable** — outside any `catch-runtime-error` construction bracket (§12.7.2 "the bracket is temporal"; §10.12.8 "Empty `select`").

**Construction is pure; the composed effect runs at the trampoline.** Applying a combinator builds an IO node and runs nothing — consistent with the laziness of `IO` everywhere (§10.3). The concurrent composition executes only when the resulting `IO` is sequenced into the program's effect (via `bind!` / `do`) and reaches the trampoline, which interprets the node by running the branches concurrently on the same execution substrate as `Par` (§10.12.5, §10.12.6) and resolving to the winner. The mechanism is implementation-internal and not prescribed (§10.12.5): a conforming implementation maps `race`/`select` onto its substrate's first-completion primitive and `timeout` onto a timer raced against the effect.

**Cancellation is the consequence of an effect ceasing to be awaited — not a user primitive.** There is no `cancel` function and no user-installable cancellation handler (consistent with §12.7's "no user-exposed panic/try-catch mechanism"). An effect is cancelled exactly when it loses a `race`/`select`, when its `timeout` timer fires first, or when its enclosing scope exits before it completes. The runtime realises cancellation by **dropping the in-flight effect's future**; that drop is what discharges the §10.12.9 obligations:

1. **Resource release on drop.** Dropping a cancelled effect's future MUST release every resource it held: an acquired resource-capacity **permit** (§10.12.4.1) returns to its token pool, and any registered reactor interest (an fd-readiness wait, a timer) is deregistered. This is the runtime obligation underneath §10.12.9 item 1 — a permit freed by cancellation MUST become claimable by an effect parked on that token, and a cancelled effect parked *awaiting* a permit MUST be removed from the pool's wait queue so it cannot strand a later release. Cancellation under volume (a long-running server cancelling per-request work) MUST NOT leak permits or reactor registrations.
2. **No completion side-effect; no fault.** A dropped effect does not run to its completion side-effect (§10.12.9 item 2) and raises no runtime panic into the cancelling context (it is not routed through the §12.4.3 fork-join ferry, nor to the supervisor of §12.7.9 — §10.12.9 item 3). Side-effects already performed before the drop point are **not** rolled back.
3. **Drop glue runs.** The cancelled computation's live heap values are released through ordinary drop glue (§12.7) as its future is dropped; reference counts are decremented exactly as on normal completion (§10.12.9 item 4). A value that was mid-construction when cancelled is in the same indeterminate-but-not-leaked state as one abandoned by a panic (§12.7.2).

**Interaction with the sequential-equivalence guarantee.** Cancellation is the **explicit-control** half of the concurrency model, the peer of the detached strand (§10.12.7). It is deliberately **outside** the §12.4.3 structured-join guarantee: a cancelled branch produces no value to join and no completion side-effect, so the set of effects a `race`/`timeout` performs is not the same as running every branch to completion sequentially. This is the program's explicit choice (the whole point of the combinator) and does not weaken the inferred half — the auto-IO scheduling of §10.12.1–§10.12.5 remains observationally identical to sequential execution. The three structured-join carve-outs are: detached strands (§10.12.7), simultaneously-panicking-branch first-error non-determinism (§12.4.3), and cancellation (this subsection).

## 12.5 Tail Call Optimization [Tested+Neg tests/spec_12_runtime.rs::tco_deep_countdown, tests/spec_12_runtime.rs::tco_match_tail_position, tests/spec_12_runtime.rs::tco_accumulator, tests/spec_12_runtime.rs::tco_let_body_tail_position, tests/spec_12_runtime.rs::tco_non_tail_recursion_unchanged]

Implementations MUST optimize self-recursive tail calls into loops (no stack frame is consumed per recursive call). This is a structural guarantee, not a heuristic: every self-recursive call in tail position is compiled to a jump back to the function's entry, so unbounded self-recursion in tail position runs in constant stack space and MUST NOT stack-overflow. A tail call is a function call in tail position — the last operation before the function returns.

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

**Interaction with launch-and-continue.** A tail-recursive loop that **launches** an effect and then recurses — the canonical accept loop `(do (handle-conn conn) (serve listener))`, where `handle-conn` is launched-and-not-joined ([§10.12.7](10-io.md#10127-launch-and-continue-detached-effects)) and the `serve` self-call is in tail position — is still a self-recursive tail call and MUST be optimized into a loop. Detaching an effect does **not** push a frame: the loop runs in constant stack space regardless of how many handlers it launches. Consequently an unbounded accept loop launching unbounded handlers does not grow the stack; the bound on outstanding work is the in-flight admission **degree** ([§10.12.4.2](10-io.md#101242-admission-degree--program-chosen-throttle)), not the stack depth. [S96]

## 12.6 Entry Point [Tested+Neg tests/spec_10_io.rs::batch_main_pure_int_return_is_rejected]

In batch mode, a program MUST define a function named `main` with no parameters that returns `IO _` (IO of any type). Execution begins by calling `main` and the program's exit code is the integer value inside the resulting `IO Int` (or 0 for non-integer IO results).

```clojure
(defn main []
  (print "hello"))   ; print returns IO Int
```

## 12.7 Error Model [Tested]

Cranelisp distinguishes two error categories: **compile-time errors** (detected before execution) and **runtime panics** (detected during execution). There is no exception mechanism, no user-exposed `try`/`catch`, and no `Result`-based error propagation for runtime faults. Runtime panics are **fatal to the current evaluation** but the execution environment (REPL session) survives.

### 12.7.1 Compile-Time Errors [Tested]

The following are compile-time errors:

- Parse errors (malformed syntax) [Tested tests/repl_negative::parse_error_stray_close]
- Type errors (unification failure, arity mismatch) [Tested tests/repl_negative::type_error_arg_mismatch]
- Unbound variable references [Tested tests/repl_negative::unbound_bare_symbol_error]
- Ambiguous name resolution [Tested crates/cranelisp-typecheck/src/checker.rs::test_import_ambiguity]
- Macro expansion errors (non-Sexp return type, expansion limit exceeded) [Tested tests/spec_09_macros::macro_body_non_sexp_int_rejected_neg, tests/spec_09_macros::neg_macro_expansion_depth_limit_exceeded]

### 12.7.2 Runtime Panics [Tested]

A **runtime panic** terminates the current evaluation. It does NOT terminate the process in REPL mode (see §12.7.4). The panicked evaluation itself cannot resume — it is unconditionally fatal to the expression being evaluated, and any heap values it had partially produced are in an indeterminate state (their drop glue did not run). User code MAY, however, **observe** a runtime panic as a value rather than letting it abort the enclosing computation, by bracketing the risky work in the `catch-runtime-error` combinator (`(Fn [(Fn [] a)] (Result a String))`, see [Appendix A.3](appendix-a-builtins.md#test-discovery-and-error-capture)): the combinator invokes a thunk and returns `(Err message)` if it panicked or `(Ok result)` otherwise. This recovers the panic *message*, not a consistent heap from the aborted thunk — an `(Err …)` result means the bracketed evaluation is void. Only language-level panics (the §12.7.2.1 sources, lowered to a `runtime/panic` call) are observable this way; hardware signals are not (see §12.7.2.1).

**The bracket is temporal, not just categorical.** `catch-runtime-error` observes a panic only if it is raised **synchronously while the thunk is being evaluated** — the thunk body plus the pure construction of any `IO` value it returns (§10.3). It does **not** reach a panic raised **later, when the trampoline runs that `IO` value**: at a `(Fn [] (IO x))` thunk the bracket ends when construction returns the `IO` node, and the node's effects execute afterward, outside it (Appendix A.3 catchability boundary). Such **effect-run-time** panics are therefore **fatal, non-catchable** runtime errors — process-terminating in batch mode, expression-aborting in the REPL (§12.7.4) — regardless of any enclosing `catch-runtime-error`. The canonical case is an **empty `select`** (`(select [])`, §10.12.8): the raise happens when the trampoline interprets the select node, never during construction, so no IO-wrapping brings it inside a bracket. This is the general rule for all run-time effect errors, not a select special case; wrapping a faulting effect in `(fn [] …)` only defers the raise past the bracket, it does not make the fault catchable. [S77 — tested-by /qa]

#### 12.7.2.1 Panic Sources [Tested]

The following conditions cause a runtime panic:

| Condition | Message | Notes |
|---|---|---|
| Non-exhaustive match | `"match failed"` | All match arms tested, none matched [Tested tests/spec_06_pattern_matching::pattern_non_exhaustive_match_on_adt_neg] |
| Integer division by zero | `"division by zero"` | `div-i64` with zero divisor [S18] |
| Vec index out of bounds | `"vec-get: index out of bounds"` | `vec-get` or `vec-set` with index < 0 or >= length [S18] |
| Stack overflow | Implementation-defined message | Exhaustion of the call stack (e.g., unbounded recursion without TCO) [S18] |

#### 12.7.2.2 Conditions That Are NOT Panics

| Condition | Behavior | Rationale |
|---|---|---|
| Integer overflow | Silent wraparound (two's complement) | Specified behavior, not an error. `Int` values are 64-bit two's complement; `add-i64`, `sub-i64`, `mul-i64` wrap on overflow. [Tested tests/spec_12_runtime::integer_overflow_wraps_silently] |
| Float division by zero | IEEE 754 result (`Inf`, `-Inf`, or `NaN`) | Follows IEEE 754 semantics. NOT a panic. [S18] |
| `parse-int` with invalid input | Returns `None` | Parsing failure is a normal `Option` result, not an error. [Tested tests/spec_appendix_a_builtins::primitive_parse_int_valid] |
| IO operation failure | Platform-defined `IO` result | See §12.7.6. |

### 12.7.3 Arithmetic Policy [Tested tests/spec_12_runtime::integer_division_by_zero_panics_neg]

Cranelisp uses **unchecked (wrapping) integer arithmetic** and **checked integer division**:

- **Integer addition, subtraction, multiplication**: Use two's complement wrapping. No overflow detection. This matches the `Int` type definition (signed 64-bit two's complement, §12.1.1). Programs that need overflow detection MUST implement it in user code (e.g., checking operand signs and comparing with the result).

- **Integer division** (`div-i64`): A divisor of zero causes a runtime panic. Division of `Int.MIN` by `-1` (which would overflow) also causes a runtime panic. All other integer divisions truncate toward zero.

- **Float arithmetic**: Follows IEEE 754 semantics throughout. Division by zero produces `Inf`, `-Inf`, or `NaN` depending on the operands. Float operations NEVER panic.

- **Modulo/remainder**: If provided, follows the same policy as integer division — zero divisor causes a runtime panic.

### 12.7.4 REPL vs Batch Error Behavior [Tested tests/spec_12_runtime::uncaught_runtime_panic_surfaces_message_and_clean_exit_run]

The execution environment determines what happens after a runtime panic:

#### 12.7.4.1 REPL Mode [S18]

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

#### 12.7.4.2 Batch Mode [Tested tests/spec_12_runtime::uncaught_runtime_panic_surfaces_message_and_clean_exit_run]

In batch mode (`cranelisp --run file.cl`), a runtime panic terminates the process with a non-zero exit code. The implementation MUST print the panic message to stderr before exiting.

### 12.7.5 Error Message Format [S18]

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

### 12.7.6 Interaction with IO Model [S18]

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

### 12.7.7 No User-Exposed Panic Mechanism [S18]

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

### 12.7.8 Implementation Requirements [S18]

A conforming implementation MUST satisfy:

1. **Panic boundary**: The implementation MUST catch runtime panics at the boundary between the runtime and JIT-compiled code. Panics MUST NOT propagate as uncaught signals or cause undefined behavior. [S18]
2. **REPL survival**: The REPL MUST continue operating after a runtime panic, with all prior session state intact. [S18]
3. **Batch exit**: In batch mode, a runtime panic MUST cause a non-zero process exit code and a message on stderr. [S18]
4. **No UB on panic**: A runtime panic MUST NOT cause undefined behavior, even if it occurs during heap allocation, closure invocation, or IO trampoline execution. Heap leaks are acceptable; use-after-free and double-free are not. [S18]
5. **Deterministic panics**: Given the same inputs, the same panic condition MUST be triggered. The implementation MUST NOT silently suppress panics or convert them to arbitrary values (except for integer overflow, which is specified as wrapping). [S18]

### 12.7.9 Supervised Detached Strands [S96]

A **detached strand** ([§10.12.7](10-io.md#10127-launch-and-continue-detached-effects)) — a launched-and-not-joined effect — has **no join point**. There is no enclosing expression waiting on it, so the structured fork-join error propagation of §12.4.3 (which re-raises a worker fault at the join) has nowhere to deliver a fault. A runtime panic (§12.7.2) raised in a detached strand is instead contained by a **supervisor**.

The supervisor is a **scheduler-/platform-declared policy**, not a pure-language construct: pure code neither installs it nor observes it directly (there is no `try` / `catch`, §12.7), so it stays out of the pure language. It is, however, an **observable runtime behavior**, which this section pins.

**Observable contract.** When a detached strand faults:

1. **The supervising context survives.** The panic MUST NOT abort the launching strand or terminate the program. In the reference server workload, the server keeps accepting and serving subsequent requests — the "server lives" semantics. [S96]
2. **The fault is handled by a declared policy, not silently discarded.** The reference workload's default policy for a request handler is **respond 500 + log + drop that request**: the faulting request receives its error response (the 500), and the failure is recorded — a supervised drop does NOT vanish, it surfaces through the dev-facing strand/log sink of the observability stream (see [§10.12.6](10-io.md#10126-execution-substrate-and-slice-delivery-informative) and [§4.12](04-expressions.md#412-trace-expression)). Only that one request is abandoned. [S96]
3. **Both extremes are non-conforming.** The supervisor MUST NOT abort the whole program on a detached fault (the structured-join behavior — wrong for fire-and-forget), and it MUST NOT swallow the failure without trace (which would make supervised drops unobservable by construction). [S96]

This contract is **observational and mechanism-neutral**: it constrains what a program and its operator observe — that the server lives, that the faulting request gets an error response, and that the drop is recorded — not how the runtime owns, polls, or schedules the detached strand.

**Honest caveat (carried from §12.4.3).** The structured fork-join's first-error-wins ordering does **not** apply across detached strands. Each supervised strand fails and is handled independently; there is no defined ordering relating faults in distinct detached strands.

## 12.8 Platform ABI [Tested tests/platform_errors::platform_manifest_not_found_carries_dll_path]

Platform functions (loaded via `(platform name)`) use the C calling convention. All parameters and return values are i64. The platform ABI defines the contract between the Cranelisp runtime and external platform libraries.

Platform DLLs are discovered via the platform DLL search order defined in §8.11.3. Every platform function MUST return `IO _` — unconditionally, because the compiler cannot verify the purity of foreign native code and must trust the declared signature (see §[8.9.3](08-modules.md#893-platform-modules) for the soundness rationale). The implementation MUST provide a mechanism for platform functions to allocate Cranelisp values (strings, IO wrappers) through a host callback interface. The specific details of the host callback interface are implementation-defined.

## 12.9 Value Display Format [Tested tests/repl_introspection::display_int_result]

This section defines the **canonical value display format** — the standard string representation of Cranelisp values. This format is used by the REPL for displaying expression results, by the `trace` special form for formatting traced arguments and return values, and by the `Display` trait's default implementations.

### 12.9.1 Format by Type [Tested tests/repl_introspection::display_int_result]

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

### 12.9.2 Qualified Names in Display [Tested tests/repl_introspection::display_int_result]

Constructor names in display output MUST use the `Type.Constructor` dot notation without module qualification of the type name. Field values are formatted recursively using this same format.

When the display format is used in a context that includes a type prefix (e.g., REPL output), the type prefix carries the module qualification. The value portion uses bare `Type.Constructor` names:

```
:(user/Option primitives/Int) (Option.Some 42)
```

Here `user/Option` and `primitives/Int` are in the type prefix; `Option.Some` and `42` are in the value display.

### 12.9.3 Elision [Tested tests/repl_introspection::display_int_result]

Implementations SHOULD truncate displayed values that exceed a reasonable size to keep output manageable and trace overhead bounded. Specifically:

- **Collections** (Vec, List): When a collection contains more than an implementation-defined threshold of elements (SHOULD default to approximately 10), the display SHOULD truncate with an ellipsis indicator: `[1, 2, 3, ... (997 more)]`.
- **Nesting depth**: When ADT values are nested beyond an implementation-defined depth threshold (SHOULD default to approximately 4 levels), inner values SHOULD be replaced with `...`.
- **String length**: When a string value exceeds an implementation-defined character threshold, the display SHOULD truncate: `"very long str..."`.

Elision is purely a display concern — it does not affect the actual value. The elision thresholds are implementation-defined; the examples above are illustrative, not normative.

Elision applies uniformly: the same rules apply to REPL output, trace parameter/result formatting, and any other use of the canonical value display format.

### 12.9.4 Relationship to REPL Output [Tested tests/repl_introspection::display_int_result]

The REPL displays expression results using the format `:QualifiedType value` where `value` follows this canonical display format. See the REPL experience specification for the full REPL output format including type prefixes, definition feedback, and related symbol display.

### 12.9.5 Relationship to Trace [Tested tests/spec_04_expressions::trace_returns_trace_type]

The `trace` special form (see [Section 4.12](04-expressions.md#412-trace-expression)) captures function arguments and return values as strings using this canonical display format. The `params` and `result` fields of the `TraceCall` constructor contain formatted value strings conforming to this section.
