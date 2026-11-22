# 12. Runtime Model

This section defines the abstract runtime semantics of Cranelisp. It specifies observable behavior without prescribing a particular implementation strategy. A conforming implementation MAY use JIT compilation, ahead-of-time compilation, interpretation, or any hybrid approach.

## 12.1 Value Representation [Tested tests/spec_12_runtime::adt_sum_some_alloc_and_match]

**The runtime representation of each concrete type is a backend-internal detail; no language-level or ABI-level uniformity across types is required or guaranteed.** Because every value's concrete type is known statically at every code-generation site — a consequence of rank-1 Hindley-Milner (see [§3.10](03-types.md#310-rank-1-hindley-milner)) together with full monomorphisation-from-roots (see [§3.6.3](03-types.md#363-monomorphisation)), made total by the concreteness rule that rejects any residual free type variable in a codegen-reaching position (see [§3.11](03-types.md#311-ambiguous-types)) — the implementation MAY choose each concrete type's runtime representation independently. It MAY use a narrower-than-word encoding (e.g. a packed scalar, a `u16` for a small character type, an `f32`), an unboxed small ADT, or any other layout, provided the **observable semantics** of [§12.3](#123-memory-management) (memory management) and [§12.4](#124-evaluation-order) (evaluation) are preserved. There is no requirement that distinct types share a representation, and there is no guarantee that any particular type is machine-word-sized. Representation is not part of the language definition or any stable ABI — it is chosen per concrete type by the backend.

### 12.1.1 — 12.1.5: Current reference representation (descriptive, not prescriptive) [Tested crates/cranelisp-primitives/src/bool.rs::test_bool_to_string_nonzero_is_true]

The layout tables and diagrams in §12.1.1–§12.1.5 below document the **current reference representation** chosen by the present backend: a machine-word (64-bit) encoding for materialised values in which the interpretation of each word depends on its statically-known type. They are **descriptive of the current backend choice, not a normative uniform-word mandate.** A conforming implementation is free to deviate from any of them for any concrete type, subject only to preserving the observable semantics of §12.3 and §12.4. Where other sections of this specification reference these layouts (e.g. the i64 element/field/capture descriptions), read them as describing the current reference representation, not as imposing a uniform-word requirement.

### 12.1.1 Scalar Types [Tested crates/cranelisp-primitives/src/bool.rs::test_bool_to_string_nonzero_is_true]

| Type | Representation |
|---|---|
| `Int` | Signed 64-bit two's complement integer |
| `Bool` | `0` for `false`, `1` for `true` (in a 64-bit word) |
| `Float` | IEEE 754 double-precision (64-bit) float, stored as its bit pattern in a 64-bit integer word |

Scalar values are NOT heap-allocated. They require no memory management.

The heap diagrams include the 16-byte `HeapHeader`: `alloc_size` at offset 0 and `rc` at offset 8. Offsets are measured from the allocation base returned as the value pointer. These diagrams describe materialised objects.

### 12.1.2 String [Tested crates/cranelisp-intrinsics/src/heap_string/tests.rs::test_alloc_string_empty]

Materialised heap strings are immutable UTF-8 byte sequences:

```
ptr -> [alloc_size: i64 | rc: i64 | length: i64 | bytes: u8...]
       offset 0          offset 8  offset 16     offset 24
```

`length` counts bytes, not characters. The bytes are not null-terminated.

### 12.1.3 Function Values (Closures) [Tested tests/spec_12_runtime::closure_multiple_captures]

Materialised function values pair a code pointer with zero or more captures:

```
ptr -> [alloc_size: i64 | rc: i64 | code_ptr: i64 | drop_glue_ptr: i64 | captures...]
       offset 0          offset 8  offset 16       offset 24            offset 32
```

Captures occupy successive 64-bit slots starting at offset 32. The drop-glue pointer describes capture disposal. Non-capturing function values have the same prefix and no captures.

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
ptr -> [alloc_size: i64 | rc: i64 | tag: i64 | field_0: i64 | field_1: i64 | ...]
       offset 0          offset 8  offset 16  offset 24       offset 32
```

- `tag` (offset 16): Integer tag identifying the constructor variant
- `field_0..field_n`: Field values, each stored as an i64

For sum types mixing nullary and data constructors, tags are assigned to ALL constructors (nullary and data) in definition order.

Example: `(deftype (Option a) None (Some [:a val]))` assigns tag 0 to `None` and tag 1 to `Some`. At runtime, `None` is the bare integer `0`, and `(Some 42)` is a heap pointer to `[alloc_size, rc, 1, 42]`.

### 12.1.5 Vec [Tested tests/spec_12_runtime::vec_of_strings_alloc_drop]

Vec is a built-in resizable array type. Its layout is:

```
ptr -> [alloc_size: i64 | rc: i64 | length: i64 | capacity: i64 | data_ptr: i64]
       offset 0          offset 8  offset 16     offset 24        offset 32
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

### 12.3.1 Requirements [S124 — partial: a value the caller owns, passed to a platform function, is never released: tests/spec_10_io::s124_print_balance_literal_run, tests/spec_10_io::s124_print_balance_literal_link, tests/spec_10_io::s124_print_balance_concat_run, tests/spec_10_io::s124_print_balance_concat_link and tests/exemplar_ownership_residue_s116::sudoku_warm_serial_solve_retains_nothing fail (ACT-1018). Tested tests/spec_12_runtime::string_literal_alloc_drop_balanced, tests/shadowed_param_reach_stale_rc_dec::binder_rename_must_not_change_rc_counters, tests/same_form_rebinding::tail_transfer_releases_the_displaced_same_name_binder_run_and_link, tests/par_cont_capture_consuming_use::par_continuation_heap_capture_survives_consuming_uses]

A conforming implementation MUST satisfy the following:

1. Heap-allocated values (strings, closures, data constructors, Vecs) MUST be freed when they are no longer reachable from any live binding or data structure. [Tested tests/spec_12_runtime::string_literal_alloc_drop_balanced, tests/nullary_arm_beside_boxed_arm_0917::nullary_arm_beside_boxed_arm_frees_its_loop_under_run, tests/spec_10_io::platform_pure_let_bound_bind_operand_balances, tests/spec_10_io::platform_pure_unused_heap_binding_beside_bind_balances, tests/spec_10_io::platform_pure_string_reused_node_yields_payload_to_each_force_and_balances, tests/spec_10_io::platform_effect_unforced_discard_balances, tests/spec_10_io::functor_io_instance_calls_balance_against_inline_bind, tests/spec_10_io::unrun_bind_over_heap_payload_pure_discard_balances] [S122 — RED tests/exemplar_ownership_residue_s116.rs::sudoku_warm_serial_solve_retains_nothing, ACT-1018]
2. Freed memory MUST NOT be accessed after deallocation. [Tested tests/spec_12_runtime::string_literal_alloc_drop_balanced, tests/shadowed_param_reach_stale_rc_dec::shadowed_param_binder_safety_matrix_run_and_link_agree, tests/shadowed_param_reach_stale_rc_dec::shadowed_fresh_rhs_binder_rc_balance_matches_ownership_off, tests/shadowed_param_reach_stale_rc_dec::renamed_fresh_rhs_binder_control_safety_matrix_green, tests/string_primitive_value_discharge::str_len_as_function_value_releases_its_argument_once]
3. The user MUST NOT need to manage memory manually — allocation and deallocation are entirely the implementation's responsibility. [Tested tests/spec_12_runtime::string_literal_alloc_drop_balanced]

The exact-balance escape, superseded-value and transitive-capture evidence is
mapped in [PLAN.md, S122 W3c reconciliation](../tests/plan/PLAN.md#s122--w3c-traceability-reconciliation-0766--0771).
[Tested tests/rc_escape_release_0763::curried_local_closure_escaping_its_frame_balances,
tests/adt_wrapped_supersede_leak_0720::adt_wrapped_supersede_residue_does_not_scale_with_n,
tests/capture_drop_glue_strands_nested_heap_0760::nested_adt_chain_past_glue_depth_limit_does_not_leak]

### 12.3.2 Implementation Freedom [Tested crates/cranelisp-intrinsics/src/alloc/tests.rs::test_live_allocs_tracking]

The implementation MAY use any memory management strategy:

- **Reference counting**: Insert increment/decrement operations at binding and scope-exit points. Note: since all values in Cranelisp are immutable, reference cycles cannot form, so reference counting is sufficient for correctness.
- **Tracing garbage collection**: Periodically trace live references from roots.
- **Region-based allocation**: Group allocations by lifetime.
- **Hybrid approaches**: Any combination of the above.

### 12.3.3 Vec Copy-on-Write [Tested tests/spec_12_runtime::vec_set_cow_preserves_original]

Vec operations (`vec-set`, `vec-push`) return a new Vec value. The implementation MAY optimize by mutating the backing storage in place when the Vec has a single owner. This is semantically invisible — the caller observes pure functional behavior regardless.

## 12.4 Evaluation Order [Uncovered S124 — was Tested]

### 12.4.1 Strict Evaluation [Uncovered S124 — was Tested tests/spec_04_expressions::application_chained]

Cranelisp uses **strict (eager) evaluation**. All sub-expressions are fully evaluated before their results are used. Specifically:

- Function arguments are evaluated left-to-right before the function body executes.
- `let` bindings are evaluated left-to-right.
- Both branches of `if` exist but only the selected branch is evaluated.
- `match` arms are tested top-to-bottom; only the first matching arm's body is evaluated.

The left-to-right ordering of `let` bindings and function arguments is the **observable** evaluation order: it is the order that constrains effect sequencing, and a conforming implementation MUST *behave as if* it holds. Because cranelisp arguments and binding values are pure — effects are sequenced through `IO`/`primitives/bind` (see [§10.12](10-io.md#1012-automatic-io-scheduling)), never through raw argument or binding evaluation — the order in which *independent* pure sub-expressions are actually evaluated is unobservable. An implementation MAY therefore evaluate them concurrently or out of order under the lenient permission of [§12.4.3](#1243-lenient-evaluation) without weakening this left-to-right guarantee. Concurrent panic reporting follows §12.4.3 (user ruling, 2026-11-15). [Uncovered S124 — was S92]

### 12.4.2 Lazy Sequences [Uncovered S124 — was Tested tests/spec_12_runtime::lazy_stream_take_from_infinite_terminates_with_demanded_element, tests/spec_12_runtime::lazy_stream_construction_does_not_force_tail]

User or library ADTs can provide lazy sequences through thunks (zero-argument closures), as the illustrative `Seq` in §4.11 does. The language does not require a `Seq` type. Laziness is explicit and user-controlled — it is NOT a property of the evaluation model itself.

### 12.4.3 Lenient Evaluation [Uncovered S124 — was Tested+Neg tests/spec_12_runtime::lenient_no_lenient_env_var_preserves_correctness, tests/spec_12_runtime::apply_arg_single_expensive_preserves_result_parity, tests/spec_12_runtime::apply_arg_panic_exits_run, tests/spec_12_runtime::apply_arg_dual_panic_exits_with_one_report, tests/concurrency_spark::dependent_spark_dependency_panic_exits_run, tests/spec_12_runtime::lenient_binding_panic_not_swallowed_neg, tests/trace::trace_records_every_call_of_spark_admitted_callee, tests/trace::s124_1038_untraced_sparks_control — the panic rule's sparked cells each have a non-panicking twin that spawns (`tests/spec_12_runtime::apply_arg_non_panicking_twins_spawn`, `tests/concurrency_spark::dependent_spark_non_panicking_twin_spawns`); the two-panic cell accepts either message and rejects two reports; the strict-trace exception: a trace declines sparks and records every frame, and its untraced twin spawns]

Except within the strict dynamic extent of a trace ([§4.12.2](04-expressions.md#4122-semantics)), an implementation MUST evaluate independent `let` bindings in parallel where a cost heuristic determines it is beneficial, and MAY likewise evaluate independent arguments of a function application in parallel under the same heuristic. This is called **lenient evaluation**. Because all binding expressions in a `let` and all argument expressions in an application are pure (effects are sequenced through `IO`/`primitives/bind`, never through raw binding or argument evaluation — see [§10.12](10-io.md#1012-automatic-io-scheduling)), evaluating independent sub-expressions concurrently produces the same result as sequential left-to-right evaluation — the non-determinism in evaluation order is not observable. The permission is granted precisely *because* it is unobservable: a conforming implementation that evaluates everything sequentially left-to-right also conforms. [Uncovered S124 — was S92]

A `let` binding is independent if its free variables do not include any name bound earlier in the same `let` block. An apply-argument is independent when its evaluation cannot observe the result of evaluating any sibling argument; because arguments are pure, sibling arguments of an application are always mutually independent in this sense. In both cases the implementation MUST apply a cost heuristic to avoid parallelizing trivially cheap sub-expressions (e.g., arithmetic operations, variable references); only sub-expressions whose estimated cost exceeds the heuristic threshold, and only when at least two such candidates are present, are eligible for parallel evaluation. [Uncovered S124 — was S92]

Lenient evaluation is semantically transparent — programs MUST NOT depend on whether any particular binding or argument is parallelized. An implementation MAY provide an opt-out mechanism (e.g., an environment variable) for debugging purposes.

**Panic rule (user ruling, 2026-11-15).** A panic in any binding, argument, worker, structured IO branch or detached strand ends the process under §12.7. It is neither propagated to a join nor recovered. If concurrent computations panic, only the first panic to reach the exit path is reported; which concurrent panic reaches it first is unspecified (user ruling, 2026-11-15).

Detached execution and cancellation retain their timing and value semantics (§10.12.7–§10.12.9). Cancellation itself is not a panic; a panic that actually occurs is governed by §12.7.

### 12.4.4 Structured Control Combinators and Cancellation [Uncovered S122]

The language provides `primitives/select`, `primitives/sleep` and **structured cancellation** ([§10.12.9](10-io.md#10129-structured-cancellation)). The library derivations `race` and `timeout` illustrate their composition ([§10.12.8](10-io.md#10128-structured-control-combinators--race--select--timeout)). This subsection pins the core operations' **typing** and **runtime semantics**; §10.12.8–§10.12.10 state the user-observable contract.

**They are ordinary typed functions, not special forms and not platform effects.** Each combinator is a normal value with a normal type; it takes `IO` value(s) and returns a new `IO` value. Because an `IO a` is already a lazy *description* of an effect (§10.1–§10.3), no special evaluation rule is needed: the combinators compose opaque IO values that the runtime executes. They are **not** GOT-dispatched platform effects — the core control operations are runtime-provided, and a platform DLL never sees that composition (§12.8); this keeps the platform boundary thin even for the explicit surface. `race` is library composition over `select`, as described in §10.12.8. Their indicative types:

```
sleep   : Int -> IO Int
race    : forall a.   IO a -> IO a -> IO a
select  : forall a.   Vec (IO a) -> IO a
timeout : forall a.   Int -> IO a -> IO (Option a)
```

`race`/`select` are homogeneous: the competing branches share one result type `a`, and the combinator returns that `a` (the winner's value). A program that must distinguish *which* branch won encodes the discriminant in `a` (§10.12.8 item 3). `timeout` wraps the result in `Option` to carry the timer-fired outcome (`None`).

**Collection and duration units.** `select` takes a `Vec (IO a)` — the `[..]` literal of §10.12.8 is a `Vec`, not the `Nil`/`Cons` `List` ADT. Durations are plain `Int` **milliseconds**: `sleep : Int -> IO Int` parks for the given number of milliseconds and resumes with `0`, and `timeout`'s deadline is likewise an `Int` count of milliseconds (§10.12.8 "Duration unit"). The language has no dedicated `Duration` type. An **empty** `select` (`(select [])`) has no branch that can win; the runtime MUST raise a runtime panic (§12.7.2) — "select over empty collection" — rather than return a synthesised value, which at a heap-typed `a` would be an unsound null (§10.12.8 "Empty `select`"). The panic ends the process in every mode (§12.7; user ruling, 2026-11-15).

**Construction is pure; the composed effect runs at the trampoline.** Applying a combinator builds an IO value and runs nothing — consistent with the laziness of `IO` everywhere (§10.3). The concurrent composition executes only when the resulting `IO` is sequenced into the program's effect (via `primitives/bind`) and reaches the trampoline, which executes the composition by running the branches concurrently on the same execution substrate as automatic parallel composition (§10.12.5, §10.12.6) and resolving to the winner. The mechanism is implementation-internal and not prescribed (§10.12.5): a conforming implementation maps `race`/`select` onto its substrate's first-completion primitive and the library `timeout` derives its behavior by selecting between a tagged effect and a tagged timer (§10.12.8).

**Cancellation follows the program's effect structure — it is not a user primitive.** There is no `cancel` function and no user-installable cancellation handler. An in-flight effect is cancelled exactly when the cancellation context it executes in is cancelled ([§10.12.9](10-io.md#10129-structured-cancellation)): because its `primitives/select` branch loses or because an enclosing context is cancelled. Library `race` and `timeout` inherit these rules from their `select` composition. This includes every detached strand launched within that context ([§10.12.7](10-io.md#10127-launch-and-continue-detached-effects) item 5), independent of whether the runtime ran a given eligible effect detached, inline or on a worker. Function return and normal completion cancel nothing. The runtime realises cancellation by **dropping the in-flight effect's future**; that drop is what discharges the §10.12.9 obligations:

1. **Resource release on drop.** Dropping a cancelled effect's future MUST release every resource it held: an acquired resource-capacity **permit** (§10.12.4.1) returns to its token pool, and any registered reactor interest (an fd-readiness wait, a timer) is deregistered. This is the runtime obligation underneath §10.12.9 item 1 — a permit freed by cancellation MUST become claimable by an effect parked on that token, and a cancelled effect parked *awaiting* a permit MUST be removed from the pool's wait queue so it cannot strand a later release. Cancellation under volume (a long-running server cancelling per-request work) MUST NOT leak permits or reactor registrations.
2. **No completion side-effect; no fault.** A dropped effect does not run to its completion side-effect (§10.12.9 item 2) and does not itself raise a runtime panic (§10.12.9 item 3). Side-effects already performed before the drop point are **not** rolled back.
3. **Drop glue runs.** The cancelled computation's live heap values are released through ordinary drop glue (§12.7) as its future is dropped; reference counts are decremented exactly as on normal completion (§10.12.9 item 4).

**Interaction with the sequential-equivalence guarantee.** Cancellation is the **explicit-control** half of the concurrency model, the peer of the detached strand (§10.12.7). It is deliberately **outside** the §12.4.3 structured-join guarantee: a cancelled branch produces no value to join and no completion side-effect, so the set of effects a `race`/`timeout` performs is not the same as running every branch to completion sequentially. This is the program's explicit choice (the whole point of the combinator) and does not weaken the inferred half — the auto-IO scheduling of §10.12.1–§10.12.5 remains observationally identical to sequential execution. Panic termination is governed separately by §12.7 (user ruling, 2026-11-15).

## 12.5 Tail Call Optimization [Uncovered S124 — was Tested+Neg tests/spec_12_runtime.rs::tco_deep_countdown, tests/spec_12_runtime.rs::tco_match_tail_position, tests/spec_12_runtime.rs::tco_accumulator, tests/spec_12_runtime.rs::tco_let_body_tail_position, tests/spec_12_runtime.rs::tco_non_tail_recursion_unchanged]

Implementations MUST optimize self-recursive tail calls into loops (no stack frame is consumed per recursive call). This is a structural guarantee, not a heuristic: every self-recursive call in tail position is compiled to a jump back to the function's entry, so unbounded self-recursion in tail position runs in constant stack space and MUST NOT stack-overflow. A tail call is a function call in tail position — the last operation before the function returns.

Tail position is defined recursively:
- The body of a function is in tail position
- In `(if c t e)`: both `t` and `e` are in tail position if the `if` is
- In `(let [bindings] body)`: `body` is in tail position if the `let` is
- Library macro calls have the tail positions of their expanded core forms; `do` has no independent tail-position rule.
- In `(match scrut [p1 b1 p2 b2 ...])`: each `b_i` is in tail position if the `match` is
- Arguments to function calls are NOT in tail position
- Conditions in `if` are NOT in tail position
- Binding values in `let` are NOT in tail position

Implementation-defined: Whether mutual recursion, lambda self-recursion, or constrained polymorphic self-recursion are optimized.

**Interaction with launch-and-continue.** A tail-recursive loop that **launches** an effect and then recurses — the canonical accept loop `(primitives/bind (handle-conn conn) (fn [_] (serve listener)))`, where `handle-conn` is launched-and-not-joined ([§10.12.7](10-io.md#10127-launch-and-continue-detached-effects)) — MUST run in constant stack space under the iterative IO execution rule (§10.8.2). Detaching an effect does **not** push a frame: the loop runs in constant stack space regardless of how many handlers it launches. Consequently an unbounded accept loop launching unbounded handlers does not grow the stack; the bound on outstanding work is the in-flight admission **degree** ([§10.12.4.2](10-io.md#101242-admission-degree--program-chosen-throttle)), not the stack depth. [Uncovered S124 — was S96]

## 12.6 Entry Point [Tested+Neg tests/spec_10_io.rs::batch_main_pure_int_return_is_rejected, tests/spec_10_io.rs::main_returning_io_string_exits_zero_run_and_linked]

In batch mode, a program MUST define a function named `main` with no parameters that returns `IO _` (IO of any type). Execution begins by calling `main` and the program's exit code is the integer value inside the resulting `IO Int` (or 0 for non-integer IO results).

```clojure
(defn main []
  (print "hello"))   ; print returns IO Int
```

This rule does not apply under `--test`, which neither requires nor calls `main`; a `main` that is present compiles as an ordinary definition ([REPL §0.2.2](../repl/spec/00-cli-invocation.md#022-test-mode---test-s122)). [S122]

## 12.7 Error Model [Partial — the stack-overflow row, float division by zero and §12.7.7 are untested; see the subsections]

Cranelisp distinguishes two error categories: **compile-time errors** (detected before execution) and **runtime panics** (detected during execution). There is no exception mechanism, no user-exposed `try`/`catch`, and no `Result`-based error propagation for runtime faults. Runtime panics **end the process in every mode**, including the REPL (user ruling, 2026-11-15).

### 12.7.1 Compile-Time Errors [Tested]

The following are compile-time errors:

- Parse errors (malformed syntax) [Tested tests/repl_negative::parse_error_stray_close]
- Type errors (unification failure, arity mismatch) [Tested tests/repl_negative::type_error_arg_mismatch]
- Unbound variable references [Tested tests/repl_negative::unbound_bare_symbol_error]
- Ambiguous name resolution [Tested tests/spec_06_pattern_matching::contested_bare_pattern_indeterminate_scrutinee_poisoned_neg]
- Macro expansion errors (non-Sexp return type, expansion limit exceeded) [Tested tests/spec_09_macros::macro_body_non_sexp_int_rejected_neg, tests/spec_09_macros::neg_macro_expansion_depth_limit_exceeded]

**User ruling, 2026-11-15.** A call to a symbol left broken by a redefinition MUST be refused at compile time, before the call executes. This does not authorize creating broken symbols where the guarded-publication rules of REPL §18 prohibit them.

### 12.7.2 Runtime Panics [Tested+Neg tests/spec_12_runtime::callee_panic_with_scalar_result_stops_the_calling_loop, tests/spec_12_runtime::callee_panic_message_is_not_replaced_by_callers_later_panic_in_every_mode, tests/spec_09_macros::runtime_error_during_expansion_clean_report, tests/spec_10_io::auto_io_par_branch_panic_exits_neg, tests/test_runner.rs::panicking_test_does_not_end_run_or_repl, tests/spec_12_runtime::removed_catch_runtime_error_is_unbound_in_every_mode, tests/spec_12_runtime::callee_in_range_scalar_result_loop_terminates_control — no caller resumes past a callee's panic; a macro-expansion, `Par`-branch and `--test` child panic each end their process; `catch-runtime-error` is unbound in every mode. Callees, workers, IO and detached strands are evidenced at §12.4.3, §12.7.6, §12.7.8 and §12.7.9]

**User ruling, 2026-11-15.** A runtime panic MUST report its message and terminate the process. This applies in the REPL, `--run`, `--test` and linked executables, including panics in callees, workers, IO execution, detached strands and macro expansion. The `runtime/panic` intrinsic never returns. No caller resumes with a placeholder value; there is no panic propagation or recovery. `catch-runtime-error` is removed.

Programs avoid panics through checked operations returning `Option`; checked integer division is specified in §12.7.3.

#### 12.7.2.1 Panic Sources [S122 — partial: the stack-overflow row is untested; see the rows]

The following conditions cause a runtime panic:

| Condition | Message | Notes |
|---|---|---|
| Non-exhaustive match | `"match failed"` | All match arms tested, none matched [Tested+Neg tests/spec_12_runtime::panic_sources_report_exact_messages_run, tests/spec_12_runtime::matched_io_value_has_no_match_panic_control — reached through a `bind`-built IO value, the only incomplete match exhaustiveness checking admits] |
| Integer division by zero | `"division by zero"` | `div-i64` with zero divisor [Tested+Neg tests/spec_12_runtime::panic_sources_report_exact_messages_run, tests/spec_12_runtime::integer_div_min_by_one_does_not_panic_control] |
| Vec index out of bounds | `"vec-get: index out of bounds"` | `vec-get` or `vec-set` with index < 0 or >= length [Tested+Neg tests/spec_12_runtime::vec_get_index_past_length_panics_and_exits, tests/spec_12_runtime::vec_set_negative_index_on_unique_vec_panics, tests/spec_12_runtime::vec_set_index_equal_to_length_on_unique_vec_panics, tests/spec_12_runtime::vec_set_index_past_length_on_shared_vec_panics, tests/spec_12_runtime::vec_set_dynamic_out_of_range_index_panics_in_every_mode, tests/spec_12_runtime::vec_set_in_range_index_writes_without_panic_neg] |
| Stack overflow | Implementation-defined message | Exhaustion of the call stack (e.g., unbounded recursion without TCO) [S18] |

#### 12.7.2.2 Conditions That Are NOT Panics

| Condition | Behavior | Rationale |
|---|---|---|
| Integer overflow | Silent wraparound (two's complement) | Specified behavior, not an error. `Int` values are 64-bit two's complement; `add-i64`, `sub-i64`, `mul-i64` wrap on overflow. [Tested tests/spec_12_runtime::integer_overflow_wraps_silently] |
| Float division by zero | IEEE 754 result (`Inf`, `-Inf`, or `NaN`) | Follows IEEE 754 semantics. NOT a panic. [S18] |
| `parse-int` with invalid input | Returns `None` | Parsing failure is a normal `Option` result, not an error. [Tested tests/spec_appendix_a_builtins::primitive_parse_int_valid] |
| IO operation failure | Platform-defined `IO` result | See §12.7.6. |

### 12.7.3 Arithmetic Policy [Tested+Neg tests/spec_12_runtime::panic_sources_report_exact_messages_run, tests/spec_12_runtime::integer_div_min_by_neg_one_wraps_without_panic, tests/spec_12_runtime::integer_div_value_use_min_by_neg_one_wraps_without_panic, tests/spec_12_runtime::integer_div_min_by_one_does_not_panic_control, tests/spec_12_runtime::integer_div_value_use_min_by_one_does_not_panic_control, tests/spec_12_runtime::checked_quot_returns_option_without_panicking_run, tests/spec_12_runtime::checked_quot_repl_displays_option_int_without_panicking, tests/spec_12_runtime::integer_overflow_wraps_silently — zero division panics; `Int.MIN / -1` wraps to `Int.MIN` in direct and function-value calls in every mode; `checked-quot` gives `None` for both failure cases and truncates toward zero. Modulo is not provided; float rules are untested]

Cranelisp uses **wrapping integer arithmetic**; integer division panics on a zero divisor. Checked operations returning `Option` are the panic-avoidance surface (§12.7.2):

- **Integer addition, subtraction, multiplication**: Use two's complement wrapping. No overflow detection. This matches the `Int` type definition (signed 64-bit two's complement, §12.1.1). Programs that need overflow detection MUST implement it in user code (e.g., checking operand signs and comparing with the result).

- **Integer division** (`div-i64`; user ruling, 2026-11-15): A divisor of zero causes a runtime panic. Division of `Int.MIN` by `-1` wraps to `Int.MIN` by the same two's complement rule as integer addition, subtraction and multiplication; it does not panic. All other integer divisions truncate toward zero.

- **Checked integer quotient (user ruling, 2026-11-15).** The compiler primitive `primitives/checked-quot` has type `(Fn [Int Int] (Option Int))`. It returns `None` for a zero divisor or `Int.MIN` divided by `-1`, and `Some` of the quotient truncated toward zero otherwise. These failure cases do not panic.

- **Float arithmetic**: Follows IEEE 754 semantics throughout. Division by zero produces `Inf`, `-Inf`, or `NaN` depending on the operands. Float operations NEVER panic.

- **Modulo/remainder**: If provided, follows the same policy as integer division — zero divisor causes a runtime panic.

### 12.7.4 REPL vs Batch Error Behavior [Tested+Neg — see 12.7.4.1 and 12.7.4.2; the shared exit checker's detection proof is tests/spec_12_runtime::panic_exit_checker_rejects_wrong_reports_and_resumption]

**User ruling, 2026-11-15.** All execution modes obey §12.7.2.

#### 12.7.4.1 REPL Mode [Tested+Neg tests/spec_12_runtime::vec_get_index_past_length_panics_and_exits, tests/platform_errors::platform_dispatch_fault_exits_repl, tests/panic_streams::prior_repl_result_and_print_precede_panic_on_merged_pipe — the REPL exits non-zero after the report, evaluates no later form and prints no further prompt]

A runtime panic ends the REPL process after reporting the panic message. The REPL MUST NOT re-prompt or evaluate later input after the panic.

#### 12.7.4.2 Batch Mode [Tested+Neg tests/spec_12_runtime::uncaught_runtime_panic_surfaces_message_and_clean_exit_run, tests/spec_12_runtime::uncaught_runtime_panic_surfaces_message_and_clean_exit_link, tests/spec_12_runtime::runtime_panic_in_io_continuation_surfaces_run, tests/spec_12_runtime::clean_program_produces_no_error_in_run_mode]

In batch and linked execution, a runtime panic terminates the process with a non-zero exit code. The implementation MUST print the panic message to stderr before exiting.

### 12.7.5 Error Message Format [Tested+Neg tests/spec_12_runtime::uncaught_panic_report_is_not_a_codegen_error_run, tests/spec_12_runtime::uncaught_panic_report_is_not_a_codegen_error_link_control, tests/spec_12_runtime::vec_get_index_past_length_panics_and_exits, tests/spec_09_macros::runtime_error_during_expansion_clean_report, tests/spec_12_runtime::panic_exit_checker_rejects_wrong_reports_and_resumption — exactly one stderr line, prefixed, in the REPL, `--run`, `--link` and macro expansion, never on stdout and never a codegen error; the located form is accepted, not required]

**User ruling, 2026-11-15.** In every mode, including the REPL and macro expansion, a runtime panic MUST be reported once as plain text on stderr, with this prefix:

```
error: runtime panic: <message>
```

The `<message>` is the panic source's descriptive string (e.g., `"match failed"`, `"division by zero"`, `"vec-get: index out of bounds"`).

Implementations SHOULD include source location information (file and line) when available. The format for source-located panics is:

```
error: runtime panic: <file>:<line>: <message>
```

### 12.7.6 Interaction with IO Model [Uncovered S124 — was Tested+Neg tests/platform_errors::platform_dispatch_fault_exits_repl, tests/platform_errors::dispatch_fault_during_io_surfaces_run, tests/platform_errors::platform_dispatch_error_exits_link, tests/platform_errors::platform_dispatch_non_faulting_controls_finish, tests/spec_10_io::auto_io_par_branch_panic_exits_neg — a dispatch fault ends the process in every mode with one FQ-named, unprefixed line carrying the fault text; a `Par` branch panic ends the process. The `--test` leg is unit-pinned (src/session_v4/test_runner/child/tests.rs::a_status_fail_names_the_final_stderr_line): no eligible test can force a platform effect. The platform-failure SHOULD has no committed evidence]

Runtime panics and the IO model (§10) interact as follows:

**Panics during IO trampoline execution**: When a runtime panic occurs during execution of a platform operation, the process ends under §12.7.2 (user ruling, 2026-11-15).

**Platform dispatch faults (user ruling, 2026-11-15).** A fault during dispatch of a platform operation MUST end the process; it is not returned to a runner for recovery. The process MUST report the fault on one stderr line naming the fully qualified platform function and carrying the fault text, then exit with a non-zero status, not by signal. The report MUST NOT begin with `error: runtime panic: `. Connective wording is diagnostic, not fixed by this requirement. This records the [Phase 3 → 4 checkpoint ruling](../sprints/archive/sprint-123.md#user-rulings-at-the-phase-3--4-checkpoint-2026-11-15); the panic-report format of §12.7.5 does not apply to a dispatch fault.

**Platform operation failures**: Platform operations (e.g., file I/O, network) that encounter recoverable errors (file not found, connection refused) SHOULD return an error-indicating value within the IO type rather than panicking. The recommended pattern is to return `IO (Option a)` or a platform-specific error ADT:

```clojure
;; Platform operation that may fail — returns None on failure
(defn read-file [path] ...)   ; :: (Fn [String] (IO (Option String)))

;; User code handles the failure case explicitly
(primitives/bind (read-file "data.txt")
  (fn [contents]
    (match contents
      [(primitives/Some text) (print text)
       primitives/None (print "file not found")])))
```

Platform operations MUST NOT panic for expected failure modes (file not found, permission denied, network timeout). Panics from platform code are reserved for **contract violations** (null pointers, corrupted state) that indicate programming errors rather than environmental conditions.

**Panics during parallel IO execution** (§10.12): A panic in any branch ends the process under §12.7.2 (user ruling, 2026-11-15).

### 12.7.7 No User-Exposed Panic Mechanism [Uncovered S124 — was S18]

There is no `panic`, `error`, `throw`, or `raise` special form or function available to user code. User code cannot deliberately trigger a runtime panic. Runtime panics originate only from the conditions listed in §12.7.2.1.

Programs that need to signal error conditions MUST use the type system:

```clojure
;; Use the compiler-seeded error-value ADTs; no library is needed.
(import [primitives [Result Ok Err Option Some None String parse-int gt-i64]])

(defn parse-config [:String s]
  (match (parse-int s)
    [(Some n) (if (gt-i64 n 0) (Ok n) (Err "must be positive"))
     None (Err "not a number")]))
```

Expected failures are represented in values; a runtime panic ends the process (§12.7.2).

### 12.7.8 Implementation Requirements [Tested+Neg tests/spec_12_runtime::callee_bounds_panic_with_string_consumer_is_reported, tests/spec_12_runtime::callee_division_panic_with_string_consumer_is_reported, tests/spec_12_runtime::callee_bounds_panic_with_released_string_result_is_reported, tests/spec_12_runtime::callee_vec_set_bounds_panic_with_vec_consumer_is_reported, tests/spec_12_runtime::callee_bounds_panic_through_forwarding_frame_is_reported, tests/spec_12_runtime::uncaught_callee_panic_with_string_consumer_is_reported_link, tests/spec_12_runtime::callee_in_range_get_with_string_consumer_does_not_panic_neg — a callee's panic ends the process before a heap consumer reads a sentinel, in every mode; no signal death]

**User ruling, 2026-11-15.** A panic MUST terminate the process after reporting its message, without resuming user code, fabricating a return value, or causing undefined behavior. This applies during heap allocation, closure invocation and IO execution as well as direct calls. The process-exit rule replaces the former JIT recovery boundary and REPL-survival requirements.

### 12.7.9 Supervised Detached Strands [Tested+Neg tests/concurrency_fanout::detached_faulting_effect_exits_the_process, tests/concurrency_fanout_web::web_handler_fault_ends_server_process, tests/concurrency_fanout::launch_and_continue_runs_concurrently_launcher_does_not_await]

**User ruling, 2026-11-15.** A panic in a detached strand ends the whole process under §12.7.2. There is no supervisor recovery policy that keeps a server alive after a panic. A request handler that must keep the server running uses checked operations and handles their returned values. Cancellation remains distinct from a panic (§10.12.9).

## 12.8 Platform ABI [Tested tests/platform_errors::platform_manifest_not_found_carries_dll_path]

Platform functions (loaded via `(platform name)`) use the C calling convention. All parameters and return values are i64. The platform ABI defines the contract between the Cranelisp runtime and external platform libraries.

Platform DLLs are discovered via the platform DLL search order defined in §8.11.3. Every platform function MUST return `IO _` — unconditionally, because the compiler cannot verify the purity of foreign native code and must trust the declared signature (see §[8.9.3](08-modules.md#893-platform-modules) for the soundness rationale). The implementation MUST provide a mechanism for platform functions to allocate Cranelisp values (strings, IO wrappers) through a host callback interface. The specific details of the host callback interface are implementation-defined.

## 12.9 Value Display Format [Uncovered S124 — was Tested tests/repl_introspection::display_int_result]

This section defines the **canonical value display format** — the standard string representation of Cranelisp values. This format is used by the REPL for displaying expression results and by the `trace` special form for formatting traced arguments and return values. It is compiler-provided and independent of library `Display` traits and `show` methods; a library chooses its own string-conversion behavior.

### 12.9.1 Format by Type [Uncovered S124 — was Tested tests/repl_introspection::display_int_result, tests/spec_10_io.rs::repl_pure_int_result_prints_io_notice_then_payload]

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
| Closure / function value | `#closure` | `#closure` |
| `IO` | An IO value nested inside a displayed value shows as `#io`. A top-level REPL IO expression is executed and its payload displayed under the payload's type ([REPL §1.2.1](../repl/spec/01-display-format.md#121-io-expression-results)). | `(Box #io)` for an IO value inside `Box` |
| `Trace` | Displayed as the ADT value | `(Trace.TraceCall ...)` |

`#io` and `#closure` are display-only markers, rejected by the reader under [§1.6](01-lexical.md#16-reader-macros).

### 12.9.2 Qualified Names in Display [Tested tests/repl_introspection::display_int_result]

Constructor names in display output MUST use the `Type.Constructor` dot notation without module qualification of the type name. Field values are formatted recursively using this same format.

When the display format is used in a context that includes a type prefix (e.g., REPL output), the type prefix carries the module qualification. The value portion uses bare `Type.Constructor` names:

```
:(user/Option primitives/Int) (Option.Some 42)
```

Here the type prefix is `(user/Option primitives/Int)` and the value display is `(Option.Some 42)`.

### 12.9.3 Elision [Uncovered S124 — was Tested tests/repl_introspection::display_int_result]

Implementations SHOULD truncate displayed values that exceed a reasonable size to keep output manageable and trace overhead bounded. Specifically:

- **Vec**: When a Vec contains more than an implementation-defined threshold of elements (SHOULD default to approximately 10), the display SHOULD truncate with an ellipsis indicator: `[1, 2, 3, ... (997 more)]`.
- **Nesting depth** (including user/library ADTs such as `List`): When ADT values are nested beyond an implementation-defined depth threshold (SHOULD default to approximately 4 levels), inner values SHOULD be replaced with `...`.
- **String length**: When a string value exceeds an implementation-defined character threshold, the display SHOULD truncate: `"very long str..."`.

Elision is purely a display concern — it does not affect the actual value. The elision thresholds are implementation-defined; the examples above are illustrative, not normative.

Elision applies uniformly: the same rules apply to REPL output, trace parameter/result formatting, and any other use of the canonical value display format.

### 12.9.4 Relationship to REPL Output [Tested tests/repl_introspection::display_int_result]

The REPL displays expression results using the format `:QualifiedType value` where `value` follows this canonical display format. See the REPL experience specification for the full REPL output format including type prefixes, definition feedback, and related symbol display.

### 12.9.5 Relationship to Trace [Tested tests/spec_04_expressions::trace_returns_trace_type]

The `trace` special form (see [Section 4.12](04-expressions.md#412-trace-expression)) captures function arguments and return values as strings using this canonical display format. The `params` and `result` fields of the `TraceCall` constructor contain formatted value strings conforming to this section.
