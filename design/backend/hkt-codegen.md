# HKT Codegen & Checked Division — Sprint 24 Backend Design

## 1. HKT Codegen Assessment

### 1.1 TyConApp Resolution Status

`Type::TyConApp(TypeId, Vec<Type>)` exists in `crates/cranelisp-types/src/types.rs` and is handled by all type utility functions (`contains_var`, `apply`, `collect_free_vars`, `max_type_var_id`, display formatting). The architecture review confirmed: **TyConApp is fully resolved by typecheck/monomorphisation before codegen sees it**.

The resolution path:
1. Typecheck introduces `TyConApp` during HKT trait method inference (e.g., `fmap` on `(Functor f)` produces `TyConApp(f, [a])`)
2. Unification binds the constructor variable: `TyConApp(f, [a])` unifies with `ADT("Option", [Int])` → `f = Option`
3. Monomorphisation applies the substitution, replacing `TyConApp` with concrete `ADT` before codegen

**Verification**: The backend's codegen functions (`is_heap_type`, `collect_var_ids_from_type`, `substitute_type_inline`, match compilation, vec codegen) match on `Type::ADT`, `Type::Fn`, `Type::Var`, and primitives. They do **not** match on `TyConApp`. This is correct — if a `TyConApp` leaked through to codegen, it would fall into the wildcard `_ => ...` arms and be treated as a non-heap scalar, which is wrong but would manifest as a crash rather than silent corruption.

### 1.2 Backend Changes Required: None

HKT monomorphised method calls compile identically to existing monomorphised trait methods. For example, `(fmap inc (Some 3))` monomorphises to `fmap$Option$Int$Int` which is a regular function call on concrete types. The backend already handles this pattern.

### 1.3 Defensive Measure (Recommended)

Add a debug assertion in `HeapCategory::classify` and `is_heap_type` to panic if `TyConApp` reaches codegen, rather than silently falling through to `Mixed`:

```rust
// In HeapCategory::classify — current code already does this:
Type::Var(_) | Type::TyConApp(_, _) => HeapCategory::Mixed,
```

The current `Mixed` classification is conservative-safe (triggers RC operations on values that may not need them) but masks a pipeline bug if `TyConApp` appears post-monomorphisation. A `debug_assert!` or ICE (internal compiler error) in a codegen entry point would catch this earlier. This is optional — the current behavior is safe, just harder to debug.

## 2. Checked Integer Division

### 2.1 Spec Requirements (§12.7.3)

| Condition | Required Behavior |
|---|---|
| `div-i64` with zero divisor | Runtime panic: `"division by zero"` |
| `div-i64` with `Int.MIN / -1` | Runtime panic: `"division by zero"` (overflow) |
| All other integer divisions | Truncate toward zero (`sdiv` semantics) |
| Float division by zero | IEEE 754 result (Inf, -Inf, NaN) — NOT a panic |
| Modulo/remainder with zero | Runtime panic (same as division) |

### 2.2 Current State

`div-i64` in `crates/cranelisp-backend/src/operators.rs` already has a partial checked division implementation via `emit_checked_div()`:

- **Division by zero**: Implemented. Branches on `rhs == 0`, calls `runtime_panic("division by zero")` via the existing panic function, returns dummy `0`.
- **MIN / -1 overflow**: **NOT implemented**. The current code proceeds directly to `sdiv` after the zero check. On Cranelift, `sdiv` with MIN/-1 causes a hardware trap (SIGFPE on x86/arm64 via Cranelift's `trapnz` semantics), which is uncontrolled — it does not go through the panic boundary.

The sketch (`sketch/src/codegen/primitives.rs`) implements both checks in `emit_checked_div()`:
1. Check `r == 0` → panic "integer division by zero"
2. Check `l == i64::MIN && r == -1` → panic "integer overflow in /"

### 2.3 Design: Guard Insertion

Extend `emit_checked_div()` to add the MIN/-1 guard between the zero-check and the `sdiv`:

```
entry:
    is_zero = icmp eq rhs, 0
    brif is_zero → panic_divzero, check_overflow

check_overflow:
    is_min = icmp eq lhs, i64::MIN     ;; 0x8000000000000000
    is_neg1 = icmp eq rhs, -1
    both = band is_min, is_neg1
    brif both → panic_overflow, ok

panic_divzero:
    call runtime_panic("division by zero")
    return 0

panic_overflow:
    call runtime_panic("division by zero")     ;; spec says "division by zero" for this too
    return 0

ok:
    result = sdiv lhs, rhs
    return result
```

**Panic message**: The spec (§12.7.2.1) says the message for division by zero is `"division by zero"`. The MIN/-1 case is not explicitly named in the panic sources table, but §12.7.3 groups it with division. The sketch uses a separate message ("integer overflow in /"). We follow the spec literally: use `"division by zero"` for both conditions. If `/spec` or `/qa` wants a distinct message for MIN/-1, that's a spec change.

**Block structure**: Three basic blocks (panic_divzero, check_overflow, ok) plus the entry block. The panic blocks are unreachable in the normal path. Both panic blocks call `runtime_panic` and return a dummy value — the panic boundary in the REPL catches the error flag before the dummy value propagates.

### 2.4 Trait Method Mapping

The Num trait `/` method for Int maps to `div-i64` via `primitive_for_trait_method()` in `operators.rs`. Since `div-i64` already routes through `emit_checked_div()`, the checked guards apply to both raw `(div-i64 x y)` and `(/ x y)` calls. No additional wiring needed.

### 2.5 Modulo/Remainder

Spec §12.7.3 says modulo follows the same policy. The current codebase does not have a `mod-i64` or `rem-i64` primitive. If/when one is added, it must use the same guard pattern (zero-divisor check before `srem`). No work needed now — this is a note for the future.

### 2.6 Float Division

No changes. Float division already uses `fdiv` which produces IEEE 754 results (Inf, NaN) without panicking. This is correct per spec.

## 3. link_multi_module_project Investigation

### 3.1 Failure Description

The test in `tests/sprint23.rs` creates a two-module project:
- `helper.cl`: `(defn add-one [:Int x] (add-i64 x 1))`
- `main.cl`: `(import [helper [add-one]]) (defn main [] (add-one 41))`

It runs `--link main.cl` and expects the linked executable to exit with code 42.

### 3.2 Error

```
Undefined symbols for architecture arm64:
  "_helper/add-one", referenced from:
      _main in main.o
```

The linker cannot find `_helper/add-one` — the symbol is referenced in `main.o` but not defined in `helper.o`.

### 3.3 Root Cause Analysis

This is a **cross-module symbol export** issue in the ObjectModule path. The function `add-one` is defined in `helper.cl` and compiled into `helper.o`, but the linker symbol name or visibility is wrong. Possible causes:

1. **Symbol naming mismatch**: The function might be exported as `add-one` (without module prefix) in `helper.o` but referenced as `helper/add-one` in `main.o`. Or vice versa — the naming convention may differ between declaration-site and use-site.

2. **Linkage visibility**: The function might be compiled with `Linkage::Local` in the ObjectModule instead of `Linkage::Export`. In JIT mode (Interactive), all functions are accessible via the GOT. In ObjectModule mode (linking), they need explicit export linkage.

3. **Module-qualified name construction**: The ObjectModule path may not apply the same `module_path/fn_name` convention that the reference site expects.

### 3.4 Investigation Path for Implementation

1. Search for how function names are constructed during ObjectModule compilation — look for `declare_function` calls with module-qualified names
2. Compare the symbol table of `helper.o` (using `nm helper.o`) against what `main.o` expects
3. Check whether Interactive vs Batch CompileMode affects symbol naming in the ObjectModule path
4. The fix likely involves ensuring the ObjectModule uses consistent `module/name` symbol naming with `Linkage::Export` for public functions

This is a genuine bug, not a test issue. It should be fixed as part of Sprint 24 debt clearance.

## 4. FIXME Resolution: CompileMode Enum Consistency

### 4.1 The FIXME

`design/backend/module-caching.md:422` contains:

> `CompileMode::Interactive` (GOT-indirect) in both modes so that `.o` files are interchangeable. `CompileMode::Release` (direct calls) is reserved for LLVM whole-program compilation where no caching occurs.
>
> <!-- FIXME(/backend): /arch review I1 — this row previously said `CompileMode::Batch` which contradicts the rename in §8. Fixed inline but verify consistency with the final CompileMode enum. -->

### 4.2 Current CompileMode Enum

From `crates/cranelisp-types/src/pipeline.rs`:

```rust
pub enum CompileMode {
    Interactive,  // GOT-indirect calls for hot-reload
    Batch,        // Direct function calls, no GOT indirection
    Release,      // Whole-program optimisation, standalone binary
}
```

### 4.3 Assessment

The enum has three variants: `Interactive`, `Batch`, `Release`. The design doc text at line 422 says both REPL and batch use `Interactive` (GOT-indirect) for cache interchangeability, with `Release` reserved for LLVM.

The actual code in `src/pipeline.rs` uses:
- `CompileMode::Interactive` for REPL module compilation (line 420, 581)
- `CompileMode::Batch` for batch entry point compilation (line 673)

This means the design doc's claim that "both use `CompileMode::Interactive`" is **not currently true** — batch uses `CompileMode::Batch`. The FIXME is asking whether this is intentional or whether batch should also use `Interactive` for cache interoperability.

### 4.4 Resolution

The design doc's §8 path-unification strategy says `.o` files should be interchangeable between REPL and batch. If `Batch` mode produces different object code (direct calls instead of GOT-indirect), cached `.o` files from batch aren't reusable in REPL mode, violating the interchangeability goal.

**Recommended fix**: Update the design doc text to accurately reflect the current state. The three-variant enum is correct as-is. Batch and Interactive produce different calling patterns by design — batch doesn't need hot-reload. Cache interchangeability was an aspiration documented in §8 but the current implementation does not achieve it, and that's acceptable at this stage. The FIXME should be resolved by:

1. Updating the table row at line 422 to say: "Module compilation uses `CompileMode::Interactive` in REPL and `CompileMode::Batch` in batch. Object files are not currently interchangeable between modes. `CompileMode::Release` is reserved for LLVM whole-program compilation."
2. Removing the FIXME comment.

If cache interchangeability becomes a goal, that's a separate design decision for `/arch` to make.

## 5. Sketch Comparison

### 5.1 Checked Division

The sketch's `emit_checked_div()` in `sketch/src/codegen/primitives.rs` implements both guards:
1. `r == 0` → panic "integer division by zero"
2. `l == i64::MIN && r == -1` → panic "integer overflow in /"

The reimplementation's approach follows the same structure with minor differences:

| Aspect | Sketch | Reimplementation |
|---|---|---|
| Zero check | `icmp eq r, 0` → brif to panic block | Same |
| MIN/-1 check | `icmp eq l, MIN`, `icmp eq r, -1`, `band` | Same pattern (to be added) |
| Panic mechanism | `emit_panic_with_message()` + `trap(user(1))` | `runtime_panic(msg_ptr, msg_len)` + return dummy |
| Panic message (MIN/-1) | "integer overflow in /" | "division by zero" (per spec §12.7.2.1) |
| Block structure | `emit_checked_branch()` helper | Inline block creation |

**Divergence**: The sketch uses `trap` after the panic message, which halts execution. The reimplementation uses `runtime_panic` which sets a thread-local error flag and returns, allowing the REPL to recover (per the panic boundary design in `design/backend/sprint19-panic-boundary.md`). This is intentional — the reimplementation has a more sophisticated panic boundary.

**Divergence**: The sketch uses "integer overflow in /" for the MIN/-1 case. The reimplementation uses "division by zero" for both cases, following the spec's panic sources table which only lists "division by zero" for integer division failures. This is a spec-following decision.

### 5.2 HKT Codegen

The sketch does not separate codegen and typecheck into crates — both live in `sketch/src/`. The sketch's monomorphisation resolves `TyConApp` before codegen just as the reimplementation's architecture requires. The sketch's codegen never matches on `TyConApp`. The reimplementation follows the same approach: no HKT-specific codegen changes.

### 5.3 Checked Arithmetic (Num Trait)

The sketch has checked variants for all four Num.Int operations (`Num.+$Int`, `Num.-$Int`, `Num.*$Int`, `Num./$Int`) alongside unchecked raw primitives (`add-i64`, etc.). The reimplementation currently maps `Num./` → `div-i64` → checked division, but `Num.+`, `Num.-`, `Num.*` map to unchecked wrapping operations. This matches spec §12.7.3 which specifies wrapping for +/-/* and checked for / only. The sketch's checked +/-/* is stricter than the spec requires. The reimplementation correctly follows the spec here.
