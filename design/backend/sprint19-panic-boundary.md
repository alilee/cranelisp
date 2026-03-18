# Sprint 19 T3: Catchable Runtime Panics

Spec reference: `spec/12-runtime.md` §12.7.2 (runtime panics), §12.7.8 (panic boundary).

## Problem

Two codegen paths emit hardware traps that bypass `std::panic::catch_unwind` at the REPL eval boundary:

1. **Match exhaustiveness** (`emit_match_panic`): emits `trap(MATCH_EXHAUSTION_TRAP)` which raises SIGILL.
2. **Integer division by zero** (`div-i64` via `emit_builtin_op`): emits bare `sdiv` which raises SIGFPE on x86-64 (and traps on aarch64).

Both signals are uncatchable by `catch_unwind`, so they crash the REPL process instead of producing a recoverable error.

## Existing Pattern: `emit_vec_bounds_panic`

`vec_codegen.rs` already implements the correct pattern:

1. Obtain `self.ctx.panic_func_id` (the `FuncId` for `runtime_panic`).
2. Declare an anonymous data section containing the error message bytes.
3. Emit `global_value` + `iconst` to get `(msg_ptr, msg_len)`.
4. Call `runtime_panic(msg_ptr, msg_len)` via `declare_func_in_func`.
5. Follow the call with a `trap` terminator (Cranelift requires a block terminator; the call never returns because `runtime_panic` is `extern "C-unwind"` and panics).

`runtime_panic` in `crates/cranelisp-runtime/src/panic.rs` calls `panic!()`, which is caught by `catch_unwind` at the eval boundary.

## T3a: Match Exhaustiveness

**File**: `crates/cranelisp-backend/src/compiler/match_codegen.rs`, fn `emit_match_panic`.

**Change**: Replace the bare `trap` with the `emit_vec_bounds_panic` pattern:

- Access `self.ctx.panic_func_id` (already available on `FnCompiler` via `self.ctx`).
- Declare anonymous data: `b"match failed"` (matches spec §12.7.2.1 table).
- Call `runtime_panic(msg_ptr, msg_len)`.
- Keep the trailing `trap` as an unreachable terminator (same as `emit_vec_bounds_panic` does).

The method already has `&mut self` so it has access to `self.module` and `self.ctx.panic_func_id`. No signature change needed.

**Edge case**: `panic_func_id` is `None` before runtime symbols are declared. This only happens if the JIT hasn't called `declare_runtime_symbols()`. Return a `CodegenError` in that case (same pattern as `compile_vec_get`).

## T3b: Integer Division by Zero

**File**: `crates/cranelisp-backend/src/operators.rs`, the `"div-i64"` arm of `emit_builtin_op`.

**Change**: Add a zero-check before `sdiv`:

1. Compare the divisor (right operand) against zero with `icmp(Equal, rhs, zero)`.
2. Branch: if zero, jump to a panic block; otherwise jump to the ok block.
3. Panic block: call `runtime_panic` with `b"division by zero"` (matches spec table).
4. Ok block: emit `sdiv` and continue.

**Signature impact**: `emit_builtin_op` is currently a free function taking `(&mut FunctionBuilder, &str, &[Value], Span)`. It does not have access to `module` or `panic_func_id`, which are needed to declare the data section and call `runtime_panic`.

Options:
- **(A) Expand the signature** to pass `module` and `panic_func_id` — affects all call sites (2 in `apply.rs`).
- **(B) Handle div-i64 at the call site** in `apply.rs` before dispatching to `emit_builtin_op` — special-cases one operator.
- **(C) Extract a helper** `emit_checked_div` on `FnCompiler` that does the check + call, and route `div-i64` through it instead of through `emit_builtin_op`.

**Recommended**: Option (A). The signature change is minimal (add `&mut JITModule` and `Option<FuncId>`), the two call sites are adjacent in `apply.rs`, and it keeps all operator codegen in one place. Future checked operations (e.g., `mod-i64` if added) would follow the same path.

**Edge case — modulo**: No `mod-i64` or `rem-i64` primitive exists today. If one is added later (spec §12.7.3 mentions "if provided"), it would use `srem` which has the same zero-divisor trap. The same zero-check pattern applies. Document this in the operator table for future reference.

**Edge case — `sdiv` overflow**: `sdiv(i64::MIN, -1)` also traps on x86-64. The spec §12.7.3 says integer overflow wraps silently, but this is technically a division trap, not an overflow. For Sprint 19, treat this as out-of-scope (the spec doesn't mention it and it's extremely rare). File a FIXME if desired.

## Summary

| Task | File | Pattern | Message |
|------|------|---------|---------|
| T3a | `match_codegen.rs` | Call `runtime_panic` + trailing trap | `"match failed"` |
| T3b | `operators.rs` | Zero-check branch + panic block | `"division by zero"` |

Both changes ensure that runtime errors go through `runtime_panic` -> `panic!()` -> `catch_unwind`, keeping the REPL alive per §12.7.8.
