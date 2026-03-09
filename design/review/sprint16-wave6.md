# Sprint 16 Wave 6 Review — PlatformEffect Codegen & CLIO Base Pointer Fix

**Reviewer**: `/review`
**Date**: 2026-03-09
**Scope**: CLIO base pointer convention, PlatformEffect codegen, JIT name resolution, IO test helper, platform governance specs

## Findings

### B1 — BLOCKER: HostCallbacks.alloc returns base pointer, CLIO assumes payload pointer

**Files**: `crates/cranelisp-platform/src/lib.rs` (lines 114, 246-254, 270-283, 396-411), `src/platform.rs` (line 165)

The `HostCallbacks` struct documents its `alloc` field as:
```rust
/// Allocate `size` bytes, returns payload pointer (base + 16).
pub alloc: extern "C" fn(i64) -> i64,
```

The host passes `cranelisp_runtime::heap_alloc` as this callback (`src/platform.rs` line 165). But `heap_alloc` returns a **base pointer** (offset 0, where `alloc_size` lives), not a payload pointer. See `crates/cranelisp-runtime/src/alloc.rs` lines 170-175:
```rust
/// Returns base pointer.
pub extern "C" fn heap_alloc(payload_size: i64) -> i64 {
    alloc_with_rc(payload_size as usize) as i64
}
```

All `CLIO` and `CLString` code treats the allocator's return value as a payload pointer:
- `CLIO::pure()`: writes `IO_TAG_PURE` at `payload+0` (overwrites `alloc_size` header), writes value at `payload+8` (overwrites `rc` header), returns `payload - 16` (points before the allocation).
- `CLIO::effect_on_resource()`: same pattern with 3 fields — overwrites header, returns garbage pointer.
- `CLString::from(&str)`: writes length at `payload+0`, copies bytes at `payload+8` — same corruption.
- `CLString::as_str()`: reads from `self.0 + 16` where `self.0` is `payload - 16` = `base - 16` — reads from before the allocation.

This is a memory corruption bug that will crash or produce undefined behavior as soon as any platform DLL function is actually invoked. The tests pass currently because all platform tests that exercise the DLL path are `#[ignore]`.

**Resolution**: Either:
(a) Change `heap_alloc` to return `base + 16` (payload pointer) when used as the host callback — but this breaks the base-pointer convention used everywhere else. NOT recommended.
(b) **Recommended**: Add a separate `heap_alloc_payload` wrapper that returns `base + HeapHeader::SIZE` and use it as the `HostCallbacks.alloc` value. This preserves the internal base-pointer convention while giving DLLs the payload pointer they expect. Update the `HostCallbacks` doc comment to match.

**Owned by**: `/platform` (CLIO/CLString), `/int` (host callback wiring)

### B2 — BLOCKER: CLHeap::dec_rc reads alloc_size from wrong pointer when base pointer is wrong

**File**: `crates/cranelisp-platform/src/lib.rs` lines 445-461

`CLHeap::dec_rc()` reads `total_size` from `*(base as *const i64)` and frees with that size. Because of B1, `base` = `payload - 16` which points before the actual allocation. The `total_size` read will be garbage, and `dealloc` will corrupt the heap. This is a downstream consequence of B1 but worth calling out separately because it means **any CLOwned<CLString> drop will corrupt the heap** once B1 is fixed — unless the pointer convention is correct end-to-end.

**Owned by**: `/platform`

### I1 — IMPORTANT: PlatformEffect codegen uses consuming convention but platform functions borrow-then-own

**File**: `crates/cranelisp-backend/src/compiler/apply.rs` lines 144-153

The fallthrough for unrecognized builtins (platform effect functions) uses `compile_consuming_arg_list` which inc's variable args for consuming convention. This is correct IF the platform function's DLL code calls `CLString.own()` (which also inc's, per `CLOwned::new` at line 483). The combined effect would be +2 inc for a variable arg, with only -1 from the callee's scope cleanup. The platform function's `CLOwned` drop does -1, so the net is +2 -1 -1 = 0. This is correct.

However, if a platform function does NOT call `.own()` on a heap parameter (e.g., it reads the string inline without capturing), the consuming convention expects the callee to dec the parameter. Platform DLL functions are `extern "C"` and have no automatic drop glue — they do not dec parameters unless `.own()` (or manual dec) is used. This would leak the inc from `compile_consuming_arg_list`.

**Observation**: The stdio spec says "Must use `CLString.own()` (capture-RC protocol) when capturing heap parameters into deferred closures" — but the codegen unconditionally uses consuming convention. A platform function that borrows without `.own()` will leak. The ABI contract should clarify: **all heap-typed platform function parameters must be consumed** (via `.own()` or explicit dec), regardless of whether the function captures them.

**Owned by**: `/platform` (ABI contract clarification), `/backend` (codegen convention documentation)

### I2 — IMPORTANT: No `// SAFETY:` comment on CLIO pointer arithmetic

**File**: `crates/cranelisp-platform/src/lib.rs`, unsafe blocks in `CLIO::pure()` (lines 249-252), `CLIO::effect_on_resource()` (lines 277-280), `CLString::as_str()` (lines 372-379), `CLString::from(&str)` (lines 402-408)

Per the review checklist, every `unsafe` block must have a `// SAFETY:` comment. These blocks have descriptive comments above the methods but not the standard safety annotations at each unsafe block. The pointer arithmetic is the highest-risk code in the platform crate and deserves explicit safety justifications.

**Owned by**: `/platform`

### I3 — IMPORTANT: `HEAP_HEADER_SIZE` is duplicated between cranelisp-platform and cranelisp-types

`cranelisp-platform` defines `pub const HEAP_HEADER_SIZE: i64 = 16` (line 62). `cranelisp-types` defines `HeapHeader::SIZE: usize = 16`. The runtime uses `HeapHeader::SIZE`. Having two independent constants for the same layout fact is a maintenance hazard — if the header layout changes, both must be updated.

**Resolution**: `cranelisp-platform` should derive its constant from `HeapHeader::SIZE` (e.g., `pub const HEAP_HEADER_SIZE: i64 = HeapHeader::SIZE as i64`) or re-export from cranelisp-types. Check if a dependency from cranelisp-platform to cranelisp-types is already established.

**Owned by**: `/platform`, `/arch` (crate dependency decision)

### I4 — IMPORTANT: `repl_eval_display` IO formatting is fragile string manipulation

**File**: `tests/helpers/mod.rs` lines 183-210

The IO display path in `repl_eval_display` does ad-hoc string surgery: it finds the first space in the inner display string, extracts the type prefix by stripping the leading `:`, and reassembles with `:(IO ...)`. This breaks if:
- The inner display has no space (line 203 fallback just returns `inner_display` without IO wrapper)
- The inner type contains spaces (e.g., `:(Option Int)` -> would split incorrectly)
- The value itself starts with `:`

This is a test helper so the blast radius is limited, but it will cause silent test failures as more complex IO types are exercised.

**Owned by**: `/qa` (test helper), `/int` (REPL display infrastructure)

### S1 — SUGGESTION: `is_known_builtin` and `is_extern_primitive` / `is_vec_primitive` should share a common enum

**Files**: `crates/cranelisp-backend/src/operators.rs` lines 81-108, `crates/cranelisp-backend/src/compiler/apply.rs` lines 671-701

The dispatch chain in `compile_resolved_call` for `BuiltinFn` has 5 branches: bind, vec primitive, extern primitive, unknown builtin (platform effect), known inline builtin. The classification relies on 3 separate string-matching functions (`is_vec_primitive`, `is_extern_primitive`, `is_known_builtin`). Adding a new primitive requires updating the correct function. A `PrimitiveClass` enum with a single `classify(name) -> PrimitiveClass` function would make the dispatch exhaustive and prevent accidental fallthrough to the wrong branch.

**Owned by**: `/backend`

### S2 — SUGGESTION: Platform governance specs are well-structured

**Files**: `platforms/stdio/spec.md`, `platforms/test-capture/spec.md`

Good design: consumer requirements from skills, conformance rules, capture-RC protocol, thread safety notes. The test-capture spec correctly mirrors stdio's interface. The test lifecycle documentation is clear.

One gap: neither spec defines what happens if `print` is called with a null/invalid string pointer. Platform functions receive raw `i64` values — defensive checks (null pointer, negative length) would prevent hard crashes in the DLL when the compiler has a bug.

**Owned by**: `/platform`

### S3 — SUGGESTION: IO test coverage is thorough for Pure/Bind but platform Effect path is untested

**File**: `tests/io.rs`

The test file has 42 tests covering Pure, bind, type inference, match, REPL display, and negative cases. All platform Effect tests (lines 414-503) are `#[ignore]` with "needs platform-aware test helper" notes. Given B1, this is expected — the platform path genuinely doesn't work yet. The test plan correctly acknowledges this as Sprint 17 work.

The non-ignored tests form a solid regression gate for the core IO infrastructure. No action needed until B1 is resolved.

### S4 — SUGGESTION: `resolve_primitive_jit_name` handles PlatformEffect jit_name correctly

**File**: `crates/cranelisp-typecheck/src/infer.rs` lines 295-336

The function correctly checks for `DefKind::Primitive { jit_name: Some(jit), .. }` and returns the JIT-level symbol name (e.g., `cranelisp_print` for the `print` function). This is clean and handles both qualified and unqualified names. The test coverage (7 unit tests at lines 2069-2139) is adequate.

## Design Doc Assessment

- `design/backend/io-trampoline.md` exists and covers the IO tree structure and trampoline algorithm. Not assessed in detail this review.
- `design/platform/platform-dlls.md` exists. Should be updated to document the base-pointer vs payload-pointer convention once B1 is resolved.
- No design doc exists specifically for the CLIO base pointer convention — the convention is only documented in code comments. Once B1 is resolved, the chosen approach should be documented in the platform design doc.

## Summary

| ID | Severity | Summary | Owner |
|----|----------|---------|-------|
| B1 | Blocker | `heap_alloc` returns base ptr, CLIO/CLString assume payload ptr — memory corruption | `/platform`, `/int` |
| B2 | Blocker | `CLHeap::dec_rc` reads garbage alloc_size due to B1 — heap corruption on drop | `/platform` |
| I1 | Important | Platform consuming convention requires all heap params consumed; ABI contract underspecified | `/platform`, `/backend` |
| I2 | Important | Missing `// SAFETY:` comments on unsafe blocks in CLIO/CLString | `/platform` |
| I3 | Important | `HEAP_HEADER_SIZE` duplicated between cranelisp-platform and cranelisp-types | `/platform`, `/arch` |
| I4 | Important | `repl_eval_display` IO formatting uses fragile string surgery | `/qa`, `/int` |
| S1 | Suggestion | Dispatch chain for builtins should use enum instead of 3 string-matching fns | `/backend` |
| S2 | Suggestion | Platform specs well-structured; add defensive null checks | `/platform` |
| S3 | Suggestion | Platform Effect tests correctly deferred; solid Pure/Bind coverage | — |
| S4 | Suggestion | `resolve_primitive_jit_name` handles PlatformEffect correctly | — |

## Next Skills

- `/platform` — **Urgent**: Fix B1/B2 base pointer convention mismatch before any platform DLL integration testing
- `/int` — Update `HostCallbacks` wiring once `/platform` decides on the fix approach
- `/backend` — Consider S1 cleanup when next touching the dispatch chain
