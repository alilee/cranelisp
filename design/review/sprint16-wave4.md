# Sprint 16 Wave 4 — Code Review

Reviewer: `/review`
Date: 2026-03-09
Scope: All code changes since commit `747e6e8` (Sprint 15 close).

## Summary

| Severity | Count |
|----------|-------|
| **B (Blocker)** | 2 |
| **I (Important)** | 6 |
| **S (Suggestion)** | 7 |

**Overall assessment**: The Wave 4 IO additions are architecturally sound. The design docs are thorough and the implementation follows them closely. The trampoline is correctly iterative, `bind` codegen correctly incs both arguments, and the platform DLL loading is well-structured with proper error handling. Two blockers need attention before sprint close: the `in_call_position` flag is not thread-safe for future concurrent use and has a re-entrancy gap, and the `determine_exit_code` function does not match the design doc's specification for IO-wrapped results. Six Important findings relate to code quality and design adherence.

---

## B (Blocker) — Must fix before sprint close

### B1: `determine_exit_code` does not match design doc for IO results

**File**: `src/pipeline.rs` lines 944-950
**Owning skill**: `/int`

The design doc (`design/int/io-integration.md` section I6) specifies that `determine_exit_code` should inspect the IO type wrapper:

```rust
fn determine_exit_code(inner_value: i64, result_type: &Type) -> i32 {
    match result_type {
        Type::ADT(name, args) if name.as_ref() == "IO" => {
            match args.first() {
                Some(Type::Int) => inner_value as i32,
                _ => 0,
            }
        }
        _ => 0,
    }
}
```

But the actual implementation receives the *already unwrapped* inner type (because `compile_module_graph` extracts it at line 1098), and checks for `Type::Int` directly:

```rust
pub fn determine_exit_code(value: i64, ty: &Type) -> i32 {
    match ty {
        Type::Int => value as i32,
        _ => 0,
    }
}
```

The call site in `main.rs` passes `result.ty` which is the inner type after IO unwrapping. This **works correctly** at runtime, but the function signature and doc comment reference spec 10.6.1 about IO-wrapped results, while it actually receives the unwrapped inner type. This creates a contract mismatch: if someone calls `determine_exit_code` with an IO-wrapped type (as the design doc shows), it would incorrectly return 0.

**Recommended fix**: Either (a) make the function accept the IO-wrapped type as the design doc specifies, or (b) rename to `exit_code_from_inner_value` and update the doc comment to clarify it expects the already-unwrapped inner type. Option (b) is simpler and matches the actual call sites.

### B2: `in_call_position` flag is not scoped and has re-entrancy gaps

**File**: `crates/cranelisp-typecheck/src/infer.rs` lines 224-227, `crates/cranelisp-typecheck/src/checker.rs` line 54
**Owning skill**: `/typecheck`

The `in_call_position` field on `TypeChecker` is set before inferring the callee and restored after:

```rust
let prev_call_position = self.in_call_position;
self.in_call_position = true;
let callee_ty = self.infer_expr(callee);
self.in_call_position = prev_call_position;
```

This is fragile: if `infer_expr(callee)` recurses through nested applications (e.g., `((f x) y)` where the callee is itself an application), the flag will be restored to `false` by the inner `infer_apply` before the outer one finishes. Consider the expression `(add ((fn [x] x) add) 1)` where the inner `(fn [x] x)` gets `add` in non-call position.

More concretely, the constrained-fn check at line 110 fires if `!self.in_call_position`, but `in_call_position` is a single boolean shared across all nesting levels. The save/restore pattern should work for simple cases, but it is not a stack-based scope mechanism and may produce incorrect errors or miss errors in edge cases with deeply nested applications.

**Recommended fix**: Use a scope-based approach: push/pop an integer depth counter, or pass `in_call_position` as a parameter to `infer_expr` rather than storing it as mutable state.

---

## I (Important) — Should fix in this sprint

### I1: Duplicate `is_io_type`/`extract_io_inner_type` in pipeline.rs and repl.rs

**File**: `src/pipeline.rs` lines 922-932, `src/repl.rs` lines 887-902
**Owning skill**: `/int`

Both files define identical `is_io_type()` and `extract_io_inner_type()` helper functions. The design doc (`design/int/io-integration.md` section "Implementation Order") explicitly calls out: "I6 and I7 share the IO detection pattern... Extract as a helper."

**Recommended fix**: Extract both functions into a shared location. Options: (a) add to `cranelisp-types` as methods on `Type`, (b) add to `src/pipeline.rs` and `pub` export them for `src/repl.rs` to use, or (c) add a small `src/io_helpers.rs` module. Option (a) is cleanest.

### I2: `expect()` in non-test pipeline code (builtins.rs)

**File**: `crates/cranelisp-typecheck/src/builtins.rs` lines 328, 637, 674
**Owning skill**: `/typecheck`

Three `.expect()` calls in non-test code violate `src/CLAUDE.md` conventions:

- Line 328: `expect("primitives module should exist")` — pre-existing
- Line 637: `expect("invariant: IO type should be registered before adding Bind")`
- Line 674: `expect("primitives module should exist")`

Per conventions: "No `expect()` in pipeline code. If it's a programmer invariant, use `unreachable!`."

Line 328 is pre-existing (not introduced by this sprint), but lines 637 and 674 are new. The `.unwrap_or_else(|e| { unreachable!("invariant: ...") })` pattern is used correctly at lines 468, 509, 578 — these new sites should follow the same pattern.

**Recommended fix**: Replace `.expect(msg)` with `unwrap_or_else` + `unreachable!` on lines 637 and 674, matching the pattern established at lines 468-470.

### I3: `CLIO` derives `Clone, Copy` but contains allocation side effects

**File**: `crates/cranelisp-platform/src/lib.rs` line 233
**Owning skill**: `/platform`

`CLIO<CL>` is `#[derive(Clone, Copy, Debug)]`. Since `CLIO` wraps an i64 (a heap pointer), copying it produces a second reference to the same heap-allocated IO node without incrementing the RC. This is intentional at the C-ABI boundary (the value crosses from Rust to JIT code as a raw i64), but `Clone`/`Copy` on a type that represents a heap-allocated resource is misleading and could lead to use-after-free if someone copies a `CLIO` value and both copies are used.

The type is currently used correctly (platform functions return it once, it crosses into JIT code), but the derives create a foot-gun for future platform authors.

**Recommended fix**: Remove `Clone, Copy` from `CLIO`. Platform functions return `CLIO` by value (moved), and the `From<CLIO<CL>> for i64` conversion consumes it. If copy semantics are needed at the C-ABI boundary, use explicit `.into()` calls.

### I4: `unsafe impl Send for LoadedPlatform` justification is weak

**File**: `src/platform.rs` lines 33-35
**Owning skill**: `/int`

The safety comment says "We don't send them across threads in practice, but the JIT builder API requires the pointers to be usable." This is not a sufficient justification for `unsafe impl Send`. The `Send` implementation should explain *why* it is safe, not *why* it is needed. The actual safety argument is that the library handle and function pointers are valid for the process lifetime (loaded DLLs are not unloaded), so the pointers remain valid regardless of which thread accesses them.

**Recommended fix**: Update the safety comment to: "SAFETY: LoadedPlatform holds a Library handle whose code segment is mapped for the process lifetime (DLLs are never unloaded). Function pointers into the code segment are valid from any thread."

### I5: `call_continuation` transmutes through `usize` instead of directly

**File**: `crates/cranelisp-runtime/src/io.rs` line 96
**Owning skill**: `/platform` (or `/backend`)

```rust
let call: extern "C" fn(i64, i64) -> i64 =
    unsafe { std::mem::transmute(code_ptr as usize) };
```

The intermediate cast `code_ptr as usize` is unnecessary and obscures the actual safety-critical operation. On 64-bit platforms `i64` and `usize` have the same width, but this is not portable. The design doc section 5.1 shows the cast as `transmute(code_ptr as *const ())`, which is clearer about the intent (i64 -> function pointer).

**Recommended fix**: Change to `std::mem::transmute(code_ptr as *const ())` to match the design doc and make the pointer semantics explicit.

### I6: Missing enforcement of internal constructor restriction

**File**: `crates/cranelisp-typecheck/src/adt.rs`, `crates/cranelisp-typecheck/src/infer.rs`
**Owning skill**: `/typecheck`

The design doc (`design/typecheck/io-types.md` section 1 "Enforcement points") specifies two enforcement points for internal constructors:

1. **AST builder / typechecker**: When `(Bind x f)` is encountered, reject with "cannot construct internal type constructor `Bind`".
2. **Pattern matching**: When a match arm uses `(Bind ...)`, reject with "cannot match on internal type constructor `Bind`".

Neither enforcement is implemented. The `internal: bool` field is added to `ConstructorInfo` and set to `true` for Bind, but no code checks this field to reject construction or pattern matching. In practice, Bind is not registered in the symbol table (so `(Bind x f)` would fail name resolution), but if someone explicitly imports it via qualified name or if the internal flag is used for other constructors in the future, the lack of enforcement is a gap.

**Recommended fix**: Add checks in the constructor application path and the pattern matching path that reject `ConstructorInfo` with `internal: true`. This can be deferred if Bind is truly unreachable by name resolution, but should be documented as a known gap.

---

## S (Suggestion) — Optional improvement

### S1: `builtin_docstring` function is 60 lines of match arms

**File**: `crates/cranelisp-typecheck/src/builtins.rs` lines 703-763
**Owning skill**: `/typecheck`

The function is within the 100-line limit but could be data-driven (a static map or array) for easier maintenance. The docstrings could also be co-located with the primitive definitions in `cranelisp-types` rather than duplicated in the typechecker.

### S2: `format_value_only` partially duplicates `format_result_value`

**File**: `src/repl.rs` lines 950-985
**Owning skill**: `/int`

`format_value_only` recreates logic that exists in `format_result_value`, with the difference that it omits the `:Type ` prefix. For ADTs, it works around this by calling `format_adt_value` and stripping the prefix with string manipulation (finding the first space). This is fragile — if the type string contains spaces internally, the strip could be incorrect.

**Recommended fix**: Refactor `format_result_value` to accept an option for prefix inclusion, or extract the value-formatting logic into a shared helper that both functions call.

### S3: `scan_for_platform_decls` re-reads and re-parses the source file

**File**: `src/pipeline.rs` lines 1127-1146
**Owning skill**: `/int`

The pipeline reads and parses the entry module source during `discover_module_graph`, then `scan_for_platform_decls` reads and parses the same file again. This is a minor inefficiency (the file is small and read twice in quick succession). The design doc acknowledges this: "These are extracted at the pipeline level... to keep platform loading in the integration layer."

**Recommended fix**: Consider caching the parsed sexps from `discover_module_graph` and passing them to the platform scan. Low priority since the cost is negligible.

### S4: No `// SAFETY:` comments on several `unsafe` blocks in io.rs

**File**: `crates/cranelisp-runtime/src/io.rs` lines 50, 54, 64, 65, 74, 75, 94, 96
**Owning skill**: `/platform`

Per the review checklist, every `unsafe` block should have a `// SAFETY:` comment. The trampoline function `run_io_trampoline` has multiple `unsafe` blocks that read IO node fields by raw pointer, but none carry `// SAFETY:` comments. The function-level doc comment explains the invariant (io_ptr must be valid, tree must be live), but individual blocks should note what they are reading and why the pointer arithmetic is correct.

### S5: Test-only test helper in `repl.rs` for `force_io_and_format` manually allocates

**File**: `src/repl.rs` lines 3365-3434 (test code)
**Owning skill**: `/int`

The tests for `force_io_and_format` manually allocate Pure nodes with raw pointer writes. This is fine for unit tests but couples the test to heap layout details. If the heap header size changes, these tests silently break. Consider using the test helpers from `cranelisp-runtime/src/io.rs` (e.g., `make_pure_node`) if they can be made `pub(crate)` or `pub` for testing.

### S6: `Ordering::SeqCst` everywhere in CLHeap — consider relaxing

**File**: `crates/cranelisp-platform/src/lib.rs` lines 422, 438
**Owning skill**: `/platform`

The design doc notes that `SeqCst` matches the backend's Cranelift `atomic_rmw` semantics. However, `Acquire` for inc and `Release` for dec (with `Acquire` fence before dealloc) would be sufficient and potentially faster on ARM. The design doc explicitly rejects `Relaxed` as unsound, which is correct. This is a future optimization opportunity, not a correctness issue.

### S7: `>>` function in `stdlib/core/io.cl` captures `b` by value, not by thunk

**File**: `stdlib/core/io.cl` line 27
**Owning skill**: `/stdlib`

```clojure
(defn >> [a b] (bind a (fn [_] b)))
```

The `b` argument is evaluated before `>>` is called (strict evaluation). If `b` is an IO action, its *description* (the IO tree node) is constructed eagerly but not forced — this is correct for the deferred IO model. However, the naming `>>` (sequence operator) may confuse users who expect lazy evaluation of the second argument. This is inherent to the language's strict evaluation model and is not a bug, but a doc comment noting this would be helpful.

---

## Design Doc Assessment

### Coverage

All four design docs exist and are thorough:
- `design/backend/io-trampoline.md` — Excellent. Covers layout, codegen, drop glue, thunk mechanics, liveness invariant. Includes rejected alternatives.
- `design/typecheck/io-types.md` — Excellent. Covers IO seeding, Bind existential handling, `bind` typing, main validation. Sketch references included.
- `design/platform/platform-dlls.md` — Excellent. Covers C-ABI contract, wrapper types, capture-RC protocol, `declare_platform!` macro, search path, rejected alternatives.
- `design/int/io-integration.md` — Good. Covers D1b, I3, I6, I7. Status table at the bottom tracks completion.

### Currency

Design docs are current with the code. One divergence noted (B1: `determine_exit_code` signature). The platform-dlls.md accurately describes the `declare_platform!` macro implementation.

### Missing docs

No missing design docs for this wave. All major subsystems changed have corresponding design documentation.

---

## Unsafe Code Audit

### `cranelisp-runtime/src/io.rs`

The trampoline uses `unsafe` for raw pointer reads of IO node fields. The safety invariant is documented at the function level but not at individual `unsafe` blocks (S4). The `transmute` in `call_continuation` goes through an unnecessary `usize` intermediate (I5). No `unsafe` in test code except for helper node construction (appropriate — testing the unsafe boundary).

### `cranelisp-platform/src/lib.rs`

Extensive `unsafe` for C-ABI contract handling. Well-encapsulated — all `unsafe` is in this one crate. `unsafe impl Send/Sync for PlatformFn` has an adequate comment. `CLHeap::inc_rc`/`dec_rc` use `AtomicI64` correctly with `SeqCst` ordering. The `call_effect_thunk` function correctly documents its safety requirements.

### `src/platform.rs`

`unsafe` confined to `libloading` calls (DLL loading). All `unsafe` calls use `?` for error propagation. `unsafe impl Send for LoadedPlatform` needs a better justification (I4).

### Containment

The unsafe surface is well-contained: `cranelisp-platform` (ABI contract), `cranelisp-runtime/io.rs` (trampoline), and `src/platform.rs` (DLL loading). No unsafe leakage into other modules.

---

## Test Coverage Assessment

### New unit tests

- `cranelisp-runtime/src/io.rs`: 8 tests covering Pure, Effect, Bind, nested bind, deep chain (1000 levels), identity continuation, unknown tag panic. Good coverage.
- `cranelisp-typecheck/src/builtins.rs`: 12+ tests covering IO type registration, Bind internal, bind primitive typing, docstrings for all rings. Thorough.
- `src/platform.rs`: 14 tests covering platform form detection, path resolution (all 4 tiers), type sig parsing, DLL loading, TC registration. Good coverage.
- `src/pipeline.rs`: 5 tests covering `is_io_type`, `extract_io_inner_type`, `determine_exit_code`. Adequate.
- `src/repl.rs`: 6 tests covering IO detection, IO forcing with Pure nodes, panic recovery. Good.
- `tests/macros.rs`: 6 new negative tests (D3 scope). Good.
- `tests/ring1.rs`: 3 new negative tests for pattern matching restrictions (D5). Good.
- `tests/ring2.rs`: 12 new negative tests for module boundaries, type system invariants (D5). Good.

### Gaps

1. **No integration test for end-to-end IO**: There is no test that loads the stdio platform, compiles a program with `(print "hello")`, runs the trampoline, and verifies stdout output. The platform DLL tests verify loading/registration but not execution. (The `core/io.cl` file is noted as untested in `stdlib/CLAUDE.md`.)
2. **No test for `bind` codegen**: The trampoline tests construct Bind nodes manually. There is no test that compiles `(bind (Pure 42) (fn [x] (Pure (add-i64 x 1))))` through the full pipeline and verifies the result is 43.
3. **No test for internal constructor rejection**: Since enforcement is not implemented (I6), there are no tests verifying that `(Bind x f)` fails. This pairs with I6.

---

## Findings by File

| Finding | File | Line(s) | Severity |
|---------|------|---------|----------|
| B1 | `src/pipeline.rs` | 944-950 | Blocker |
| B2 | `crates/cranelisp-typecheck/src/infer.rs` | 224-227 | Blocker |
| I1 | `src/pipeline.rs`, `src/repl.rs` | 922-932, 887-902 | Important |
| I2 | `crates/cranelisp-typecheck/src/builtins.rs` | 637, 674 | Important |
| I3 | `crates/cranelisp-platform/src/lib.rs` | 233 | Important |
| I4 | `src/platform.rs` | 33-35 | Important |
| I5 | `crates/cranelisp-runtime/src/io.rs` | 96 | Important |
| I6 | `crates/cranelisp-typecheck/src/adt.rs` | (missing) | Important |
| S1 | `crates/cranelisp-typecheck/src/builtins.rs` | 703-763 | Suggestion |
| S2 | `src/repl.rs` | 950-985 | Suggestion |
| S3 | `src/pipeline.rs` | 1127-1146 | Suggestion |
| S4 | `crates/cranelisp-runtime/src/io.rs` | 50-96 | Suggestion |
| S5 | `src/repl.rs` | 3365-3434 | Suggestion |
| S6 | `crates/cranelisp-platform/src/lib.rs` | 422, 438 | Suggestion |
| S7 | `stdlib/core/io.cl` | 27 | Suggestion |
