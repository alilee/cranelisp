# Sprint 20 Wave 1 Review — Trace Codegen, Stdlib, REPL Integration

**Reviewer**: `/review`
**Date**: 2026-03-19
**Scope**: Wave 1 new code (T1 trace codegen, T2 stdlib trace, T3 REPL integration) + R1 S16-19 high-level assessment

## Files Reviewed

| File | Lines | Status |
|---|---|---|
| `crates/cranelisp-runtime/src/trace.rs` | 517 | NEW |
| `crates/cranelisp-backend/src/compiler/trace_codegen.rs` | 383 | NEW |
| `stdlib/core/trace.cl` | 63 | NEW |
| `src/repl.rs` (trace sections) | ~120 new lines | MODIFIED |
| `crates/cranelisp-runtime/src/lib.rs` | trace re-exports | MODIFIED |
| `crates/cranelisp-backend/src/jit.rs` | trace symbol registration | MODIFIED |
| `crates/cranelisp-backend/src/compiler/mod.rs` | TracedFnInfo, Expr::Trace dispatch | MODIFIED |

---

## Wave 1 Findings

### F-1 (I) — GOT_TABLE_SIZE duplicated between runtime and backend

`crates/cranelisp-runtime/src/trace.rs:25` defines `const GOT_TABLE_SIZE: usize = 1024` with a comment "Must match `GOT_TABLE_SIZE` in `cranelisp-backend/src/codegen_types.rs`". The authoritative definition is in `cranelisp-backend/src/codegen_types.rs`. The runtime crate cannot depend on the backend (correct dependency direction), but this creates a divergence risk.

**Recommendation**: Move `GOT_TABLE_SIZE` to `cranelisp-types` (which both crates depend on). This eliminates the manual synchronization requirement. Alternatively, pass `GOT_BYTES` as a parameter to `cranelisp_trace_swap_got` so the runtime doesn't need to know the size at all — it already receives `n_slots` for the per-function iteration.

**Severity**: Important — if the backend changes GOT_TABLE_SIZE and the runtime is not updated, the GOT memcpy will silently corrupt memory.

### F-2 (I) — Mutex::lock().unwrap() in non-test runtime code

`trace.rs` calls `TRACE_STACK.lock().unwrap()` at 7 call sites (lines 202, 212, 221, 312, 334, 389, 492). Per `src/CLAUDE.md`, `unwrap()` is permitted only in tests and `main()`. A poisoned mutex (from a prior panic during trace) would crash the REPL.

**Recommendation**: Replace with `.lock().unwrap_or_else(|e| e.into_inner())` to recover from a poisoned mutex (the trace data may be stale but the REPL remains alive), or use a non-poisoning lock pattern. This is runtime infrastructure called from JIT code, so a panic here is unrecoverable.

**Severity**: Important — a panic inside `cranelisp_trace_enter/exit` during JIT execution cannot be caught by `catch_unwind` (JIT frames lack unwind tables). The REPL would crash.

### F-3 (S) — `got_layout()` uses `.expect()` in non-test code

`trace.rs:84` uses `Layout::from_size_align(GOT_BYTES, 8).expect("GOT layout")`. While this is a static invariant (8192 bytes, 8-byte alignment will always succeed), `src/CLAUDE.md` says to use `unreachable!("invariant: ...")` for true programmer errors rather than `expect()`.

**Recommendation**: Either inline the constant layout since the values are known at compile time, or change to `.unwrap_or_else(|_| unreachable!("invariant: GOT layout always valid"))`.

**Severity**: Suggestion.

### F-4 (S) — Leaked allocations in trace_codegen are intentional but undocumented as a design choice

`trace_codegen.rs` leaks 5 categories of allocations per trace expression compilation:
- `slots_ptr` (line 69): `Box<[u32]>` GOT slot array
- `wrappers_buf_ptr` (line 73): `Box<[i64]>` wrapper buffer
- `name_ptr` (line 269): `Box<[u8]>` function name bytes
- `param_type_ptrs` (lines 276): `Box<Type>` per parameter
- `result_type_ptr` (line 278): `Box<Type>` for result

The comment on lines 266-268 says "valid for the program lifetime" but there is no design doc explaining the leak-until-exit strategy or quantifying the memory cost (roughly 48-96 bytes per traced function per trace expression).

**Recommendation**: Add a brief note in a trace design doc or as a doc comment on `compile_trace` explaining: (a) why leaking is acceptable (REPL session lifetime, bounded by number of distinct trace expressions), (b) the approximate per-trace cost, (c) that this is a deliberate choice rather than a bug.

**Severity**: Suggestion — the leaks are correct for a REPL (process lifetime), but reviewers and maintainers should know it's intentional.

### F-5 (S) — `compile_trace_wrapper_fn` is 148 lines

`trace_codegen.rs` lines 235-382. The function builds a Cranelift IR function from scratch, which inherently requires many steps. At 148 lines it exceeds the ~100-line guideline. The logic is linear and clear, but could be split.

**Recommendation**: Consider extracting the "emit format calls for params" section (lines 300-308) and the "emit trace_enter call" section (lines 312-337) into helper methods. Not urgent since the function reads well top-to-bottom.

**Severity**: Suggestion.

### F-6 (B) — `unsafe impl Send + Sync for TraceDisplayState` is unnecessary and misleading

`src/repl.rs:49-50`. `TraceDisplayState` contains raw pointers (`*const HashMap<...>`), which makes it `!Send + !Sync` by default. The `unsafe impl` is provided with the comment "only accessed from the JIT execution thread". However, `TraceDisplayState` is stored as a stack-local variable in `execute_expr` and its pointer is placed in a `thread_local! { Cell<*const TraceDisplayState> }`. Since the `Cell` is already thread-local, the struct itself never needs to cross thread boundaries. The `Send + Sync` impls serve no purpose — the struct is never sent to another thread or shared.

The real question is whether `Cell<*const TraceDisplayState>` requires `TraceDisplayState: Send`. It does not — the `Cell` stores a raw pointer (`*const`), which is `Copy`, and `Cell<*const T>` is `Send` regardless of `T`. So these impls are dead code that falsely implies the struct is safe to share.

**Recommendation**: Remove both `unsafe impl` lines. If the compiler later requires them (it shouldn't), add them back with a precise safety argument.

**Severity**: Blocker — unnecessary `unsafe impl Send/Sync` on a type with raw pointers weakens the type system's safety guarantees. Even though it's harmless today, it sets a precedent and could mask future bugs if the struct's usage changes.

### F-7 (S) — `TracedFnInfo.name` is a bare `String`, not `Symbol`

`compiler/mod.rs:56`: `pub name: String`. Per `src/CLAUDE.md`, identifiers should use typed newtypes. However, this is a qualified name (`"user/fact"`) rather than a bare `Symbol`, and no existing newtype covers qualified display names. The `String` is used only for trace display, never for lookup.

**Recommendation**: Acceptable as-is since it's a display-only field. If a `QualifiedName` newtype is introduced later, migrate then.

**Severity**: Suggestion.

### F-8 (I) — `compile_trace` body-discard logic is duplicated

`trace_codegen.rs` duplicates the body-result discard pattern (check `expr_types`, check `is_heap_type`, emit `rc_dec`) between `compile_trace` (lines 115-126) and `compile_trace_no_swap` (lines 163-174). This is an exact copy-paste.

**Recommendation**: Extract a `discard_body_result(&mut self, body_result: Value, body: &Expr)` helper method. This also future-proofs against divergence if the discard logic changes.

**Severity**: Important — per checklist item 6, no copy-pasted blocks.

### F-9 (S) — `stdlib/core/trace.cl` tree display is a stub

`trace-show-tree` (lines 50-62) cannot recursively display children because `children` is typed as `Int` (runtime SList encoding) and there are no runtime SList traversal builtins. The `FIXME(/platform)` at line 45 correctly delegates this. The function works but the user experience is degraded — `trace-show-tree` and `trace-show` produce nearly identical output.

**Recommendation**: No action needed for Wave 1. The FIXME is correctly filed. When `/platform` exposes SList traversal externs, the tree display should be the first consumer.

**Severity**: Suggestion (known limitation, correctly tracked).

### F-10 (S) — `trace-call-string` stringifies `params` as a single value, not as a list

`trace.cl:25`: `(str-concat n (str-concat " " (str-concat p ")")))` treats `p` (the params SList) as a single displayable value. Since `p` is typed as `Int` (the SList encoding), this will display a raw integer pointer rather than the formatted parameter strings. The params SList contains pre-formatted String heap pointers, but the stdlib function has no way to iterate and join them.

**Recommendation**: This is the same underlying issue as F-9 — SList traversal is needed. The formatted output will be wrong for multi-parameter functions until then. Consider documenting this limitation in the function docstring.

**Severity**: Suggestion (blocked on same FIXME as F-9).

### F-11 (I) — No SAFETY comment on several `unsafe` blocks in `trace.rs`

The `unsafe` blocks in `cranelisp_trace_swap_got` (lines 238-239, 244-245, 248, 250, 252-255, 259-262), `cranelisp_trace_enter` (lines 299-301, 305-307), and `cranelisp_trace_exit` (lines 335-343) lack `// SAFETY:` comments. Per the review checklist item 5: "Every `unsafe` block must have a `// SAFETY:` comment explaining why the invariants hold."

The `write_i64` and `read_i64` helper functions have safety docs on the function signature, which partially addresses this, but the callers using `std::slice::from_raw_parts` and raw pointer arithmetic in `cranelisp_trace_swap_got` need their own safety arguments.

**Recommendation**: Add `// SAFETY:` comments to each `unsafe` block, particularly the `slice::from_raw_parts` calls in `cranelisp_trace_swap_got` (which trust parameters from JIT code) and the string construction in `cranelisp_trace_enter`.

**Severity**: Important — per review checklist, every `unsafe` block needs a safety comment.

---

## Checklist Walkthrough (Wave 1)

| # | Criterion | Verdict | Notes |
|---|---|---|---|
| 1. Error Handling | PARTIAL | F-2 (unwrap in runtime), F-3 (expect). No spans needed (runtime fns). |
| 2. Code Structure | PARTIAL | F-5 (148-line function). Otherwise good decomposition. |
| 3. Naming | PASS with F-7 | String newtypes used elsewhere. TracedFnInfo.name is display-only. |
| 4. Scope Management | N/A | No scope operations in new code. |
| 5. Single Source of Truth | FAIL — F-1 | GOT_TABLE_SIZE duplicated between runtime and backend. |
| 6. Duplication | FAIL — F-8 | Body-discard logic duplicated in trace_codegen. |
| 7. Architectural Boundaries | PASS | Runtime does not depend on backend. Backend does not depend on binary. Integration layer bridges correctly. |
| 7a. Idiomatic Rust | PARTIAL — F-6 | Unnecessary `unsafe impl Send/Sync`. |
| 8. Serialization | N/A | No cross-boundary types added. |
| 9. Testing | PASS | trace.rs has 6 unit tests. trace_codegen is tested via integration tests. |
| 10. Performance | PASS | No O(n) scans. GOT group lookup is O(n) but bounded by function count. |
| Unsafe audit | PARTIAL — F-11 | Missing SAFETY comments on several blocks. F-6 unnecessary impl. |
| Design doc | N/A | Trace design is documented in sketch/docs/trace.md. New code follows that design. |

---

## R1 — S16-19 High-Level Assessment

### Runtime Panic Mechanism (S16+)

**File**: `crates/cranelisp-runtime/src/panic.rs`

The thread-local error flag pattern is well-designed. `runtime_panic` stores a message in a `thread_local! { RefCell<Option<String>> }` and the host calls `take_runtime_error()` after every JIT invocation. This correctly works around the limitation that `catch_unwind` cannot unwind through JIT frames.

**Concern (S)**: The pattern requires discipline — every JIT call site must check `take_runtime_error()`. If a new call site is added without the check, runtime panics become silent. Consider a wrapper type for JIT results that forces the check (e.g., a `JitResult` that consults the thread-local in its constructor). Low priority since the call sites are concentrated in `repl.rs`.

### IO Trampoline (S16)

**File**: `crates/cranelisp-runtime/src/io.rs`

The iterative trampoline with explicit continuation stack is correct and well-tested (7 unit tests including a 1000-deep bind chain). The continuation calling convention (`env_ptr, val -> io_ptr`) matches the closure layout.

**Concern (I)**: Line 80 uses `panic!("cranelisp_run_io: unknown IO tag {tag}")`. This is in `run_io_trampoline` which is called from `cranelisp_run_io` (extern "C"). If the panic unwinds through JIT frames, it causes UB. The REPL wraps the call in `catch_unwind` (repl.rs line 1162), but batch mode calls it directly. The same thread-local error pattern from `panic.rs` should be used here instead of `panic!`.

**Concern (S)**: No RC operations during trampoline execution. The design doc (§6) says the IO tree must remain live. This is correct but fragile — if a future optimization tries to free intermediate nodes, it would break. The invariant should be documented as an assertion in the code, not just the design doc.

### Slash Command Quality (S17-19)

The REPL has 17+ slash commands with well-structured dispatch (`ReplCommand` enum, individual `handle_*` functions). The universal output format (`:Type value ; classification`) is consistently applied.

**No structural concerns.** The handler functions are appropriately sized (mostly 20-60 lines). The `eval_and_display` function at repl.rs:1326 coordinates the full REPL loop.

### Structural Concerns

1. **repl.rs is 3278 lines.** This is large for a single file. The slash command handlers alone account for ~1500 lines. Consider splitting into `repl/session.rs` (core eval loop), `repl/commands.rs` (slash command dispatch and handlers), and `repl/trace.rs` (trace support). This is not blocking but will become important as more features are added.

2. **`compile_expr_with_traced_fns` in repl.rs** (line 1077) replicates the backend's `compile_expr_with_got_and_symbols` with one extra field (`traced_fns`). The comment acknowledges this: "The backend's public API does not expose this parameter, so we replicate the compilation pipeline here." This is a near-duplicate function that will diverge. The backend API should be extended to accept `traced_fns` as an optional parameter rather than maintaining a parallel codepath.

---

## Summary

| Severity | Count | IDs |
|---|---|---|
| Blocker (B) | 1 | F-6 |
| Important (I) | 4 | F-1, F-2, F-8, F-11 |
| Suggestion (S) | 6 | F-3, F-4, F-5, F-7, F-9, F-10 |

**Overall assessment**: The trace implementation follows the sketch design closely and the architecture is sound — runtime/backend/integration layering is correct, GOT swap/restore is atomic via memcpy, and thread ownership uses proper CAS. The blocker (F-6) is a quick fix. The important findings (F-1, F-2, F-8, F-11) should be addressed before the sprint closes. The R1 assessment of S16-19 shows solid infrastructure with one important concern (IO trampoline panic) and manageable technical debt (repl.rs size).

## Next Skills

- `/backend` — address F-1 (move GOT_TABLE_SIZE to cranelisp-types), F-8 (extract body-discard helper)
- `/platform` — address F-1 if GOT_TABLE_SIZE move involves platform crate
- `/int` — address F-2 (mutex poisoning), F-6 (remove unsafe impls), F-11 (SAFETY comments), and the `compile_expr_with_traced_fns` duplication noted in R1
