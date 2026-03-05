# Ring 1 Review Checklist

Ring 1 specific review criteria. Apply AFTER the general `checklist.md`. Ring 1 property: **Strings, ADTs with fields, closures, reference counting. Heap management established as a clean layer over Ring 0.**

Ring 1 exercises: `cranelisp-types` (heap layouts), `cranelisp-frontend` (string literals, data constructors, lambda captures), `cranelisp-typecheck` (ADT type checking, polymorphic constructors, exhaustiveness over data types), `cranelisp-backend` (heap allocation, RC emission, closure compilation, ADT codegen, drop glue), `cranelisp-runtime` (allocator, RC primitives, string intrinsics, panic handler), and the `cranelisp` binary crate (REPL display of heap values, error recovery with RC).

---

## 1. Heap Layout Adherence (Mandatory)

These checks enforce the base-pointer convention and offset correctness specified in `design/arch/interfaces.md`. Ring 1 introduces the first heap objects -- if layouts are wrong here, every subsequent ring inherits corrupt memory access patterns.

Derived from `design/arch/interfaces.md` "Heap Object Layouts", `design/arch/CLAUDE.md` decision 10 (base-pointer ABI), and `src/CLAUDE.md` "Heap Access".

- [ ] **Base-pointer convention.** `runtime/alloc` returns the base pointer (offset 0 of the allocation). All field accesses use positive offsets. No interior pointers. No negative offsets for any field access. (Departing from the sketch's interior-pointer convention per `design/arch/CLAUDE.md` decision 10.)
- [ ] **`HeapHeader` at offset 0.** Every heap-allocated value starts with `[alloc_size: i64 @ offset 0 | rc: i64 @ offset 8]`. `HeapHeader::SIZE == 16`, `HeapHeader::ALLOC_SIZE_OFFSET == 0`, `HeapHeader::RC_OFFSET == 8`. Compile-time assertions verify these in `cranelisp-types`.
- [ ] **Payload starts at offset 16.** All type-specific payload (string len, ADT tag, closure code_ptr) begins at `HeapHeader::SIZE`. No type stores payload before the header.
- [ ] **Layout constants use `offset_of!` and struct constants.** No hardcoded numeric offsets (e.g., bare `16`, `24`) in codegen. Every heap access uses constants from the layout struct: `HeapHeader::RC_OFFSET`, `HeapAdt::TAG_OFFSET`, `HeapAdt::field_offset(i)`, `HeapClosure::CODE_PTR_OFFSET`, `HeapClosure::capture_offset(i)`. (Addresses `src/CLAUDE.md` "Heap Access" -- representation containment.)
- [ ] **Every `heap_load` / `heap_store` has a semantic comment.** Per `src/CLAUDE.md` "Heap Access": every load or store on a heap pointer must include a comment stating the field name and width. E.g., `heap_load(ptr, HeapAdt::TAG_OFFSET) // tag: i64`.
- [ ] **Compile-time assertions exist for ALL layout structs.** `HeapHeader`, `HeapString`, `HeapAdt`, and `HeapClosure` each have `const _: () = assert!(...)` verifying their offsets. These fail at build time if the layout changes unexpectedly.
- [ ] **`alloc_size` is written correctly.** The total allocation size (header + payload) is stored at offset 0. `heap_dealloc` reads this to know how much to free. Incorrect `alloc_size` causes silent memory corruption.

## 2. Reference Counting Correctness (Mandatory)

RC bugs are the hardest class of errors to diagnose -- they manifest as use-after-free, double-free, or leaks far from the causal site. Every item here is a potential Ring 1 blocker.

Derived from `design/arch/interfaces.md` "Reference Counting Operations" and "Consuming Calling Convention", `src/CLAUDE.md` "Scope Management", codegen audit HIGH-2 (duplicated heap classification), codegen audit MED-5 (duplicated dec preamble), codegen audit LOW-1 (magic number threshold).

- [ ] **RC initialized to 1 on allocation.** Every call to `runtime/alloc` writes `rc = 1` at `HeapHeader::RC_OFFSET`. The allocating binding owns the value.
- [ ] **Atomic RC from Ring 1.** RC operations use `atomic_rmw` with Release ordering for both inc and dec. Not plain `load`/`add`/`store`. Per `design/arch/CLAUDE.md` decision 13 and NFR C.4.1. (Avoids a breaking ABI change when concurrency arrives in Ring 4.)
- [ ] **Acquire fence before deallocation.** When `old_rc == 1` after an atomic dec (meaning this was the last reference), an Acquire fence is emitted before reading object fields for drop glue. Per `design/arch/interfaces.md` "Reference Counting Operations" -- matches `std::sync::Arc` semantics.
- [ ] **No inc without a corresponding dec path.** Every `emit_rc_inc` has a reachable `emit_rc_dec` or scope-exit cleanup that will eventually decrement the count. Review the inc/dec balance for each code path: function entry, function exit, let bindings, match arms, if branches.
- [ ] **Consuming calling convention for cranelisp-to-cranelisp calls.** Callee owns heap-typed parameters. Caller prepares: (a) last-use variable in scope -- transfer ownership, no inc, mark consumed; (b) non-last-use variable or capture -- inc before call; (c) temporary expression result -- no action (rc=1 transferred). (Per `design/arch/interfaces.md` "Consuming Calling Convention".)
- [ ] **Borrowed calling convention for extern/platform calls.** Callee does NOT own heap-typed parameters. Caller decs temporaries after the call returns. All string primitives (`str-concat`, `str-eq`, etc.) use borrowed convention. Mixing conventions causes double-free or leak.
- [ ] **Capture rule: captures are NEVER last-use.** A variable closed over by a lambda is never eligible for last-use transfer. The closure environment holds an implicit reference; drop glue manages it. If `emit_consuming_caller_rc` treats a captured variable as last-use, the closure's env reference becomes dangling. (Addresses a critical correctness invariant from `design/arch/interfaces.md`.)
- [ ] **Scope cleanup emits dec for all heap-typed bindings EXCEPT the return value.** The return value is transferred to the caller or parent scope. All other heap-typed bindings in the scope stack must be decremented. If the return value is one of the bindings, its dec is skipped and its ownership transfers out.
- [ ] **`HeapCategory::classify` is the sole heap-classification authority.** No `Type::is_heap()` convenience method that could diverge. The classify function covers `String` (AlwaysHeap), `Fn` (AlwaysHeap in Ring 1), `ADT` (depends on constructors -- AlwaysHeap if any data constructor, NeverHeap if all nullary, Mixed if both). (Addresses codegen audit HIGH-2 -- duplicated classification logic.)
- [ ] **`NULLARY_TAG_THRESHOLD` is a named constant.** No bare `1024` in codegen. Used to discriminate nullary ADT tags (small i64 values) from heap pointers. (Addresses codegen audit LOW-1.)
- [ ] **`CRANELISP_RC_TRACE=1` produces balanced inc/dec output.** For every test, tracing shows that every inc has a matching dec and every allocation is freed. No leaks, no double-frees.
- [ ] **`emit_rc_inc` and `emit_rc_dec` are the only RC emission points.** No code path emits `atomic_rmw` on the RC field outside these two functions. This confines RC logic to two functions and prevents inconsistent ordering or threshold bugs. (Addresses `src/CLAUDE.md` "Heap Access" -- representation containment.)
- [ ] **Dec preamble is not duplicated.** The null/low-value guard, atomic subtract, underflow check, and `old_rc == 1` branch should exist in one place, not copied between `emit_dec_inline` and `emit_closure_dec_inline`. (Addresses codegen audit MED-5.)

## 3. String Opacity (Mandatory)

Derived from `design/arch/CLAUDE.md` decision 12, `design/arch/interfaces.md` "HeapString", and `design/arch/design-space.md` section 2 (string representation).

- [ ] **Backend never reads or writes string bytes.** All string content access goes through extern functions in `cranelisp-runtime`. The backend knows `HeapHeader` (for RC) but does NOT import `HeapString` layout constants (`LEN_OFFSET`, `DATA_OFFSET`).
- [ ] **Backend does not import `HeapString`.** The `HeapString` struct is owned by `cranelisp-runtime`. The backend crate has no `use` of `HeapString` or any of its associated constants. Verify this with a grep of backend source.
- [ ] **String literal codegen uses `runtime/alloc_string`.** Backend stores literal bytes in JIT data section at compile time. At runtime, emits `call runtime/alloc_string(data_ptr, len)`. Does NOT allocate string memory inline and write bytes one-at-a-time via `istore8` loops. (Addresses codegen audit MED-7 -- per-byte `istore8` pattern for panic strings.)
- [ ] **No per-byte `istore8` loops for string construction.** All string construction (including panic messages) goes through `runtime/alloc_string` or equivalent runtime functions. The prototype had per-byte IR emission that created quadratically large IR for long strings. (Addresses codegen audit MED-7.)
- [ ] **String comparison goes through `str-eq`.** The backend does not emit inline byte comparison for strings. Comparison uses the `str-eq` extern primitive.
- [ ] **String primitives registered with borrowed convention.** All string extern functions (`str-concat`, `str-eq`, `str-len`, `int-to-string`, `float-to-string`, `bool-to-string`, `string-identity`, `parse-int`) are borrowed -- callee does not consume heap arguments.

## 4. ADT Codegen Patterns (Mandatory)

Derived from `design/arch/interfaces.md` "HeapAdt", codegen audit HIGH-3 (vec ops complexity), and the Ring 1 scope in `design/arch/roadmap.md`.

- [ ] **Nullary constructors are bare i64 tags.** Tags are `0`, `1`, `2`, etc. No heap allocation. No RC. (Per `design/arch/interfaces.md` "Nullary/data discrimination".)
- [ ] **Data constructors are heap-allocated.** Layout: `[HeapHeader | tag: i64 @ offset 16 | field_0: i64 @ offset 24 | field_1: i64 @ offset 32 | ...]`. Uses `HeapAdt::TAG_OFFSET`, `HeapAdt::FIELDS_START`, `HeapAdt::field_offset(i)`.
- [ ] **Mixed sum type discrimination uses `NULLARY_TAG_THRESHOLD`.** For an ADT with both nullary and data constructors (e.g., `Option`), the match discriminator checks `value < NULLARY_TAG_THRESHOLD` for nullary, then loads the heap tag at `HeapAdt::TAG_OFFSET` for data constructors.
- [ ] **Tag values are consistent between constructor creation and match.** A constructor assigned tag `N` must produce the same tag `N` when matched. Tags are assigned sequentially starting from 0, covering both nullary and data constructors in declaration order.
- [ ] **Field offsets match construction and access.** A constructor that stores `field_0` at `HeapAdt::field_offset(0)` must have its match bindings and field accessors read from the same offset. Off-by-one errors in field indexing cause silent data corruption.
- [ ] **Drop glue for ADTs decrements all heap-typed fields.** A drop function for `(deftype Node [:Node left :Node right])` must dec both `left` and `right` before freeing the node. For sum types, drop glue discriminates on tag and only decs the fields that exist for that constructor.
- [ ] **Drop glue handles mixed nullary/data correctly.** For an ADT like `Option`, drop glue must check whether the value is nullary (no-op) or a heap pointer (dec fields, then free). The `NULLARY_TAG_THRESHOLD` guard must be present in drop glue.
- [ ] **Polymorphic ADTs type-check correctly.** `(deftype (Option a) None (Some [:a val]))` -- `Some` has type `(Fn [a] (Option a))`, `None` has type `(Option a)`. Type parameters are resolved at each use site.
- [ ] **Exhaustiveness checking covers data constructors.** A match on `(Option a)` requires both `None` and `Some` arms. Missing arms are `CranelispError::TypeError`. (Per spec 6.5.)
- [ ] **Constructor patterns bind field values in match.** `(match opt [(Option.Some x) x (Option.None 0)])` binds `x` to the `val` field of `Some`. The binding is loaded from the correct heap offset.

## 5. Closure Patterns (Mandatory)

Derived from `design/arch/interfaces.md` "HeapClosure" and "Closure Calling Convention", codegen audit HIGH-1 (FnCompiler init duplication), codegen audit HIGH-5 (par-bind continuation duplication).

- [ ] **Closure layout: `[HeapHeader | code_ptr | cap_0 | cap_1 | ... | cap_n]`.** `HeapClosure::CODE_PTR_OFFSET == 16`, `HeapClosure::CAPTURES_START == 24`, `HeapClosure::capture_offset(i)`. No `drop_ptr` inline in the closure struct.
- [ ] **Lambda body signature: `(env_ptr: i64, params...) -> i64`.** `env_ptr` is the closure's base pointer. Callee loads captures via `heap_load(env_ptr, HeapClosure::capture_offset(i))`.
- [ ] **`env_ptr` is always the first parameter.** For all lambda bodies -- capturing and non-capturing alike. Non-capturing lambdas and named-function wrappers ignore `env_ptr` but still receive it.
- [ ] **Non-capturing lambdas allocate a minimal closure.** `[HeapHeader | code_ptr]` with zero captures. The wrapper function ignores `env_ptr`. No special-casing of non-capturing lambdas as bare function pointers -- all function values are closures.
- [ ] **Indirect call protocol: `call_indirect(sig, code_ptr, [closure_ptr, args...])`.** `code_ptr` is loaded from `HeapClosure::CODE_PTR_OFFSET`. The closure pointer itself is passed as the first argument. No confusion between direct and indirect call conventions.
- [ ] **Closure drop via side-table, not inline.** Per `design/arch/CLAUDE.md` decision 11: the backend maintains a `HashMap<*const u8, *const u8>` (code_ptr to drop_fn). No `drop_ptr` field in the closure struct. Drop glue is looked up by code_ptr at dec time.
- [ ] **Drop glue decs all heap-typed captures.** A closure over `[x: String, y: Int]` has drop glue that decs `x` (heap) and skips `y` (not heap). Drop glue is generated per-lambda at compile time.
- [ ] **Capture ordering is deterministic.** Captures are stored in a consistent order (e.g., sorted by variable name). Both the closure constructor and the lambda body must agree on the order.
- [ ] **`FnCompiler` construction is not duplicated.** A single `inner_compiler()` method or builder creates inner `FnCompiler` instances for lambda bodies, continuations, and drop glue. No copy-pasted struct literals with 20+ fields. (Addresses codegen audit HIGH-1.)
- [ ] **Named function-as-value wraps in a closure.** `(let [f factorial] (f 5))` wraps `factorial` in a minimal closure `[HeapHeader | code_ptr]`. The wrapper function has signature `(env_ptr, param) -> i64` and delegates to the original function.
- [ ] **No leaked `Box` raw pointers.** If any data is allocated via `Box::into_raw` for embedding in JIT code (e.g., function name bytes for tracing), it must be registered for cleanup on session teardown. (Addresses codegen audit MED-3.)

## 6. JIT Symbol Names (Mandatory)

Derived from `src/CLAUDE.md` "JIT Symbol Names" and `design/review/naming-convention-review.md`.

- [ ] **No `cranelisp_` prefix on any JIT symbol.** The prefix used in the sketch is banned. All symbols follow the naming convention: `runtime/alloc` (not `cranelisp_alloc`), `str-concat` (not `cranelisp_str_concat`), `runtime/panic` (not `cranelisp_panic`).
- [ ] **No `cranelisp_` prefix on Rust function names.** Rust function names use `snake_case` matching the spec name: `heap_alloc` (not `cranelisp_alloc`), `str_concat` (not `cranelisp_str_concat`), `runtime_panic` (not `cranelisp_panic`). Per `src/CLAUDE.md` rule 6.
- [ ] **Runtime infrastructure uses `runtime/` prefix.** Internal functions (alloc, dealloc, panic, rc_underflow_check) are prefixed with `runtime/`. These are not callable from user code.
- [ ] **User-visible primitives use spec names.** `str-concat`, `str-eq`, `int-to-string` -- kebab-case, matching `spec/appendix-a-builtins.md`.
- [ ] **ADT constructor JIT names follow module system.** Constructors are `name` or `module/name` (e.g., `Some`, `user/Point`). Per naming convention table row added by naming review finding F-2.
- [ ] **Drop glue and internal codegen functions have clear names.** Compiler-generated functions (drop glue, curry wrappers) follow an established naming pattern that does not collide with user names. Per naming review finding F-3.

## 7. Code Quality (Mandatory)

These apply the general source conventions from `src/CLAUDE.md` to the Ring 1 additions specifically. Ring 1 introduces significantly more code than Ring 0 (heap infrastructure, RC, closures, ADTs) -- if quality standards slip here, the complexity compounds.

- [ ] **No `unwrap()` in non-test code.** Use `?` with `CranelispError`. (Per `src/CLAUDE.md`.)
- [ ] **No `panic!()` in non-test code.** Use `unreachable!("invariant: <description>")` for true programmer errors. Never panic on user input. (Per `src/CLAUDE.md`.)
- [ ] **No `expect()` in pipeline code.** For programmer invariants, use `unreachable!`. For user-facing errors, return `CranelispError` with a span. (Per `src/CLAUDE.md`.)
- [ ] **No god functions (>100 lines).** Decompose into named helpers. The prototype's primary structural debt was functions exceeding 200 lines. The following prototype functions must NOT be replicated: `compile_vec_set_inline` (230 lines), `compile_run_tests` (233 lines), `compile_par_bind_continuation` (200 lines). (Per `src/CLAUDE.md`, addresses codegen audit HIGH-3/HIGH-4/HIGH-5.)
- [ ] **Max 8 parameters per function.** Group related parameters into context structs. The prototype's `compile_function` had 21 parameters. (Per `src/CLAUDE.md`, addresses codegen audit LOW-2.)
- [ ] **`unsafe` blocks have `// SAFETY:` comments.** Every `unsafe` block in `cranelisp-runtime` (allocator, RC, string intrinsics) and `cranelisp-backend` (if any) must have a `// SAFETY:` comment explaining why the unsafe operation is sound. This is standard Rust practice and critical for code that manages raw heap pointers.
- [ ] **`#[must_use]` on public Result-returning functions.** Prevents silent error drops at API boundaries. Apply to all public functions in `cranelisp-runtime`, `cranelisp-types`, `cranelisp-backend`, `cranelisp-typecheck`, and `cranelisp-frontend` that return `Result`. (Sprint 1 deferred item M-5.)
- [ ] **Design doc exists for each skill's changes.** Each compiler skill that adds Ring 1 code must have a design document in its `design/{skill}/` directory describing its approach. Per `design/CLAUDE.md` "Design Doc Expectations".

## 8. String Newtypes (Mandatory)

These re-emphasize the `design/arch/CLAUDE.md` "String Newtypes" rule specifically for Ring 1 additions, which introduce new identifier categories (type parameters, constructor names).

- [ ] **Constructor names use `Symbol`.** ADT constructor names (`Some`, `None`, `Cons`, `Nil`) are `Symbol`, not bare `String`.
- [ ] **Type parameter names use `Symbol`.** In `(deftype (Option a) ...)`, the `a` is represented as `Symbol`, not `String`.
- [ ] **JIT symbol names use `JitSymbol`.** When registering compiled functions, constructors, or drop glue in the JIT, use the `JitSymbol` newtype. No bare `String` for JIT registration.
- [ ] **`ClosureDropTable` keys and values are typed.** The side-table mapping code_ptr to drop_fn should not use bare `*const u8` as both key and value without type distinction. Consider a `CodePtr` newtype or clear documentation of which pointer is which.

## 9. Backend Specifics (Ring 1)

Derived from the Ring 0 backend checklist items that carry forward, plus new Ring 1 concerns.

- [ ] **Single ISA construction point carries forward.** The shared `build_isa_flags(is_pic: bool)` function from Ring 0 is used for Ring 1 additions too. No new ISA construction. (Addresses cache audit HIGH-2.)
- [ ] **`CodegenContext` carries heap-specific fields.** `type_defs`, `constructor_to_type`, `expr_types`, `method_resolutions` are in the shared immutable context. Drop function caches, closure drop table, and mutable codegen state are per-function on `FnCompiler`. (Addresses codegen audit HIGH-1.)
- [ ] **All heap allocation goes through `compile_alloc`.** A single helper function that emits the `call runtime/alloc(payload_size)` sequence. No inline allocation logic scattered across closure, ADT, and string codegen.
- [ ] **Scope cleanup handles heap-typed and non-heap-typed bindings.** At scope exit, only heap-typed bindings are decremented. `HeapCategory::classify` determines which bindings need cleanup.
- [ ] **TCO interacts correctly with RC.** `emit_scope_cleanup_for_tco` must dec all heap-typed bindings in the current scope (except the tail-call arguments being passed) before jumping to the loop header. Omitting cleanup causes leaks; decrementing arguments causes use-after-free.
- [ ] **Match arm bodies have independent scope frames.** Each match arm pushes a new scope for its bindings. Pattern-bound variables are only visible within that arm's body. Scope cleanup runs at the end of each arm (before the merge block).

## 10. Runtime Crate (`cranelisp-runtime`)

Derived from `design/arch/architecture.md` "cranelisp-runtime" and the Ring 1 platform deliverables.

- [ ] **Allocator writes `alloc_size` and `rc` correctly.** `heap_alloc(payload_size)` allocates `HeapHeader::SIZE + payload_size` bytes, writes `alloc_size = HeapHeader::SIZE + payload_size` at offset 0, writes `rc = 1` at `HeapHeader::RC_OFFSET`, returns the base pointer.
- [ ] **Deallocator reads `alloc_size` from the base pointer.** `heap_dealloc(base_ptr)` reads the total size from offset 0 and frees exactly that many bytes. Incorrect size causes heap corruption.
- [ ] **`runtime_panic` uses `panic!` + `catch_unwind`.** The panic propagates through Rust frames. The binary crate wraps JIT execution in `catch_unwind`. This strategy must be documented as Ring-1-only -- Ring 2+ (with closures calling back into Rust) may require reassessment.
- [ ] **`rc_underflow_check` is debug-only.** Uses `debug_assert!` internally. No-op in release builds. Called from JIT code only when `CRANELISP_RC_TRACE` is active or in debug builds.
- [ ] **String intrinsics handle empty strings.** `str_concat("", "hello")`, `str_eq("", "")`, `str_len("")` all work correctly. Edge case: `parse_int("")` returns `None`.
- [ ] **No `cranelisp-runtime` function allocates without setting RC.** Every allocation path sets `rc = 1`. `heap_alloc_string` sets RC on the HeapHeader before returning.

## 11. Typecheck Specifics (Ring 1)

Derived from the Ring 1 scope in `design/arch/roadmap.md` and typechecker audit findings.

- [ ] **ADT type definitions register constructors and accessors.** `register_type_def` populates `constructor_to_type`, registers constructor schemes in the symbol table, and generates accessor functions for fields.
- [ ] **Polymorphic ADTs instantiate type parameters.** `(Some 42)` unifies the constructor's `a` with `Int`, yielding `(Option Int)`. Unification errors produce clear type errors with spans.
- [ ] **Exhaustiveness checking for sum types with data constructors.** `(match opt [(Option.Some x) ... ])` without a `None` arm is a type error.
- [ ] **`String` type is fully exercised.** String literals in expression position are accepted (no longer rejected as in Ring 0). String type flows through inference, unification, and codegen correctly.
- [ ] **`HeapCategory` information flows to codegen.** `expr_types: HashMap<Span, Type>` in `CheckResult` is populated for all expressions so the backend can determine heap classification at every expression site.

## 12. REPL Display and Error Recovery (Ring 1)

Derived from `repl/spec.md`, the Ring 1 acceptance criteria, and Ring 0 checklist section 8.

- [ ] **ADT values display correctly.** `(Option.Some 42)` displays as `:(user/Option primitives/Int) (Option.Some 42)`. `Option.None` displays as `:(user/Option a) Option.None`. Nested ADTs display recursively.
- [ ] **String values display with quotes.** `"hello"` displays as `:primitives/String "hello"`. Strings are read from heap via `cranelisp-runtime`'s `string_read` function, not by the REPL reading heap memory directly.
- [ ] **Closure values display as `<closure>`.** `(fn [x] (+ x 1))` displays as `:(Fn [primitives/Int] primitives/Int) <closure>`. No attempt to decompile closures.
- [ ] **Error recovery does not leak heap memory.** If a type error or codegen error occurs mid-compilation, any heap allocations from the partially-compiled expression are cleaned up. The REPL session state (symbol table, type environment, GOT) is rolled back to the pre-input state.
- [ ] **RC state is consistent after REPL error recovery.** No orphaned allocations with dangling references. No RC underflow on the next successful input.

---

## Ring 1 Acceptance Gate

Before Ring 1 is declared complete, `/review` verifies:

1. **All items on this checklist pass.** Every checkbox is checked or has an explicit waiver with rationale.
2. **All items on `checklist.md` (general) pass.**
3. **Zero HIGH findings outstanding.** Any HIGH finding from review must be resolved before the gate.
4. **MEDIUM findings acknowledged.** Each MEDIUM finding is either resolved or explicitly deferred with rationale in the ring completion report (`ring1-report.md`).
5. **Ring 1 roadmap acceptance criteria pass.** Per `design/arch/roadmap.md` Ring 1 acceptance criteria:
   - `"hello"` evaluates to `:primitives/String "hello"`
   - `(Some 42)` evaluates to `:(user/Option primitives/Int) (Option.Some 42)`
   - Closures capture and execute correctly
   - `CRANELISP_RC_TRACE=1` shows balanced inc/dec for all tests
   - No memory leaks detected by runtime tracking
   - ~100 additional integration tests green
6. **RC correctness is proven, not assumed.** `CRANELISP_RC_TRACE` output is balanced for the full test suite. `LIVE_ALLOCS` tracking shows zero live allocations at program/test exit.
7. **No `cranelisp_` prefix in any JIT symbol or Rust function name.**
8. **All design docs updated.** Each compiler skill has a design document in `design/{skill}/` reflecting its Ring 1 implementation.

## Cross-References

- `design/review/checklist.md` -- general checklist (apply first)
- `design/review/ring0-checklist.md` -- Ring 0 checklist (Ring 0 items carry forward)
- `design/review/naming-convention-review.md` -- naming convention findings (F-2, F-3 relevant to Ring 1)
- `design/review/CLAUDE.md` -- review infrastructure ownership
- `design/arch/interfaces.md` -- heap object layouts, RC operations, calling conventions, extern primitives
- `design/arch/architecture.md` -- crate responsibilities, pipeline design
- `design/arch/design-space.md` -- Ring 1 decision analysis against NFRs
- `design/arch/CLAUDE.md` -- architectural principles, Ring 1 key decisions (10-13)
- `design/arch/roadmap.md` -- Ring 1 acceptance criteria
- `src/CLAUDE.md` -- source conventions (error handling, code structure, naming, heap access, scope)
- `sketch/audits/codegen.md` -- codegen audit: HIGH-1 (FnCompiler duplication), HIGH-2 (heap classification), HIGH-3 (vec ops), MED-1 (unwrap/expect), MED-3 (leaked Box), MED-5 (dec preamble duplication), MED-7 (istore8 string), LOW-1 (magic 1024), LOW-2 (21 parameters)
- `sketch/audits/typechecker.md` -- typechecker audit: HIGH-4/HIGH-5 (panics), MED-4 (env clone)
- `sketch/audits/module.md` -- module audit: LOW-2 (unwrap after ensure_got)
- `sketch/audits/cache.md` -- cache audit: HIGH-2 (ISA duplication)
- `spec/12-runtime.md` -- runtime spec (heap, RC, calling conventions)
- `sprints/SPRINT.md` -- Sprint 2 plan (Ring 1 chunks A+B+C)

## Next skills

- `/backend` -- Ring 1 heap allocation, RC emission, closure compilation, ADT codegen: the heaviest Ring 1 code, reviewed against sections 1-5 and 9
- `/platform` -- Ring 1 `cranelisp-runtime` allocator, RC primitives, string intrinsics: reviewed against sections 3, 6, and 10
- `/typecheck` -- Ring 1 ADT type checking, polymorphic constructors, exhaustiveness: reviewed against section 11
- `/frontend` -- Ring 1 string literal parsing, data constructor syntax: reviewed against section 3
- `/qa` -- Ring 1 integration tests, RC correctness verification: provides the evidence for the acceptance gate
- `/arch` -- Escalation target for heap layout or calling convention deviations found during review
