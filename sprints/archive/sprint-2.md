# Sprint 2: Ring 1 — Heap Foundation, ADTs, Closures

**Status**: COMPLETE
**Ring**: 1 (Heap)
**Goal**: Add heap infrastructure, strings, ADTs with fields, and closures to the compiler pipeline, with proven RC correctness.

## Ring 1 Chunking

Ring 1 features (from `design/arch/roadmap.md` §"Ring 1: Heap") decomposed into delivery increments. Each chunk produces a testable result without interim scaffolding.

### Chunk A: Heap Foundation + Strings
- Runtime allocator (`cranelisp_alloc`, RC header layout)
- RC primitives (inc, dec, drop glue, `CRANELISP_RC_TRACE`, `LIVE_ALLOCS`)
- Consuming calling convention, last-use optimization
- String type: inference, codegen, heap allocation, RC, display
- String primitives (`str-concat`, `str-eq`, `int-to-string`, etc.)
- **Why first**: Every other chunk depends on heap infrastructure. Strings are the simplest heap type to validate the RC pipeline end-to-end.

### Chunk B: ADTs with Fields
- Product types: `(deftype Point [:Int x :Int y])`
- Sum types with data constructors: `(deftype (Option a) None (Some [:a val]))`
- Polymorphic ADTs with type parameters
- Shortcut syntax: `(deftype Pair [first second])`
- Constructor patterns with field bindings in match
- Field accessors
- ADT heap allocation, RC, drop glue (nested heap fields)
- ADT value display in REPL
- **Depends on**: Chunk A (heap infrastructure)

### Chunk C: Closures
- Lambda with variable capture
- Closure environment allocation + RC
- Higher-order functions (functions as values, passed as arguments)
- Named functions as values
- Closure display in REPL
- Activates the 11 ignored Ring 0 lambda tests
- **Depends on**: Chunk A (heap infrastructure)

### Chunk D: Vec
- Vec literal syntax `[1 2 3]`
- Vec codegen (heap-allocated, element storage)
- Vec primitives (`vec-get`, `vec-set`, `vec-push`, `vec-len`)
- Vec RC (element RC, COW semantics)
- **Depends on**: Chunk A (heap infrastructure)

### Dependency Graph

```
A (heap + strings)
├── B (ADTs with fields)
├── C (closures)
└── D (Vec)
```

B, C, D are independent of each other but all require A.

## Scope Selection

**`/arch` decision**: Chunks A + B + C. Defer D (Vec) to Sprint 3.

**Rationale**: A is prerequisite for everything. B (ADTs with fields) is the primary Ring 1 value — unlocks `Option`, `Result`, polymorphic types. C (closures) activates the 11 ignored tests and is foundational for Ring 2 traits. D (Vec) is self-contained and defers cleanly without creating throwaway scaffolding.

**`/arch` Wave 1 deliverables** (from review):
- Heap layout: byte-level spec (header, alignment, return pointer)
- Closure environment layout: architectural decision (fn_ptr + env_ptr pair, calling convention)
- String representation: Rust-managed via extern functions vs. inline layout
- First `PrimitiveKind::Extern` primitives: string intrinsics specification
- Panic strategy for closures: can Ring 1 closures create re-entrant JIT calls?
- REPL display interface for heap types (ADT, closure, string formatting)

**Deferred to Sprint 3**: Chunk D (Vec — literal syntax, codegen, primitives, element RC, COW).

## Proposed Wave Structure

{Finalized after chunk selection}

| Wave | Skills | What it produces |
|------|--------|-----------------|
| 0 | `/spec`, `/arch` | NFR appendix (`spec/appendix-b-nfr.md`); design space analysis (`design/arch/design-space.md`) |
| 1 | `/arch` | Ring 1 interface subset for selected chunks (informed by NFRs + design space); Sprint 1 deferred items |
| 2 | `/frontend`, `/typecheck`, `/backend`, `/platform` | Crates extended for selected chunks + design docs in `design/{skill}/` |
| 2.5 | `/review` (parallel per crate) | Per-skill code reviews |
| 3 | `/qa`, `/spec` | Pipeline wiring, integration tests, spec resolution |
| 4 | `/examples`, `/docs`, `/repl`, `/stdlib`, `/port` | Validation from user perspective |
| 5 | `/review` | Ring gate (or sprint gate if Ring 1 spans multiple sprints) |

## Deferred Items from Sprint 1

| ID | Item | Responsible Skill | Proposed Wave |
|----|------|-------------------|---------------|
| M-1 | `NULLARY_TAG_THRESHOLD` duplicated in types + backend | `/backend` | 2 |
| M-2 | `CheckResult` has `type_defs`/`constructor_to_type` not in `interfaces.md` | `/arch` | 1 |
| M-3 | `Warning` type uses bare String | `/arch` specifies, `/typecheck` implements | 1–2 |
| M-5 | No `#[must_use]` on public Result-returning functions | All compiler skills | 2 |
| M-6 | `not` primitive not in `spec/appendix-a-builtins.md` | `/spec` | 3 |
| F-1 | Exhaustiveness checking for non-ADT scrutinee types undefined | `/spec` | 3 |

## Skill Assignments

Each skill fills in its own section after scope is finalized.

### Wave 0 Prerequisites

#### /spec — Non-Functional Requirements Appendix
**Input**: Existing spec (16 files), sketch design docs (`sketch/docs/heap_layout.md`, `sketch/docs/comparison.md`, `sketch/docs/data-structures.md`, `sketch/docs/closures.md`), `sketch/ROADMAP.md` §"Deferred to reimplementation", `lib/plan-stdlib.md` §8 Risks
**Task**: Write `spec/appendix-b-nfr.md` capturing non-functional requirements and future-facing properties that architectural decisions must not preclude. Categories:
1. **Performance properties**: RC=1 copy-on-write optimization (mutate-in-place when refcount is 1), lenient evaluation strategy
2. **Data structure strategies**: RRB (Relaxed Radix Balanced) trees for Vec (persistent, structural sharing), HAMT (Hash Array Mapped Trie) for Map, rope strings
3. **Runtime characteristics**: structural sharing across persistent collections, cache-friendly layouts, allocation pressure targets
4. **Concurrency preparation**: what properties must hold for future par-let / par-bind! (from spec §04, §10, §12)

For each NFR: state the requirement, its rationale, what it constrains in current design, and when it becomes active (which ring or "post-ring").
**Output**: `spec/appendix-b-nfr.md`
**Blocked by**: —
**Wave**: 0
**Acceptance**: Each NFR has requirement, rationale, design constraint, and activation timeline. `/arch` can use this to evaluate whether Ring 1 heap layouts foreclose future options.

#### /arch — Design Space Analysis
**Input**: `spec/appendix-b-nfr.md` (Wave 0), existing `design/arch/architecture.md`, `design/arch/interfaces.md`, sketch design docs
**Task**: Write `design/arch/design-space.md` analyzing how current and proposed architectural decisions interact with the NFRs. For each major Ring 1 decision (heap header layout, RC calling convention, closure environment layout, string representation, ADT layout):
1. What the current design commits to
2. What it leaves open for later change
3. What would break if the NFR were activated (e.g., switching Vec from flat array to RRB tree)
4. Containment strategy: which files/abstractions would need to change

This is a risk-informed analysis, not a commitment to implement any NFR. It ensures Ring 1 decisions are made with eyes open.
**Output**: `design/arch/design-space.md`
**Blocked by**: 0a (/spec NFR appendix)
**Wave**: 0
**Acceptance**: Every Ring 1 heap-related decision has a forward-compatibility assessment. No "we can't do X later because Ring 1 baked in Y" surprises.

---

### /arch
**Input**: Ring 0 completed crate structure; `design/arch/interfaces.md` current; `design/arch/design-space.md` (Wave 0); `spec/appendix-b-nfr.md` (Wave 0); sketch oracle (`sketch/docs/heap_layout.md`, `sketch/docs/closures.md`, `sketch/docs/data-structures.md`); spec `12-runtime.md` (heap layouts, calling conventions, RC); Sprint 1 deferred items M-2, M-3
**Task**: Deliver the architectural specifications that Wave 2 skills (frontend, typecheck, backend, platform) need to implement Chunks A+B+C without ambiguity or cross-skill conflict. Informed by the design space analysis — ensure heap layouts and conventions don't foreclose NFR paths. Specifically:

1. **Heap layout specification** — Add `#[repr(C)]` struct definitions to `design/arch/interfaces.md` under a new "Heap Object Layouts" section. Byte-level specs for:
   - `HeapHeader` (alloc_size at offset 0, rc at offset 8; 16 bytes total)
   - `HeapString` (header + len + bytes; `DATA_OFFSET = 24`)
   - `HeapAdt` (header + tag + fields; `FIELDS_START = 24`, `field_offset(i)`)
   - `HeapClosure` (header + code_ptr + captures; `CAPTURES_START = 24`, `capture_offset(i)`)
   - Compile-time assertions for all offsets
   - Decision: alloc returns **base pointer** (start of struct), not payload pointer. All offsets positive. This is a departure from the sketch (which returned payload pointer with negative offsets for RC header) — document rationale.

2. **Closure environment layout and calling convention** — Add to interfaces.md:
   - Lambda body signature: `(env_ptr: i64, params...) -> i64`
   - `env_ptr` is the closure base pointer itself; callee loads captures via `HeapClosure::capture_offset(i)`
   - Non-capturing lambdas and named-function wrappers allocate a minimal closure `[header | code_ptr]` (no captures)
   - Closure drop glue strategy: per-lambda generated drop function stored in a **side table** (not in the closure struct itself). Decision: Ring 1 closures do NOT store `drop_ptr` inline — the backend maintains a `HashMap<*const u8, *const u8>` mapping code_ptr to drop_fn. Rationale: keeps closure layout uniform (header + code_ptr + captures), avoids the sketch's `drop_ptr` field which was null for most closures and created a wasted 8 bytes per allocation.
   - Re-entrant JIT calls from closures: **not needed in Ring 1**. Closures capture values, not thunks. Macro mini-pipeline (Ring 3) is the first case requiring re-entrant compilation. Document this boundary.

3. **String representation decision** — Specify in interfaces.md:
   - Strings are Rust-managed via extern functions in `cranelisp-runtime`. The JIT never reads or writes string bytes directly — all string operations go through extern calls.
   - `HeapString` layout is owned by `cranelisp-runtime`; the backend only knows it as an opaque heap pointer with `HeapHeader` for RC.
   - String allocation: `cranelisp-runtime` exports `cranelisp_alloc_string(bytes_ptr: *const u8, len: i64) -> i64` that allocates `HeapHeader + len_field + bytes`, copies bytes, returns base pointer.
   - String literal codegen: backend stores literal bytes in JIT data section, calls `cranelisp_alloc_string` at runtime.

4. **String intrinsics specification** — Add `PrimitiveKind::Extern` entries to interfaces.md under a new "Ring 1 Extern Primitives" section:
   - `str-concat :: (Fn [String String] String)` — `cranelisp_str_concat(a: i64, b: i64) -> i64`
   - `str-eq :: (Fn [String String] Bool)` — `cranelisp_str_eq(a: i64, b: i64) -> i64`
   - `int-to-string :: (Fn [Int] String)` — `cranelisp_int_to_string(n: i64) -> i64`
   - `float-to-string :: (Fn [Float] String)` — `cranelisp_float_to_string(f: i64) -> i64`
   - `bool-to-string :: (Fn [Bool] String)` — `cranelisp_bool_to_string(b: i64) -> i64`
   - `string-identity :: (Fn [String] String)` — `cranelisp_string_identity(s: i64) -> i64` (RC inc + return)
   - `parse-int :: (Fn [String] (Option Int))` — `cranelisp_parse_int(s: i64) -> i64` (depends on Chunk B for Option ADT)
   - All string externs use borrowed calling convention (callee does not own args).

5. **REPL display interface for heap types** — Add `ValueFormatter` signatures to interfaces.md:
   - `format_result_value(result: i64, ty: &Type, symbol_tables: &HashMap<ModuleFullPath, SymbolTable>) -> String`
   - Dispatch by type: String reads via `cranelisp-runtime` helper; ADT reads tag + fields from heap using `HeapAdt` layout; Closure displays as `<closure>`.
   - Lives in the binary crate (needs both type info and runtime memory access).

6. **Resolve M-2**: Add `type_defs` and `constructor_to_type` fields to `CheckResult` in interfaces.md. These flow from typecheck to backend so the backend can emit ADT constructors, match discrimination, and drop glue without depending on typechecker internals. Specify:
   - `type_defs: HashMap<TypeName, TypeDefInfo>` — all ADT definitions encountered in the compilation unit
   - `constructor_to_type: HashMap<Symbol, TypeName>` — maps constructor name to its parent type

7. **Resolve M-3**: Specify `WarningKind` enum in interfaces.md and update `Warning` type:
   - `pub enum WarningKind { UnusedBinding, UnreachableArm, ShadowedName, Other }`
   - `pub struct Warning { pub kind: WarningKind, pub message: String, pub span: Span }`
   - Rationale: typed warnings enable filtering, counting by category, and future `-Werror` flag support.

8. **Codegen emit helpers specification** — Document in interfaces.md the `heap_load`/`heap_store` helper pattern and per-type `emit_*_alloc` methods that `/backend` must implement. These are the ONLY codegen code that imports layout constants, containing representation knowledge to a single file.

**Output**:
- Updated `design/arch/interfaces.md` with all items above (heap layouts, closure convention, string repr, extern primitives, display interface, M-2, M-3, emit helpers)
- Updated `design/arch/CLAUDE.md` Key Decisions section with Ring 1 decisions (base-pointer ABI, closure drop side-table, Rust-managed strings)
- Updated `src/CLAUDE.md` if any new cross-cutting conventions emerge (e.g., heap access patterns)

**Blocked by**: Nothing (Wave 1 has no dependencies)
**Wave**: 1
**Acceptance**:
- `design/arch/interfaces.md` contains `#[repr(C)]` struct definitions for `HeapHeader`, `HeapString`, `HeapAdt`, `HeapClosure` with compile-time offset assertions
- `design/arch/interfaces.md` contains closure calling convention (env_ptr first arg, capture loading, drop side-table)
- `design/arch/interfaces.md` contains string representation decision (Rust-managed, opaque to backend) and `cranelisp_alloc_string` signature
- `design/arch/interfaces.md` lists all 7 Ring 1 string extern primitives with JIT symbol names and type signatures
- `design/arch/interfaces.md` contains `ValueFormatter` signatures for REPL display of String, ADT, and Closure values
- `CheckResult` in interfaces.md includes `type_defs` and `constructor_to_type` fields (M-2 resolved)
- `Warning` type in interfaces.md uses `WarningKind` enum (M-3 resolved)
- Emit helper pattern documented (heap_load/heap_store + per-type emit methods)
- No ambiguity remains for Wave 2 skills to begin implementation of Chunks A, B, or C
- `/review` confirms specifications are internally consistent and complete

---

**Wave 2 cross-cutting requirement — Design documents**: Every compiler skill (`/frontend`, `/typecheck`, `/backend`, `/platform`) MUST create or update design documents in their `design/{skill}/` directory as part of their Wave 2 deliverables. These documents explain the solution design — algorithms, data structures, internal architecture, trade-offs, and rejected alternatives. They are reviewed by `/review` in Wave 2.5 for completeness. See `design/CLAUDE.md` and each subdirectory's `CLAUDE.md` for guidance.

---

### /frontend
**Input**: `/arch` Wave 1 deliverables (no new interface types needed -- `Expr::StringLit`, `TypeExpr::Applied`, `Pattern::Constructor` with bindings, and full `deftype` field syntax already exist in `interfaces.md` and are implemented in the frontend crate)
**Task**: Remove Ring 0 rejection gates that block Chunk A+B+C features. Specifically:
1. **StringLit acceptance** (Chunk A): Replace the `Sexp::Str` rejection in `build_expr` with `Expr::StringLit { value, span }` emission. This is a single-arm change in `ast_builder.rs:735`.
2. **Docstring interaction audit** (Chunk A): Verify that `extract_optional_docstring` correctly distinguishes docstrings from string-valued expressions. The detection relies on positional context (strings after `defn`/`deftype` name are docstrings), which is unambiguous -- but add unit tests confirming `(defn greet "docstring" [x] x)` captures the docstring while `(let [s "hello"] s)` does not.
3. **`#[must_use]` on public Result functions** (deferred item M-5): Add `#[must_use]` to `parse()` in `reader.rs` and `lib.rs`.
4. **Unit tests for Ring 1 paths**: Add tests exercising paths that existed structurally in Ring 0 but had no test coverage because the features were deferred:
   - `TypeExpr::Applied` via annotation: `:(Option Int) (Some 42)` parses to `Annotate { Applied("Option", [Named("Int")]), ... }`
   - Constructor pattern with field bindings: `(match x [(Some v) v])` produces `Pattern::Constructor { name: "Some", bindings: ["v"] }`
   - Product type with fields: `(deftype Point [:Int x :Int y])` produces correct `ConstructorDef` with two fields
   - Sum type with data constructors: `(deftype (Option a) None (Some [:a val]))` produces two constructors, one nullary, one with a field
   - String literal as expression: `"hello"` produces `Expr::StringLit`

**Note**: Constructor patterns with bindings (`(Some x)`), `TypeExpr::Applied`, product/sum type syntax, and `desugar_type_def` were all implemented complete in Ring 0 per the frontend plan (sections 3.3, 3.4, 3.7). No structural code changes are needed for Chunks B or C -- the AST builder already produces the correct AST nodes. The typechecker and backend are responsible for the new semantics.
**Output**: Updated `cranelisp-frontend` crate where `Sexp::Str` produces `Expr::StringLit`, `#[must_use]` on public functions, and ~15 new unit tests covering Ring 1 AST paths.
**Blocked by**: None (no new interface types needed from `/arch`; can start immediately)
**Wave**: 2
**Acceptance**:
- `build_expr` on `Sexp::Str("hello", span)` returns `Ok(Expr::StringLit { value: "hello", span })`
- `build_expr` on `Sexp::Str(...)` no longer returns `Err` with "strings not yet supported"
- Docstring vs. string-expression tests pass (no false capture)
- `TypeExpr::Applied` annotation round-trip test passes
- Constructor pattern with bindings test passes
- Product and sum type with fields tests pass
- All existing Ring 0 tests remain green (accretive)
- `cargo clippy` clean on `cranelisp-frontend`

### /typecheck
**Input**: Ring 1 interface additions from `/arch` (Wave 1): heap layout spec, closure environment layout, any `WarningKind` enum definition (M-3). Existing Ring 0 typecheck crate with enum-only ADTs, scope stack, unification, two-pass pipeline.

**Task**: Extend `cranelisp-typecheck` to handle all three Ring 1 chunks (strings, ADTs with fields, closures):

1. **String type inference** (Chunk A): Enable `infer_string_lit` — return `Type::String`, record in `expr_types`. Replace the Ring 0 error stub in `infer.rs`. Add `Type::String` resolution for annotations (already works via `Type::from_name`; verify only).

2. **ADTs with fields** (Chunk B):
   - **Remove Ring 0 guards** in `register_type_def` (`adt.rs`): lift the rejection of type parameters and data constructor fields. Full registration: allocate fresh type vars for type parameters, resolve field `TypeExpr` entries via `resolve_type_expr`, populate `ConstructorInfo.fields` with `FieldInfo` entries.
   - **Polymorphic constructor schemes**: Data constructors get polymorphic schemes. `(deftype (Option a) None (Some [:a val]))` produces `None :: forall a. (Option a)` and `Some :: forall a. (Fn [a] (Option a))`. Nullary constructors of polymorphic types also get polymorphic schemes. Register as `ModuleEntry::Constructor` with generalized schemes.
   - **Shortcut syntax**: `(deftype Pair [first second])` — bare field names with `TypeExpr::TypeVar` field types. The frontend delivers the same `ConstructorDef` structure; the typechecker allocates fresh vars for unnamed type params and generalizes. No special-case code needed beyond the general polymorphic registration.
   - **`resolve_type_expr` for `TypeExpr::Applied`** (`resolve.rs`): Enable the currently-erroring case. Resolve `(Option Int)` to `Type::ADT(TypeName("Option"), vec![Type::Int])`. Validate arity: number of type args must equal type params in `TypeDefInfo`. Return `TypeError` on mismatch.
   - **Constructor pattern checking** (`infer.rs`): Extend `check_constructor_pattern` to handle data constructors with field bindings. Instantiate the constructor's polymorphic scheme with fresh vars, unify the instantiated result type with the scrutinee type, then bind each pattern variable to the corresponding instantiated field type in the arm scope. Validate binding count matches field count.
   - **Exhaustiveness checking**: No algorithmic change needed — `check_exhaustiveness` already tracks coverage by constructor name. Data constructors participate in the same name-based coverage check as nullary constructors.
   - **Field accessors**: If `/arch` specifies accessor functions (e.g., `Point.x :: (Fn [Point] Int)`), register them as `ModuleEntry::Def` with appropriate schemes during type registration.

3. **Closure/lambda type inference** (Chunk C): Lambda inference already works in Ring 0 (`infer_lambda`). Ring 1 changes are minimal from the typechecker:
   - Confirm `expr_types` records `Type::Fn(...)` for all lambda expressions (already done via `record_expr_type` in `infer_lambda`).
   - No capture detection in the typechecker — capture analysis is a codegen concern (`/backend`). The typechecker infers the *type* of a closure; the backend determines *what* it captures.
   - Named functions as values (`(let [f inc] (f 5))`) already work via `infer_var` instantiation.

4. **`expr_types` completeness** (all chunks): Audit all `infer_*` methods to confirm `record_expr_type` is called for every expression. Add `debug_assert!` in `build_check_result` verifying no `Type::Var` remains unresolved in the final `expr_types`. The backend relies on `expr_types` + `HeapCategory::classify` for RC decisions — missing entries would cause silent codegen bugs.

5. **Deferred items**:
   - **M-3 (WarningKind)**: If `/arch` defines a `WarningKind` enum in Wave 1, switch `Warning` construction in the typecheck crate from bare `String` to the new enum. If `/arch` defers M-3, no action this sprint.
   - **M-5 (#[must_use])**: Add `#[must_use]` to all public `Result`-returning functions: `check_program`, `check_repl_input`, and any new public API surface.

**Output**:
- Updated `cranelisp-typecheck` crate: `adt.rs` (full ADT registration with polymorphic constructors), `infer.rs` (string lit inference, data constructor pattern bindings), `resolve.rs` (`TypeExpr::Applied` resolution with arity validation), `program.rs` (updated registration pipeline for parameterized types).
- Unit tests for each new capability (~30 minimum): polymorphic ADT registration, constructor scheme instantiation and verification, data constructor pattern type checking with bindings, `TypeExpr::Applied` resolution (valid + arity mismatch), string literal inference, exhaustiveness with mixed nullary/data constructors, shortcut syntax types.
- `#[must_use]` on public API functions.
- Updated `plan-typecheck.md` with Ring 1 section.

**Blocked by**: `/arch` Wave 1 (heap layout spec, closure environment layout, `TypeExpr::Applied` arity validation protocol, any `WarningKind` definition). Ring 0 typecheck crate (complete).

**Wave**: 2

**Acceptance**:
- `(deftype Point [:Int x :Int y])` registers with `TypeDefInfo` (2-field constructor) and constructor scheme `(Fn [Int Int] Point)`.
- `(deftype (Option a) None (Some [:a val]))` registers with polymorphic schemes: `None :: forall a. (Option a)`, `Some :: forall a. (Fn [a] (Option a))`.
- `(deftype Pair [first second])` shortcut syntax produces polymorphic product constructor.
- `TypeExpr::Applied` resolves: annotation `:(Option Int)` yields `Type::ADT("Option", [Type::Int])`. Arity mismatch `:(Option Int Bool)` returns `TypeError`.
- Constructor patterns with bindings type-check: `(match (Some 1) [(Some x) x None 0])` infers `x : Int`, result type `Int`.
- Exhaustiveness handles mixed constructors: match on `(Option a)` missing `None` reports non-exhaustive error.
- String literal `"hello"` infers as `Type::String` and appears in `expr_types`.
- Lambda `(fn [x] (+ x 1))` records `Type::Fn([Int], Int)` in `expr_types`.
- All `expr_types` in `CheckResult` are fully resolved (no `Type::Var`) — verified by `debug_assert!`.
- All Ring 0 unit tests pass unchanged (regression).
- `cargo clippy` clean on `cranelisp-typecheck`.
- ~30 new unit tests covering the above.

### /backend
**Input**: `/arch` Wave 1 deliverables (heap layout byte-level spec, closure environment layout, string representation decision, REPL display interface for heap types); `/typecheck` Ring 1 type information in `CheckResult` (ADT `TypeDefInfo` with field types, `expr_types` containing `Type::String`, `Type::ADT`, `Type::Fn` for heap classification); `/platform` runtime intrinsics (`cranelisp_alloc`, `cranelisp_free`, RC dec/free functions) from `cranelisp-runtime`.

**Task**:

Chunk A — Heap foundation + strings:
1. **Intrinsic registration**: Register `cranelisp_alloc`, `cranelisp_free`, RC intrinsics (`cranelisp_dec_guarded`, `cranelisp_dec_closure_guarded`, `cranelisp_dec_mixed_guarded`, `cranelisp_rc_underflow_check`), and string extern primitives (`cranelisp_str_concat`, `cranelisp_str_eq`, `cranelisp_int_to_string`, etc.) on the `JITBuilder`. Create an `IntrinsicRegistry` struct as the single source of truth for all runtime function declarations (addresses cache audit HIGH-1).
2. **Heap classification integration**: Use `HeapCategory::classify()` from `cranelisp-types` and `expr_types` from `CheckResult` to determine which values need RC management at every expression node.
3. **RC emission**: Implement `emit_rc_inc(ptr)` and `emit_rc_dec(ptr, type)` helpers in codegen. Inc: load from `ptr - 8`, add 1, store back. Dec: call the appropriate `cranelisp_dec_*` runtime function based on type (plain for strings, closure-guarded for closures, mixed-guarded for ADTs with both nullary and data constructors). Implement scope-level dec: track heap-typed bindings in a scope stack (`push_scope`/`pop_scope`), emit dec for all live heap bindings at scope exit via `pop_scope_for_value(result)` which skips the returned value.
4. **Drop glue functions**: Emit JIT-compiled drop glue functions per type. Each drop glue loads heap-typed fields from the dying object, emits dec for each, then calls `cranelisp_free`. The drop glue function pointer is passed to `cranelisp_dec_guarded` so the runtime can call it when rc reaches zero. For strings, drop glue is null (just free). For ADTs with heap fields, drop glue loads each field and decs it. For closures, drop glue loads each captured heap value and decs it.
5. **Consuming calling convention**: Callee owns heap-typed parameters (tracked in scope stack, dec'd at scope exit). Caller emits inc for non-last-use heap args; transfers ownership (no inc) for last-use args; temp expressions transfer ownership directly (no inc needed). Implement `emit_consuming_caller_rc()`.
6. **Last-use optimization**: Implement liveness analysis to identify the final use of each variable binding within a function body. At last-use sites, mark the variable consumed (skip scope-exit dec on caller side) so ownership transfers without redundant inc/dec pairs.
7. **String codegen**: Compile `Expr::StringLit` by calling `cranelisp_alloc` to allocate `[length | bytes...]`, store length at offset 0, copy UTF-8 bytes at offset 8 (using `iconst` + `store` for small strings, or an extern helper for larger ones). Compile string extern primitives (`str-concat`, `str-eq`, `int-to-string`, `float-to-string`, `str-len`) as `ResolvedCall::BuiltinFn` dispatching to extern function calls via declared `FuncId`s.
8. **`CRANELISP_RC_TRACE` diagnostic output**: The runtime handles trace logging internally. The backend's role is to pass type/source information to the runtime intrinsics where applicable, and to ensure the `CRANELISP_RC_TRACE` env var check happens at `Jit::new()` to gate any backend-side tracing overhead.

Chunk B — ADTs with fields:
9. **Data constructor codegen**: For constructors with fields, call `cranelisp_alloc(8 * (1 + n_fields))`, store tag at offset 0, store each compiled field value at offset `8 * (i + 1)`. Nullary constructors remain bare i64 tags (Ring 0 behavior preserved, accretive). Use `type_defs` and `constructor_to_type` from `CheckResult` to look up constructor metadata.
10. **Match with field extraction**: Extend `compile_match` in `match_codegen.rs` to handle `Constructor { bindings }` with non-empty bindings. For data constructors: load tag from `ptr + 0`, compare with expected tag; on match, load each field from `ptr + 8 * (i + 1)` and bind to pattern variables via `def_var`. Emit RC inc for extracted heap-typed fields (they gain a new reference via the binding). Mixed nullary/data discrimination: check `scrutinee < NULLARY_TAG_THRESHOLD` for nullary path, else load tag from heap for data path. Use `arm_blocks[i+1]` as fallthrough target (not separate next blocks, per prototype gotcha).
11. **Field accessor codegen**: Compile accessor calls (`.field_name` syntax resolved by `/typecheck` into `BuiltinFn` or accessor function references) as loads from the field's known offset within the constructor layout.
12. **ADT drop glue**: Emit per-type drop glue functions. For each constructor with heap-typed fields: load field at known offset, call the appropriate dec (which may recursively invoke nested drop glue), then free the outer object. Use `expr_types` to determine concrete field types for polymorphic ADTs.

Chunk C — Closures:
13. **Closure compilation**: Compile `Lambda` with captures. (a) Emit an inner function with signature `(env_ptr, params...) -> i64` that loads captured values from the environment at known offsets (`env_ptr + 8 * (i + 1)` for capture `i`, since offset 0 is the code pointer). The inner function's body compiles with the captured variables bound from these loads. (b) At the lambda expression site, call `cranelisp_alloc(8 * (1 + n_captures))`, store the inner function pointer at offset 0, store each captured value at offset `8 * (i + 1)`. The resulting pointer is the closure value.
14. **Closure call codegen**: In `compile_apply` (`apply.rs`), when the callee is a closure value (detected via `expr_types` as `Type::Fn` and not a known direct function), emit: load `code_ptr` from `closure_ptr + 0`, build a signature with `(n_params + 1)` i64 args (env_ptr first), then `call_indirect(sig_ref, code_ptr, [closure_ptr, arg_0, ..., arg_n])`.
15. **Named functions as values**: When a top-level function is referenced as a value (e.g., `(let [f add-i64] ...)` or passed as an argument), generate a closure wrapper: allocate `[wrapper_code_ptr]` (one slot, zero captures). The wrapper function has signature `(env_ptr, params...) -> i64`, ignores `env_ptr`, and tail-calls the real function directly. This ensures all function values have uniform closure representation.
16. **Closure RC**: When storing captured values into the environment, emit RC inc for each heap-typed capture (the closure gains a new reference). Closure drop glue loads each capture slot and emits dec for heap-typed captures before freeing the environment. Closures participate in the consuming calling convention as heap values.
17. **Activate ignored Ring 0 lambda tests**: The 11 tests ignored in Ring 0 (lambda as value, higher-order functions, operator as value) should now pass with closure codegen in place.

Deferred items from Sprint 1:
18. **M-1 resolution**: Remove `NULLARY_TAG_THRESHOLD` definition from `cranelisp-backend/src/codegen_types.rs` and import from `cranelisp_types::NULLARY_TAG_THRESHOLD` instead. Single-line fix.
19. **M-5 `#[must_use]`**: Add `#[must_use]` attribute to all public `Result`-returning functions in `cranelisp-backend` (`compile_program`, `compile_and_run_expr_with_got`, `Jit::new`, `Jit::compile_defn`, `Jit::finalize_and_get_ptr`, etc.).

REPL display:
20. **`format_result` extension**: Extend `format_result` in `src/repl.rs` to display heap types. Strings: read length from `ptr + 0`, read UTF-8 bytes from `ptr + 8`, display as `:String "contents"`. ADTs: read tag from `ptr + 0`, look up constructor name in `TypeDefInfo`, read fields, recursively format each field, display as `:(Option Int) (Option.Some 42)`. Closures: display as `:(Fn [Int] Int) <closure>` (no heap introspection needed, just type info). Requires `TypeDefInfo` to be passed to `format_result`.

**Output**:
- `cranelisp-backend/src/compiler/heap.rs` — alloc emission, RC inc/dec helpers, drop glue generation, scope stack, consuming convention, last-use analysis
- `cranelisp-backend/src/compiler/closure.rs` — closure compilation (inner function + environment allocation), closure call emission, named-function-as-value wrapping
- `cranelisp-backend/src/compiler/string.rs` — string literal codegen, string primitive extern dispatch
- `cranelisp-backend/src/compiler/match_codegen.rs` — extended for constructor patterns with field bindings and mixed nullary/data discrimination
- `cranelisp-backend/src/compiler/apply.rs` — extended for closure calls (`call_indirect`) and consuming calling convention at call sites
- `cranelisp-backend/src/jit.rs` — `IntrinsicRegistry` struct, all runtime intrinsic declarations
- `cranelisp-backend/src/codegen_types.rs` — `NULLARY_TAG_THRESHOLD` removed (M-1), `#[must_use]` added (M-5)
- `src/repl.rs` — `format_result` extended for String, ADT, and closure display
- Unit tests for each new codegen module (heap helpers, closure compilation, string codegen, match-with-fields, drop glue, scope stack)

**Blocked by**: `/arch` Wave 1 (heap layout byte-level spec, closure environment layout decision, string representation decision, REPL display interface for heap types); `/platform` Wave 2 (runtime intrinsics in `cranelisp-runtime`: `cranelisp_alloc`, `cranelisp_free`, `cranelisp_dec_guarded` variants, string extern functions)

**Wave**: 2 (parallel with `/frontend`, `/typecheck`, `/platform`)

**Acceptance**:
- All Ring 0 tests still pass (regression gate)
- String literals compile, execute, and display correctly: `"hello"` round-trips through codegen
- String primitives (`str-concat`, `str-eq`, `int-to-string`) produce correct results
- ADT data constructors allocate on heap: `(Some 42)` stores `[tag=1, 42]` via `cranelisp_alloc`
- Match with field extraction: `(match (Some 1) [(Some x) x None 0])` returns `1`
- Mixed nullary/data match: correctly discriminates `None` (bare tag) from `(Some v)` (heap pointer)
- Field accessors compile and execute correctly
- Closures capture variables: `(let [n 5] (fn [x] (+ n x)))` returns a closure value
- Closure calls: `((fn [x] (+ x 1)) 5)` returns `6`
- Higher-order functions: `(let [f (fn [x] (* x x))] (f 7))` returns `49`
- Named functions as values: `(let [f add-i64] (f 1 2))` returns `3`
- 11 previously-ignored Ring 0 lambda tests now pass
- `CRANELISP_RC_TRACE=1` shows balanced alloc/inc/dec/free for all heap tests
- No memory leaks: `LIVE_ALLOCS` tracking confirms every alloc is paired with a free
- ADT drop glue correctly frees nested heap values: `(Some "hello")` frees both the `Some` wrapper and the `String`
- Closure drop glue correctly decs captured heap values before freeing the environment
- `format_result` displays strings as `:String "hello"`, ADTs as `:(Option Int) (Option.Some 42)`, closures as `:(Fn [...] ...) <closure>`
- `#[must_use]` on all public `Result`-returning functions in `cranelisp-backend`
- `NULLARY_TAG_THRESHOLD` imported from `cranelisp-types`, not defined in backend (M-1 resolved)
- No function exceeds 100 lines; no `unwrap()` in pipeline code; `cargo clippy` clean

### /platform
**Input**: `/arch` Wave 1 heap layout spec (byte-level header, alignment, return pointer); `/arch` string representation decision (Rust-managed via extern functions vs. inline); `/arch` closure environment layout decision (fn_ptr + env_ptr pair, calling convention)
**Task**: Expand `cranelisp-runtime` from its Ring 0 stub (panic only) to full Chunk A heap infrastructure, plus the RC runtime support needed by Chunks B and C:
1. **Allocator**: `cranelisp_alloc` (extern "C") and `cranelisp_free` — heap layout `[total_size: i64][rc: i64][payload...]`, 8-byte alignment, payload pointer returned. Rust-callable `alloc_with_rc(size)` shared helper.
2. **Allocation tracking**: `ALLOC_COUNT`, `DEALLOC_COUNT`, `BYTES_ALLOCATED`, `BYTES_CURRENT`, `BYTES_PEAK` atomic counters. `LIVE_ALLOCS: Mutex<HashSet<usize>>` for double-free detection (debug builds only via `cfg(debug_assertions)`). `reset_counts()` for test isolation.
3. **RC primitives**: `cranelisp_dec_guarded(val, guard, drop_fn_ptr)` — guarded decrement with nullary tag skip (val < 1024), atomic Release dec, Acquire fence before free, drop function dispatch. `cranelisp_dec_closure_guarded(val, guard)` — closure-specific variant loading drop_ptr from closure layout slot. `cranelisp_dec_mixed_guarded(val, guard, drop_fn_ptr)` — mixed nullary/data ADT variant. `cranelisp_rc_underflow_check(val, old_rc)` — debug_assert underflow detection + RC trace logging.
4. **RC trace logging**: `CRANELISP_RC_TRACE=1` env var enables stderr logging of every alloc/free/inc/dec with pointer address and RC value. Gated behind `cfg(debug_assertions)`.
5. **String primitives**: `alloc_string(bytes)` Rust helper (layout: `[len: i64][bytes: u8...]`). Extern functions: `str-concat(a, b)`, `str-eq(a, b)`, `int-to-string(value)`, `float-to-string(value)`, `bool-to-string(value)`, `string-identity(value)`, `parse-int(ptr)` (returns Option Int ADT: bare tag 0 for None, heap `[tag=1, n]` for Some).
6. **Panic handler**: Retain existing `cranelisp_panic` with `extern "C-unwind"` + `panic!()` design from Ring 0. No changes needed — the catch_unwind boundary in the binary crate handles recovery. Ring 1 runtime errors (double-free, RC underflow) use `debug_assert!` only.
7. **Crate structure**: Organize `cranelisp-runtime/src/` into submodules: `intrinsics.rs` (alloc, free, RC primitives), `primitives.rs` (module root + `alloc_string` helper), `primitives/int.rs`, `primitives/float.rs`, `primitives/bool.rs`, `primitives/string.rs`. Move existing panic handler into `intrinsics.rs`, re-export from `lib.rs`.

**Output**:
- `cranelisp-runtime` crate with full Chunk A heap infrastructure: allocator, RC primitives, string primitives, allocation tracking, RC trace logging
- All functions exported as `extern "C"` with `#[unsafe(export_name = "...")]` for JIT symbol resolution
- Unit tests for every exported function (alloc/free round-trip, RC dec to zero triggers free, guarded dec skips guard value, guarded dec skips nullary tags, string concat/eq, int/float/bool to-string, parse-int Some/None cases, RC trace output, LIVE_ALLOCS double-free detection)
- Public Rust API: `alloc_with_rc()`, `alloc_string()`, `alloc_count()`, `dealloc_count()`, `bytes_current()`, `reset_counts()`, `is_live()` for use by `/qa` integration tests and future runtime modules
**Blocked by**: `/arch` Wave 1 (heap layout byte-level spec, string representation decision)
**Wave**: 2
**Acceptance**:
- `cargo test -p cranelisp-runtime` passes with all unit tests green
- `CRANELISP_RC_TRACE=1 cargo test -p cranelisp-runtime` shows balanced alloc/free traces
- `alloc_with_rc` + `cranelisp_free` round-trip: alloc_count == dealloc_count, bytes_current == 0
- `cranelisp_dec_guarded` with drop_fn_ptr=0 frees on rc=0; with non-zero drop_fn_ptr calls the drop function
- `cranelisp_dec_guarded` skips when val==guard or val<1024 (nullary tags)
- String primitives produce correct heap strings (verified by reading back length + bytes)
- `parse-int` returns None (tag 0) for non-numeric, Some (heap `[1, n]`) for valid integers
- No `unwrap()` in non-test code (per `src/CLAUDE.md`); `cargo clippy -p cranelisp-runtime` clean
- Vec primitives NOT included (deferred to Sprint 3 with Chunk D)
- `cranelisp-platform` NOT modified (C-ABI contract deferred to Ring 2)

### /qa
**Input**: Ring 1 compiler crates from `/frontend`, `/typecheck`, `/backend`, `/platform` (Chunks A+B+C); Ring 1 interface types from `/arch`; existing Ring 0 pipeline (`compile_and_run`, `repl_session`) and 102 Ring 0 tests (12 ignored)
**Task**:
1. **Pipeline wiring** — Extend `compile_and_run` / `compile_unit()` for heap types: wire runtime allocator, RC primitives, drop glue, and closure compilation into the batch and REPL pipelines. Ensure `format_result` can display String, ADT, and closure values (`:primitives/String "hello"`, `:(user/Option primitives/Int) (Option.Some 42)`, `:(Fn [...] ...) <closure>`).
2. **Activate ignored tests** — Remove `#[ignore]` from the 12 Ring 0 lambda/closure tests once Chunk C (closures) lands. Verify they pass in both batch and REPL modes.
3. **New test helpers** — Implement `assert_rc_balanced(src)` helper: runs with `CRANELISP_RC_TRACE=1`, parses alloc/inc/dec/free events, asserts all allocations are freed and no double-frees occur. Implement `compile_and_run_heap(src) -> (i64, Type, String)` helper that returns the formatted display string for heap-typed results.
4. **Integration tests (~105 new in `tests/ring1.rs`)** covering:
   - **Strings (~15)**: string literals, `str-concat`, `str-eq`, `int-to-string`, string in let bindings, string as function argument/return, string comparison, string display in batch and REPL
   - **ADT products (~15)**: product type construction and match, field accessors, accessor as first-class value, first-class constructors, shortcut syntax, multi-field products, nested let with products, products as function arguments/returns, product display
   - **ADT sums (~15)**: sum type construction and match, `Option`-style Some/None, polymorphic ADT `(Option a)` instantiation, wildcard patterns, variable patterns, nested match, sum accessors, sum display
   - **Closures (~20)**: simple capture, multiple captures, closure returned from function, nested closures, higher-order functions, named function as value, zero-param lambda, multi-param lambda, closure with ADT capture, closure returning ADT, closure display
   - **Exhaustiveness (~8)**: non-exhaustive match compile error (or runtime panic), exhaustive with all constructors, exhaustive with wildcard, exhaustive with var pattern, missing None for Option, product type exhaustiveness
   - **Dual-mode parity (~15)**: `compile_both` for strings, ADTs (product + sum), closures, higher-order functions, match with field bindings — every major Ring 1 feature verified in batch + REPL
   - **Error paths (~10)**: type error in ADT constructor args, wrong constructor for match, unbound field accessor, closure arity mismatch, string passed where Int expected, ADT type parameter mismatch
   - **Let-polymorphism with closures (~7)**: let-bound identity at multiple types, polymorphic higher-order, let-bound lambda with capture
5. **RC correctness tests (~35 new in `tests/rc.rs`, serial `--test-threads=1`)** covering:
   - **String RC (~8)**: string alloc and drop, string in let (freed on scope exit), string passed to function (consuming convention), string concat intermediate freed, string in if branches (only one path allocated), string returned from function (ownership transfer)
   - **ADT RC (~12)**: product with heap fields (nested drop glue), sum with heap variant (`(Some "hello")` drops wrapper + string), ADT in let scope, ADT returned from function, ADT in match arms (consumed correctly), ADT with multiple heap fields, ADT constructor in temporary position
   - **Closure RC (~10)**: closure env alloc and drop, closure capturing string (string freed when closure freed), closure capturing ADT, multiple closures sharing captured value (inc/dec balance), closure passed to function, closure returned from function (env survives), closure in let scope
   - **Cross-cutting RC (~5)**: closure capturing ADT containing string (3-level nesting), ADT containing closure, string built from ADT field then ADT dropped, function returning closure that captures string argument
6. **Batch/REPL parity audit** — Verify that every Ring 1 integration test that runs in batch also produces identical results in REPL. Use `compile_both` for value-returning tests. For display-format tests, verify REPL output matches spec.
7. **Test suite runtime stewardship** — Measure full suite time after Ring 1. Flag any test exceeding 100ms. Target: all non-ignored tests complete in under 10s. Report runtime in wave completion notes.
8. **Usability register triage** — Process any Ring 1 findings filed by `/examples`, `/docs`, `/repl`, `/stdlib`, `/port`, `/platform`. Triage as blocking/important/deferred and route to responsible skill.

**Output**:
- `tests/ring1.rs` — ~105 integration tests (strings, ADTs, closures, exhaustiveness, errors, parity)
- `tests/rc.rs` — ~35 RC correctness tests (serial)
- Updated `tests/helpers/mod.rs` — `assert_rc_balanced`, `compile_and_run_heap` helpers
- 12 previously-ignored lambda tests activated (in `tests/ring0.rs`)
- Pipeline extensions in `src/` for heap type display
- Wave completion report with test counts and suite runtime
- Usability register updated with any Ring 1 findings

**Blocked by**: `/frontend` + `/typecheck` + `/backend` + `/platform` (Wave 2 compiler crates); `/arch` (Wave 1 interfaces for heap layout, closure env, string repr, display interface)
**Wave**: 3
**Acceptance**:
- All 12 previously-ignored lambda tests pass (batch + REPL)
- ~140 new tests green (~105 integration + ~35 RC)
- All 102 Ring 0 tests still pass (regression gate)
- `CRANELISP_RC_TRACE=1 cargo test --test rc -- --test-threads=1` shows balanced alloc/free for every test
- `compile_both` parity verified for all Ring 1 feature categories
- Full test suite (Ring 0 + Ring 1) completes in under 10s
- No blocking usability findings open in `tests/plan/usability.md`

### /spec
**Input**: Deferred items M-6 and F-1 from Sprint 1; Ring 1 feature scope (heap, strings, ADTs with fields, closures); FIXME in `spec/06-pattern-matching.md` line 225
**Task**:
1. Resolve M-6: add `not` primitive to `spec/appendix-a-builtins.md` §A.3 inline primitives as `not :: (Fn [Bool] Bool)` with description "Boolean negation". The primitive is already implemented in the compiler (`cranelisp-types/src/operator.rs`, `cranelisp-backend/src/operators.rs`) -- this is a spec-only gap.
2. Resolve F-1: update `spec/06-pattern-matching.md` §6.5 to require that `match` on non-ADT scrutinee types (`Int`, `Bool`, `Float`, `String`, function types, type variables) MUST include a wildcard or variable pattern (since these types have no finite set of constructors to enumerate). Remove the existing FIXME comment. A `match` on a non-ADT type without a catch-all arm is a compile-time error.
3. Reactive: arbitrate spec ambiguities raised by `/frontend`, `/typecheck`, `/backend`, or `/qa` during Ring 1 implementation -- particularly around ADT field semantics, string representation, closure capture semantics, and RC ownership conventions. Consult the sketch oracle as needed (`cd sketch && cargo run -- --run <example>`).
**Output**:
- Updated `spec/appendix-a-builtins.md` with `not` entry
- Updated `spec/06-pattern-matching.md` §6.5 with non-ADT exhaustiveness rule, FIXME removed
- Any additional spec clarifications prompted by Ring 1 implementation questions
**Blocked by**: None (M-6 and F-1 have no dependencies; reactive work triggers on demand)
**Wave**: 3 (spec updates land alongside `/qa` integration tests; reactive arbitration available from Wave 1 onward)
**Acceptance**:
- `not` appears in `spec/appendix-a-builtins.md` §A.3 with correct type signature `(Fn [Bool] Bool)`
- `spec/06-pattern-matching.md` §6.5 defines exhaustiveness for non-ADT scrutinee types (wildcard/variable required)
- FIXME comment at §6.5 line 225 is removed
- No open FIXME comments addressed to `/spec` remain in files touched this sprint

### /examples
**Input**: Ring 1 compiler (Chunks A+B+C), updated `design/arch/interfaces.md` for heap types, passing `/qa` integration tests for strings, ADTs with fields, and closures
**Task**: Write examples 09–13 from the learning sequence (`examples/plan-examples.md`), covering Ring 1 features delivered in this sprint. Each example introduces one concept, uses only features from prior examples, and follows the existing batch-mode format (integer `main` return for verification). Specifically:
- `09-strings.cl` — String literals, `str-concat`, `int-to-string`; result verified via string length or boolean conversion of `str-eq`
- `10-adts.cl` — Product types (`deftype Point [:Int x :Int y]`), sum types with data (`deftype (Option a) None (Some [:a val])`), polymorphic ADTs, shortcut syntax (`deftype Pair [first second]`); constructors and field accessors
- `11-destructuring.cl` — Pattern matching on data constructors: `(match (Some 42) [(Some x) x None 0])`, product destructuring, nested patterns, wildcard in data match
- `12-closures.cl` — Anonymous functions `(fn [x] (+ x 1))`, variable capture `(let [y 10] (fn [x] (+ x y)))`, closures as return values
- `13-higher-order.cl` — Functions as arguments (`defn apply-twice [f x] (f (f x))`), functions returning functions (`defn make-adder [n] (fn [x] (+ n x))`), composing higher-order patterns

Update `examples/plan-examples.md` §4 "Ring 1 Examples" from outline to concrete code. File usability findings to `/qa`'s usability register if ADT definition syntax, pattern matching ergonomics, string operations, closure capture, or error messages reveal friction from a learner's perspective.

**Note on numbering**: The existing examples 01–08 were delivered in Sprint 1. The plan originally numbered Ring 1 examples starting at 11, but examples 16 (Vectors) and 17 (Lists) are deferred with Vec to Sprint 3. The delivered files will be renumbered 09–13 to maintain a contiguous sequence; the plan will be updated to reflect the new numbering.

**Output**:
- 5 new example files: `examples/09-strings.cl` through `examples/13-higher-order.cl`
- Updated `examples/plan-examples.md` with concrete Ring 1 code (replacing outlines)
- Usability findings filed to `tests/plan/usability.md` (if any)

**Blocked by**: `/qa` Wave 3 (pipeline wiring and integration tests for Chunks A+B+C must pass before examples can be validated against the compiler)
**Wave**: 4
**Acceptance**:
- All 5 new examples compile and run correctly via `cargo run -- --run examples/NN-name.cl`
- Each example returns the expected integer from `main`
- Each example introduces exactly one new Ring 1 concept and uses only features from prior examples
- Ring 1 acceptance criteria from `design/arch/roadmap.md` are exercised: string literals, polymorphic ADT constructors, data-constructor match, closures with capture, higher-order function application
- No regressions: existing examples 01–08 continue to pass

### /docs
**Input**: Working Ring 1 pipeline (Wave 3), `user/plan-docs.md`, `user/getting-started.md`, spec sections 01, 03, 04, 05, 06
**Task**: Update user-facing documentation for Ring 1 features (Chunks A+B+C). Three deliverables:

1. **Update `user/getting-started.md`**: Add sections covering strings (literals, `str-concat`, `str-eq`), ADTs with fields (product types, sum types, `Option`, constructor patterns in match), and closures (`fn`, functions as values, higher-order functions). Update the "What is Next" section to reflect Ring 1 as delivered. Ensure all examples are accurate against the working Ring 1 compiler.

2. **Draft tutorial curriculum sections 14--18, 21** (from `user/plan-docs.md`): Write section/prompt/trigger/answer definitions for the 6 Ring 1 tutorial sections that correspond to Chunks A+B+C:
   - 14 `text` -- string literals and string primitives
   - 15 `data-types` -- product types with fields
   - 16 `sum-types` -- sum types with data constructors
   - 17 `maybe` -- Option type (None/Some)
   - 18 `matching-data` -- pattern matching on data constructors
   - 21 `functions-as-values` -- closures, fn, passing functions

   Defer sections 19 (collections/Vec), 20 (lists), 22 (map-filter-reduce) to Sprint 3 since Vec is deferred.

3. **File usability findings**: Exercise Ring 1 features from a beginner perspective. File findings to the usability register (`tests/plan/usability.md`) for error messages that are confusing when working with ADTs, closures, or strings; REPL display issues for heap types; learning curve gaps where a concept has no good introduction path.

**Output**: Updated `user/getting-started.md` with Ring 1 content; `user/tutorial/curriculum.md` with sections 14--18 and 21; usability findings filed
**Blocked by**: `/qa` (Wave 3) -- needs working pipeline with Ring 1 features to verify documentation accuracy
**Wave**: 4
**Acceptance**: All REPL transcripts in `getting-started.md` are verified against the working compiler. Tutorial sections cover strings, product types, sum types, Option, constructor pattern matching, and closures. No Ring 1 features from Chunks A+B+C are undocumented. Usability findings (if any) filed to register.

### /repl
**Input**: Ring 1 compiler (Chunks A+B+C) delivering string values, ADTs with fields, and closures; `format_result` extended for heap types; `repl/spec.md` Ring 1 requirements (sections 1.2, 1.5)
**Task**: Extend `tests/repl_experience.rs` with Ring 1 REPL experience tests covering four areas: (1) **String display** — string literal evaluation displays `:String "contents"` with escape handling; string primitives (`str-concat`, `str-eq`, `int-to-string`) return correct types; format_result renders strings with surrounding quotes. (2) **ADT display** — data constructors display as `:(Option Int) (Option.Some 42)` with recursive field formatting; product types display all fields `:(Point) (Point 3 4)`; polymorphic ADT type parameters appear in type display; nested heap fields in ADTs display recursively (e.g., `(Some "hello")`). (3) **Closure display** — lambda expressions display as `:(Fn [Int] Int) <closure>`; closures with captures evaluate correctly and display the `<closure>` sentinel; named functions passed as values display appropriately. (4) **Error quality for heap types** — type errors involving heap types mention expected/actual types clearly (e.g., passing a String where Int is expected); pattern match exhaustiveness errors for sum types with data constructors are actionable; closure arity mismatches produce clear messages; errors involving polymorphic ADTs show the parameterized type. Also add session continuity tests: define ADTs then closures over them, trigger an error in between, verify all definitions and heap state survive. File usability findings to `tests/plan/usability.md` for any display format gaps, unhelpful error messages, or missing type information encountered during test design.
**Output**: 20-30 new tests in `tests/repl_experience.rs` (Ring 1 sections); usability findings filed if any
**Blocked by**: `/backend` (heap infrastructure, closure compilation, `format_result` for heap types), `/typecheck` (ADT type checking, String type), `/qa` (pipeline wiring for Ring 1)
**Wave**: 4
**Acceptance**: All new Ring 1 REPL experience tests pass; string/ADT/closure display formats match `repl/spec.md` section 1.5; error messages for heap type mismatches include expected and actual types; session state survives errors between heap-type definitions; no open blocking usability findings from `/repl`

### /review
**Input**: Completed crate code from `/frontend`, `/typecheck`, `/backend`, `/platform` (Wave 2); Ring 0 report (`design/review/ring0-report.md`); prototype audit files (`sketch/audits/*.md`); `/arch` Wave 1 heap layout and closure environment specs
**Task**:
1. **Ring 1 checklist** (Wave 1, parallel with `/arch`): Write `design/review/ring1-checklist.md` derived from Ring 1 scope (heap allocation, RC, strings, ADTs with fields, closures). Key sections:
   - RC correctness: every `emit_inc` has a matching `emit_dec` or ownership transfer; no double-free, no leak; `CRANELISP_RC_TRACE` balanced for all test programs
   - Consuming calling convention: callee owns heap params; last-use optimization correct; captures never last-use transferred
   - Drop glue: generated for every heap-containing ADT; recursive dec for nested heap fields; nullary constructors skip drop
   - Closure lifecycle: env allocation has RC header; captured variables inc'd at capture; env dec'd when closure is dec'd; drop glue walks captures
   - Heap layout consistency: header layout (total_size at base+0, rc at base+8, data at base+16) uniform across strings, ADTs, closures, with no off-by-one in field offsets
   - `unsafe` code audit criteria: every `unsafe` block has `// SAFETY:` comment; raw pointer arithmetic confined to small wrapper functions; JIT fn-pointer casts validate calling convention and non-null; `unsafe impl Send/Sync` justified
   - Ring 0 deferred items: verify M-1 (NULLARY_TAG_THRESHOLD dedup), M-2 (CheckResult fields in interfaces.md), M-3 (WarningKind enum if warnings emitted), M-5 (#[must_use] annotations)
2. **Per-crate reviews** (Wave 2.5): Review each compiler crate's Ring 1 additions against `ring1-checklist.md` and `checklist.md`. Produce findings (HIGH/MEDIUM/LOW) reported to owning skills. Focus areas by crate:
   - `cranelisp-runtime`: alloc/free correctness, RC primitives, `LIVE_ALLOCS` leak detection, no `unwrap()` in runtime paths
   - `cranelisp-types`: new boundary types for heap (HeapCategory usage, ADT TypeDefInfo with fields, closure Type representation), serde derives
   - `cranelisp-frontend`: string literal parsing, ADT syntax with type params and fields, lambda capture detection (if frontend-visible)
   - `cranelisp-typecheck`: ADT type checking (product + sum + polymorphic), exhaustiveness with data constructors, String type inference, closure type inference
   - `cranelisp-backend`: RC emission (inc/dec/drop glue), heap allocation codegen, closure compilation (env allocation, capture loading, env RC), ADT constructor codegen (field storage, tag + heap layout), consuming calling convention, scope cleanup correctness, `unsafe` blocks
   - `cranelisp-platform`: runtime crate extensions (alloc, RC primitives, panic handler ABI -- verify H-1 fix)
3. **Ring gate review** (Wave 5): Full ring-completion assessment. Write `design/review/ring1-report.md` covering:
   - Ring 1 checklist evaluation (all items checked or waived with rationale)
   - General checklist evaluation
   - Per-crate quality assessment
   - RC correctness verdict: `CRANELISP_RC_TRACE=1` shows balanced inc/dec across all test programs; `LIVE_ALLOCS` reports zero leaks; no double-frees
   - Audit debt disposition: verify no HIGH prototype audit findings reintroduced (especially codegen HIGH-1 FnCompiler duplication, HIGH-2 heap classification duplication, module HIGH-1 god object)
   - Ring 1 acceptance criteria verification (from `design/arch/roadmap.md`)
   - Conditions for gate clearance (MUST/SHOULD/MAY)
   - Recommendations for Ring 2
**Output**:
- `design/review/ring1-checklist.md` (Wave 1)
- Per-crate review findings reported to owning skills (Wave 2.5)
- `design/review/ring1-report.md` with gate verdict (Wave 5)
**Blocked by**: Wave 1 (`/arch` heap layout specs) for checklist; Wave 2 (compiler skills) for per-crate reviews; Wave 4 (user-proxy validation) for ring gate
**Wave**: 1 (checklist), 2.5 (per-crate reviews), 5 (ring gate)
**Acceptance**:
- `ring1-checklist.md` covers all Ring 1 concerns (RC, closures, ADT heap, strings, drop glue, `unsafe` audit, deferred items)
- Every compiler crate reviewed with findings delivered to owning skill; zero unacknowledged HIGH findings at gate time
- `ring1-report.md` produced with explicit PASS/PASS WITH CONDITIONS/FAIL verdict
- All Ring 0 deferred items (M-1, M-2, M-3, M-5) tracked to resolution or re-deferral with rationale

### /stdlib
**Input**: Ring 1 compiler (Chunks A+B+C complete), `lib/plan-stdlib.md`, `design/arch/interfaces.md`, `spec/07-traits.md`
**Task**: Review the Ring 1 compiler from the stdlib author's perspective. Validate that heap types (String, ADTs, closures) have the runtime representations, primitives, and error messages needed for stdlib development starting at Ring 2. Specifically:

1. **String primitive audit** — Verify that all string primitives needed by `text/string.cl` and `text/display.cl` are available or specified: `str-concat`, `str-eq`, `int-to-string`, `float-to-string`, `str-len`, `substring`, `char-at`. Identify any missing primitives that will block Ring 2 stdlib modules. File findings to usability register.
2. **ADT representation review** — Confirm that product types, sum types, polymorphic ADTs, and constructor patterns work as `fn/option.cl`, `fn/result.cl`, and `collections/list.cl` will need them. Pay attention to: nested ADT RC (e.g., `(List (Option Int))`), constructor arity in match patterns, field accessor generation. File findings.
3. **Closure capability check** — Verify that closures support the patterns needed by `fn/compose.cl` and `collections/functor.cl`: functions as values, higher-order function arguments, closure capture of heap types (String, ADT). File findings.
4. **Error message quality** — Exercise type errors, match exhaustiveness failures, and constructor misuse from a library author's perspective. Flag unhelpful or misleading messages that would confuse stdlib development.
5. **Update `lib/plan-stdlib.md`** — Annotate the Ring 2 build order (Section 5.3) with any adjustments based on Ring 1 findings. Add any new risks discovered.

No stdlib code is written this sprint. Ring 1 has no module system, so stdlib files cannot be loaded yet.

**Output**:
- Usability findings filed in `tests/plan/usability.md` (Ring 1 section, category: `missing API` / `error quality` / `ergonomics`)
- Updated `lib/plan-stdlib.md` with Ring 1 review notes and any risk adjustments
- Readiness assessment: go/no-go for Ring 2 stdlib development

**Blocked by**: Wave 2+3 (compiler skills and `/qa` must deliver Ring 1 compiler before stdlib can review it)
**Wave**: 4
**Acceptance**:
- At least one review pass through Ring 1 string primitives, ADT codegen, and closure support
- All blocking findings filed in usability register with actionable descriptions
- `lib/plan-stdlib.md` updated with review notes (even if "no issues found")
- No stdlib source files created (confirms Ring 1 = "nothing lights up" per plan)

### /port
**Input**: Ring 1 compiler (Chunks A+B+C complete), updated `design/arch/interfaces.md` for heap types
**Task**: Re-assess the Sudoku Solver exemplar against Ring 1 features. Update `exemplar/plan-exemplar.md` with a "Ring 1 Assessment" section (parallel to the existing Ring 0 Assessment) that evaluates which exemplar components become expressible with ADTs-with-fields, strings, and closures — and which gaps remain. Identify any design adjustments needed (e.g., if the `Cell`/`Grid`/`SolveResult` ADT shapes interact poorly with Ring 1 limitations like no traits, no modules, no Vec). File usability findings to `/qa` if ADT definition, pattern matching, string operations, or closure capture reveal friction during evaluation.
**Output**: Updated `exemplar/plan-exemplar.md` with Ring 1 Assessment section; usability findings filed if any
**Blocked by**: Wave 3 complete (pipeline wired, integration tests passing for ADTs + closures + strings)
**Wave**: 4
**Acceptance**: `exemplar/plan-exemplar.md` contains a Ring 1 Assessment section that (a) evaluates each exemplar module against Ring 1 capabilities, (b) identifies what becomes expressible vs what still blocks, and (c) notes any design adjustments for the exemplar based on Ring 1 realities

## Task List

| # | Wave | Skill | Task | Status | Blocked By |
|---|------|-------|------|--------|------------|
| 0a | 0 | /spec | Write `spec/appendix-c-nfr.md`: non-functional requirements — expanded to 22 NFRs across 6 sections (C.1–C.6) including C.2.4 (collection extensibility), C.4.4 (concurrent channels), C.5.3 (three-mode compilation), C.5.4 (target portability/WASM) | done | — |
| 0b | 0 | /arch | Write `design/arch/design-space.md`: two-part analysis — Part 1 (§1–9) Ring 1 decisions vs NFRs; Part 2 (§10–14) beyond-ring resilience: three-mode compilation, WASM, collection extensibility, concurrent channels, peer language patterns | done | 0a |
| 1 | 1 | /arch | Heap layout spec, closure env layout, string repr, extern primitives, display interface, M-2, M-3, emit helpers in `interfaces.md` (informed by design-space.md) | **done** | 0b |
| 2 | 1 | /review | Write `design/review/ring1-checklist.md` | **done** | — |
| 3 | 2 | /frontend | Remove Ring 0 rejection gates (StringLit), docstring audit, `#[must_use]`, ~15 unit tests, design docs in `design/frontend/` | **done** | — |
| 4 | 2 | /typecheck | String inference, full ADTs (polymorphic constructors, Applied resolution, pattern bindings, exhaustiveness), expr_types audit, M-3, M-5, ~30 unit tests, design docs in `design/typecheck/` | **done** | 1 |
| 5 | 2 | /backend | Chunk A (heap alloc, RC inc/dec/drop, consuming convention, last-use, string codegen), Chunk B (ADT constructor/match/accessor/drop glue), Chunk C (closure compile/call/RC, named-fn-as-value), M-1, M-5, format_result for heap types, design docs in `design/backend/` | **done** | 1, 6 |
| 6 | 2 | /platform | Expand cranelisp-runtime: allocator, alloc tracking, RC primitives, RC trace, string primitives, crate restructure, design docs in `design/platform/` | **done** | 1 |
| 7 | 2.5 | /review | Per-crate reviews against ring1-checklist + general checklist; design doc completeness assessment | **done** | 3, 4, 5, 6 |
| 7a | 2.5R | /backend | Address review findings F-1 (compile_apply length), F-3 (compile_defn params), plus F-5, F-8, F-9 | **done** | 7 |
| 7b | 2.5R | /arch | Address review finding F-2 (HeapCategory::classify ADT heuristic), plus F-4 (remove Type::is_heap) | **done** | 7 |
| 7c | 2.5R | /review | Re-review: confirm F-1, F-2, F-3 resolved, no new issues — **GATE PASSES** | **done** | 7a, 7b |
| 8 | 3 | /qa | Pipeline wiring (2 fixes), 104 integration tests (ring1.rs), 35 RC tests (rc.rs), 3 new helpers. 738 tests total, 2 ignored (parse-int ADT return) | **done** | 7c |
| 9 | 3 | /spec | M-6 (`not` in appendix-a), F-1 (non-ADT exhaustiveness in §6.5), reactive arbitration | **done** | — |
| 10 | 4 | /examples | 5 examples (09-strings, 10-adts, 11-destructuring, 12-closures, 13-higher-order), 13 example tests pass | **done** | 8 |
| 11 | 4 | /docs | Update getting-started.md (Ring 1 sections: strings, ADTs with fields, closures, higher-order, putting it together, primitives table), draft tutorial sections 14–18 + 21 in `user/tutorial/curriculum.md`, file usability findings U1.6, U1.7, U1.8 | **done** | 8 |
| 12 | 4 | /repl | 36 Ring 1 REPL experience tests (string/ADT/closure display, error quality, session continuity), filed U1.9 | **done** | 8 |
| 13 | 4 | /stdlib | Ring 1 capability review, updated plan-stdlib.md §9, filed U1.1–U1.5, GO verdict for Ring 2 | **done** | 8 |
| 14 | 4 | /port | Ring 1 Sudoku Solver assessment, updated plan-exemplar.md, filed U1.10–U1.11, Vec is critical blocker | **done** | 8 |
| 15 | 5 | /review | Ring 1 gate review — **PASS**. Report: `design/review/ring1-report.md` | **done** | 7, 8, 10, 11, 12, 13, 14 |
| 16 | 5+ | /qa | E2E test runner + 21 black-box subprocess tests (Layer 4). Ring 0: smoke, arithmetic, booleans, let, defn, recursion, conditionals, errors. Ring 1: strings, ADTs, matching, closures, higher-order. 2 multi-feature sessions. | **done** | 8 |

## Notes

### Sprint Planning Process

1. `/sprint` decomposes current ring into chunks — **done**
2. `/arch` selects chunks for this sprint — **done** (A + B + C; defer D)
3. Each skill contributes its own assignment section — **done**
4. `/sprint` consolidates into task list — **done**
5. User approves final plan → status changes to ACTIVE

### Wave 0 Expansion (beyond-ring analysis)

Task 0b was expanded after initial completion. The user identified that the design space analysis should cover not just Ring 1 decisions but broader architectural resilience:
- **Three-mode compilation**: dev (JIT/REPL), quick build (link cached .o), release (LLVM global optimisation)
- **WASM/target portability**: pointer-width containment, runtime portability, platform DLL abstraction
- **Collection extensibility**: primitive types stay simple, stdlib provides advanced alternatives (RRB, HAMT) via traits
- **Concurrent channels**: CSP-style channels as stdlib + runtime, no language changes; shared task-pool infra with lenient eval
- **Peer language patterns**: Roc (dual backend, platform system), Clojure (persistent data structures, core.async), GHC (multiple backends), Carp (ownership/RC=1 validation)

New NFRs added to `spec/appendix-c-nfr.md`: C.2.4 (collection extensibility), C.4.4 (concurrent communication), C.5.3 expanded to three-mode (was two-tier), C.5.4 (target portability). Total NFRs now 22 across 6 sections.

### Wave 1 Gate (passed)
- Task 0a (`/spec`): done
- Task 0b (`/arch`): done
- Task 1 (`/arch`): done — all 8 sub-items in interfaces.md, CLAUDE.md updates
- FIXME scan: clean (no unresolved FIXMEs in Wave 0/1 output files)
- Task 2 (`/review`): done — ring1-checklist.md with 87 items across 12 sections
- Wave 2 tasks 3, 4, 6 unblocked; task 5 blocked on task 6

### Wave 2 Gate (passed)
- Task 3 (`/frontend`): done — StringLit acceptance, docstring audit, #[must_use], 17 new tests (146 total), design docs
- Task 4 (`/typecheck`): done — string inference, full ADTs with polymorphic constructors, pattern bindings, exhaustiveness, WarningKind (M-3), #[must_use] (M-5), 36 new tests (126 total), design docs
- Task 5 (`/backend`): done — string codegen, ADT constructor/match with field bindings, closure compilation with captures, named-fn-as-value wrapping, format_result for heap types, M-1 resolved, 23 backend tests + 8 repl display tests, design docs. RC drop glue/consuming convention deferred to Ring 2.
- Task 6 (`/platform`): done (completed in previous wave)
- Full workspace: 594 tests, 0 failures, 0 ignored, clippy clean
- Wave 2.5 (task 7, /review) now unblocked

### Design doc infrastructure added (mid-sprint)
- Created `design/frontend/`, `design/typecheck/`, `design/backend/`, `design/platform/` with CLAUDE.md files
- Updated skill definitions to own their design subdirectories
- Updated `/review` workflow: starts with design docs, ends with completeness assessment
- Wave 2 tasks updated to include design doc deliverables

Key architectural findings:
1. The 7-crate DAG, representation containment, and extern-function pattern are resilient to all examined directions.
2. Two specific risks: pointer-width conflation in emit helpers (WASM risk), FnCompiler portability (must not call JIT APIs).
3. No immediate architectural changes required.

### Task 6 (/platform) completed
- 7 source files created/restructured: `alloc.rs`, `rc.rs`, `string.rs`, `panic.rs` (moved), `primitives/{mod,int,float,bool}.rs`, `lib.rs` rewritten
- 42 unit tests, all passing (parallel-safe with delta-based counter assertions and mutex poison recovery)
- `HeapHeader` added to `cranelisp-types` (shared between runtime and backend)
- `cranelisp-runtime` now depends on `cranelisp-types` — FIXME filed in `src/CLAUDE.md` for `/arch`
- Design doc written: `design/platform/runtime.md`
- Key design decision: RC inc/dec are inline (per arch spec), NOT extern functions. Runtime provides trace logging and underflow check only.
- Clippy clean with `-W clippy::all`
- Task 5 (`/backend`) is now unblocked

### Naming convention change (mid-sprint)
A new JIT symbol naming convention was established in `src/CLAUDE.md` §"JIT Symbol Names":
- No `cranelisp_` prefix on any symbol
- Infrastructure symbols use `runtime/name` JIT registration names
- Primitives use spec names exactly (kebab-case)
- Rust function names are descriptive without location prefixes

Runtime code (`cranelisp-runtime`) has been renamed and passes 42 tests. Design docs updated by owning skills:
- `/arch`: `design/arch/interfaces.md`, `CLAUDE.md`, `architecture.md`, `design-space.md`, `ring0-interfaces.md` — all updated, plus 3 missing functions added (F-5)
- `/platform`: `design/platform/runtime.md`, `crates/cranelisp-runtime/plan-platform.md` — all updated
- `/backend`: `crates/cranelisp-backend/plan-backend.md` — all updated
- `/review`: naming-convention-review.md written — 0 Blockers, 2 Important (F-5, F-7), 5 Suggestions — all resolved
- `sprints/SPRINT.md`: ~30 occurrences in historical task descriptions — acceptable as-is

Skill definition guardrails added: `/arch` and `/review` now have "What /skill Does NOT Do" sections preventing accidental code edits (matching `/sprint`'s existing guardrail).

### Wave 2.5 Review (task 7 complete, refactor pending)
- Review report: `design/review/sprint2-wave2-review.md`
- **0 Blockers, 3 Important, 9 Suggestions**
- Important findings requiring refactor before gate passes:
  - F-1: `compile_apply` 145 lines (guideline: 100) → `/backend`
  - F-2: `HeapCategory::classify` misclassifies non-parameterized ADTs with data constructors → `/arch`
  - F-3: `compile_defn` 8 params with clippy suppression → `/backend`
- Tasks 7a (`/backend`) and 7b (`/arch`) address these in parallel; task 7c (`/review`) re-inspects
- Task 8 (`/qa`) blocked until 7c passes

### Task 9 (/spec) completed
- M-6: `not` added to `spec/appendix-a-builtins.md` — all 19 inline primitives now documented
- F-1: Non-ADT exhaustiveness defined in `spec/06-pattern-matching.md` §6.5.2 — requires wildcard/variable catch-all for Int, Bool, Float, String, function types
- FIXME scan: no new `FIXME(/spec)` in Wave 2 files
- **New finding**: `/typecheck` should implement the non-ADT exhaustiveness rule per §6.5.2 (deferred to Wave 3 or later)

## Outcome

### Delivered
- Heap infrastructure: allocator, RC header layout, inc/dec/drop primitives, RC trace logging
- String type: literals, 8 extern primitives, heap allocation, RC, REPL display
- ADTs with fields: product types, sum types, polymorphic ADTs, shortcut syntax, constructors, pattern matching with field bindings, exhaustiveness checking (ADT + non-ADT per spec §6.5)
- Closures: lambda with captures, closure environment allocation + RC, higher-order functions, named functions as values
- HeapCategory::classify with constructor-aware ADT classification
- CompileContext struct, compile_apply decomposition, FnCompiler::inner constructor
- Pipeline wiring: Ring 1 extern primitives in typechecker, REPL defn intrinsics
- 779 tests (392 unit + 387 integration), 0 failures, clippy clean
- 5 examples (09-strings through 13-higher-order)
- User docs: getting-started.md Ring 1 sections, tutorial curriculum (46 prompts)
- Spec updates: `not` in appendix-a, non-ADT exhaustiveness in §6.5
- Design docs in design/{frontend,typecheck,backend,platform}/
- Review reports: sprint2-wave2-review.md, ring1-report.md
- Usability register: 11 findings (U1.1–U1.11), none blocking

### Deferred
- Vec (Chunk D) — deferred to Sprint 3
- RC consuming calling convention — deferred to Ring 2 activation
- `parse-int` Option return type — requires Ring 2 module system (2 ignored tests)
- Shared expression visitor extraction (F-10) — Ring 2

### Findings
- Vec is the critical-path blocker for application-scale programs (U1.10)
- Polymorphic ADT REPL display shows raw pointers for heap-typed type variables (U1.9)
- HeapCategory heuristic was buggy — non-parameterized data ADTs misclassified (F-2, fixed)
- REPL defn path was missing declare_intrinsics() — closures/ADTs would fail in REPL (fixed)
- Ring 1 extern primitives were missing from typechecker symbol table (fixed)
- Bitmask encoding viable for exemplar Sudoku candidate sets (design insight from /port)
