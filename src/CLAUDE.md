# src/

Cross-cutting source conventions for the Cranelisp reimplementation. All compiler skills must follow these rules. Local `CLAUDE.md` files in subdirectories may add conventions but must not contradict these.

## Error Handling

- **No `unwrap()` in pipeline code.** Use `?` with `CranelispError`. `unwrap()` is permitted only in tests and in `main()`.
- **No `panic!()`** Use `unreachable!("invariant: <description>")` for true programmer errors (logic bugs that should never occur). Never `panic!` on user input.
- **No `expect()` in pipeline code.** If the value might be None/Err due to user input, return a proper error. If it's a programmer invariant, use `unreachable!`.
- **Every error carries a `Span`** for source location. Parse errors use byte offset converted to Span at the reader boundary.
- **Warnings are data, not side effects.** Accumulate `Vec<Warning>`, never `eprintln!`. Warnings flow to the caller and are displayed by the binary crate.

## Code Structure

- **Max ~100 lines per function.** If a function grows beyond this, decompose it into named helpers. Long functions are the prototype's primary structural debt.
- **Max 8 parameters.** Group related parameters into context structs. The prototype's `compile_function` had 21 parameters — this must not recur.
- **One dispatch method per Expr variant.** `infer_expr` and `compile_expr` dispatch to `infer_let`, `infer_apply`, `compile_let`, `compile_apply`, etc.
- **Named structs for multi-field returns.** No bare tuples `(Vec<Type>, Type, String)` — use `MonoDefn`, `OverloadVariant`, etc.

## Naming Conventions

- **String newtypes for all identifiers.** `Symbol`, `ModuleFullPath`, `FQSymbol`, `TraitName`, `TypeName`, `ModuleName`, `LinkerSymbol`. Never pass bare `String` or `&str` where a typed identifier is expected.
- **Named constants for magic numbers.** `GOT_TABLE_SIZE`, `NULLARY_TAG_THRESHOLD`, etc. No bare numeric literals in logic.
- **Rust naming conventions.** `snake_case` for functions and variables, `CamelCase` for types and enum variants, `SCREAMING_SNAKE` for constants.

### JIT Symbol Names

All symbols registered in the JIT share a single flat namespace. Names must be unambiguous across user code, primitives, trait impls, and runtime infrastructure. The naming scheme uses module-qualified paths (`module/name`) as the primary disambiguation mechanism, matching the language's own module system.

**Categories:**

| Category | JIT name format | Example | Visible to users? |
|----------|----------------|---------|-------------------|
| User function | `name` or `module/name` | `factorial`, `user/factorial` | Yes |
| Trait method impl | `Trait.method$Type` | `Display.show$Int` | Via trait dispatch |
| Multi-sig variant | `name$Params` | `add$Int+Int` | Via overload dispatch |
| ADT constructor | `name` or `module/name` | `Some`, `Cons`, `user/Point` | Yes — via module system |
| Extern primitive | `name` (kebab-case) | `str-concat`, `int-to-string` | Yes — in `primitives` module |
| Runtime infrastructure | `runtime/name` | `runtime/alloc`, `runtime/panic` | No |

**Rules:**

1. **User-visible primitives** use the spec name exactly (kebab-case, per `spec/appendix-a-builtins.md`). The Rust function implementing the primitive follows Rust `snake_case` conventions — the two names are independent.
2. **Runtime infrastructure** (allocator, dealloc, RC underflow check, etc.) uses the `runtime/` module prefix. These are internal — never callable from user code.
3. **Platform functions** loaded from DLLs use the platform's declared names, prefixed by the platform module path.
4. **No `cranelisp_` prefix.** The `cranelisp_` prefix used in the sketch added no information (everything is cranelisp) and made a name-change harder. Use module-qualified names instead.
5. **`#[unsafe(no_mangle)]` on runtime functions** is optional — symbols are registered by function pointer via `JITBuilder::symbol()`, not by linker symbol name. Use it only if stable names in debugger stack traces are desired.
6. **Rust function names** for extern primitives should match the spec name in `snake_case` (e.g., `int_to_string` for `int-to-string`). Do not prefix with `cranelisp_`.

## Scope Management

- **Scope stack (push/pop), not `env.clone()`.** The prototype cloned `local_env` (~70+ entries) at every scope boundary. Use a stack-based approach: push a scope frame, pop on exit.
- **Consuming calling convention.** Callee owns heap parameters. Caller emits inc for non-last-use, or transfers ownership for last-use.

## Heap Access

- **Representation containment.** Only emit helpers (`heap_load`, `heap_store`, `emit_*_alloc`, `emit_rc_inc`, `emit_rc_dec`) may import layout constants (`HEAP_HEADER_SIZE`, field offsets). No other codegen code references raw byte offsets. This confines layout assumptions to a single module.
- **Pointer-width documentation.** Every `heap_load` / `heap_store` call must include a comment stating the semantic field being accessed and its width. E.g., `heap_load(ptr, 16, 8) // tag: i64`.
- **Base-pointer convention.** Heap pointers point to offset 0 of the allocation. All field accesses use positive offsets. No interior pointers.

## Serialization

- **Serde derives on all cross-boundary types.** `#[derive(Serialize, Deserialize)]` on types in `cranelisp-types`.
- **`#[serde(skip)]` for runtime-only fields.** Function pointers, JIT handles, `Duration` — skip with sensible defaults.

## Type System

- **Ring 0 defines the full `Type` enum.** All variants (`Int`, `Bool`, `String`, `Float`, `Fn`, `ADT`, `Var`, `TyConApp`) exist from the start. Rings exercise them incrementally.
- **`Type::from_name()` / `Type::type_name()`** centralize primitive name mapping. No scattered match blocks.
- **`TypeId` is `u32`.** Not `usize`. 4 billion type variables is sufficient.

## Cluster-Atomic Orchestration (Sprint 66 Wave 3a-β)

- **`src/cluster.rs`** hosts `ProcessedCluster` and the `process_cluster` / `insert_cluster` free functions per `design/arch/facades/int.md` §"process_cluster". Per Decision 44's 2026-05-13 third amendment, `ProcessedCluster` carries cluster-level cross-symbol bookkeeping directly (warnings, resolved-import bindings, introspection records) — there is no separate `ModuleCheckAccumulator` on either the typecheck side or the int side. The pre-S66 type is fully retired.
- A **cluster** is the unit of typecheck atomicity (Decision 44):
  - Non-`(begin)` REPL input = one-form cluster.
  - `(begin form₁ … formN)` REPL input = explicit multi-form cluster.
  - Batch file = one big cluster of the file's non-structural forms.
- `process_cluster` is the SOLE crate-crossing where `ResolutionGap` values become scheduler calls. Frontend and typecheck stay pure with respect to live state (return `Gap`, never call the scheduler).
- **Typecheck dispatch surface** collapsed to one call per cluster — `cranelisp_typecheck::check_forms(parsed, &mut ctx, symbol_tables)`. `worker::check_program_compat` is the int-side bridge that converts `Vec<TopLevel>` (the legacy program shape) into `Vec<ParsedEntry>` for `check_forms`, constructs `ClusterContext::Live`, and dispatches.
- **Build-form dispatch** uses `worker::build_program_compat` as a drop-in replacement for the retired `cranelisp_frontend::build_program`. Per-form `build_form` is the new boundary; structural decls (`mod`/`import`/`export`/`platform`) flow through `extract_module_declarations` peeling.
- **Status**: `process_cluster` delegates to `worker::check_program_compat` (which dispatches `check_forms` against the live `SymbolTable`). The full staging pivot to `ClusterContext::Cluster { staging, … }` is FIXME 0176's responsibility — the orchestration shell here is the durable surface that receives the redirect.

## Int-owned JIT intrinsics (Sprint 66 Wave 3a-γ)

Three runtime extern functions in `src/session_v4.rs` are JIT-emitted-call targets — backend-emitted CLIF declares them as `Linkage::Import` and `JITBuilder::symbol()` must resolve them at JIT setup:

| JIT symbol | Rust fn | Reader (CLIF emitted from) |
|---|---|---|
| `discover-tests` | `discover_tests_extern` | `(run-tests ...)` special form |
| `run-test` | `run_test_extern` | `(run-tests ...)` special form |
| `cranelisp_trace_format` | `repl_trace_format` | `(trace ...)` special form |

These are **intrinsics** per `design/arch/facades/intrinsics.md` — registered uniformly with `heap_alloc` / `runtime/panic` / primitive arithmetic. **Unconditional registration is mandatory**: every JIT-build site in this crate folds in `crate::session_v4::int_intrinsics()` before calling `Jit::new_with_symbols`. The two current sites are `worker::inline_jit_codegen_for_names` and `pipeline::compile_and_execute_expr` (plus its trace variant). New JIT-build sites MUST do the same.

**No syntactic gating.** Do not re-introduce per-program scans that gate intrinsic registration — the pre-S66 `program_uses_test_forms` / `program_needs_trace` / `any_compiled_defn_uses_test_forms` helpers were deleted in Wave 3a-γ. See FIXME 0178 for the architectural rationale (forbidden-patterns clause to land on `facades/intrinsics.md`).

The thread-local state these intrinsics dereference (`TestRunnerState`, `TraceDisplayState`) is set just-in-time before invoking compiled code. `TestRunnerState` lives on `SharedState` (built once in `CompilerSession::new`, stable for session lifetime); the REPL `/mod` command updates only its `current_module` field through its `Mutex`. The intrinsics null-check the pointer and return harmless defaults when no eval is active.

## Known regressions from the Wave 3a-β collapse

The Wave 3a-β typecheck-collapse refactor regressed several test categories where the pre-S66 multi-call shape carried cross-form state across separate `check_form` invocations. The new single-call shape rebuilds that state per `check_forms` call, which exposes accumulator-fragmentation issues on:

- **Constrained polymorphism across multiple REPL inputs** — e.g., `(defn id [x] x)\n(id 7)\n`. The second-form mono dispatch interacts pathologically with the per-call typecheck state; investigation in flight via FIXME `target: /typecheck`.
- **Multi-clause macro compilation through `compile_macro_clause_inline`** — the legacy threading of `&mut CheckState` + `&mut ModuleCheckAccumulator` is now no-op (the accumulator is local to `check_forms`). Some macro-clause flows expect cross-form context that the new shape doesn't surface.

These will be addressed in the FIXME 0176 follow-up that lifts `ClusterContext::Cluster` + staging into `process_cluster` proper.

## Testing

- **Every module gets `#[cfg(test)] mod tests`.** Unit tests live next to the code they test.
- **Integration tests in `tests/`.** Owned by `/qa`, organized by ring.
- **Test names describe the behavior, not the implementation.** `test_let_polymorphism_infers_identity` not `test_case_47`.

## Dependencies Between Crates

- `cranelisp-types`: no dependencies (except `serde`, `std`)
- `cranelisp-frontend`: depends on `cranelisp-types`
- `cranelisp-typecheck`: depends on `cranelisp-types`
- `cranelisp-backend`: depends on `cranelisp-types`, `cranelisp-runtime`
- `cranelisp-runtime`: depends on `cranelisp-platform`, `cranelisp-types`
- `cranelisp-platform`: no dependencies (except `std`)
- `cranelisp` (binary): depends on all above

No circular dependencies. Cargo enforces this at build time.

## Debugging Cross-Crate Failures

When an integration test fails and the root cause could be in any crate, follow the isolation process in `tests/CLAUDE.md` §"Isolating Cross-Crate Failures". The key principle: write a crate-level unit test that asserts the expected state at the crate boundary. If it passes, the bug is in the integration wiring. If it fails, fix the crate.
