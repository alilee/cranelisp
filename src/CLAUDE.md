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

## Synthetic-module mount + import installer (S76 W-Absorb)

- **`src/bootstrap.rs`** hosts `mount_synthetic_modules(symbol_tables, next_id)` — int's reconstruction of the deleted `cranelisp_typecheck::register_builtins` body (FIXME 0242, now resolved). It seeds, in bootstrap order: special forms at root `""` (`ModuleEntry::SpecialForm`); intrinsic type names + `Vec` in `primitives`; the synthetic `macros` module (`Sexp`/`SList` ADTs + `sconcat`); `Option`, `IO` (+ `bind`), `Trace` (ADT data only — bodies are in `cranelisp-intrinsics`, codegen in backend), and `TestResult` in `primitives`. Called from `CompilerSession::new` (after the `PRIMITIVES_TABLE` `into_concrete` mount) and from `platform.rs`'s test fixture. `Def` entries use `ModuleEntry::def(scheme, kind)` (the Tier-1 builder); non-`Def` entries (`SpecialForm`/`IntrinsicType`/`TypeDef`) use plain struct literals + `insert` (the broader `declare_*` vocabulary stays deferred — FIXME 0241). ADTs are reconstructed directly (TypeDef entry + per-ctor `Def { kind: DefKind::Constructor }` with a synthesised `Expr::ConstrADT` body), since typecheck's `register_type_def` is no longer reachable. Fresh type vars for the polymorphic ADTs/`bind` come from `next_id` (high-water advances monotonically).
- **`src/imports.rs`** hosts the int-side import/export installer (`install_imports` / `install_exports`) — replaces typecheck's struck `register_imports`/`register_exports` (BC §2 invariants 2+8). Writes per-symbol `ModuleEntry::Import { source, visibility }` bindings into the current module's table (visibility `Private` for `(import …)`, `Public` for `(export …)` re-export edges; the `Reexport` variant is retired) + module-path aliases into `SharedState.module_aliases` (keyed `<owner>.<alias>`). Resolution semantics (glob/specific/member-glob, visibility checks, ambiguity detection via `insert_detecting_ambiguity`) mirror the deleted typecheck bodies. typecheck reads `module_aliases` read-only; `ModuleCompiler` carries `module_aliases: &ModuleAliases` and threads it into `check_forms`.

## Cluster-Atomic Orchestration (Sprint 66 Wave 3a-β)

- **`src/cluster.rs`** hosts `ProcessedCluster` and the `process_cluster` / `insert_cluster` free functions per `design/arch/facades/int.md` §"process_cluster". Per Decision 44's 2026-05-13 third amendment, `ProcessedCluster` carries cluster-level cross-symbol bookkeeping directly (warnings, resolved-import bindings, introspection records) — there is no separate `ModuleCheckAccumulator` on either the typecheck side or the int side. The pre-S66 type is fully retired.
- A **cluster** is the unit of typecheck atomicity (Decision 44):
  - Non-`(begin)` REPL input = one-form cluster.
  - `(begin form₁ … formN)` REPL input = explicit multi-form cluster.
  - Batch file = one big cluster of the file's non-structural forms.
- `process_cluster` is the SOLE crate-crossing where `ResolutionGap` values become scheduler calls. Frontend and typecheck stay pure with respect to live state (return `Gap`, never call the scheduler).
- **Typecheck dispatch surface** collapsed to one call per cluster — `cranelisp_typecheck::check_forms(parsed, &mut ctx, symbol_tables)`. `worker::check_program_compat` is the int-side bridge that converts `Vec<TopLevel>` (the legacy program shape) into `Vec<ParsedEntry>` for `check_forms`, constructs `ClusterContext::Live`, and dispatches.
- **Build-form dispatch** uses `worker::build_program_compat` as a drop-in replacement for the retired `cranelisp_frontend::build_program`. Per-form `build_form` is the new boundary; structural decls (`mod`/`import`/`export`/`platform`) flow through `extract_module_declarations` peeling.
- **Status (Sprint 66 Wave 3b-2c.2).** `process_cluster` delegates to `worker::check_program_compat`. The staging-commit/discard infrastructure (`worker::process_cluster_with_staging` + `worker::commit_staging_to_live`) is wired and tested by inspection but **not yet activated on the hot path** — `check_program_compat` continues to use `ClusterContext::Live` pending FIXME 0179 (cluster-mode read-union of staging and live). Several per-form registration paths (e.g. `register_type_def` → `find_same_name_constructor_scheme` in `crates/cranelisp-typecheck/src/adt.rs`, trait-impl default-method registration) write to the current symbol table then immediately read back via `TypeCheckEnv::current_symbol_table(state)` — a live-only accessor. Activating Cluster mode without the read-union flip regresses ~12 tests across `spec_05_definitions`, `spec_12_runtime`, and trait-impl suites. When FIXME 0179 lands, replace `check_program_compat`'s Live-mode body with a call to `process_cluster_with_staging` and add a single-form / multi-form routing predicate.

## Macro expansion (S76 W-Macro, fire B) — recognition primitive + single executor

The macro **two-jobs split** (`design/arch/macro-expansion-ownership.md`) is landed on int's side:

- **Recognition is a `cranelisp-types` query.** `src/expander.rs::recognize_macro_head` wraps `cranelisp_types::resolve_macro_head` over a committed first-hop (`View::single(live)` over the current module). It handles imports/reexports/aliases/visibility and returns the macro's canonical `FQSymbol`, `Ok(None)` for a non-macro or forward (pre-`defmacro`) reference, `Err` only for hard failures (private / unknown qualified module). **Zero int→typecheck dependency for recognition** — it is a types query (`macro-availability-model.md` §0.7). The bespoke chain-walks are gone: `resolve_macro_definition` (worker) is replaced by `recognize_macro_head` + a direct `read_macro_meta` lookup on the resolved canonical entry; both resolvers (`worker::SymbolTableMacroResolver`, `session_v4::ReadOnlyMacroResolver`) call the one primitive.
- **Execution is the single `JitMacroExpander`.** `src/expander.rs::JitMacroExpander` implements `cranelisp_types::MacroExpander` over the surviving invocation core (`invoke_clause` + `invoke_jit_protected` signal-protected JIT call + `rewrite_spans` + `src/marshal.rs`). Given `(fq, args, span)` it reads `clauses_meta` from the canonical `DefKind::Macro` entry, selects the matching clause, loads the clause fn's GOT-slot code ptr (`__macro_{name}_clause_{idx}`), marshals/invokes/unmarshals, and rewrites spans. An absent clause-code GOT slot surfaces a clear `MacroInvokeError::Aborted` ("…not in memory…") rather than misbehaving. The shared `execute_matched_clause` is the **one** invocation core — there is no `MacroEntry`-based parallel executor (`MacroEntry`, `build_macro_entry_from_clauses`, `expand_macro_call_with_entry` all deleted).
- **The walk.** `expand_sexp_recursive` survives as the live driver (the orchestrator-driven three-pass Pass-1 loop with just-in-time dependency compilation — `macro-availability-model.md` §0.4 — is the target, but the as-built live path is the `process_module_forms` worker loop, **not** the dead `cluster::process_cluster` scaffold). The walk's `MacroResolver` trait now does recognition (`recognize`) + on-demand clause compilation only; execution flows through `JitMacroExpander` (it exposes `symbol_tables()` for the walk to build the expander).
- **Macro sexp for on-demand compile** is read back from `SharedState.introspection` (keyed by `FQSymbol`), not the symbol-table entry (the per-entry `sexp` field was retired, Decision 41) — `worker::resolve_macro_sexp_from`.
- **Deleted dead scaffolding.** `scheduler::block_for_macro_codegen` + its private helpers (`push_priority_entries_locked`, `wire_priority_edges_locked`) and `worker::collect_transitive_uncompiled_deps` are deleted — the locked decision forbids same-module non-macro clause callees (round-trip safety, §0.3), so there is no empty-slot case to pre-compile (`macro-availability-model.md` §0.7). **NOTE:** with `block_for_macro_codegen` gone, `PriorityEntry` is no longer constructed anywhere — the priority-codegen-queue subsystem (`PriorityEntry`, `take_priority_work`'s `BlockingJitCodegen` scan, etc.) is now dead but not yet removed (scheduler-owned; flagged for a scheduler cleanup, not chased in W-Macro).

**Not yet landed (architecture wall, W-Macro three-pass target — `macro-availability-model.md` §0.4):** the orchestrator-driven Pass-1 expand loop in `process_cluster` with **just-in-time dependency-module compilation by pausing** is NOT built. The live path is the `process_module_forms` worker loop; `cluster::process_cluster` is a zero-caller facade-conformance scaffold (do not build a second Pass-1 loop there — that is a parallel pipeline). Lifting macro expansion onto `process_cluster` is the FIXME 0176/0179 staging-activation work. Consequence: a macro clause that references a **dependency** symbol or an **FQ cross-module macro** that needs just-in-time compile is not yet supported (the 3 failing `s76_macro_availability` cases — `fq_macro_reference_expands_without_import`, `macro_clause_calls_imported_helper_at_expansion_works`, and the same-module-`defn` rejection-diagnostic shape).

## Int-owned JIT intrinsics (Sprint 66 Wave 3a-γ; S76 W-Collapse update)

Two parked runtime extern functions in `src/session_v4.rs` are JIT-emitted-call
targets — backend-emitted CLIF declares them as `Linkage::Import` and the JIT
must resolve them at setup:

| JIT symbol | Rust fn | Reader (CLIF emitted from) |
|---|---|---|
| `discover-tests` | `discover_tests_extern` | `(run-tests ...)` special form |
| `run-test` | `run_test_extern` | `(run-tests ...)` special form |

(S76 FIXME 0256, trace ruling 2026-06-04: the trace family — `cranelisp_trace_format`
+ the 12 `cranelisp_trace_*` bodies — LEFT int. It lives in `cranelisp_intrinsics::trace`,
is published via `intrinsics_table()`, and is registered by `Jit::new(symbol_tables)`.
`src/trace.rs` is deleted; int hosts no `(trace ...)` runtime.)

**S76 W-Collapse status — the 2 above are currently UNregistered (FIXME 0261).**
JIT construction now flows through `worker::build_session_jit` → `Jit::new(symbol_tables)`,
which derives the whole JIT symbol set from `symbol_tables` + `cranelisp_intrinsics::INTRINSICS_TABLE`
and has **no extension point** for these 2 parked int-hosted intrinsics. `int_intrinsics()`
(in `session_v4.rs`) is therefore presently uncalled (`#[allow(dead_code)]`). Programs
with literal `(discover-tests)` / `(run-test ...)` forms will not resolve those symbols
until the `Jit::new` extension point lands (backend; FIXME 0261). When it lands, re-wire
`int_intrinsics()` into the `Jit::new` call and drop the `#[allow]`.

**No syntactic gating.** Do not re-introduce per-program scans that gate intrinsic registration — the pre-S66 `program_uses_test_forms` / `program_needs_trace` / `any_compiled_defn_uses_test_forms` helpers were deleted in Wave 3a-γ. See FIXME 0178 for the architectural rationale (forbidden-patterns clause to land on `facades/intrinsics.md`).

The thread-local state these intrinsics dereference (`TestRunnerState`) is set just-in-time before invoking compiled code. `TestRunnerState` lives on `SharedState` (built once in `CompilerSession::new`, stable for session lifetime); the REPL `/mod` command updates only its `current_module` field through its `Mutex`. The intrinsics null-check the pointer and return harmless defaults when no eval is active. (`TraceDisplayState` was deleted with the trace family in S76 — see above.)

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
