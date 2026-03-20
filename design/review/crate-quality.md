# Crate Quality Review — X1

**Reviewer**: /review
**Date**: 2026-03-20
**Scope**: All 7 compilation units in the reimplementation
**Codebase snapshot**: commit 01eff04 (sprint 20, 1241 tests)

---

## cranelisp-types

**Rating**: Good
**Files**: 12 files, ~2,315 lines total
**Unit tests**: Yes, ~49 tests across 3 modules (types, heap, operator)

### Structure

Well-organized as the shared boundary crate. Each concern has its own module: `ast.rs`, `types.rs`, `check.rs`, `module.rs`, `error.rs`, `heap.rs`, `pipeline.rs`, `operator.rs`, `sexp.rs`, `span.rs`, `newtype.rs`, `marshal.rs`. The `lib.rs` re-exports key types at the crate root for ergonomic access. String newtypes (`Symbol`, `ModuleFullPath`, etc.) are well-factored via a macro in `newtype.rs`.

### Findings

| # | Class | Finding | File:Line | Action |
|---|-------|---------|-----------|--------|
| 1 | S | `ring0_primitives()` and `ring1_primitives()` are 129 and 127 lines respectively — pure data tables but flagged by the 100-line guideline. These are declarative data, not logic, so the length is acceptable. | operator.rs:39, :178 | No action needed; data tables are exempted from the guideline |
| 2 | S | `io_inner_type()` doesn't check the ADT name before extracting args — `(Option Int)` would also extract `Int`. The `is_io()` check is separate and callers combine them, but the method name is misleading. | types.rs:62 | Consider adding an `is_io()` guard inside `io_inner_type()` or renaming to `adt_first_arg()` |
| 3 | S | `ReplInput` duplicates the shape of `TopLevel` variants (DefnMulti, TypeDef). The `toplevel_to_repl_input` function in ast_builder.rs exists to bridge them. Consider making `ReplInput` wrap `TopLevel` plus `Expr`. | ast.rs:273 | /frontend could refactor in a future sprint |
| 4 | S | `CheckResult` and `ReplCheckResult` share 8 fields. Consider extracting a `SharedCheckResult` struct to DRY them. | check.rs:48, :74 | Minor refactor suggestion |
| 5 | I | `cranelisp-platform` lists `cranelisp-types` as a dependency in Cargo.toml but never uses it. This contradicts `src/CLAUDE.md` which says cranelisp-platform should have no dependencies except std. | ../cranelisp-platform/Cargo.toml | /platform should remove the unused dependency |

---

## cranelisp-frontend

**Rating**: Good
**Files**: 6 files, ~6,714 lines total
**Unit tests**: Yes, ~224 tests across 5 modules

### Structure

Clean three-phase architecture: reader -> quasiquote expansion -> AST builder. Each phase is a separate module. The `defmacro` module handles macro-specific parsing (multi-clause, bracket destructuring) without polluting the core AST builder. The `module_extract` module handles module declaration parsing.

Public API is well-factored: `lib.rs` re-exports a clean surface (`parse`, `build_program`, `build_repl_input`, `build_repl_input_from_sexps`).

### Findings

| # | Class | Finding | File:Line | Action |
|---|-------|---------|-----------|--------|
| 1 | S | `ast_builder.rs` is 2,885 lines — the largest frontend file. Could be split into `build_top_level.rs` and `build_expr.rs` since top-level and expression building are distinct concerns. | ast_builder.rs | Consider splitting when next touched |
| 2 | S | One `.unwrap()` in non-test code: `args.into_iter().next().unwrap()` on line 150. This is guarded by a length check (`args.len() == 1`) two lines above so it's safe, but `?` would be cleaner. | ast_builder.rs:150 | Replace with `.next().ok_or_else(...)` |
| 3 | S | Formatting logic `format_sexp` is defined at the bottom of ast_builder.rs but is a display concern, not a building concern. | ast_builder.rs | Consider moving to a `sexp_format.rs` or into cranelisp-types |

---

## cranelisp-typecheck

**Rating**: Needs Attention
**Files**: 10 files, ~10,645 lines total
**Unit tests**: Yes, ~258 tests across 11 test modules

### Structure

Good decomposition: `checker.rs` (central state), `infer.rs` (per-variant inference), `program.rs` (batch checking), `traits.rs` (trait declarations/impls), `adt.rs` (ADT type registration), `builtins.rs` (primitive and synthetic type registration), `unify.rs`, `resolve.rs` (type expression resolution), `scheme.rs`, `scope.rs`. The borrow-splitting pattern (`pub(crate)` fields, `impl TypeChecker` in multiple modules) is documented and justified.

The main concern is `builtins.rs` at 2,131 lines — it registers all primitives, synthetic types (SList, Sexp, IO, Trace), and their constructors. While largely mechanical, its size makes it hard to navigate.

### Findings

| # | Class | Finding | File:Line | Action |
|---|-------|---------|-----------|--------|
| 1 | I | `builtins.rs` has ~20 `.unwrap()` calls in non-test code (lines 1250-2069). These are on module table lookups that "should" exist because the code just inserted them. Each should use `.unwrap_or_else(\|\| unreachable!("invariant: ..."))` per `src/CLAUDE.md`. | builtins.rs:1250+ | /typecheck batch convert to `unreachable!` with invariant description |
| 2 | I | `register_trace_type()` is 136 lines — exceeds the 100-line guideline. This is the only function in the crate that exceeds it. | builtins.rs:734 | Extract helper functions for individual constructor registrations |
| 3 | I | `builtins.rs` at 2,131 lines is the second-largest file in the codebase. The synthetic type registrations (SList, Sexp, IO, Trace) could each be their own module under a `builtins/` directory. | builtins.rs | /typecheck consider splitting |
| 4 | I | `program.rs` has one `.unwrap()` in non-test code: `type_vars.get(&defn.name).unwrap()` at line 336. This is inside a loop where the key was just inserted, but violates CLAUDE.md. | program.rs:336 | Convert to `unreachable!` |
| 5 | S | 7 `#[allow(dead_code)]` annotations in `traits.rs`. Some of these are genuinely deferred (Ring 2 fields stored for future use), but the comment on line 41 is the only one that explains why. The rest should document their deferral ring. | traits.rs:41-787 | Add Ring annotation comments |
| 6 | S | Two `TODO(Ring 2)` comments in `program.rs` (lines 689, 712) for uncommenting monomorphisation. These are stale if Ring 2 is complete. | program.rs:689,712 | /typecheck verify and remove if already implemented |

---

## cranelisp-backend

**Rating**: Needs Attention
**Files**: 14 files (7 modules + submodules), ~9,752 lines total
**Unit tests**: Yes, ~88 tests across 7 test modules

### Structure

Good decomposition into `compiler/` submodules: `mod.rs` (FnCompiler), `apply.rs`, `control_flow.rs`, `literals.rs`, `match_codegen.rs`, `trace_codegen.rs`, `vec_codegen.rs`. Supporting modules: `jit.rs` (ISA + JIT lifecycle), `got.rs` (GOT state), `heap.rs` (emit helpers), `operators.rs` (inline IR), `display.rs` (value formatting), `codegen_types.rs`.

The `FnCompiler` + `CompileContext` pattern successfully avoids the prototype's 21-parameter function problem.

### Findings

| # | Class | Finding | File:Line | Action |
|---|-------|---------|-----------|--------|
| 1 | B | `CompiledExpr::execute()` (line 77) is a **safe** function that internally calls `unsafe { std::mem::transmute }`. This is unsound — callers can invoke it without an `unsafe` block, yet it relies on the invariant that `func_ptr` is valid JIT code. It should be `pub unsafe fn execute()` like `CompiledProgram::execute()` on line 53. | lib.rs:77 | /backend mark as `unsafe fn` |
| 2 | I | 7 functions exceed 100 lines in the backend: `compile_body` (107), `compile_resolved_call` (131), `build_closure_drop_glue` (104), `compile_lambda_body` (117), `compile_trace_wrapper_fn` (147), `compile_vec_set_cow` (113), `build_adt_drop_glue_fn` (161). The drop glue and trace wrapper functions are the worst offenders. | compiler/* | /backend decompose the 3 worst (trace_wrapper, adt_drop_glue, resolved_call) |
| 3 | I | `lib.rs` at 2,317 lines mixes public API, batch compilation pipeline, and ~1,700 lines of integration tests. The test suite should be in a separate file or at least in a `tests/` submodule under the crate. | lib.rs | /backend extract tests |
| 4 | I | `register_intrinsics()` in `jit.rs` is 112 lines of repetitive `builder.symbol(...)` calls. This is pure data — could be a static table iterated by a loop. | jit.rs:63 | /backend refactor to table-driven registration |
| 5 | S | `unsafe impl Send/Sync` for `DefCodegen` and `ModuleCodegenState` have SAFETY comments, but they are brief. The `DefCodegen` comment says pointers are "only used from the JIT execution thread" — but `Send` means it *can* be sent across threads. The justification should explain that the pointers' validity doesn't depend on which thread reads them (they're stable after JIT finalization). | codegen_types.rs:28, got.rs:24 | /backend improve SAFETY comments |
| 6 | S | `display.rs` has 6 `unsafe` blocks for heap pointer dereferencing (reading ADT tags, fields, vec elements, strings). All have inline comments but no `// SAFETY:` formal comments per the review checklist. | display.rs:315,437,457,542,547,554 | /backend add formal SAFETY comments |

---

## cranelisp-runtime

**Rating**: Good
**Files**: 11 files (8 modules + primitives/), ~2,666 lines total
**Unit tests**: Yes, ~75 tests across 11 modules

### Structure

Well-organized by responsibility: `alloc.rs`, `rc.rs`, `string.rs`, `vec.rs`, `io.rs`, `trace.rs`, `panic.rs`, `marshal.rs`, `primitives/` (int, float, bool). The `lib.rs` provides clear re-exports grouped by category (runtime infrastructure, string, vec, primitives, IO, trace).

Base-pointer convention is consistently applied. `HeapHeader` layout is imported from `cranelisp-types` (single source of truth).

### Findings

| # | Class | Finding | File:Line | Action |
|---|-------|---------|-----------|--------|
| 1 | I | `panic!()` in `io.rs:80` on unknown IO tag. Per `src/CLAUDE.md`, runtime code should use `unreachable!("invariant: ...")` for true programmer errors, not `panic!`. Since an unknown tag IS an invariant violation (typechecker should prevent it), this should be `unreachable!`. | io.rs:80 | /platform change to `unreachable!("invariant: valid IO tag")` |
| 2 | I | `.expect("GOT layout")` in `trace.rs:91` — violates the "no expect() in pipeline code" rule. The Layout is constructed from compile-time constants so it cannot fail, making `unreachable!` appropriate. | trace.rs:91 | /platform change to `.unwrap_or_else(\|_\| unreachable!("invariant: GOT layout is valid"))` |
| 3 | S | `io.rs` has numerous raw pointer dereferences without `// SAFETY:` comments. The function-level doc comment explains the ABI contract, but individual `unsafe` blocks should each explain why the invariant holds at that point. | io.rs:50-188 | /platform add per-block SAFETY comments |
| 4 | S | No unit tests for `cranelisp-platform` (0 `#[test]` annotations). The platform ABI contract types, scheduling class conversion, and safe wrappers should have basic tests. | cranelisp-platform/src/lib.rs | /platform add basic unit tests |

---

## cranelisp-platform

**Rating**: Needs Attention
**Files**: 1 file, 814 lines total
**Unit tests**: None (0 tests)

### Structure

Single-file crate defining the C-ABI contract between host and platform DLLs. Contains the `declare_platform!` macro, safe wrappers (`CLInt`, `CLString`, etc.), `HostCallbacks`, manifest parsing, and scheduling classes. The `SchedulingClass` enum is well-designed.

### Findings

| # | Class | Finding | File:Line | Action |
|---|-------|---------|-----------|--------|
| 1 | I | Zero unit tests in the entire crate. Scheduling class conversions, ABI constant values, safe wrapper roundtrips, and manifest parsing should all be tested. | lib.rs | /platform add unit tests |
| 2 | I | Unused dependency on `cranelisp-types` in `Cargo.toml`. No `use cranelisp_types` anywhere in the crate. This violates the documented dependency graph in `src/CLAUDE.md` which says cranelisp-platform has "no dependencies (except std)". | Cargo.toml | /platform remove unused dependency |
| 3 | I | `unsafe impl Send/Sync for PlatformFn` at lines 106-107. The SAFETY comment (line 104) says "constructed and accessed within unsafe blocks during DLL loading" but doesn't explain why the function pointers remain valid across threads. DLL function pointers are process-wide and stable, which is the actual safety argument. | lib.rs:104-107 | /platform improve SAFETY comment |
| 4 | S | `manifest_to_descriptors()` is an `unsafe fn` taking raw C pointers. At 100+ lines, it's at the edge of the guideline. The inner loop for platform function parsing could be extracted. | lib.rs:596 | /platform extract helper |

---

## src/ (integration binary)

**Rating**: Needs Attention
**Files**: 7 files, ~7,312 lines total
**Unit tests**: Yes, ~110 tests across 7 modules

### Structure

Good separation of concerns: `main.rs` (CLI), `pipeline.rs` (module graph compilation), `repl.rs` (REPL session), `expander.rs` (macro expansion), `marshal.rs` (Sexp marshalling), `platform.rs` (DLL loading), `lib.rs` (public API for tests).

`repl.rs` at 3,283 lines is the largest file in the entire codebase. It contains session state, evaluation logic, formatting, slash command handling, and the main REPL loop. This is the area with the most structural debt.

### Findings

| # | Class | Finding | File:Line | Action |
|---|-------|---------|-----------|--------|
| 1 | I | `repl.rs` at 3,283 lines is too large. Slash command handlers (~1,200 lines, functions `handle_sig` through `handle_mod`) should be extracted to `src/repl_commands.rs`. Value formatting (`format_result`, `format_type_display_universal`) should delegate fully to `cranelisp_backend::display`. | repl.rs | /int extract slash commands and formatting |
| 2 | I | `pipeline.rs` has 3 functions exceeding 100 lines: `discover_module_recursive` (121), `discover_import_dependencies` (93, close to limit), `compile_module_graph` (157). The `compile_module_graph` function is the worst — it handles module ordering, compilation, and entry point selection in one function. | pipeline.rs:319,455,963 | /int decompose `compile_module_graph` |
| 3 | I | 5 `.unwrap()` calls in non-test `repl.rs`: line 260 (`sexps.into_iter().next().unwrap()`) and lines 2430, 2447, 2464, 2481, 2498 (all `.as_ref().unwrap()` on slash command display entries). The first is guarded by a length check. The latter 5 are on `Option` fields in `DefCodegen` that may legitimately be `None` for some definitions. | repl.rs:260,2430-2498 | /int replace with proper error handling or `if let` |
| 4 | I | `repl.rs` has a `TraceDisplayState` with raw pointers and a thread-local `Cell<*const TraceDisplayState>`. The SAFETY comment (line 38-41) explains lifetime but not thread safety. Since it uses `thread_local!` and never crosses threads, the safety argument is that it's never `Send`/`Sync` — but this should be stated explicitly. | repl.rs:42-55 | /int add explicit SAFETY documentation |
| 5 | I | `marshal.rs` has 2 `unsafe fn` helpers (`read_i64`, `write_i64`) that encapsulate raw pointer access — good. But the callers (e.g., `marshal_sexp_to_heap` at line 161) also contain `unsafe` blocks doing `alloc_with_rc` calls that should reference the SAFETY invariant. | marshal.rs | /int add SAFETY comments on outer unsafe blocks |
| 6 | S | 4 `TODO` comments across pipeline.rs and related files (inline module extraction, Ring 2 mono). These should be tracked or removed. | pipeline.rs:378, typecheck/program.rs:689,712 | /int audit and resolve |

---

## Cross-Crate Summary

### Statistics

| Crate | Files | Lines | Tests | Rating |
|-------|-------|-------|-------|--------|
| cranelisp-types | 12 | 2,315 | 49 | Good |
| cranelisp-frontend | 6 | 6,714 | 224 | Good |
| cranelisp-typecheck | 10 | 10,645 | 258 | Needs Attention |
| cranelisp-backend | 14 | 9,752 | 88 | Needs Attention |
| cranelisp-runtime | 11 | 2,666 | 75 | Good |
| cranelisp-platform | 1 | 814 | 0 | Needs Attention |
| src/ (binary) | 7 | 7,312 | 110 | Needs Attention |
| **Total** | **61** | **40,218** | **804** | — |

### Blockers (must fix before next ring gate)

| # | Crate | Finding |
|---|-------|---------|
| B1 | cranelisp-backend | `CompiledExpr::execute()` is a safe wrapper around unsafe code — should be `unsafe fn` |

### Top-priority debt (Important findings, by impact)

1. **`repl.rs` size (3,283 lines)** — the single largest maintainability risk. Slash commands should be extracted.
2. **20+ `.unwrap()` calls in non-test `builtins.rs`** — violates CLAUDE.md error handling rules systematically.
3. **7 functions >100 lines in backend** — the drop glue and trace wrapper generators need decomposition.
4. **Zero tests in cranelisp-platform** — the ABI boundary crate has no unit test coverage at all.
5. **Unused cranelisp-types dependency in cranelisp-platform** — contradicts documented dependency graph.
6. **`compile_module_graph` at 157 lines** — the integration pipeline's most complex function needs decomposition.

### Positive patterns observed

- **String newtypes** are used consistently for `Symbol`, `ModuleFullPath`, `TypeName`, etc. No bare string identifiers in cross-crate boundaries.
- **HeapCategory as single source of truth** — the audit finding about duplicated heap classification is well-addressed.
- **Single ISA construction** in `jit.rs` — the audit finding about multiple ISA constructions is resolved.
- **FnCompiler + CompileContext** successfully replace the prototype's 21-parameter `compile_function`.
- **Per-variant dispatch** in both `infer_expr` and `compile_expr` — clean, maintainable dispatch tables.
- **ScopeStack** instead of environment cloning — avoids the prototype's worst performance debt.
- **Warnings as data** — accumulated as `Vec<Warning>`, never printed via `eprintln!`.
- **`unreachable!("invariant: ...")` pattern** is mostly followed (28 uses vs 3 panic/expect violations).
- **HeapHeader constants** (`SIZE`, `RC_OFFSET`, `ALLOC_SIZE_OFFSET`) with compile-time assertions.

### Architectural conformance

The crate dependency graph matches the specification in `src/CLAUDE.md` except for the spurious `cranelisp-platform -> cranelisp-types` edge. No circular dependencies exist. The boundary types (`CheckResult`, `ReplCheckResult`, `CompileMode`, etc.) live correctly in `cranelisp-types`.

---

## Next skills

- `/backend` — fix B1 (CompiledExpr safety), decompose large functions, extract tests from lib.rs
- `/typecheck` — convert builtins.rs unwrap() calls, split builtins into submodules
- `/int` — extract repl.rs slash commands, decompose compile_module_graph
- `/platform` — add unit tests, remove unused dependency, improve SAFETY comments
