# Coverage Gap Analysis

Generated: 2026-03-20
Workspace coverage: **86.72%** line coverage (40,790 regions, 5,419 missed)
Test suite: 1,140 tests (261 integration, ~880 unit across crates)

## 1. Per-Crate Coverage Summary

| Crate / File | Regions | Missed | Line % | Functions Hit | Priority |
|---|---|---|---|---|---|
| **cranelisp (binary)** | | | | | |
| `src/repl.rs` | 3,479 | 1,526 | 56.1% | 100/146 fns | P1 |
| `src/pipeline.rs` | 1,910 | 127 | 93.4% | 83/91 fns | P3 |
| `src/expander.rs` | 779 | 111 | 85.8% | 34/41 fns | P2 |
| `src/platform.rs` | 710 | 83 | 88.3% | 28/33 fns | P3 |
| `src/marshal.rs` | 510 | 78 | 84.7% | 26/28 fns | P3 |
| `src/main.rs` | 66 | 66 | 0.0% | 0/3 fns | P4 |
| **cranelisp-platform** | | | | | |
| `crates/.../lib.rs` | 452 | 337 | 25.4% | 3/52 fns | P3 |
| **cranelisp-runtime** | | | | | |
| `string.rs` | 552 | 193 | 65.0% | 24/35 fns | P1 |
| `marshal.rs` | 290 | 82 | 71.7% | 16/19 fns | P2 |
| `rc.rs` | 43 | 12 | 72.1% | 7/9 fns | P3 |
| `trace.rs` | 423 | 53 | 87.5% | 26/29 fns | P3 |
| `alloc.rs` | 257 | 34 | 86.8% | 19/25 fns | P3 |
| **cranelisp-frontend** | | | | | |
| `ast_builder.rs` | 3,041 | 519 | 82.9% | 155/156 fns | P2 |
| `reader.rs` | 1,690 | 168 | 90.1% | 126/128 fns | P3 |
| `lib.rs` | 19 | 5 | 73.7% | 3/4 fns | P3 |
| **cranelisp-typecheck** | | | | | |
| `checker.rs` | 1,390 | 150 | 89.2% | 84/92 fns | P3 |
| `program.rs` | 1,714 | 145 | 91.5% | 55/58 fns | P3 |
| `traits.rs` | 1,637 | 103 | 93.7% | 80/86 fns | P3 |
| **cranelisp-backend** | | | | | |
| `operators.rs` | 642 | 46 | 92.8% | 30/33 fns | P3 |
| `lib.rs` | 2,052 | 84 | 95.9% | 59/59 fns | P3 |
| **cranelisp-types** | | | | | |
| `error.rs` | 47 | 25 | 46.8% | 3/3 fns | P3 |
| `pipeline.rs` | 8 | 5 | 37.5% | 1/2 fns | P3 |
| **platforms** | | | | | |
| `platforms/stdio/src/lib.rs` | 27 | 27 | 0.0% | 0/4 fns | P4 |
| `platforms/test-capture/src/lib.rs` | 98 | 98 | 0.0% | 0/14 fns | P4 |

## 2. Per-File Gap Analysis (files <80% coverage)

### 2.1 `src/repl.rs` -- 56.1% (P1, largest gap)

**3,290 lines, 1,526 missed regions.** This file contains both the `ReplSession` eval engine (well-tested via integration tests) and ~40 slash command handlers + display formatters (poorly covered).

#### Covered (via integration tests and unit tests):
- `ReplSession::new()`, `eval()`, `eval_sexp()`, `compile_and_execute()` -- core eval path
- `format_result()`, `format_result_value()` -- value display
- `parens_balanced()`, `is_comment_only()`, `is_import_form()`, `is_annotation_prefix()` -- utility fns (unit tests)
- E2E tests exercise slash commands indirectly via the binary, but llvm-cov attributes this to the binary process, NOT to `cargo test` coverage

#### Uncovered -- Structural (hard to test without refactoring):
- **`run_repl()` (lines 1418-1492)**: The interactive REPL loop reads from stdin, writes to stdout. It cannot be unit-tested directly. E2E tests cover this via subprocess invocation, but llvm-cov does not instrument the subprocess binary.
- **`create_repl_session()` (lines 1393-1408)**: Depends on file system (prelude loading from cwd). Tested indirectly by E2E tests.
- **`eval_and_display()` (lines 1338-1386)**: Orchestration function that calls `session.eval()` and writes output. Tested by E2E but not by in-process tests.
- **`dispatch_slash_command()` (lines 1295-1335)**: Dispatch switch. Tested by E2E but not in-process.

These functions (~260 lines) are the REPL's I/O boundary. They are tested by E2E tests (126 tests in `tests/e2e.rs`), but the coverage tool does not see this because E2E tests invoke the binary as a subprocess. The B3 refactoring (extract testable REPL core) will address this by separating I/O from logic.

#### Uncovered -- Missing Tests (addressable now):
- **`handle_sig()` (line 1558)**: Tested by E2E `/sig` tests, but not by in-process tests.
- **`handle_doc()` (line 1583)**: Tested by E2E but not in-process.
- **`handle_type()` (line 1620)**: Tested by E2E `/type` tests.
- **`handle_info()` (line 1656)**: Tested by E2E but coverage not counted.
- **`handle_list()` (line 1699)**: Tested by E2E and `repl_negative.rs`, but handler itself not covered.
- **`handle_time()` (line 1788)**: Tested by E2E.
- **`handle_expand()` (line 1819)**: Tested by E2E.
- **`handle_imports()` (line 1885)**: Tested by E2E.
- **`handle_exports()` (line 1977)**: Tested by E2E.
- **`handle_source/sexp/ast/clif/disasm()` (lines 2428-2511)**: Developer introspection commands. Tested by E2E.
- **`handle_mod()` (line 2521)**: Tested by E2E.
- **Display formatters** (`format_entry_signature`, `format_type_display_universal`, `format_trait_display_universal`, `format_macro_display_universal`, `format_builtin_type_display`, `special_form_feedback`, etc. -- lines 2158-2421): ~260 lines of formatting logic exercised by E2E but not counted.

**Root cause**: All 17 slash command handlers accept `&mut impl Write` (testable API!), but no in-process tests exist that call them directly. The handlers are already factored for testability -- they just lack callers in the test suite.

**Estimate**: ~25 unit tests calling handlers directly on a `ReplSession::new()` would cover ~600 missed lines (slash command handlers + display formatters). Another ~15 tests for the formatting functions would cover ~200 more lines. Total: ~40 tests for ~800 lines, raising `repl.rs` from 56% to ~80%.

#### Uncovered -- Trace/IO paths:
- **`repl_trace_format()` (line 77)**: Trace display callback. Tested by `ring4_trace.rs` via E2E.
- **`force_io_and_format()` (line 1163)**: IO trampoline display. Tested by `tests/io.rs` indirectly.
- **`invoke_jit_eval()` (line 2536)**: JIT panic boundary. Tested by runtime panic E2E tests.
- **`build_traced_fns()` (line 962)**: Trace infrastructure. Tested by trace tests.
- **`compile_expr_with_traced_fns()` (line 1089)**: Trace wrapper compilation.

These ~200 lines are tested by integration/E2E tests but not counted in coverage.

### 2.2 `crates/cranelisp-runtime/src/string.rs` -- 65.0% (P1)

**528 lines, 193 missed.** The string runtime has unit tests for core functions but is missing tests for newer string operations.

#### Covered:
- `alloc_string`, `str_concat`, `str_eq`, `str_len`, `string_identity`, `string_read`, `heap_alloc_string` -- tested by unit tests in the file

#### Uncovered -- Missing Unit Tests:
- **`str_substring()` (line 176)**: Clamping logic, edge cases
- **`str_char_at()` (line 189)**: Unicode handling, out-of-bounds
- **`str_split()` (line 207)**: Vec allocation, separator handling
- **`str_join()` (line 232)**: Vec reading, separator joining
- **`str_replace()` (line 252)**: Replacement logic
- **`str_trim()` (line 262)**: Whitespace trimming
- **`str_starts_with()` (line 270)**: Prefix matching
- **`str_ends_with()` (line 278)**: Suffix matching
- **`str_contains()` (line 286)**: Substring search
- **`str_to_upper()` (line 294)**: Case conversion
- **`str_to_lower()` (line 302)**: Case conversion

**Root cause**: These 11 functions were added in later rings (Ring 3 string operations) but their unit tests were not written. They are exercised by integration tests in `tests/ring2.rs` and `tests/stdlib.rs` but the runtime crate's own test module does not cover them.

**Estimate**: 15-20 unit tests (one per function + edge cases for substring/char_at/split) would cover ~160 missed lines, raising `string.rs` from 65% to ~95%.

### 2.3 `crates/cranelisp-runtime/src/marshal.rs` -- 71.7% (P2)

**304 lines, 82 missed.** The Sexp marshalling runtime has tests for `sconcat` but not for `quote_sexp`.

#### Uncovered:
- **`quote_sexp()` (line 191)**: Converts runtime values to quoted Sexp representation. Complex function with 7 tag branches (~60 lines).
- **`quote_slist()` (line 253)**: Recursive SList quoting (~20 lines).
- **`shallow_rc_inc()` (line 116)**: RC increment for shallow copies.
- **`deep_rc_inc_slist()` (line 129)**: Deep RC increment for SList values.

**Root cause**: `quote_sexp` is called from JIT-compiled macro code. Testing it requires constructing runtime Sexp values manually (possible but tedious). The RC helpers are exercised by macro expansion but not directly tested.

**Estimate**: 8-10 unit tests would cover ~70 missed lines, raising `marshal.rs` from 72% to ~95%.

### 2.4 `crates/cranelisp-platform/src/lib.rs` -- 25.4% (P3)

**814 lines, 337 missed.** This crate defines the platform C-ABI types and the `declare_platform!` macro.

#### Covered:
- Type definitions, constants, `SchedulingClass::from_u32()` -- trivially covered
- `manifest_to_descriptors()` -- covered when platforms are loaded

#### Uncovered:
- **`CLIO` methods**: `pure()`, `effect()`, `effect_on_resource()`, `call_effect_thunk()` -- these run inside platform DLLs, not in the test binary
- **`CLString` methods**: `as_str()`, `CLOwned`, `HeapManaged` trait impls -- same reason
- **`HostCallbacks`, `HostContext`**: Initialization path
- **`derive_jit_name()`**: Utility function
- **From impls**: Various type conversions

**Root cause**: This crate is the shared ABI layer between host and platform DLLs. Most of its code runs inside the DLL process space. The `declare_platform!` macro generates code that runs in the DLL. Coverage instrumentation does not cross DLL boundaries.

**Estimate**: ~15 unit tests for the Rust API (`CLString`, `CLIO`, `SchedulingClass`, `derive_jit_name`) would cover ~150 lines, raising to ~45%. The remaining gap is macro-generated code and DLL-side functions that cannot be tested in-process without restructuring.

### 2.5 `crates/cranelisp-frontend/src/ast_builder.rs` -- 82.9% (P2)

**~3,041 regions, 519 missed.** Large file covering AST construction from S-expressions.

#### Uncovered (estimated):
- Error paths in form parsing (malformed `defn`, `deftype`, `deftrait`, `impl` bodies)
- Rare AST forms (multi-arity `defn`, complex `match` patterns with nested destructuring)
- `build_repl_input_from_sexps()` annotation path

**Root cause**: The happy paths are well-tested through integration tests. Error paths for malformed syntax are partially tested by `repl_negative.rs` but many invalid-input variations are untested.

**Estimate**: ~20 unit tests for error paths would cover ~300 missed lines, raising to ~93%.

### 2.6 `src/expander.rs` -- 85.8% (P2)

**847 lines, 111 missed.** The macro expander.

#### Uncovered:
- Error paths in clause matching (wrong arity, bracket destructuring failures)
- Multi-clause dispatch edge cases
- `format_expanded_sexp()` for unusual Sexp shapes

**Estimate**: ~10 tests for error paths and edge cases would cover ~80 missed lines, raising to ~95%.

### 2.7 `crates/cranelisp-types/src/error.rs` -- 46.8% (P3)

**107 lines, 25 missed.** Error type Display impls.

#### Uncovered:
- `Display` impl for `ModuleError` with `file: Some(path)` variant
- `Display` impl for `MacroError`
- `span()` and `message()` accessor methods

**Root cause**: These Display paths are exercised when errors are printed, but the specific formatting is not asserted in unit tests.

**Estimate**: 5 unit tests would cover all missed lines.

### 2.8 `crates/cranelisp-types/src/pipeline.rs` -- 37.5% (P3)

**79 lines, 5 missed.** Pipeline types and `NoOpExpander`.

#### Uncovered:
- `NoOpExpander::expand()` -- returns `Err` (the error path for "macros not available")

**Estimate**: 1 unit test.

### 2.9 `src/main.rs` -- 0.0% (P4)

**87 lines, 66 missed.** Binary entry point.

**Root cause**: `main()`, `parse_args()`, and `run_file()` are the binary entry point. `cargo test` does not execute `main()`. E2E tests invoke the binary as a subprocess but coverage is not attributed.

**Estimate**: `parse_args()` could have 3-4 unit tests. `run_file()` and `main()` are inherently untestable via in-process tests. ~20 lines coverable.

### 2.10 `platforms/stdio/src/lib.rs` and `platforms/test-capture/src/lib.rs` -- 0.0% (P4)

**62 + 152 lines, all missed.** Platform DLLs compiled as cdylib.

**Root cause**: These are separate dynamic libraries loaded at runtime. `cargo test` does not execute their code paths directly. They are tested indirectly via `tests/io.rs` which loads the test-capture platform via the DLL loading mechanism. Coverage instrumentation does not cross the DLL boundary.

**Estimate**: Not addressable without building a test harness that links the platform code statically for testing. Low priority -- these are thin wrappers around stdlib I/O.

## 3. Prioritized List of Missing Tests

### P1 -- User-Visible Correctness Risk

| # | Gap | File | Tests Needed | Lines Covered |
|---|---|---|---|---|
| 1 | Slash command handlers (in-process) | `src/repl.rs` | ~25 | ~600 |
| 2 | Display formatters (in-process) | `src/repl.rs` | ~15 | ~200 |
| 3 | String runtime operations | `runtime/string.rs` | ~18 | ~160 |

**Subtotal: ~58 tests covering ~960 missed lines**

### P2 -- Robustness Risk (Error Paths)

| # | Gap | File | Tests Needed | Lines Covered |
|---|---|---|---|---|
| 4 | AST builder error paths | `frontend/ast_builder.rs` | ~20 | ~300 |
| 5 | Runtime marshal `quote_sexp` | `runtime/marshal.rs` | ~10 | ~70 |
| 6 | Macro expander error paths | `src/expander.rs` | ~10 | ~80 |

**Subtotal: ~40 tests covering ~450 missed lines**

### P3 -- Maintenance Risk (Infrastructure)

| # | Gap | File | Tests Needed | Lines Covered |
|---|---|---|---|---|
| 7 | Platform crate Rust API | `platform/lib.rs` | ~15 | ~150 |
| 8 | Error Display impls | `types/error.rs` | ~5 | ~25 |
| 9 | Pipeline types | `types/pipeline.rs` | ~1 | ~5 |
| 10 | RC trace/alloc edge cases | `runtime/rc.rs`, `alloc.rs` | ~5 | ~30 |

**Subtotal: ~26 tests covering ~210 missed lines**

### P4 -- Low Risk (Entry Points / DLLs)

| # | Gap | File | Tests Needed | Lines Covered |
|---|---|---|---|---|
| 11 | Binary `parse_args` | `src/main.rs` | ~4 | ~20 |
| 12 | Platform DLLs | `platforms/*/src/lib.rs` | N/A | N/A |

**Subtotal: ~4 tests covering ~20 lines** (DLLs not addressable)

## 4. Impact Estimate

| Action | Tests | Lines Recovered | Coverage Delta |
|---|---|---|---|
| P1 (slash commands + string ops) | ~58 | ~960 | 86.7% -> 89.1% |
| P1 + P2 (+ error paths) | ~98 | ~1,410 | 86.7% -> 90.2% |
| P1 + P2 + P3 (+ infrastructure) | ~124 | ~1,620 | 86.7% -> 90.7% |
| All addressable | ~128 | ~1,640 | 86.7% -> 90.7% |

Theoretical maximum (excluding DLLs and binary entry point): ~91-92% (remaining gap is DLL code, binary main, and unreachable error guards).

## 5. Recommendations

### This Sprint (Sprint 21)

**Close P1 gaps (items 1-3): ~58 tests**

1. **Slash command handler unit tests** (item 1, ~25 tests): The handlers already accept `&mut impl Write`. Write tests that create a `ReplSession::new()`, define some symbols via `session.eval()`, then call handlers directly with a `Vec<u8>` as the Write target. This is the highest-ROI gap -- covers ~600 missed lines with straightforward tests.

2. **Display formatter unit tests** (item 2, ~15 tests): Test `format_entry_signature`, `format_type_display_universal`, `format_trait_display_universal`, `format_builtin_type_display`, `special_form_feedback` directly. These are pure functions that can be tested without JIT compilation.

3. **String runtime unit tests** (item 3, ~18 tests): Add tests to the existing `#[cfg(test)] mod tests` in `string.rs`. Each function is `extern "C"` and can be called directly with heap-allocated test strings. Follow the pattern of existing tests (`test_str_concat`, `test_str_eq_equal`, etc.).

**Note on B3 refactoring interaction**: The B3 task extracts REPL command handling into a testable core. Once that refactoring lands, some of the slash command tests written here may need adjustment (function signatures may change). However, the test *logic* and *assertions* will remain valid -- only the call sites change. Writing the tests now is still worthwhile because: (a) they validate current behavior before refactoring, (b) they serve as regression tests during refactoring, and (c) most will survive the refactoring with minimal changes since the handlers are already factored to accept `impl Write`.

### Next Sprint

**Close P2 gaps (items 4-6): ~40 tests**

4. AST builder error path tests: malformed forms, missing parameters, wrong types
5. Marshal `quote_sexp` tests: construct runtime Sexp values, verify quoting
6. Expander error path tests: wrong arity, bad destructuring

### Later (Ring 5 / Release Prep)

**P3 and P4 gaps**: Infrastructure tests, platform crate API tests, binary arg parsing. These are low-risk and can wait until the release hardening phase.

### Not Addressable

- Platform DLL coverage (0% for stdio and test-capture): These are cdylib crates whose code runs in a separate process space. Coverage instrumentation cannot cross DLL boundaries. They are validated indirectly by IO integration tests. Considered acceptable at 0% -- the DLLs are thin wrappers (~60-150 lines each) around stdlib I/O.

- `src/main.rs` (0%): Binary entry point. The `parse_args` function could have unit tests (move it to `lib.rs` or add `#[cfg(test)]` module in `main.rs`), but `main()` and `run_file()` are inherently untestable in-process. E2E tests cover this path.
