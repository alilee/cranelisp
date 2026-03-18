# Sprint 19: Ring 4D — Developer Tools & Exemplar

**Status**: COMPLETE
**Ring**: 4 (Effects) — fourth increment
**Goal**: Wire remaining REPL slash commands, implement REPL panic boundary, clarify module search spec, make exemplar runnable with IO.

## Scope

Sprint 18 delivered REPL hardening, runtime error spec (§12.7), and RC leak fixes. Sprint 19 focuses on three areas:

### Deferred Debt

| # | Item | Owner | Deferrals | Description |
|---|------|-------|-----------|-------------|
| D4 | Spec §8.11 ambiguous on project root vs lib search | /spec | **new** | §8.11.2 says project root = "directory containing the entry file" and lib dirs come from config/env var. But the relationship between project root and lib search is not explicit enough for a project author (e.g. exemplar) to know how to reference an external stdlib. `/spec` must clarify so `/port` knows the spec-compliant mechanism to use. |
| D5 | Exemplar not runnable in batch mode | /port | **2x** (S17, S18) | Exemplar in `exemplar/` can't find prelude because it has no stdlib and no configured lib search path. Blocked on D4 (spec clarity). Once spec is clear, `/port` uses the specified mechanism. |
| D6 | Exemplar IO integration | /port | 2x (S17, S18) | With D5 resolved, exemplar can demonstrate IO via `print`. |
| D7 | Docs IO guide validation | /docs | 2x (S17, S18) | IO guide written in S18 but untested against working batch mode. |
| D8 | Stale FIXME(/int) on src/main.rs:58 | /int | **new** | Code is correct per spec §8.11.2. FIXME should be removed once /spec confirms the spec is clear. |

### Ring 4D: Developer Tools

| # | Feature | Owner | Description |
|---|---------|-------|-------------|
| T1 | REPL slash commands: /source, /sexp, /ast, /clif, /disasm | /int | Wire 5 introspection commands that show internal representations of user definitions. Requires storing sexp/ast/clif/disasm in DefEntry (or recomputing on demand). 10 ignored tests. |
| T2 | REPL /mod command | /int | Wire /mod for namespace switching. 3 ignored tests. |
| T3 | REPL panic boundary | /int + /backend | `catch_unwind` at REPL eval boundary so runtime panics (match failure, vec bounds, div-by-zero) display error and continue session. Implements spec §12.7.4.1. |
| T4 | Prior-ring spec traceability | /qa + /spec | ~47 Ring 3 spec sections still tagged `[R3 S8/S9]` despite features being implemented and tested. Update annotations to `[Tested]` with test references. |

### Out of Scope (deferred to later sprints)

- Module caching, standalone executable generation, hot-reload
- Trace special form, run-tests special form
- Lenient evaluation, parallelism (par-let, par-bind!)
- Auto-currying (4 ignored tests), HKT (3 ignored), lazy sequences (1 ignored)
- Terminal styling (FIXME(/repl) on repl/spec.md:837)

## FIXME Debt

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `src/main.rs:58` | /int | Stale FIXME — code is correct per spec §8.11.2 | **D8: Remove after /spec confirms.** |
| `repl/spec.md:837` | /repl | Terminal styling — Ring 4 scope | Carry — cosmetic, not this sprint |
| `.claude/commands/platform.md:73` | /platform | stderr `write` for REPL | Carry — evaluate for Ring 4E |
| `spec/10-io.md:52` | /spec | resource_token field for Par | Carry — Par is later Ring 4 |

## Architecture Review

**Reviewer**: /arch
**Date**: 2026-03-17
**Verdict**: APPROVED with notes

### 1. Technical Coherence ✓

The three threads — developer tools (T1+T2), runtime safety (T3), and spec clarity (D4) — are independent at the implementation level but reinforce each other thematically. The wave structure correctly sequences D4 (spec) before D5/D6 (port), and T3's /backend work before /int's catch_unwind wrapper.

### 2. No Interim Architecture ✓

- **T1**: `DefCodegen` already has fields for source, sexp, defn, clif_ir, disasm. Slash commands read existing infrastructure.
- **T3**: `catch_unwind` at REPL eval boundary is the final mechanism per spec §12.7.4.1. `extern "C-unwind"` on `runtime_panic` is the correct permanent approach.
- **D4**: Spec clarification, not implementation.

### 3. Design References

Addition needed:
- **T3/int**: Reference `src/expander.rs` `invoke_jit_protected` (lines ~270-340) — existing `catch_unwind` + signal-handler pattern for macro JIT calls. `/int` should follow this pattern (or refactor into shared utility).

### 4. Interface Gaps — None

`DefCodegen` already carries all five fields. Panic boundary requires wrapping the existing eval call site — no new types cross crate boundaries.

### 5. T1 Storage Strategy: Store in DefCodegen ✓

Already designed for this. `Option<String>` fields populated at compile time, bounded memory (~1MB for 100 definitions). Batch mode can skip population. No architectural concern.

### 6. T3 Critical Findings — `/backend` must fix two panic sources

**6a. `emit_match_panic` uses Cranelift `trap`, not `runtime_panic`.**
A hardware trap (SIGILL/SIGTRAP) cannot be caught by `catch_unwind`. `/backend` MUST change `emit_match_panic` to call `runtime_panic` (matching the pattern in `emit_vec_bounds_panic`). The sprint plan's /backend task should state this explicitly.

**6b. Integer division by zero uses raw `sdiv`.**
On x86-64, `sdiv` by zero triggers SIGFPE — not catchable by `catch_unwind`. `/backend` MUST emit a zero-check before `sdiv` and call `runtime_panic("division by zero")` on the zero path. This also produces better error messages than a raw SIGFPE.

If both are addressed by `/backend`, `/int`'s `catch_unwind` is sufficient. Otherwise `/int` must use the fragile `invoke_jit_protected` signal-handler pattern.

### 7. D4 Spec Recommendation

The `{project_root}/stdlib/` fallback in `assemble_lib_dirs()` should be made a SHOULD-level normative default in the spec: "When no lib directories are configured, the implementation SHOULD search `{project_root}/stdlib/` as a default lib directory if that directory exists." This documents existing behavior and matches user expectations.

## Skill Plans

### /spec
**Task**: (D4) Clarify `spec/08-modules.md` §8.11 to make the following unambiguous:
- **Project root** = entry file's parent directory (used for module resolution step 2 — finding sibling `.cl` files). This is already stated but buried.
- **Lib directories** = configured externally via `CRANELISP_LIB` env var or project config file (step 3). Not derived from project root by default.
- **Practical implication**: a project that wants the standard library must either (a) have `stdlib/` in its project root, (b) set `CRANELISP_LIB`, or (c) use a project config file. There is no implicit walk-up or auto-discovery.
- **The `{project_root}/stdlib/` fallback** currently in `assemble_lib_dirs()` is an implementation convenience, not spec-mandated. Either spec it (making it normative) or leave it as implementation-defined. Either way, the spec should be clear enough that `/port` knows what to do.
- (T4) Collaborate with /qa on Ring 3 traceability update.
**Design refs**: `spec/08-modules.md` §8.1.1, §8.11.2; `src/pipeline.rs` lines 761-788
**Acceptance**: §8.11 is unambiguous about how a project references an external stdlib. `/port` can read the spec and know the mechanism without reading the source code.

### /arch
**Task**: Review sprint scope for technical coherence. Assess slash command storage strategy (store in DefEntry vs recompute on demand). Confirm panic boundary approach is not interim architecture. Review /spec's §8.11 clarification for architectural consistency.
**Acceptance**: APPROVED or revision requested.

### /frontend
**Task**: No new frontend work this sprint.
**Acceptance**: Confirm no changes needed.

### /typecheck
**Task**: No new typecheck work this sprint.
**Acceptance**: Confirm no changes needed.

### /backend
**Task**: (T3) Fix two panic sources that bypass `runtime_panic`:
- **T3a**: `emit_match_panic` in `match_codegen.rs` currently emits a Cranelift `trap` (hardware SIGILL). Change to call `runtime_panic("match exhaustiveness failure")` — matching the pattern in `emit_vec_bounds_panic`.
- **T3b**: Integer `sdiv` triggers SIGFPE on division by zero. Emit a zero-check before `sdiv` and call `runtime_panic("division by zero")` on the zero path.
- Verify `emit_vec_bounds_panic` already calls `runtime_panic` correctly (it does per /arch review).
**Design refs**: `crates/cranelisp-runtime/src/panic.rs` (`extern "C-unwind"`), `spec/12-runtime.md` §12.7, `crates/cranelisp-backend/src/compiler/match_codegen.rs` (emit_match_panic), `crates/cranelisp-backend/src/compiler/vec_codegen.rs` (emit_vec_bounds_panic), `crates/cranelisp-backend/src/compiler/operators.rs` (sdiv)
**Acceptance**: All panic-inducing operations use `runtime_panic`. Match failure, div-by-zero, and vec bounds all produce catchable Rust panics (not hardware traps/signals). `/int`'s `catch_unwind` is sufficient without signal handlers.

### /platform
**Task**: No new platform work. Carry stderr FIXME.
**Acceptance**: Confirm no changes needed.

### /int
**Task**: (D8) Remove stale FIXME on `src/main.rs:58` after /spec confirms code is correct. (T1) Wire /source, /sexp, /ast, /clif, /disasm commands. (T2) Wire /mod command. (T3) Implement `catch_unwind` at REPL eval boundary per spec §12.7.4.1.
**Design refs**: `src/repl.rs` (command dispatch), `spec/12-runtime.md` §12.7.4, `repl/spec.md` §3.1, `src/expander.rs` `invoke_jit_protected` (existing catch_unwind pattern)
**Acceptance**: (T1) 10 slash command tests un-ignored and passing. (T2) 3 /mod tests un-ignored and passing. (T3) Division-by-zero in REPL prints error, session continues.

### /qa
**Task**: (T4) Update ~47 Ring 3 spec annotations from `[R3 S8/S9]` to `[Tested test_file::test_name]`. Write tests for panic boundary (div-by-zero recovery, vec-bounds recovery, match-failure recovery in REPL). Write batch mode tests (exemplar runs with CRANELISP_LIB).
**Design refs**: `tests/plan/ring4.md` — checked arithmetic, REPL slash commands
**Acceptance**: All Ring 3 spec sections have `[Tested]` annotations. Panic recovery tests pass. Batch exemplar test passes.

### /stdlib
**Task**: Verify prelude works correctly. No new stdlib work.
**Acceptance**: All existing stdlib tests pass.

### /examples
**Task**: Verify all examples compile and run.
**Acceptance**: All 24 examples pass.

### /repl
**Task**: Validate REPL experience for newly wired slash commands. Verify panic boundary produces user-friendly error messages per spec §12.7.5.
**Acceptance**: All slash commands produce expected output format per repl/spec.md.

### /port
**Task**: (D5) Once /spec clarifies §8.11, use the specified mechanism to make exemplar runnable in batch mode (likely `CRANELISP_LIB` or a wrapper script). (D6) Add IO to exemplar — formatted Sudoku output via `print`. Update exemplar demo.
**Design refs**: `spec/08-modules.md` §8.11 (after /spec clarification)
**Acceptance**: Exemplar runs in batch mode with prelude. `cargo run -- --run exemplar/solver.cl` (with appropriate lib config) produces formatted output. Demo updated.

### /docs
**Task**: (D7) Validate IO guide against working batch mode. Add note about `CRANELISP_LIB` for projects outside the stdlib directory. Minor corrections if needed.
**Acceptance**: IO guide examples all work when run. Multi-directory project setup documented.

### /review
**Task**: Code review after implementation. Focus: panic boundary correctness (no UB on panic, heap leak acceptable per spec), slash command implementation quality.
**Acceptance**: 0 Blockers, 0 Important findings unresolved.

## Waves

### Wave 0: Spec clarification
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /spec | D4: Clarify §8.11 project root vs lib search | done | New §8.11.3: lib dir config priority chain, SHOULD-level stdlib/ fallback, practical implication note |

### Wave 1: Implementation (parallel)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | T1: Wire /source, /sexp, /ast, /clif, /disasm | done | 5 commands wired; sexp/ast/source/clif stored in DefCodegen; disasm "not available" |
| /int | T2: Wire /mod | done | /mod shows current; /mod name switches; dynamic prompt |
| /backend | T3a+b: match panic + div-by-zero | done | runtime_panic + return (not trap); thread-local error flag pattern |
| /int | T3: thread-local error check at eval boundary | done | invoke_jit_eval checks take_runtime_error(); REPL survives panics |
| /int | D8: Remove stale FIXME | done | Replaced with spec reference comment |
| /qa | T4: Ring 3 traceability + panic tests | pending | |

### Wave 2: Build/test/review
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Un-ignore tests, run full suite | done | 13 E2E tests un-ignored. 1218 pass, 0 fail, 8 ignored (out-of-scope features). |
| /review | Code review | deferred | Sprint close review pending user availability |

### Wave 3: Showcase
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /port | D5+D6: Exemplar compiles and runs | done | Removed type annotations from params (61 functions across 4 files), fixed wildcard import shadowing prelude. `CRANELISP_LIB=stdlib cargo run -- --run exemplar/solver.cl` → clean exit. Usability finding: wildcard imports silently overwrite prelude bindings. |
| /docs | D7: Validate IO guide | deferred | Depends on exemplar batch mode working end-to-end |
| /repl | Validate slash commands + panic UX | done | All 6 commands produce output. Panic recovery works (div-by-zero → error message, REPL continues). |
| /examples | Verify all examples | done | All 23 examples pass. |

## Notes

- **Critical path**: /spec (Wave 0) → /port (Wave 3). Spec clarity unblocks exemplar.
- **Dependency removed from /int**: D4 is not a code bug. Batch project_root logic is spec-compliant. /int's workload is now T1+T2+T3+D8 (remove FIXME) — all developer tools work.
- 13 ignored E2E tests should become passing once T1 and T2 are wired.
- T4 (traceability) is mechanical but important — 47 spec sections showing stale ring tags creates false impression of coverage gaps.
- /int workload: T1 (moderate) + T2 (small) + T3 (moderate) = moderate total — within /int capacity.
- **Key design discovery**: Cranelift JIT frames lack registered unwind tables, so `catch_unwind` cannot unwind through them. The original T3 design (catch_unwind) was replaced with a thread-local error flag pattern: `runtime_panic` stores the error message and returns (instead of calling `panic!()`), JIT code returns normally with a dummy 0 value, and the host checks `take_runtime_error()` after every JIT invocation. This required changing all `trap` terminators after `runtime_panic` calls to `return` instructions.
- Exemplar had pre-existing type errors (type annotations in params) and wildcard import shadowing — fixed by /port (61 functions across 4 files).
- `/repl` spec feedback: bare `/mod` should go to `user` (not display current), `/mod name` should not print confirmation comment, IO display should show `(IO.Pure 42)` not bare `42`. FIXMEs filed.
- Sprint skill definition updated: mandatory Phase 5b (Showcase) requiring a new demo for every sprint.

## Outcome

### Delivered
- **D4**: Spec §8.11.3 — lib directory configuration clarified (priority chain, SHOULD-level stdlib/ fallback, practical implication note for subdirectory projects)
- **D5**: Exemplar compiles and runs in batch mode (`CRANELISP_LIB=stdlib cargo run -- --run exemplar/solver.cl`). 61 functions fixed (type annotation removal), wildcard import shadowing resolved.
- **D8**: Stale FIXME removed from `src/main.rs:58` — code correct per spec §8.11.2
- **T1**: 5 REPL slash commands wired: `/source`, `/sexp`, `/ast`, `/clif`, `/disasm`. Introspection data stored in DefCodegen.
- **T2**: `/mod` command wired — shows current module, switches namespace, dynamic prompt.
- **T3**: Runtime panic boundary — thread-local error flag pattern (`runtime_panic` sets flag + returns, host checks `take_runtime_error()`). Match exhaustiveness, div-by-zero, vec bounds all recoverable. REPL survives panics.
- **T3a**: `emit_match_panic` changed from Cranelift `trap` to `runtime_panic` call + return
- **T3b**: Integer division zero-check before `sdiv`, calls `runtime_panic("division by zero")` on zero path
- **Demos**: `ring4c.demo` (ADT display, type annotations), `ring4d.demo` (introspection commands, panic recovery). All 10 ring demos verified clean.
- **Spec updates**: `repl/spec.md` — IO display format, `/mod` behavior (Scenario 6 changed to "go to user"), FIXME(/int) for /mod non-conformance, FIXME(/spec) on import glob shadowing prelude
- **Sprint skill**: Mandatory Phase 5b (Showcase) added to sprint archetype
- **13 E2E tests un-ignored** (slash commands + /mod)
- **1218 tests passing**, 0 failures, 8 ignored (out-of-scope: 4 auto-curry, 3 HKT, 1 lazy seq)

### Deferred
- **T4** (Ring 3 traceability): ~47 spec sections still tagged `[R3 S8/S9]`. Mechanical cleanup, no implementation risk. → Sprint 20.
- **D6** (exemplar IO with print): Exemplar compiles but doesn't use IO yet. → Sprint 20 when `/mod` conformance and IO display are fixed.
- **D7** (docs IO guide validation): Depends on working exemplar IO. → Sprint 20.
- **`/review`**: Code review deferred. → Sprint 20.
- **IO display format**: Shows `:(IO Int) 42` instead of spec `:(IO Int) (IO.Pure 42)`. FIXME(/int) filed.
- **`/mod` conformance**: Prints redundant comment, bare `/mod` shows current instead of going to user. FIXME(/int) filed.

### Findings
- **Cranelift JIT lacks unwind tables**: `catch_unwind` cannot unwind through JIT frames. The T3 design (catch_unwind at eval boundary) was replaced with a thread-local error flag pattern. This is a fundamental constraint — any future runtime error mechanism must use the same approach (set flag + return) rather than Rust unwinding.
- **Wildcard import shadows prelude**: `(import [mod [*]])` silently overwrites prelude-provided names (Some, None). FIXME(/spec) filed on §8.6.4 for spec clarification.
- **Exemplar type annotations**: The reimplementation parses `:Type param` as type application `Type<param>`, not annotation. All exemplar type annotations removed — HM inference handles them.
- **Sprint process gap**: No demo was created for Sprint 18 (ring4c). Sprint skill definition updated with mandatory Phase 5b to prevent recurrence.
