# Sprint 20: Ring 4E — Trace & Debt Clearance

**Status**: COMPLETE
**Ring**: 4 (Effects) — fifth increment
**Goal**: Implement trace special form, clear all multi-deferred debt, resolve active FIXMEs, complete Ring 3 traceability, and deliver code review for Sprints 16-19.

## Scope

Sprint 19 delivered developer tools (6 slash commands), REPL panic boundary, and batch mode for the exemplar. Sprint 20 combines progression (trace) with clearing accumulated debt.

### Ring 4E: Trace & Display Format

| # | Feature | Owner | Description |
|---|---------|-------|-------------|
| T0 | Extract value display format to `cranelisp-backend` | /arch + /backend | Move canonical value formatting functions from `src/repl.rs` to `cranelisp-backend/src/display.rs`. REPL keeps `:Type` prefix layer, calls into backend for value formatting. Implements spec §12.9. Trace runtime and REPL share one implementation. |
| T1 | `(trace expr)` special form | /backend + /typecheck + /frontend | Module-scoped special form in `primitives` (NOT a parser keyword — has regular call syntax, resolved through module system). `Trace` ADT with clean field names: `name`, `params`, `result`, `children`, `nanos`. NOT auto-imported. Spec §4.12. |
| T2 | Trace display stdlib | /stdlib | `trace-show-tree`, `trace-call-string`, `trace-show` in `stdlib/core/trace.cl`. Re-export `trace`, `Trace`, `TraceCall`, field accessors from `primitives` via `export`. |
| T3 | Trace REPL integration | /int | Display trace results in REPL using standard ADT format. No auto-formatting — users call stdlib display functions. |

### Deferred Debt

| # | Item | Owner | Deferrals | Description |
|---|------|-------|-----------|-------------|
| D6 | Exemplar IO with print | /port | **3x** (S17→S18→S19) | Exemplar compiles but doesn't use `print` for output. Blocked by F1 (IO display fix). **Must ship — 3x deferred.** |
| D7 | Docs IO guide validation | /docs | **3x** (S17→S18→S19) | IO guide written in S18 but never validated against working batch mode. Depends on D6. **Must ship — 3x deferred.** |
| R1 | Code review (S16-S19) | /review | 1x (S19) | Four sprints of unreviewed code: IO foundation, IO sequencing, REPL hardening, developer tools. |
| T4 | Ring 3 spec traceability | /qa + /spec | 1x (S19) | ~80 spec annotations still tagged `[R3 S8/S9]` despite features being implemented and tested. |

### FIXME Resolutions

| # | File | Owner | Issue |
|---|------|-------|-------|
| F1 | `repl/spec.md:127` | /int | IO display shows `:(IO Int) 42` instead of `:(IO Int) (IO.Pure 42)`. |
| F2 | `repl/spec.md:771` | /int | `/mod name` prints redundant comment; bare `/mod` should switch to `user`. |
| F3 | `spec/08-modules.md:408` | /spec | Clarify interaction between explicit glob imports and implicit prelude glob (§8.6.4). |

### Out of Scope (deferred to later sprints)

- Run-tests special form (Sprint 21 — depends on trace)
- Auto-currying (Sprint 21; 4 ignored tests), HKT (3 ignored), lazy sequences (1 ignored)
- Module caching, standalone executable generation, hot-reload (Sprints 22-23)
- Lenient evaluation, automatic IO scheduling (Sprint 24)
- Terminal styling (FIXME(/repl) on repl/spec.md:839)
- resource_token for Par (FIXME(/spec) on spec/10-io.md:52)
- stderr write for REPL (FIXME(/platform) on .claude/commands/platform.md:73)

## FIXME Debt

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `repl/spec.md:127` | /int | IO display format | **F1: done** |
| `repl/spec.md:771` | /int | /mod conformance | **F2: done** |
| `spec/08-modules.md:408` | /spec | Glob import vs prelude | **F3: done** |
| `repl/spec.md:839` | /repl | Terminal styling | Carry — cosmetic, not this sprint |
| `.claude/commands/platform.md:73` | /platform | stderr write for REPL | Carry — evaluate for later Ring 4 |
| `spec/10-io.md:52` | /spec | resource_token for Par | Carry — Par not yet in scope |

## Architecture Review

**Status: APPROVED** (revised after spec work) — scope is technically coherent. Trace is fully specced (§4.12, §3.2.4, §12.9). Value display format extracted to language spec.

### Key Decisions

1. **T0 display extraction**: `cranelisp-backend/src/display.rs` — approved. No new inter-crate dependencies. Both REPL and trace runtime share one implementation.

2. **Trace is NOT a parser keyword** (Principle 10): `(trace expr)` has regular call syntax and flows through the module system. The typechecker intercepts it when the callee resolves to `primitives/trace`. This keeps the parser small and the module system authoritative.

3. **Trace ADT NOT auto-imported**: `Trace`, `TraceCall`, `trace`, and field accessors are in `primitives` but excluded from auto-import. Stdlib re-exports via `core.trace`.

4. **Value display format is language-level** (§12.9): Extracted from REPL spec. Both REPL and trace reference it. Includes elision rules (SHOULD-level).

### Concerns

1. **Trace runtime complexity**: Thread-local state, CAS, heap allocation in `cranelisp-runtime/src/trace.rs`. `/backend` and `/platform` must coordinate.
2. **`TRACE_TC_PTR` pattern**: JIT calling back into host via leaked `*const TypeChecker`. Acceptable for debug tool, must not spread.
3. **`children` encoding**: Implementation-defined per spec. `/backend` and `/stdlib` must agree.

## Skill Plans

### /spec
**Task**: (F3) Clarify §8.6.4 glob import vs prelude. (T4) Collaborate with /qa on Ring 3 traceability.
**Acceptance**: F3 done. Ring 3 annotations updated.

### /arch
**Task**: (T0) Approve display extraction. Document API. Add Principle 10 (parser keywords for distinct syntax only).
**Acceptance**: T0 done. Principle 10 added.

### /frontend
**Task**: (T1) Remove trace from parser keywords. Parse `(trace expr)` as `Expr::Apply`.
**Acceptance**: Done. `trace` flows through module system.

### /typecheck
**Task**: (T1) Seed Trace ADT. Handle `(trace expr)` when callee resolves to primitives/trace.
**Acceptance**: Done. 258 typecheck tests pass.

### /backend
**Task**: (T0) Extract display functions to `cranelisp-backend/src/display.rs`. (T1) Trace codegen — GOT copy-swap, wrappers, runtime fns. New `compiler/trace.rs`.
**Design refs**: `spec/12-runtime.md` §12.9, `spec/04-expressions.md` §4.12, sketch `src/codegen/trace.rs`, memory file `trace.md`
**Acceptance**: (T0) Done. (T1) `(trace (fib 5))` produces a `Trace` value with correct call tree.

### /platform
**Task**: No new platform work. Carry stderr FIXME.
**Acceptance**: Confirm no changes needed.

### /int
**Task**: (T0) Update src/repl.rs to call backend display API. (F1) Fix IO display. (F2) Fix /mod. (T3) Trace REPL integration.
**Acceptance**: T0/F1/F2 done. T3: trace values display as standard ADT.

### /qa
**Task**: (T4) Ring 3 traceability (~80 annotations). Write trace integration tests.
**Acceptance**: Zero `[R0-R3 S*]` annotations for implemented features. Trace tests pass.

### /stdlib
**Task**: (T2) Create `stdlib/core/trace.cl`: re-export from primitives via `export`, display functions.
**Acceptance**: `(import [core [trace [*]]])` brings in trace + display fns.

### /examples
**Task**: Verify all examples. Add trace example if appropriate.
**Acceptance**: All examples pass.

### /repl
**Task**: Create `repl/demos/ring4e.demo`. Verify all prior demos.
**Acceptance**: New demo plays cleanly.

### /port
**Task**: (D6) Add IO output to exemplar.
**Acceptance**: `CRANELISP_LIB=stdlib cargo run -- --run exemplar/solver.cl` produces formatted output.

### /docs
**Task**: (D7) Validate IO guide.
**Acceptance**: All IO guide examples work.

### /review
**Task**: (R1) Code review S16-19 + sprint 20 code. Assess within each implementation wave.
**Acceptance**: 0 Blockers, 0 Important findings unresolved.

## Waves

### Wave 0: Spec + Display Extraction
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /spec | F3: Clarify §8.6.4 glob import vs prelude | done | Explicit imports shadow prelude; remediation strategies documented |
| /arch | T0: Approve display extraction | done | API documented in interfaces.md; Principle 10 added |
| /backend | T0: Extract value display to `cranelisp-backend/src/display.rs` | done | 5 public + 13 internal functions |
| /int | T0: Update src/repl.rs to call backend display API | done | Re-exports for backward compat |
| /int | F1: Fix IO display | done | `force_io_and_format` wraps in `(IO.Pure ...)` |
| /int | F2: Fix /mod conformance | done | Bare `/mod` → user, no confirmation |
| /review | Review T0 + F1/F2 | done | PASS, 3I resolved (duplication unified, SAFETY comments, unit tests) |
| /frontend | T1: Remove trace from parser keywords | done | Parses as Apply, module-scoped |
| /typecheck | T1: Seed Trace ADT, handle in infer_apply | done | 258 tests pass, NOT auto-imported |
| /port | D6: Exemplar IO with print | done | Formatted puzzle board via print |

### Wave 1: Trace codegen + stdlib + integration
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /backend | T1: Trace codegen — GOT copy-swap, wrappers, runtime | done | trace_codegen.rs + runtime/trace.rs, 7 extern fns, 5 runtime unit tests |
| /stdlib | T2: core/trace.cl — export primitives, display fns | done | Re-exports + 3 display fns. FIXME: recursive tree needs SList externs |
| /int | T3: Trace REPL integration — standard ADT display | done | TRACE_DISPLAY_STATE, repl_trace_format, build_traced_fns |
| /review | Review T1 + T2 + R1 (S16-19) | done | 1B+4I resolved: Send/Sync removed, GOT_TABLE_SIZE deduped, mutex poison recovery, body-discard helper, SAFETY comments |

### Wave 2: Build/test/review (iterative until settled)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Write trace integration tests | done | 20 tests, all pass |
| /qa | T4: Ring 3 traceability (~25 of ~80) | partial | spec/09-macros, spec/11-stdlib, spec/appendix-a updated |
| /typecheck | Fix: register `trace` as special form in primitives | done | Was missing — import now works |
| /backend | Fix: intercept trace Apply in compile_expr | done | Redirects Apply(trace, [body]) → compile_trace |
| /runtime | Fix: field accessor extern fns wired | done | 5 accessor functions implemented + registered in JIT |
| /typecheck | Fix: params field type mismatch (String→Int) | done | Root cause of SIGSEGV: drop glue on SList value. params is opaque Int. |
| /review | Trace bug fixes assessed | done | All 4 bugs found and fixed during build/test/review cycle |

### Wave 3: Showcase
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /repl | Demo ring4e.demo — trace, IO display, /mod | done | 42 lines, all 13 demos verified |
| /port | D6: Exemplar IO with print | done | Wave 1 — formatted puzzle board |
| /docs | D7: Validate IO guide | done | 10 format fixes, CRANELISP_LIB docs, CLI syntax fixes |
| /examples | Verify all examples | done | 24 pass, trace example deferred (REPL-only) |

## Notes

- **Critical path**: T1 (trace codegen) → T2/T3 (stdlib + REPL). Debt clearance done in Wave 0.
- **Spec work completed**: Trace fully specced (§4.12, §3.2.4, §12.9, §2.3.10, A.2/A.4, §11.5). Value display format extracted from REPL spec to language spec §12.9.
- **Principle 10 added**: Parser keywords for distinct syntax only. Module-scoped special forms (trace) flow through the module system.
- **T0 is a code move, not a rewrite**: ~200 lines of formatting code extracted. /review found 3I, all resolved.
- **D6 and D7 are at 3x deferrals** — D6 done, D7 pending showcase wave.
- **Serialise agent file access**: Background agents that edit overlapping files caused lost work. Run sequentially when files overlap.

## Outcome

### Delivered
- **T0**: Display format extraction to `cranelisp-backend/src/display.rs` (spec §12.9). 5 public + 13 internal functions. REPL and trace share one implementation.
- **T1**: `(trace expr)` special form — end-to-end: spec (§4.12, §3.2.4, §12.9, §2.3.10), AST, typecheck, codegen (GOT copy-swap), runtime (7 extern fns), REPL integration, stdlib display, 23 integration tests.
- **T2**: `stdlib/core/trace.cl` — re-exports from primitives via `export`, 3 display functions (`trace-show-tree`, `trace-show`, `trace-call-string`).
- **T3**: Trace REPL integration — `TRACE_DISPLAY_STATE`, `repl_trace_format`, `build_traced_fns`, trace-aware compilation path.
- **T4**: Ring 3 spec traceability — all `[R3 S8]`/`[R3 S9]` annotations resolved (~36 updates across 6 spec files).
- **F1**: IO display fixed — `:(IO primitives/Int) (IO.Pure 42)`. FIXMEs removed from `repl/spec.md`.
- **F2**: `/mod` conformance fixed — bare `/mod` → user, no confirmation message.
- **F3**: `spec/08-modules.md` §8.6.4 — explicit imports shadow prelude, remediation strategies documented.
- **D6**: Exemplar IO with print — formatted Sudoku puzzle board output (3x deferred, shipped).
- **D7**: IO guide validated — 10 display format fixes, `CRANELISP_LIB` documented, batch CLI syntax fixed (3x deferred, shipped).
- **Arch Principle 10**: Parser keywords for distinct syntax only. Module-scoped special forms flow through the module system.
- **Borrowed-var RC fix**: Pattern match field bindings are now borrowed from the scrutinee. Drop glue runs only at dealloc time (when RC reaches 0), not during scope cleanup. Prevents double-free on ADTs with heap-typed fields.
- **Trace accessor RC fix**: Heap-typed field accessors (`name`, `params`, `result`, `children`) inc the returned value to prevent dangling interior pointers when the parent is dec'd.
- **Sketch consultation requirements**: All compiler skill definitions updated to require studying the sketch's approach before designing alternatives.
- **Sprint process**: `/review` runs within implementation waves, not deferred. "Review" in step names means "iterate until settled."
- **Ring 4E demo**: `ring4e.demo` — trace tree display, IO format, /mod switching.
- **1241 tests passing** (up from 1218), 0 failures, 8 ignored (pre-existing future-ring features).

### Deferred
- **Trace subexpression RC interaction**: `(accessor (trace expr))` requires the accessor to RC-inc the returned value — fixed for trace-specific accessors, but the general pattern (extern function returning interior pointer from a temporary argument) is not addressed. General ADT field accessor functions would have the same issue.
- **`stdlib/core/trace.cl` FIXME(/platform)**: `trace-children-head`/`trace-children-tail` runtime externs would simplify tree traversal but are not needed — pattern matching on `SCons`/`SNil` works directly.

### Findings
- **RC double-free architectural gap**: The reimplementation's `emit_inline_drop_glue` was decrementing ADT fields during scope cleanup, causing double-free when fields were independently extracted. The sketch solved this with `borrowed_vars` — a mechanism the reimplementation was missing because the RC design didn't consult the sketch. Fixed by implementing borrowed-var tracking and moving field decs to the dealloc path.
- **Sketch consultation process gap**: Design docs were written without studying the sketch's approach to the same problems. Skill definitions updated to require "Sketch comparison" sections in all design docs. `/review` now checks for this.
- **Parallel agent file conflicts**: Background agents editing overlapping files caused lost work (all changes reverted). Mitigation: run agents sequentially when they touch the same files.
- **Module-scoped special forms** (Principle 10): `trace` exposed that special forms with regular call syntax don't need parser keywords. They flow through the module system and are recognized by the typechecker/codegen when the callee resolves to the right symbol.
