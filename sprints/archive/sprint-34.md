# Sprint 34: Pipeline v3 Step 7 — Decompose CompilationSession

**Status**: COMPLETE
**Ring**: — (structural)
**Goal**: Separate pipeline core state from worker state in `CompilationSession`, enforcing the boundary that `compile_unit` cannot accidentally touch codegen worker fields.

## Scope

One pipeline v3 migration step:

### Step 7: Decompose CompilationSession

Per `design/arch/pipeline-v3-roadmap.md` Step 7:

`CompilationSession` currently has 24 pub fields mixing pipeline state (tc, expander, compile_stack, lib_dirs) with in-mem codegen state (got_state, jit_modules, traced_fns) and object codegen state (cache_state, compiled_o_paths, cross_module_func_sigs). The goal is to group these into sub-structs so that ownership and access boundaries are clear.

**Proposed sub-structs**:

- **`InMemWorkerState`**: `{ got_state, jit_modules, traced_fns, trace_extra_symbols }`
  - Owned by `flush_inmem_queue` and `codegen_and_execute` (interactive path)

- **`ObjectWorkerState`**: `{ cache_state, cache_writer, compiled_o_paths, compiled_module_structures, cross_module_func_sigs }`
  - Owned by `flush_object_queue` and `codegen_and_execute` (batch/cache path)

- **Pipeline core** (stays on `CompilationSession`): `tc`, `expander`, `compile_stack`, `lib_dirs`, `project_root`, `scheduling_registry`, `platform_symbols`, `loaded_platforms`, `interactive`, queues

**Key architectural challenge**: `compile_unit_inner` calls `codegen_and_execute` via:
1. Auto-prelude trigger (line 198) — recursive compile_unit + codegen
2. `load_dependencies` (line 472) — recursive compile_unit + codegen

This means `compile_unit` indirectly accesses worker state through `codegen_and_execute`. The decomposition must either:
- (a) Accept that worker state is accessible through `codegen_and_execute` but not directly from `compile_unit_inner`, or
- (b) Change `load_dependencies` and auto-prelude to push to queues + flush instead of calling `codegen_and_execute` directly

/arch should decide the approach.

**Changes**:
1. Define `InMemWorkerState` and `ObjectWorkerState` structs
2. Add them as fields on `CompilationSession`, replacing the individual fields
3. Update all access sites: `session.got_state` → `session.inmem_worker.got_state`, etc.
4. Move `flush_inmem_queue` and `flush_object_queue` to use the worker state sub-structs
5. Update `codegen_and_execute` to accept worker state references
6. Update all callers (main.rs, tests, REPL)

**Verification**: `cargo test` passes. Compile errors if `compile_unit_inner` directly accesses worker state fields.

## FIXME Debt

No blocking FIXMEs found.

## Architecture Review

### Decision: Option (a) — Accept partial separation

**Recommendation**: Proceed with option (a): group worker state into sub-structs on `CompilationSession`; accept that `codegen_and_execute` (called from within `compile_unit_inner` via auto-prelude and `load_dependencies`) accesses worker state through the session.

**Rationale for rejecting (b) and (c)**:

Option (b) — queue-based dependency codegen — would change `load_dependencies` and auto-prelude to push to queues instead of calling `codegen_and_execute` directly. This is semantically wrong for dependency loading. Dependencies must be fully compiled and registered in the GOT *before* the parent module can proceed to stages 3-5 (expansion, AST build, typecheck). The parent module's macro expansion may invoke dependency-defined macros, its typechecking needs dependency type signatures in the TC, and its codegen needs dependency code pointers in the GOT. A queue-based approach would require a flush-and-block between each dependency load — which is functionally identical to a direct call but with extra indirection and a misleading abstraction (queues suggest deferred work, but this work cannot be deferred). The queue abstraction will earn its keep in Step 11 for *independent* codegen work; forcing it onto *sequential dependency loading* adds complexity without benefit.

Option (c) — defer — is unnecessary. The coupling is real but bounded, and the decomposition still delivers its primary value (clarity, readability, preparation for Step 11) even with the indirect access.

**Why (a) is sufficient**: The goal of Step 7 is to make the ownership boundary *visible and habitual*, not to enforce it at the type-system level. The key invariant — "compile_unit_inner does not name worker state fields" — is verifiable by code review and grep. `compile_unit_inner` calls `codegen_and_execute` as an opaque operation; it does not reach into `session.inmem_worker.got_state` or `session.object_worker.cache_state` directly. The type-system enforcement comes in Step 11 when worker state moves into thread-local storage on codegen worker threads, at which point `compile_unit` physically cannot access it.

### Field classification

**`InMemWorkerState`** (4 fields — used only by interactive codegen path):
- `got_state` — GOT slot management, code pointer registration
- `jit_modules` — keeps JIT code alive
- `traced_fns` — trace wrapper info for expression compilation
- `trace_extra_symbols` — trace format override symbols

**`ObjectWorkerState`** (5 fields — used only by cache/link codegen path):
- `cache_state` — cache directory, manifest
- `cache_writer` — background .o writer handle
- `compiled_o_paths` — .o files for --link
- `compiled_module_structures` — module structures for --link
- `cross_module_func_sigs` — accumulated signatures for .o generation

**Pipeline core** (stays on `CompilationSession`):
- `tc` — typechecker (stages 2-5)
- `expander` — macro expander (stage 3)
- `compile_stack` — cycle detection
- `lib_dirs` — module resolution
- `project_root` — DLL path resolution
- `scheduling_registry` — bind chain analysis (stage 4b)
- `platform_symbols` — see below
- `loaded_platforms` — DLL lifetime management
- `interactive` — mode flag (consumed by `codegen_and_execute` to choose GOT vs direct)
- `inmem_queue`, `object_queue` — codegen queues

**V1-only fields** (5 fields — not used by pipeline_v2.rs):
- `batch_jit`, `func_sigs`, `batch_compiled_fns`, `cached_symbols`, `linker`
- Group into `V1State` sub-struct. This costs nothing, improves readability immediately, and makes the Step 14 deletion a single field removal. "They'll be deleted later" is not a reason to leave them mixed into the core fields now.

### `platform_symbols` placement

`platform_symbols` straddles the boundary: `compile_unit_inner` stage 2f populates it (from platform DLL loading), and `codegen_and_execute` reads it (passed to JIT as extra symbols). This is a pipeline-to-worker data flow, not shared mutable state — compile_unit writes, codegen reads. It belongs on pipeline core because:

1. It is populated during pipeline stage 2f, which is definitively pipeline work.
2. Codegen reads it but does not modify it.
3. In Step 11 (concurrent codegen), worker threads will receive a snapshot/reference of platform_symbols — they will not own or modify it.

The same logic applies to `interactive`: pipeline core owns it, `codegen_and_execute` reads it to choose code path.

### `compile_checked_program` and GOT state

`compile_checked_program` is a method on `CompilationSession` (pipeline.rs line 826) that directly accesses `self.got_state`. After decomposition, this becomes `self.inmem_worker.got_state`. Since `compile_checked_program` is called from `compile_and_execute_interactive` (which is called from `codegen_and_execute`), this is correct — it is codegen-side code accessing codegen-side state. The method should either move to `InMemWorkerState` or take `&mut InMemWorkerState` as a parameter. Moving it is cleaner since it also calls `compile_and_register_defn` which needs the same state.

### Structural notes

1. **Sub-structs are fields, not traits.** `InMemWorkerState` and `ObjectWorkerState` are plain structs with `pub` fields, stored as `pub inmem_worker: InMemWorkerState` and `pub object_worker: ObjectWorkerState` on `CompilationSession`. No trait abstraction, no accessor methods beyond what Rust field access provides. The flush methods take `&mut self` on `CompilationSession` and reach through to `self.inmem_worker` / `self.object_worker`. This is the simplest change that delivers the organizational benefit.

2. **`codegen_and_execute` signature stays as-is.** It takes `&mut CompilationSession` and reaches into both worker states. Splitting its signature to take `(&mut InMemWorkerState, &mut ObjectWorkerState, &PipelineCore)` would be premature — it creates an interface that will change again in Step 11 when worker states move to threads. Accept the `&mut CompilationSession` signature for now.

3. **The verification criterion "compile errors if compile_unit_inner directly accesses worker state fields" is NOT achievable with sub-structs alone.** Sub-struct fields on a `pub` struct are still accessible to any code with `&mut CompilationSession`. The real enforcement is that `compile_unit_inner` takes `&mut CompilationSession` and the code review verifies it only accesses pipeline core fields and queues. This is a convention, not a type-system guarantee, and that is acceptable for Step 7. Type-system enforcement arrives at Step 11 when worker state is physically on different threads.

### Approved with conditions

1. Group v1-only fields into `V1State` sub-struct in the same sprint.
2. `compile_checked_program` and related methods that access `got_state` must move to take `&mut InMemWorkerState` as a parameter (or become methods on `InMemWorkerState`), so the boundary is visible in signatures.
3. Do NOT change `codegen_and_execute`'s signature to take split references. Keep `&mut CompilationSession`.
4. Sprint verification: `cargo test` passes, `cargo clippy` clean, and `grep -n 'inmem_worker\|object_worker' src/pipeline_v2.rs` shows zero hits inside `compile_unit_inner` / `load_dependencies` (only inside `codegen_and_execute` and below).

## Skill Plans

### /int
**Task**: Decompose CompilationSession into pipeline core + worker states
**Design doc**: `design/arch/pipeline-v3-roadmap.md` Step 7
**Approach**: Option (a) per /arch review — sub-structs on CompilationSession, convention-based boundary. Group v1 fields into V1State. Move compile_checked_program to take &mut InMemWorkerState. Keep codegen_and_execute signature as &mut CompilationSession.
**Acceptance**: `cargo test` passes, boundary verified ✓

### /qa
**Task**: Verify test suite passes
**Acceptance**: 1533 passed, 11 pre-existing sketch_port failures ✓

### /review
**Task**: Review implementation
**Acceptance**: No Blocker findings ✓ (0B, 1I, 3S — I1 deferred with rationale)

### /arch
**Task**: Review proposal, decide on the codegen_and_execute coupling (accept vs refactor)
**Acceptance**: Review written

### /repl, /frontend, /typecheck, /backend, /platform, /stdlib, /examples, /docs, /port
**Task**: No work this sprint

## Waves

### Wave 1: Implementation
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Define sub-structs, update all access sites | done | InMemWorkerState (4), ObjectWorkerState (5), V1State (5) |
| /review | Review implementation | done | 0B, 1I, 3S — boundary verified |

### Wave 2: Verification
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Verify tests | done | 1533 passed, 11 pre-existing sketch_port |

## Notes

- The 24-field `CompilationSession` is the largest struct in the codebase. Decomposition improves readability and makes ownership clear.
- The `codegen_and_execute` coupling (called from within `compile_unit` via load_dependencies and auto-prelude) is the key design question. The roadmap says "compile_unit can only access pipeline core fields and queues" but the current recursive loading pattern violates this.
- `batch_jit`, `func_sigs`, `batch_compiled_fns`, `cached_symbols`, `linker` are v1 fields used only by v1 pipeline functions (`compile_module_graph` chain). They could go into a separate `V1State` group, but that may be premature since they'll be deleted in Step 14.
- `platform_symbols` is accessed by both compile_unit (during platform loading in stage 2d) and codegen_and_execute (passed to JIT). It straddles the pipeline/worker boundary.

## Outcome

### Delivered

**Step 7 — Decompose CompilationSession:**
- `InMemWorkerState` (4 fields): got_state, jit_modules, traced_fns, trace_extra_symbols
- `ObjectWorkerState` (5 fields): cache_state, cache_writer, compiled_o_paths, compiled_module_structures, cross_module_func_sigs
- `V1State` (5 fields): batch_jit, func_sigs, batch_compiled_fns, cached_symbols, linker
- Pipeline core (10 fields) stays on CompilationSession: tc, expander, compile_stack, lib_dirs, project_root, scheduling_registry, platform_symbols, loaded_platforms, interactive, queues
- All access sites updated across pipeline.rs, pipeline_v2.rs, main.rs, repl/*.rs, tests
- Boundary verified: compile_unit_inner and load_dependencies do NOT reference worker sub-struct fields

### Deferred

- **`compile_checked_program` signature refactoring** (I1): /arch condition 2 asked for this method to take `&mut InMemWorkerState` as a parameter. Not done because the method also needs `self.tc`, `self.platform_symbols`, and calls `self.compile_and_register_defn` which needs the full session. Splitting requires restructuring the call chain. The method is codegen-side code (called from codegen_and_execute path) so the boundary convention is not violated — it just accesses worker state through `self.inmem_worker` instead of through a parameter. Acceptable until Step 11 when type-system enforcement arrives.

### Findings

- Option (a) (partial separation with convention-based boundary) works well. The grep verification is clean — zero worker state references in compile_unit_inner/load_dependencies.
- V1State grouping was valuable — it makes immediately visible which fields are legacy and will be deleted in Step 14.
- `platform_symbols` on pipeline core was the right call — it's write-once (stage 2f) read-many (codegen), a clean data flow boundary.
