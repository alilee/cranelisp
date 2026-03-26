# Sprint 27: Pipeline Switchover

**Status**: COMPLETE
**Ring**: — (structural)
**Goal**: Complete the v2 pipeline switchover — `compile_unit()` becomes the single entry point for all compilation. Delete all v1 orchestration code.

## Context

Sprint 26 completed Steps 1-3 of the v1→v2 adapter strategy. During sprint planning, `/arch` completed the design for Steps 4-5 in `design/arch/pipeline-v2.md` §8. The design was refined through user review to:
- Recognise two production callers only (`--run` and REPL)
- Make `compile_unit()` recursive (imports trigger module loading)
- Eliminate the separate module graph discovery/topo-sort mechanism
- Accommodate future parallel codegen via `PipelineDepth`
- Remove `compile_and_run()` from the design (test helper only)

Implementation of Steps 4a-4d was attempted and succeeded (all tests passing), but the remaining v1 paths (trace/run-tests, `build_check_for_backend`, `load_module_into_session`, `--link`) needed design work before migration. Without that design, agents began adding data structures and making ad-hoc decisions. The code changes were reverted and `/arch` produced prescriptive design for all remaining paths (§15).

## Outcome

### Delivered

**Design (the sprint's durable output):**

- `design/arch/pipeline-v2.md` **§8 rewritten** — unified two-caller model (--run and REPL), recursive `compile_unit()`, `PipelineDepth` accommodation for future parallel codegen, convergence diagram, prescriptive Steps 4a-4d and 5a-5d with acceptance criteria
- `design/arch/pipeline-v2.md` **§15 added** — "Remaining v1 Paths" covering 5 secondary paths: trace/run-tests in REPL (GOT swap as pre/post concern), `build_check_for_backend()` elimination (both copies are no-ops), `load_module_into_session()` replacement, `--link` (legitimately separate path sharing stages 1-5), `compile_and_run()` test helper (thin wrapper)
- Sprint 26 added to `sprints/ROADMAP.md`

**Implementation knowledge gained (reverted but informing future work):**

- Steps 4a-4d were implemented and verified green (1531 passed, 11 failed baseline held)
- Step 4a: `compile_unit()` extended to `&str`, all 7 stages, recursive loading, cycle detection — worked
- Step 4b: REPL routed through `compile_unit()` — worked, but trace/run-tests needed fallback to v1
- Step 4c: `--run` routed through `compile_unit()` — worked, prelude used v1 batch path for performance
- Step 4d: Bind chain analysis moved inside `compile_unit()` — mechanical, worked
- Step 5: Blocked — none of the target functions were dead because secondary paths still used them
- The secondary paths then required ad-hoc design decisions by agents, violating the design-first principle

### Deferred

- **Steps 4a-4d implementation** — design is complete, implementation was proven feasible but reverted for clean re-execution with all paths designed
- **Step 5 cleanup** — requires all paths migrated first
- **11 failing sketch_port tests** — stage implementation bugs, not pipeline bugs

### Findings

1. **Design-first validated again.** Steps 4a-4d succeeded because §8 was prescriptive. The secondary path migration failed because §15 didn't exist yet. Agents adding `traced_fns`/`trace_extra_symbols` fields to `CompilationSession` without architectural review is exactly the kind of ad-hoc decision that creates structural debt.

2. **Partial migration is worse than no migration.** With main paths on v2 and secondary paths on v1, the system has more complexity than either pure state. The correct approach is to migrate everything in one pass, with all paths designed upfront.

3. **`--link` is legitimately different.** §15.4 confirms that `--link` (executable generation) needs its own orchestration path — it requires object file output, direct inter-module calls, and whole-graph visibility. It shares stages 1-5 with `compile_unit()` but not stages 6-7. This is a genuine architectural difference, not a migration gap.

4. **Prelude loading is a performance bottleneck.** The Step 4c attempt found that interactive mode (per-function JIT) is too slow for the 27-module stdlib. The v1 batch path (shared JIT, direct calls) completes in ~1s vs ~3min. This is a real constraint that the v2 design must accommodate.

5. **`build_check_for_backend()` is a no-op.** §15.2 confirms both copies are mechanical field clones with two overrides that are unnecessary in v2. Safe to delete once callers are migrated.

### Test baseline (unchanged)

1528 passed, 11 failed (sketch_port), 0 ignored, 0 clippy.
