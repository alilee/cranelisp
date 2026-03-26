# Sprint 28: Pipeline Switchover (Implementation)

**Status**: COMPLETE
**Ring**: — (structural)
**Goal**: Execute the v2 pipeline switchover. `compile_unit()` becomes the single compilation entry point. All v1 orchestration code deleted. `.o` files written on every compilation.

## Outcome

### Delivered

**compile_unit() as the unified pipeline:**
- `compile_unit()` takes `&str` source text, owns all 7 stages (parse → extract → expand → build AST → typecheck → codegen → execute)
- Recursive module loading via `session.lib_dirs` with cycle detection
- Bind chain analysis (auto IO scheduling) inside compile_unit() between stages 4 and 5

**Production paths through compile_unit():**
- `--run` via `run_batch_v2()` — prelude + entry file + all dependencies through compile_unit()
- `--link` via `compile_for_link_v2()` — compilation through compile_unit(), .o generation via CacheWriter
- `compile_and_run()` test helper — thin wrapper around compile_unit() (449 call sites unchanged)

**CodegenTarget enum (§8.4):**
- `JitAndCache` — JIT to memory + background .o write (REPL, --run)
- `ObjectOnly` — .o to disk only (--link, future)
- Added to `CompileContext` — all construction sites updated

**CacheWriter background .o generation (§16):**
- Stage 6b in compile_unit() — queues background .o write after JIT codegen
- Background writer thread with channel, supersession detection, nice priority
- `flush_cache_writes()` for --link to await completion
- Session state: `cache_state`, `compiled_o_paths`, `compiled_module_structures`, `cross_module_func_sigs`

**Dead code cleanup:**
- `build_check_for_backend()` deleted (both copies — was a no-op adapter)
- `compile_for_link()` (v1) deleted
- `compile_module_graph_for_cache()` deleted
- `compile_form()`, `process_and_build_program()`, `compile_mono_defns()` deleted
- `collect_prelude_module_paths()` deleted
- ~650 lines removed total

**Design (Sprint 27 + 28):**
- `design/arch/pipeline-v2.md` §8 rewritten — two-caller model, recursive compile_unit, prescriptive Steps 4a-4d + 5a-5d
- §15 added — 5 remaining v1 paths designed
- §16 added — cache and .o generation with CodegenTarget, CacheWriter, per-scenario design
- `io_platform_non_entry_module_error` test updated — was passing for wrong reason (missing extraction in v1)

### Deferred

**REPL migration to compile_unit():**
Three attempts were made and reverted. The REPL's display formatting, session persistence, and trace handling are deeply coupled to the v1 eval chain (eval_sexp → eval_flattened_forms → execute_* methods). Each agent attempt replicated this logic incorrectly, breaking e2e tests. The REPL remains on v1 for this sprint. A careful, incremental migration is needed — likely form-by-form rather than wholesale replacement.

**Remaining v1 code (kept because of live callers):**
- `compile_module_graph()`, `discover_module_graph()`, `toposort()` — 20+ test callers
- `load_module_into_session()`, `load_prelude_into_session()` — REPL callers
- `compile_single_module()`, `compile_graph_only()`, `compile_module_graph_cached()` — called by above
- All REPL v1 eval chain methods — still the production REPL path
- Batch JIT infrastructure (`compile_module_batch`, `ensure_batch_jit`, etc.) — called by v1 chain

**11 failing sketch_port tests** — stage implementation bugs, not pipeline bugs

### Findings

1. **REPL migration is the hardest part.** The REPL's result display, slash command introspection data, session persistence, and trace GOT-swap are tightly coupled to the v1 eval chain. Migrating requires understanding and replicating ~15 post-compilation concerns. Agents consistently get the display formatting wrong, breaking e2e tests.

2. **Agent concurrency on the same file is destructive.** The Wave 2 REPL agent and Wave 3 cleanup agent both edited `src/repl/mod.rs`. The cleanup agent overwrote the REPL migration, requiring a third attempt that also failed. Rule: never run two agents on the same file.

3. **Background .o generation works.** The CacheWriter design (channel + writer thread + supersession + nice priority) is clean and tested. Stage 6b integrates naturally into compile_unit().

4. **No premature performance workarounds.** The --run path initially used v1 batch prelude loading "for performance." This was rejected — all paths use compile_unit(). Performance tuning comes later.

5. **The compiler is the best dead code auditor.** An agent spent 114 turns grepping for callers. The compiler catches missing references instantly. Delete aggressively, let cargo check tell you what's needed.

### Test baseline

19 OK suites, 11 sketch_port failures (unchanged). 0 ignored. 0 clippy warnings.
