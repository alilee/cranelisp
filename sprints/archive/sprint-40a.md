# Sprint 40a: Pipeline v3 — Parallel compile_unit and N-Core Codegen

**Status**: CANCELLED
**Ring**: — (structural / performance)
**Goal**: Complete the pipeline v3 vision: parallel `compile_unit` (`&self`), producer-consumer codegen queues with N-core worker pools, dissolve `ReplSession`, north-star `main.rs` matching pipeline-v3.md §2.2 verbatim.

## Context

Sprint 40 delivered the structural foundation — file consolidation, API alignment, atomic GOT, shared ISA, cache-hit loading, module locks, RwLock registries, one `main.rs`. Two capabilities were deferred because `compile_unit` requires `&mut self`:

1. **Parallel dependency typechecking** — independent deps can't fork because Rust's borrow checker prevents multiple `&mut CompilationSession`
2. **N-core codegen dispatch** — infrastructure ready (atomic GOT, shared ISA, CodegenPacket) but actual dispatch still uses a single coordinator thread

The root cause is `compile_unit` taking `&mut self`. The fix requires two refactorings: `check()` on TypeChecker becomes `&self` (CheckState as local), then `compile_unit` becomes `&self` (Mutex/RwLock on shared session fields). With `&self`, parallel calls and producer-consumer queues become possible.

**All skills MUST read these documents:**
- `design/arch/pipeline-v3.md` — the target (especially §2.2 main, §6 queues, §6.5 producer-consumer, §7.4 watcher)
- `design/arch/sprint-40a-design.md` — the detailed implementation design for this sprint

## Scope

### A. North-Star main.rs

Rewrite `src/main.rs` to match pipeline-v3.md §2.2 **verbatim**. Methods not yet implemented get `todo!()` bodies. Each wave fills in a `todo!()`. This is the structural test — if the control flow doesn't compile, the design has a gap.

### B. check() becomes &self

Remove `state: CheckState` field from TypeChecker. `check()` creates `CheckState` as a stack local, passes it through all internal methods. `set_current_module` eliminated — replaced by `ensure_module_exists` + module identity in `CheckState`. REPL additive overloads reconstructed from symbol table.

### C. compile_unit becomes &self

Wrap `CompilationSession` shared fields in Mutex/RwLock. Move `compile_stack` to a parameter. `compile_unit` takes `&self`. All internal functions (`compile_unit_inner`, `load_dependencies`, `try_cache_hit_load`) take `&CompilationSession`.

### D. Producer-consumer codegen

Replace the coordinator+channel pattern with shared concurrent queues and N-core worker pools. `compile_unit` pushes `CodegenItem` to queues and returns. Workers drain continuously. `hot_flush` is a barrier. See sprint-40a-design.md Part 2.

Cache-hit loading enqueues `CodegenItem::FromCache` — workers load `.o` files, not `compile_unit`.

### E. Parallel dependency loading

In `load_dependencies`, independent cache-miss deps fork into parallel `compile_unit` calls via `std::thread::scope`. Each thread pushes codegen items to the shared queue. Workers drain concurrently.

### F. Dissolve ReplSession

Move `process_commands`, `spawn_file_watcher`, `trampoline`, `link`, `pretty_print_form` to `CompilerSession`. Delete `ReplSession` wrapper. REPL loop inlines in main per §2.2. Delete `enable_persistence`, `try_restore_user_module`.

Watcher codegen exclusion: `pause_watcher_codegen` / `resume_watcher_codegen` around the REPL eval window ensures GOT stability during execution.

## Design Reference

All implementation details are in `design/arch/sprint-40a-design.md`. Skills must read it.

## Waves

### Wave 0: North-star main.rs
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Rewrite main.rs to match §2.2 verbatim. `todo!()` for unimplemented methods. | pending | |

**Acceptance**: `cargo build` succeeds. main.rs matches §2.2 structurally. `todo!()`s are explicit.

### Wave 1: check() becomes &self
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /typecheck | Remove `state` field. `check()` creates local CheckState. All ~30 methods get `cs: &mut CheckState`. `ensure_module_exists` replaces `set_current_module`. REPL additive overloads from symbol table. `check()` → `&self`. | pending | Largest wave |

**Acceptance**: `cargo test` passes. `check()` takes `&self`. REPL additive works.

### Wave 2: compile_unit becomes &self
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Wrap session fields in Mutex/RwLock per design §1.5. `compile_stack` → parameter. `compile_unit` → `&self`. All internal functions → `&CompilationSession`. | pending | |

**Acceptance**: `cargo test` passes. `compile_unit` takes `&self`.

### Wave 3: Producer-consumer codegen + parallel deps
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Implement `CodegenQueue` (Mutex+Condvar+AtomicBool+AtomicUsize). `CodegenItem` enum (FromSource/FromCache). Worker pools (`spawn_hot_inmem_codegen`, `spawn_nice_object_codegen`). `enqueue_codegen` replaces `send_codegen`. `hot_flush_*` as barriers. Delete coordinator. Parallel fork in `load_dependencies`. `pause_watcher_codegen`/`resume_watcher_codegen`. | pending | |
| /backend | Verify `Jit::new_with_isa` works correctly in worker threads. Advise on `Linker` thread safety for `FromCache` path. | pending | |

**Acceptance**: `cargo test` passes. Multi-module compilation uses parallel codegen. Workers drain queue continuously. `--run`, `--link` work.

### Wave 4: Dissolve ReplSession
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Move `process_commands`, `spawn_file_watcher`, `trampoline`, `link`, `pretty_print_form` to CompilerSession. Delete ReplSession. Delete `enable_persistence`, `try_restore_user_module`. REPL loop inline in main. Fill in remaining `todo!()`s. | pending | |

**Acceptance**: `cargo test` passes. No `ReplSession`. REPL works via inline loop. `main.rs` has no `todo!()`s. All 13 v3 invariants hold.

### Wave 5: Verification + showcase
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Tests for parallel compile_unit, concurrent queue, lock contention. | pending | |
| /review | Thread safety review of all concurrent code. | pending | |
| /arch | Update pipeline-v3-roadmap.md. Archive pipeline-v2.md. | pending | |
| /repl | Sprint demo. | pending | |
| /stdlib | Validate 27 modules with parallel pipeline. | pending | |
| /examples | Validate all examples. | pending | |
| /port | Validate exemplar. | pending | |

## Notes

This sprint completes the pipeline v3 vision. At completion: one `main.rs` matching §2.2, no `ReplSession`, `compile_unit` takes `&self`, N-core producer-consumer codegen, parallel dependency loading, GOT-stable REPL evaluation.

## Outcome

### CANCELLED

Sprint 40a cancelled by user decision. Partial work from Waves 1-3 committed but incomplete — build is broken. Moving forward from Sprint 41.

### Delivered (partial, uncommitted wave 3 work in-progress)
- Wave 1: `check()` takes `&self`, CheckState as local (committed: c01fc67)
- Wave 2: `compile_unit` takes `&self`, session fields behind Mutex/RwLock (committed: c054789)
- Wave 3 partial: CodegenItem enum, CodegenQueue, barrier, old coordinator deleted (committed: 9e74fe9)
- Pipeline v4 design doc (committed: f9bf152)
- Additional uncommitted wave 3 work (broken build state)

### Deferred
- N-core codegen worker pools
- Parallel dependency loading
- ReplSession dissolution
- Verification and showcase
