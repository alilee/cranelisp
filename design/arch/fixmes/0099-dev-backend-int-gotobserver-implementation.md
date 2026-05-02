---
number: 0099
target: /dev
filed_by: /arch
filed_at: 2026-05-02
sprint_filed: 64
refers_to: design/arch/facades/backend.md §"GOT-population observation (extension point)", crates/cranelisp-backend/src/, src/got_trace/ (new), design/arch/decisions/0040-runtime-trace-io-trace-relocate-to-int.md, design/arch/decisions/0041-compile-to-module-per-symbol-jit-direct-writes.md
status: open
---

# Implement GotObserver: backend exposes contract; int implements ring buffer

## Issue

Resolves the implementation work surfaced by FIXME 0094 (GOT-slot population log). `/arch` chose option B (ring buffer + observer callback) over option A (Introspection extension) because:

- The project's existing observability mechanisms (`io_trace` in runtime, `scheduler_trace` in `src/observability.rs`) both use per-thread `VecDeque` ring buffers with FIFO overflow + env-var activation. GOT-slot population events fit the same shape.
- Introspection (per Decision 38) is for per-symbol *current state* (source, sexp, clif_ir, disasm, code_size). Adding `Vec<GotEvent>` to it would be the only place Introspection holds an accumulating event list — diverges from established pattern.
- Decision 40's `IoObserver` callback contract is the canonical pattern for cross-crate observability extension points. GotObserver mirrors it directly.

The facade is now pinned (`facades/backend.md` §"GOT-population observation"). This FIXME tracks the implementation.

## Proposed resolution

**Phase 1 — `cranelisp-backend`** (`/dev` narrow to backend):

1. Land the observer contract in `crates/cranelisp-backend/src/got_observer.rs` (parallel to runtime's `io_observer.rs` post-Decision-40):
   - `GotEventTag` enum (variants: `JitWrite`, `LinkerWrite`, `Redefinition`, `#[non_exhaustive]`)
   - `GotEvent` struct with `module`, `symbol`, `slot`, `ptr`, `provenance: GotProvenance`
   - `GotProvenance` enum: `Jit { jit_addr: usize }` | `Linker { linker_addr: usize }`
   - `GotObserver` fn type
   - `register_got_observer(observer: Option<GotObserver>)`
2. Wire `compile_to_module`'s `write_code` site to invoke the observer (with relaxed-load null check; no-op if unregistered) emitting a `JitWrite` event.
3. Wire `Linker::load_object`'s slot-population loop to invoke the observer emitting `LinkerWrite` events.
4. Wire REPL redefinition (entry replacement in symbol table) to emit `Redefinition` events. Note: redefinition currently happens via `SymbolTable::write_code` overwriting existing code; the GOT-slot atomic swap is the load-bearing event. Backend's `write_code` site can detect "is this a redefinition?" by checking whether the entry already had a `Code::Jit` before the call.

**Phase 2 — `src/` (int, integration layer)** (`/dev` narrow to int):

1. Create `src/got_trace/` parallel to `src/io_trace/` (post-Decision-40 relocation):
   - Per-thread `VecDeque<GotEvent>` ring buffer with FIFO overflow (matching `io_trace`'s capacity convention or smaller — GOT events are coarser than IO events).
   - Env-var activation: `CRANELISP_GOT_TRACE=1` enables the observer. Also enabled when REPL/trace mode is on.
   - `flush_to_stderr` formatter for end-of-session dump (parallel to `io_trace`).
   - `record(tag, event)` is the registered observer fn.
2. Int's session startup registers the observer when activated:
   ```rust
   if shared.introspection.is_some() || env::var("CRANELISP_GOT_TRACE").is_ok() {
       cranelisp_backend::register_got_observer(Some(int::got_trace::record));
   }
   ```
3. Production batch (`--link`, non-trace `--run`) does NOT register and pays one relaxed null-check load per call site.

## Sequencing notes

- Phase 1 (backend) is prerequisite for Phase 2 (int).
- Bundles naturally with Decision 40 / FIXME 0098-Phase 4 work (int's observability folder restructure post-relocation).
- No dependency on FIXME 0098 (the multi-crate ResolutionGap migration) — independent work that can land in any sprint after Decision 41's per-symbol JIT lands.

## Operational implication / Context

This is the third instance of the project's consistent observability pattern (alongside `io_trace` and `scheduler_trace`). Future incident response on a GOT-slot bug (a Decision 31 reclaim regression, a cross-module call hitting a stale slot, a pre-S58-style silent-NULL category that returns) will have a structured log to compare against runtime call failures. Current state remains queryable via `ModuleEntry::Def.code` + `Linker::get_symbol`; this adds the time-ordered event history.
