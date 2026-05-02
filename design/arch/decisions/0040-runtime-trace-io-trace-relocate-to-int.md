---
number: 0040
title: `trace.rs` and `io_trace.rs` relocate to int; runtime keeps an `IoObserver` callback contract; BC §4 unchanged
status: operative
---

# 0040 — `trace.rs` and `io_trace.rs` relocate to int; runtime keeps an `IoObserver` callback contract; BC §4 unchanged

`trace.rs` and `io_trace.rs` (~1700 LOC of dev-tooling currently hosted in `cranelisp-runtime`) relocate to int. The runtime crate keeps a small (~50 LOC) `IoObserver` callback contract as the trampoline-side extension point for IO-state observation. The `(trace ...)` GOT-swap orchestration moves to int as ordinary integration-layer work — the same shape as any other GOT installation. `bounded-contexts.md` §4's exclusion of "diagnostics, tracing, observability" from runtime's scope is correct as written; the implementation drift is corrected by relocation, not by BC revision.

## Shape

**Runtime defines** the IO observation taxonomy and registration API as an extension point (parallel to the existing `register_alloc_callback` host-callback pattern):

```rust
// crates/cranelisp-runtime/src/io_observer.rs (new, ~50 lines)
pub enum IoTraceTag { TrampolineEnter, PureStep, PlatformEffect, ContPop, /* … */ }
pub enum IoTracePayload { /* same variants as today, moved here */ }
pub type IoObserver = fn(IoTraceTag, &IoTracePayload);
pub fn register_io_observer(observer: Option<IoObserver>);
pub fn trace_anchor() -> &'static Instant;  // shared monotonic anchor (kept here)
```

The ~17 inline `record_event(tag, payload)` calls in `crates/cranelisp-runtime/src/io.rs` swap to invoke the registered observer with a relaxed-load null check — no-op if unregistered. `--link` binaries pay one relaxed null-check load per call site (one conditional branch after optimisation); zero ring-buffer or formatter cost.

**Int implements** all observer state and trace orchestration:

- `src/trace/` (new) absorbs `(trace ...)` special-form compilation, slash-command handlers, frame stack, ADT marshaling, and the wrapper machinery currently in `crates/cranelisp-runtime/src/trace.rs`.
- `src/io_trace/` (new) absorbs ring buffers, thread-local buffers, env-var filter parser, panic hook, `flush_to_stderr`, formatter, dump, and merge-sort currently in `crates/cranelisp-runtime/src/io_trace.rs`.
- Int's session startup (REPL mode or `--run` with `CRANELISP_IO_TRACE=1`) calls `runtime::register_io_observer(Some(int::io_trace::record))`. Production batch (`--link`, non-trace `--run`) does not register.

`TRACE_ANCHOR` stays in runtime exposed via `trace_anchor() -> &'static Instant`. The accessor in runtime preserves the merge-sort coordination story (int's scheduler trace and the IO trace use the same monotonic origin) without forcing a callback round-trip per anchor lookup.

## Why relocation, not BC revision

The original `runtime.md` §10 framing leaned BC-revision (admit "diagnostics, observability" inside the runtime BC). That direction reverses on the orchestration-vs-runtime-semantics distinction:

- **Orchestration** is one-time setup performed by int (the GOT swap that installs trace wrappers). It happens once, before execution; after the swap, runtime is just runtime, dispatching through whatever GOT it has.
- **Runtime semantics** is what the program does once running, dispatching through the post-swap GOT. The runtime crate is for things programs need at runtime: builtins, RC primitives, the IO trampoline, the heap.

Diagnostic *orchestration* and diagnostic *consumer state* are int concerns. The runtime side reduces to a small extension-point API (callback registration + event taxonomy) that lets the trampoline emit events to whatever observer int has registered. The BC is correct as written; the implementation has drifted; relocation closes the drift.

## Consequences

- `crates/cranelisp-runtime/src/trace.rs` deleted; `src/trace/` in int absorbs the orchestration + wrapper machinery.
- `crates/cranelisp-runtime/src/io_trace.rs` deleted; `src/io_trace/` in int absorbs ring buffers, panic hook, formatter, dump, merge-sort.
- `crates/cranelisp-runtime/src/io_observer.rs` new (~50 lines): `IoTraceTag`, `IoTracePayload`, `IoObserver` type, `register_io_observer`, `trace_anchor`.
- `crates/cranelisp-runtime/src/io.rs` ~17 inline calls swap from `io_trace::record_event` to invoking the registered observer.
- `crates/cranelisp-runtime/src/lib.rs` (facade) public surface gains the observer API; `facades/runtime.md` documents it as extension-point surface (NOT diagnostics).
- `bounded-contexts.md` §4 unchanged.
- `IoTraceTag` and `IoTracePayload` enums move with the API to runtime — they ARE the callback's type contract; they belong where the trampoline lives.
- Net runtime LOC reduction: ~1700. Runtime focus tightens to running-program needs plus host-callback extension points.
- `--link` binaries: zero IO-trace overhead (no observer registered).
- REPL/dev `--run`: int's startup registers the observer; user-visible behaviour unchanged.

## Cross-references

- Aligned with the existing `register_alloc_callback` host-callback pattern — runtime defines the contract, host implements.
- §2.12 (runtime facade silences on operator + RC primitives) stays applicable: `dec_shallow_io` and operator primitives remain in scope; the scope tightening is just losing the diagnostic modules.
- Sprint 63 substance-scoping resolution §1.1.

## Rationale

- Principle 1 (decoupling) — int's diagnostic concerns no longer drag runtime.
- Principle 2 (narrow interfaces) — runtime's observation surface is ~50 lines.
- Principle 3 (dependency direction unchanged) — int → runtime stays the only edge.
- Principle 7 (single source of truth) — diagnostic state has one home, in int.

## Canonical location

`crates/cranelisp-runtime/src/io_observer.rs` (new contract); `src/trace/` and `src/io_trace/` (new in int). Owner of contract: `/arch`. Owner of relocated code: `/dev` (runtime) builds the observer module and deletes the old; `/dev` (int) absorbs and registers.
