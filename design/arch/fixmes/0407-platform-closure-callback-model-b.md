---
number: 0407
target: /arch
filed_by: /arch
filed_at: 2026-06-18
sprint_filed: 86
refers_to: design/arch/platform-interface.md §3a, exemplar/plan-exemplar.md §"Two IO Models" (Model B), crates/cranelisp-platform/src/lib.rs (HostCallbacks), crates/cranelisp-intrinsics/src/io.rs (call_continuation)
status: open
---

# Platform-model GAP: a platform DLL cannot call back into a cranelisp closure (Model B)

## Issue

The web-platform review (S86 Wave E, `platform-interface.md §3a`) surfaced a
genuine platform-model gap. The exemplar's **Model B** serve form —
`serve port handler`, where the platform DLL owns the accept loop and calls
back into a cranelisp closure `(Fn [Request] (Option Response))` once per
request — is **not buildable on the current platform interface.**

Calling a cranelisp closure from native code IS established as-built, but
**only inside `cranelisp-intrinsics`** (`io::call_continuation` `io.rs:405`;
`ivar.rs:137`; `session_v4.rs:4778`): load `code_ptr` from the heap closure,
transmute to `extern "C" fn`, call with the env pointer. The **platform crate's
public surface exposes none of this**:

- no `CLClosure` / `CLFn` wrapper type for a cranelisp-function parameter;
- no `HostCallbacks` method to invoke a passed-in closure;
- a platform fn taking `(Fn [...] ...)` receives a raw `i64` with no host-side
  calling support, no RC discipline for the captured closure across the FFI
  boundary, and no error-slot ferry for a panic inside the callback.

This is consistent with the deliberate FFI-safety boundary (`test-discovery.md`:
closure-calling is confined to intrinsics so thread-locals, RC, and the error
slot are managed where they live; the platform crate is kept minimal). The gap
is real, not an oversight — but it blocks Model B.

S86 ships **Model A only** (`listen`/`accept`/`send` + a TCO `serve-loop` in
cranelisp), which is fully buildable and serves the complete showcase roundtrip.
Model B's only added value is the "purity enables concurrency" teaching moment,
which is documentation, not a required capability — so the deferral costs the
S86 showcase nothing.

## Proposed resolution

When a future sprint wants Model B (platform-owned concurrent loop), extend the
platform interface with a host-mediated closure-call capability:

1. A `CLClosure` (or `CLFn`) wrapper type — likely in `cranelisp-platform`, a
   `#[repr(transparent)]` handle over the heap closure pointer, with the FQ
   `(Fn [..] ..)` identity for marshaling, mirroring `CLAdt<T>`.
2. A new `HostCallbacks` method, e.g. `invoke_closure(c: CLClosure, args…) -> i64`,
   **wired host-side in `cranelisp-intrinsics`** (the existing `call_continuation`
   mechanism is the implementation), with a defined contract for:
   - **capture / RC**: how the closure is retained for the lifetime the DLL holds
     it (the `serve` loop holds the handler across many calls) and released on
     `serve` return;
   - **error-slot ferry**: a panic inside the callback must propagate sanely to
     the joining thread — note this intersects the standing fork-join error-slot
     ferry obligation recorded against `test-discovery.md`;
   - **threading**: if the DLL calls the (pure) handler from a thread pool, the
     RC/error-slot contract must hold across threads.
3. `ABI_VERSION` bump (3 → 4) for the new `HostCallbacks` field (bump freely
   pre-1.0, per q-callbacks-shrinkage).
4. Manifest/sig support is unchanged — `serve`'s sig already names a `(Fn …)`
   parameter; the gap is purely the host-side calling machinery.

This is a `/dev platform` + `/dev` intrinsics change (+ `/arch` for the
`HostCallbacks` ABI extension + `cranelisp-types` if `CLClosure` lands there),
not a language-feature task.

## Operational implication / Context

- **Not blocking S86.** Model A is sufficient and buildable. This is a recorded
  future extension, filed so the gap is legible and not rediscovered from scratch.
- The `shapes` ADT-platform path proves everything the web platform needs for
  Model A (ADT marshaling, schema, layout-hash, GOT-indirect dispatch, blocking
  Sequential effects). Model B is the *only* unbuilt piece.
- When actioned, this is the natural place to also resolve the standing fork-join
  error-slot ferry obligation for the callback boundary (cross-reference
  `test-discovery.md`).
