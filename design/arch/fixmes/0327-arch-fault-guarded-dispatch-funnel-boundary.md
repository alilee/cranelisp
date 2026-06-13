---
number: 0327
target: /arch
filed_by: /design (platform)
filed_at: 2026-06-13
sprint_filed: 81
refers_to: design/platform/platform.md §9a, crates/cranelisp-intrinsics/src/io.rs:192, crates/cranelisp-platform/src/lib.rs:679 §707, crates/cranelisp-types/src/error.rs:261, src/expander.rs:494, design/arch/fixmes/0289-qa-platform-interface-e2e-walks.md (item 5), design/arch/bounded-contexts.md §4b §5 §6
status: open
---

# Ratify the fault-guarded FFI-dispatch funnel boundary — guard placement + fn-name plumbing + DispatchError construction path

## Issue

S81 carries the **fault-guarded FFI-dispatch funnel** — the feature that gives
`PlatformError::DispatchError { fn_name }` (defined at `cranelisp-types/src/error.rs:261`,
no live construction site) its first producer and retires the lone suite skip
(`tests/platform_errors.rs::platform_dispatch_error_carries_fn_name`, FIXME 0289 item 5).

The mechanism (design: `design/platform/platform.md §9a`): a platform fn returns a
`CLIO::effect(thunk)` (all platform fns return `IO _` per FIXME 0318); the intrinsics IO
trampoline forces it via an **unguarded** `cranelisp_platform::call_effect_thunk(thunk_ptr)`
(`crates/cranelisp-intrinsics/src/io.rs:192`). A fault in foreign code (Rust panic or
SIGSEGV/SIGFPE/SIGILL/SIGBUS) currently has no path to a structured `DispatchError`. The
funnel wraps that call site with an `invoke_jit_protected`-style guard
(`src/expander.rs:494` — `catch_unwind` + `sigsetjmp`/signal handlers +
`take_runtime_error()`) and surfaces `DispatchError { fn_name, cause, location }`.

This **spans three components** (`/platform` + int/`/backend` + `/qa`) and needs an `/arch`
boundary ruling before `/dev` implements, per root `CLAUDE.md` §"Cross-Skill Changes" +
§"Cross-skill defect handoff also requires minimal repro" (the boundary, not the symptom,
is what the handoff names).

## Proposed resolution

`/design (platform)` recommends; `/arch` ratifies (or amends) and lands the BC text:

1. **Guard placement → the intrinsics IO trampoline** (`io.rs:192`), NOT `call_effect_thunk`
   and NOT each platform fn. One guard covers every platform fn in every mode; the trampoline
   is intrinsics-owned (BC §4b — runtime cadence host). `call_effect_thunk` stays a thin
   reclaim primitive in `cranelisp-platform` (the contract crate owns no cadence). Cites
   Principle 7 (single force site) + Principle 6 (one guard, not per-DLL).

2. **fn-name plumbing → Option A (widen the `IO_TAG_EFFECT` node with a fn-name coordinate),
   baked at the `DefKind::PlatformEffect` dispatch arm** (backend GOT-indirect arm, BC §3 —
   the symbol is statically known at codegen, baked as a relocated `&'static` Symbol/string,
   same data-symbol family as the trace `DisplayDescriptor`). The trampoline's own comment
   (`io.rs:169-183`) records that it has *no back-reference to the symbol* — this is the crux.
   Option B (thread-local "current platform fn") is **rejected** (stale under Bind/Par deferred
   force). Cost: `ABI_VERSION` 3→4 (cheap pre-1.0). **Confirm the ABI bump is acceptable** or
   direct Option B.

3. **Construction/surfacing path → two-layer (intrinsics captures, int composes).**
   Intrinsics' guard captures the fault (signal/panic/slot message) + fn-name and returns a
   fault outcome (sentinel + `set_runtime_error`, or a small intrinsics-internal struct); **int
   composes `PlatformError::DispatchError` at its existing runtime-error surface boundary**
   (`Sess::format_error` / IO-run) and wraps via `CranelispError::Platform`. Mirrors
   `invoke_jit_protected` (intrinsics sets the slot; int reads + composes). Keeps diagnostics
   in int (BC §6) and the cadence-coupled guard in intrinsics (BC §4b — diagnostics-free by
   charter). `cranelisp-types` is unchanged (`DispatchError` already exists).

4. **Land the BC text** the ruling implies: BC §4b (intrinsics gains the dispatch-guard
   responsibility on the trampoline), BC §5 (platform — `CLIO::effect*`/Effect-node ABI change
   + `ABI_VERSION` 3→4 + `call_effect_thunk` stays unguarded reclaim), BC §3 (backend bakes the
   fn-name at the platform dispatch arm), BC §6 (int composes `DispatchError`).

## Operational implication / Context

Gates the S81 platform wave's 0289-item-5 closure (the last skip). Flagged Phase-2 as the
likeliest single-item slip; genuine-zero-skips is a stretch goal, not a hard gate. The
fork-join error-slot ferry (BC §4b invariant 13) shares the thread-local error slot — confirm
no new race (platform Effects force on the trampoline's own joining thread, so the own-thread
-slot-reader property the ferry already relies on holds; flag for implementer confirmation,
not believed a new hazard). Public-API touches: `cranelisp-platform` baseline (Effect-node /
`CLIO::effect*` + `ABI_VERSION`); possibly `cranelisp-intrinsics` (fault-outcome surface).
