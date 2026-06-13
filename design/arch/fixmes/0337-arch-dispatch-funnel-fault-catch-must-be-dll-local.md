---
number: 0337
target: /arch
filed_by: /sprint
filed_at: 2026-06-13
sprint_filed: 81
refers_to: design/arch/fixmes/0327-arch-fault-guarded-dispatch-funnel-boundary.md (STEP-4 FINDING), design/arch/bounded-contexts.md §4b invariant 14 + §5 invariant 9, crates/cranelisp-platform/src/lib.rs (CLIO::effect / call_effect_thunk), crates/cranelisp-intrinsics/src/io_guard.rs, platforms/boom (repro fixture), tests/platform_errors.rs::platform_dispatch_error_carries_fn_name (ignored repro)
status: open
---

# Dispatch-funnel fault catch must be DLL-local — host `catch_unwind` cannot cross the cdylib panic-runtime boundary

## Issue (the S81 W-G step-4 finding — funnel plumbing landed, closing gap exposed)

The fault-guarded FFI-dispatch funnel (ruling 0327) was implemented across S81 W-G in
four steps. Steps 1-3 LANDED GREEN and are correct:

- **Step 1** `aeff79d` (/platform) — `IO_TAG_EFFECT` node widened to 32 bytes, field-3
  (fn-name handle) at node offset 40, `ABI_VERSION` 3→4.
- **Step 2** `d1949fb` (/backend) — bakes the cranelisp FQ fn-name (NUL-terminated
  C-string) at the `DefKind::PlatformEffect` arm + stamps field-3 post-call.
- **Step 3** `f0d25dc` (/dev int+intrinsics) — the intrinsics trampoline guards the
  Effect force (`catch_unwind` + `sigsetjmp` + SIGSEGV/FPE/ILL/BUS) and reads field-3;
  int composes `PlatformError::DispatchError { fn_name, cause, location }`.
- **Step 4** `45ea8f8` (/qa+/platform) — authored the `platforms/boom` fault fixture +
  the e2e `tests/platform_errors.rs::platform_dispatch_error_carries_fn_name`, **but
  the e2e ABORTS (exit 134) instead of surfacing `DispatchError`** — so it stays
  `#[ignore]`'d and FIXME 0327 stays OPEN.

**Root cause (verified, `nm`-confirmed):** the step-3 guard wraps the force in the
**host's** `std::panic::catch_unwind`. A real platform DLL is a `cdylib` that statically
links its **own** copy of the Rust panic runtime (`rust_begin_unwind` /
`rust_eh_personality` are defined locally in `libcranelisp_<name>.so`). A `panic!` inside
the DLL unwinds with the DLL's runtime; crossing the `dlopen` boundary into the host's
`catch_unwind` is a **foreign exception → `"Rust cannot catch foreign exceptions"` →
process abort**. A Rust null-deref also aborts (non-unwinding null-check panic) before
any SIGSEGV reaches the sigsetjmp handler. The step-3 io_guard unit tests passed only
because their panicking thunks run in the **host** crate (one shared runtime) — a
structural blind spot of in-process unit testing for a cross-DLL mechanism.

The field-3 plumbing, backend bake, int compose, and slot protocol are ALL correct and
need no change. The gap is solely **where the fault is caught**.

## Proposed resolution (the /arch boundary question)

The two-layer model (intrinsics captures, int composes) must gain a **DLL-local catch**
layer, OR adopt an unwind-capable ABI. /arch to rule between (and refine BC §4b inv 14 /
§5 inv 9 accordingly):

- **Option A — DLL-local catch + cross-C-ABI fault signal.** `cranelisp_platform::CLIO::effect`
  (or `call_effect_thunk`) wraps the thunk invocation in a **DLL-local** `catch_unwind`,
  converts a caught panic to a C-ABI fault signal returned ACROSS the boundary (sentinel +
  out-param, since the DLL links its OWN copy of `cranelisp-platform`'s thread-locals — it
  CANNOT directly set the host intrinsics error slot). The host trampoline reads the
  sentinel and sets the dispatch-fault slot (step-3 machinery, unchanged from there on).
  Crux to design: the fault-signal channel across the C boundary (the DLL's TLS ≠ host's TLS).
- **Option B — `extern "C-unwind"` ABI** for the thunk-invocation call chain
  (thunk → `call_effect_thunk` → trampoline force site) so a panic unwind propagates across
  the FFI boundary and the host `catch_unwind` CAN catch it. Simpler surface but pulls the
  whole chain onto `C-unwind` and inherits Rust's `C-unwind` caveats; SIGSEGV/signal faults
  still need the sigsetjmp half (which works once it's actually reached).
- Likely a **combination**: `C-unwind` (or DLL-local catch) for panics + the existing
  sigsetjmp/signal half for hard faults, with the null-deref-aborts-first behaviour
  addressed.

Whichever: ABI implications (another `ABI_VERSION` bump?), the TLS-across-boundary fault
channel, and which crate owns the DLL-local catch are cross-surface (platform + backend +
intrinsics) → /arch rules, then /platform + /backend implement, then /qa un-ignores the
repro.

## Repro (committed, durable)

`platforms/boom` (scalar-only platform; `crash :: (Fn [] (IO Int))` whose forced thunk
`panic!`s) + `tests/platform_errors.rs::platform_dispatch_error_carries_fn_name` (`--run`,
asserts the baked FQ name `platform.boom/crash`, currently `#[ignore]`'d because it aborts
the runner). Reproduce: `CRANELISP_PLATFORM_PATH=target/debug cranelisp --run` a program
that imports `platform.boom/crash` and calls it → abort 134.

## Operational implication / Context

The funnel's plumbing is de-risked and green (3/4 steps). This is the precisely-diagnosed
remaining gap — the S81 Phase-2 review named the funnel the "likeliest single-item slip";
genuine-zero-skips was a stretch goal, not a hard gate. Carries to a focused
/arch-ruling-then-implement follow-up. FIXME 0327 stays OPEN (its STEP-4 FINDING section
mirrors this); 0289 item 5 stays OPEN; the lone suite skip remains (1277/0/1).
